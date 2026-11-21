# SPDX-License-Identifier: Apache-2.0
"""Original publisher for the approved Capped DKP ledger.

  ingest    copy an addon export (journal + character rows) into the private ledger folder
  verify    re-check the ledger; --replay-addon replays it through the addon rules
  site      write a static public page plus standings.json, history.json and the guild logo
  render    rebuild the full guild page from published standings/history JSON (public repository)
  announce  print new events, or post them to a Discord webhook with --send

Only `announce --send` uses the network, and only to the webhook in DISCORD_WEBHOOK_URL. The URL is
never accepted on the command line and never printed. Nothing here touches the game, SavedVariables,
Git or Raid-Helper, and no command runs unless you invoke it. Community data (Raid-Helper sign-ups,
Wowhead item names and the refreshed Armory roster) is fetched separately by capped_dkp_community.py.

The public pages show player names, DKP balances, raiding class/spec with its raid role, and awarded
loot by design. They never show BattleTags, Discord IDs, Discord names, free-text notes, disciplinary
findings or who recorded, checked or approved an event. Those stay in the private ledger, which this
tool reads in full so that the public page can still be checked against it.
"""

import argparse
import base64
import hashlib
import html
import json
import math
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path

_TOOLS = str(Path(__file__).resolve().parent)
if _TOOLS not in sys.path:
    sys.path.insert(0, _TOOLS)

import capped_dkp_ledger as store  # noqa: E402
from capped_dkp_ledger import IntegrityError, RemoteError, ToolError  # noqa: E402

STANDINGS_FORMAT = "capped-dkp-public-standings"
HISTORY_FORMAT = "capped-dkp-public-history"
CURSOR_FORMAT = "capped-dkp-announce-cursor"
SITE_VERSION = 1
WEBHOOK_VARIABLE = "DISCORD_WEBHOOK_URL"
WEBHOOK_PATTERN = re.compile(
    r"https://(?:(?:ptb|canary)\.)?(?:discord|discordapp)\.com/api/webhooks/[0-9]{17,20}/[A-Za-z0-9_-]{16,128}")
DEFAULT_USERNAME = "Capped DKP Ledger"
USER_AGENT = "CappedDKP-Publisher/1.0"
TIMEOUT_SECONDS = 30
MESSAGE_LIMIT = 1900
LINE_LIMIT = 300
FIELD_LIMIT = 80
NAME_LIMIT = 120
SUMMARY_LIMIT = 200
RECENT_EVENTS = 250
CURSOR_BYTES = 4096

# Records that hold private identities, disciplinary findings, and how the guild organises its members:
# categories, teams, officer role lists, guild-rank and role mappings, rank reads that sync those roles,
# designated membership characters and manual rank checks. All are counted in history.json ("omitted")
# without saying which kind they were, and never shown on the page or in Discord. A penalty's effect on a
# balance stays visible in the standings; the finding behind it does not. A player's current Full/Trial
# status stays in the standings; the administration behind it does not. A run's team is not copied either
# (it is not in FIELDS).
IDENTITY_KINDS = frozenset({"battletag", "discord", "discordname"})
DISCIPLINARY_KINDS = frozenset({"misclaim", "penaltyappeal", "appealfile"})
ORGANISATION_KINDS = frozenset({
    "category", "team", "teamretire", "teammember",
    "roles", "rankmap", "rolemap", "guildrefresh", "membership", "verifyrank",
})
PRIVATE_KINDS = IDENTITY_KINDS | DISCIPLINARY_KINDS | ORGANISATION_KINDS
PAGE_ACTIVITY = frozenset({
    "boss", "award", "disenchant", "progression", "tradeaward", "adjust", "repair", "creditrepair", "reverse",
    "improper", "week", "depart", "returned", "policy", "adopt", "cap", "appeal", "plan", "lateplan", "farm",
    "settlecredit", "reassign", "cutover", "bank", "account", "rosteradd", "alt",
})
DISCORD_ACTIVITY = PAGE_ACTIVITY - {"account", "rosteradd", "alt"}

# Only these keys are ever copied out of an event. Free text (evidence, reason, proceeds), Discord and
# BattleTag values, spec, per-account result tables and the officers who checked or approved an event
# (checker, approval, approver) are deliberately absent.
FIELDS = (
    "character", "account", "run", "raid", "boss", "encounterName", "item", "mode", "cost", "amount",
    "action", "status", "rank", "role", "group", "method", "value", "farm",
    "start", "finish", "killed", "effective",
)
# An event's result can be the award it refers to (a reversal, for example), so only the facts that describe
# the item and its price are taken from it, never who checked or approved the original award.
RESULT_FIELDS = frozenset({"account", "item", "cost", "mode", "run", "method"})
SUMMARY_SKIPPED = frozenset({"farm", "start", "finish", "killed", "effective"})
COUNT_FIELDS = ("present", "items", "bosses", "names")

LABELS = {
    "setup": "Guild setup recorded", "roles": "Roles changed", "cap": "DKP cap changed",
    "policy": "Membership policy adopted",
    "rankmap": "Ranks mapped", "membership": "Membership changed", "guildrefresh": "Roster refreshed",
    "rolemap": "Rank roles mapped", "rotlist": "ROT list changed", "tier": "Loot guide changed",
    "classify": "Item classified", "lock": "Loot guide locked", "account": "Player added",
    "rosteradd": "Roster players added", "alt": "Alt linked", "spec": "Class or spec changed",
    "week": "Raid week started", "farm": "Farm status changed", "run": "Raid run started",
    "boss": "Boss kill confirmed", "drops": "Loot drops recorded", "drop": "Loot drop recorded",
    "dropvoid": "Loot drop voided", "open": "Loot item opened", "opendrop": "Observed drop opened",
    "claim": "Loot choice recorded", "offer": "Loot offer recorded", "pass": "Pass recorded",
    "roll": "Roll recorded", "award": "DKP award recorded", "enchanter": "Enchanter recorded",
    "disenchant": "Item disenchanted", "cancel": "Loot call cancelled", "plan": "Progression award planned",
    "lateplan": "Late progression award planned", "progression": "Progression award recorded",
    "improper": "Improper award recorded", "reverse": "Award reversed", "tradeaward": "Trade award recorded",
    "repair": "DKP repaired", "adjust": "DKP adjusted", "creditrepair": "Credit repaired",
    "depart": "Player departed", "returned": "Player returned", "appeal": "Appeal recorded",
    "adopt": "Capped DKP rules adopted", "start": "Roll call started", "rollrepair": "Roll corrected",
    "close": "Roll call closed", "verifyrank": "Guild rank verified", "matrix": "Loot matrix row published",
    "amend": "Loot matrix amended", "settlecredit": "Pending earnings released",
    "reassign": "Earning group reassigned", "shadow": "Shadow pilot started", "cutover": "Cutover declared",
    "bank": "Item banked or sold", "misclaim": "Misclaim finding recorded",
    "penaltyappeal": "Penalty appeal decided", "appealfile": "Penalty appeal filed",
    "category": "Member category set", "team": "Team created or edited", "teamretire": "Team retired",
    "teammember": "Team membership changed",
}
STATUS_TEXT = {"full": "Full member", "trial": "Trial member"}

GUILD_NAME = "Peons with Benefits"
DEFAULT_TITLE = GUILD_NAME
GUILD_SUMMARY = ("We are Peons with Benefits, a guild built on camaraderie, hard work, and good company. Inspired by "
                 "the grit of the Horde's hardest workers, we're here to fight, farm, and survive together \u2014 "
                 "and have a good time doing it.")
LOGO_FILE = "pwb-logo.png"
LOGO_ALT = "Peons with Benefits: red and parchment lettering, a crown and an orc skull"
LOGO_SIZE = (1024, 887)
WOWHEAD_ITEM = "https://www.wowhead.com/forever/item="
WOWHEAD_SCRIPT = "https://wow.zamimg.com/js/tooltips.js"
ICON_PREFIX = "https://wow.zamimg.com/images/wow/icons/small/"
ITEM_MAX = 999_999_999
LOOT_LIMIT = 200
KILL_LIMIT = 12
PUBLIC_JSON_BYTES = 64 * 1024 * 1024
RAID_DAYS = 14
MODE_LABELS = {"need": "Need", "greed": "Greed", "progression-need": "Progression", "allocation": "Allocation",
               "disenchant": "Disenchant"}
AWARD_KINDS = ("award", "progression", "disenchant", "tradeaward")
CHANGE_KINDS = ("reverse", "improper", "repair")
SPEC_KINDS = ("account", "rosteradd", "alt", "spec")
CLASSES = ("Druid", "Hunter", "Mage", "Paladin", "Priest", "Rogue", "Shaman", "Warlock", "Warrior")
CLASS_WORDS = frozenset(name.lower() for name in CLASSES)
ROLES = ("Tank", "Healer", "Melee", "Ranged")
ROLE_ICONS = {"Tank": "pwb-role-tank.png", "Healer": "pwb-role-healer.png",
              "Melee": "pwb-role-melee.png", "Ranged": "pwb-role-ranged.png"}
PAGE_ASSETS = (LOGO_FILE, *ROLE_ICONS.values())
ROLE_LABELS = {"Tank": "Tanks", "Healer": "Healers", "Melee": "Melee DPS", "Ranged": "Ranged DPS",
               "Unknown": "Unknown"}
CLASS_ROLES = {"Mage": "Ranged", "Warlock": "Ranged", "Rogue": "Melee"}
ROLE_WORDS = {
    "Tank": frozenset({"prot", "protection", "tank", "bear", "guardian", "blood", "brewmaster", "vengeance"}),
    "Healer": frozenset({"holy", "disc", "discipline", "resto", "restoration", "heal", "healer", "healing",
                         "mistweaver", "preservation"}),
    "Melee": frozenset({"fury", "arms", "rogue", "combat", "assassination", "subtlety", "ret", "retribution",
                        "enhancement", "enh", "cat", "melee", "unholy", "windwalker", "havoc"}),
    "Ranged": frozenset({"mage", "warlock", "hunter", "shadow", "balance", "moonkin", "boomkin", "elemental", "ele",
                         "fire", "arcane", "affliction", "demonology", "destruction", "marksmanship", "mm", "bm",
                         "beast", "survival", "ranged", "caster", "devastation", "augmentation"}),
}
GALLERY_LABELS = (("memory", "Memories"), ("event", "Events"), ("kill", "Raid kills"))
# The enlarged-photo viewer. The page script fills in the photo and its caption, so without one it stays closed
# and each thumbnail is a plain link to the full image.
LIGHTBOX = ('<dialog class="lightbox" aria-label="Enlarged photo">'
            '<button class="step lb-close" type="button" aria-label="Close enlarged photo">&times;</button>'
            '<button class="step lb-step lb-prev" type="button" data-step="-1" aria-label="Previous photo" hidden>'
            '&larr;</button>'
            '<button class="step lb-step lb-next" type="button" data-step="1" aria-label="Next photo" hidden>'
            '&rarr;</button><figure class="lb-figure"></figure></dialog>')
APPLY_LABELS = {"guildsofwow.com": "Apply on Guilds of WoW", "guildsforever.com": "Apply on Guilds Forever"}
# A page that knows its public address invites search engines and AI crawlers; previews without one stay unlisted.
INDEX_ROBOTS = "index, follow, max-image-preview:large"
PRIVATE_ROBOTS = "noindex, nofollow"
VERIFICATION_TOKEN = re.compile(r"[A-Za-z0-9_-]{10,100}")
PRIORITY_LABELS = {"high": "High need", "mid": "Medium need", "low": "Low need"}
# Guild ranks the public roster leaves out; matched exactly against the snapshot's rank names.
HIDDEN_RANKS = frozenset({"Side Hustle"})
LEVEL_MAX = 100
# Raid identities and boss counts match CappedDKP/Rules.lua; these are not inferred from loot drops.
RAID_INFO = {"Deeps": ("Barrow Deeps", 8), "Hyjal": ("Hyjal Summit", 13), "Onyxia": ("Onyxia's Lair", 1)}
RAID_ALIASES = {name: key for key, (name, _) in RAID_INFO.items()} | {"Mount Hyjal": "Hyjal"}
GUILD_LOGS = "https://forever.warcraftlogs.com/guild/id/833455"
RAIDER_CHARACTER = "https://forever.raider.io/characters/eu/pvp/"
# Public listing checked 2026-11-16; community.json can override these facts as the guild changes.
GUILD_FACTS = {
    "language": "English", "voice": "Discord required", "raidSize": "20-player raid focus",
    "attendance": "No attendance target published",
    "atmosphere": "Friendly company, focused raids. Come prepared; new and returning players welcome.",
    "source": "https://guildsforever.com/guilds/peons-with-benefits", "updated": "2026-11-16",
}

# The only script the page runs inline: tabs, Wowhead options, local times, the carousel and the photo viewer.
# It carries no data, so its hash is fixed and the Content-Security-Policy can allow exactly this script.
INLINE_SCRIPT = (
    'window.whTooltips={colorLinks:false,iconizeLinks:false,renameLinks:true};'
    '(function(){var d=document;'
    'function still(){return !!(window.matchMedia&&matchMedia("(prefers-reduced-motion: reduce)").matches);}'
    'var nav=d.querySelector("[data-tabs]");'
    'if(nav){var tabs=Array.from(nav.querySelectorAll("[data-panel]")),'
    'panels=tabs.map(function(t){return d.getElementById(t.dataset.panel);});'
    'function target(hash){try{return d.getElementById(decodeURIComponent(hash.slice(1)));}'
    'catch(e){if(!(e instanceof URIError))throw e;console.warn("Invalid page fragment; showing Overview.");return null;}}'
    'function select(hash,scroll,focus){var el=target(hash),'
    'panel=el&&el.closest(".tab-panel"),at=panels.indexOf(panel);if(at<0)at=0;'
    'var lost=panels.some(function(p,i){return i!==at&&p.contains(d.activeElement);});'
    'panels.forEach(function(p,i){p.hidden=i!==at;tabs[i].setAttribute("aria-selected",String(i===at));'
    'tabs[i].tabIndex=i===at?0:-1;});'
    'd.dispatchEvent(new Event("guild-tab-change"));'
    'if(lost)tabs[at].focus({preventScroll:true});'
    'if(scroll==="top")window.scrollTo(0,0);'
    'else if(scroll&&el){'
    'for(var parent=el.parentElement;parent;parent=parent.parentElement){'
    'if(parent.tagName==="DETAILS")parent.open=true;}'
    'el.scrollIntoView({block:"start"});'
    'if(focus){if(!el.hasAttribute("tabindex"))el.setAttribute("tabindex","-1");el.focus({preventScroll:true});}}}'
    'nav.setAttribute("role","tablist");'
    'tabs.forEach(function(t,i){t.setAttribute("role","tab");t.setAttribute("aria-controls",panels[i].id);'
    'panels[i].setAttribute("role","tabpanel");panels[i].setAttribute("aria-labelledby",t.id);panels[i].tabIndex=0;'
    't.addEventListener("keydown",function(e){if(e.altKey||e.ctrlKey||e.metaKey)return;var at=i;'
    'if(e.key==="ArrowRight")at=(i+1)%tabs.length;else if(e.key==="ArrowLeft")at=(i+tabs.length-1)%tabs.length;'
    'else if(e.key==="Home")at=0;else if(e.key==="End")at=tabs.length-1;'
    'else if(e.key!==" "&&e.key!=="Enter")return;'
    'e.preventDefault();tabs[at].focus({preventScroll:true});tabs[at].click();});});'
    'd.addEventListener("click",function(e){var a=e.target.closest?e.target.closest("a[href^=\\"#\\"]"):null;'
    'if(!a||e.defaultPrevented||e.button||e.ctrlKey||e.metaKey||e.shiftKey||e.altKey||a.hasAttribute("download")'
    '||(a.target&&a.target!=="_self"))return;'
    'var hash=a.getAttribute("href");if(hash!=="#"&&!target(hash))return;'
    'e.preventDefault();if(location.hash!==hash)history.pushState(null,"",hash);'
    'select(hash,a.hasAttribute("data-panel")||hash==="#"?"top":"target",!a.hasAttribute("data-panel"));});'
    'function restore(){select(location.hash,location.hash?"target":"top",false);}'
    'window.addEventListener("hashchange",restore);window.addEventListener("popstate",restore);'
    'function headerSize(){d.documentElement.style.setProperty("--nav-height",nav.parentElement.offsetHeight+"px");}'
    'headerSize();if(window.ResizeObserver)new ResizeObserver(headerSize).observe(nav.parentElement);'
    'select(location.hash,false,false);if(location.hash)requestAnimationFrame(restore);}'
    'try{var f=new Intl.DateTimeFormat(undefined,{weekday:"short",day:"numeric",month:"short",hour:"2-digit",'
    'minute:"2-digit"});d.querySelectorAll("time[data-local]").forEach(function(t){'
    'var w=new Date(t.getAttribute("datetime"));if(!isNaN(w))t.textContent=f.format(w);});}catch(e){}'
    'd.querySelectorAll("[data-carousel]").forEach(function(c){'
    'var k=c.querySelector(".track"),n=c.querySelector(".carousel-nav");if(!k||!n)return;'
    'var b=n.querySelectorAll("button[data-dir]");if(b.length<2)return;'
    'function sync(){var m=k.scrollWidth-k.clientWidth;n.hidden=m<=2;'
    'b[0].disabled=k.scrollLeft<=2;b[1].disabled=k.scrollLeft>=m-2;}'
    'b.forEach(function(x){x.addEventListener("click",function(){'
    'k.scrollBy({left:k.clientWidth*.9*Number(x.getAttribute("data-dir")),behavior:still()?"auto":"smooth"});});});'
    'k.addEventListener("scroll",sync,{passive:true});window.addEventListener("resize",sync);'
    'd.addEventListener("guild-tab-change",sync);'
    'c.querySelectorAll("input[name=gf]").forEach(function(r){r.addEventListener("change",function(){'
    'k.scrollLeft=0;sync();});});sync();});'
    'd.querySelectorAll("dialog.lightbox").forEach(function(z){'
    'if(typeof z.showModal!=="function")return;'
    'var g=z.querySelector(".lb-figure"),s=z.querySelectorAll(".lb-step"),u=null;'
    'function list(){return Array.prototype.filter.call(d.querySelectorAll("a[data-zoom]"),function(a){'
    'return a.getClientRects().length>0;});}'
    'function show(a){var l=list(),m=a.querySelector("img"),c=a.parentNode.querySelector("figcaption"),'
    'p=d.createElement("img");u=a;p.src=a.getAttribute("href");p.alt=m?m.alt:"";g.textContent="";g.appendChild(p);'
    'if(c){c=c.cloneNode(true);if(l.length>1){var n=d.createElement("span");n.className="meta";'
    'n.textContent=(l.indexOf(a)+1)+" of "+l.length;c.appendChild(n);}g.appendChild(c);}'
    'for(var i=0;i<s.length;i++)s[i].hidden=l.length<2;if(!z.open)z.showModal();}'
    'function step(o){var l=list(),i=l.indexOf(u);if(i>=0&&l.length>1)show(l[(i+o+l.length)%l.length]);}'
    'd.addEventListener("click",function(e){var t=e.target,a=t.closest?t.closest("a[data-zoom]"):null;'
    'if(!a||e.button||e.ctrlKey||e.metaKey||e.shiftKey||e.altKey)return;e.preventDefault();show(a);});'
    'z.addEventListener("click",function(e){var t=e.target,b=t.closest?t.closest(".lb-step"):null;'
    'if(b)step(Number(b.getAttribute("data-step")));'
    'else if(t===z||(t.closest&&t.closest(".lb-close")))z.close();});'
    'z.addEventListener("keydown",function(e){if(e.key==="ArrowLeft")step(-1);else if(e.key==="ArrowRight")step(1);});'
    'z.addEventListener("close",function(){if(u&&u.getClientRects().length)u.focus();u=null;});});'
    '})();'
)
SCRIPT_HASH = base64.b64encode(hashlib.sha256(INLINE_SCRIPT.encode("utf-8")).digest()).decode("ascii")
CSP = ("default-src 'none'; "
       f"script-src 'sha256-{SCRIPT_HASH}' https://wow.zamimg.com; "
       "connect-src https://nether.wowhead.com https://www.wowhead.com; "
       "img-src 'self' data: https://wow.zamimg.com; "
       "style-src 'unsafe-inline' https://wow.zamimg.com; font-src https://wow.zamimg.com; "
       "frame-src 'none'; base-uri 'none'; form-action 'none'")
CSS = """\
:root{color-scheme:dark;--bg:#100f0d;--fg:#f3e5cb;--muted:#c1b49e;--line:#443a2e;--head:#211d18;--accent:#efc783;--neg:#ff9d8c;--red:#b52d20;--ember:#241411;--emberline:#66332a}
*{box-sizing:border-box}
[hidden]{display:none!important}
html{scroll-padding-top:calc(var(--nav-height,80px) + 1rem)}
body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.6 system-ui,-apple-system,"Segoe UI",sans-serif}
.wrap{max-width:76rem;margin:0 auto;padding:0 2rem 3rem}
.topbar{position:sticky;top:0;z-index:10;display:flex;align-items:center;justify-content:space-between;gap:1rem;padding:.8rem 0;border-bottom:1px solid var(--line);background:var(--bg)}
.wordmark{display:inline-flex;align-items:center;gap:.7rem;min-height:44px;font-family:Georgia,serif;font-size:1.2rem;font-weight:bold;letter-spacing:.08em;text-decoration:none}
.wordmark img{display:block;width:48px;height:auto}
.navlinks{display:flex;gap:.2rem;flex-wrap:wrap;font-size:.9rem}
.navlinks a{display:inline-flex;align-items:center;justify-content:center;min-height:44px;padding:.55rem .85rem;border-bottom:2px solid transparent;text-decoration:none;color:var(--muted)}
.navlinks a:hover{color:var(--fg);background:var(--head)}
.navlinks a[aria-selected="true"]{color:var(--accent);border-bottom-color:var(--accent);background:var(--head)}
.navlinks a:focus-visible{outline-offset:-3px}
.tab-panel{padding-top:2rem}
.tab-panel>section:first-child{margin-top:0}
.tab-panel:focus-visible{outline-offset:3px}
@media (max-width:50rem){.topbar{align-items:flex-start;flex-direction:column;gap:.2rem}.navlinks{width:100%;display:grid;grid-template-columns:repeat(3,minmax(0,1fr))}}
@media print{.topbar{position:static}.tab-panel[hidden]{display:block!important}.navlinks,.skip{display:none!important}}
.hero{display:grid;grid-template-columns:minmax(0,1.1fr) minmax(0,1fr);align-items:center;gap:2.5rem;padding:3rem 0}
h1{font:700 clamp(2.8rem,6vw,5.2rem)/1.02 Georgia,serif;margin:0 0 1.2rem;letter-spacing:-.03em}
.hero p{color:var(--muted);max-width:46ch;margin:0 0 1.5rem}
.hero .realm{color:var(--accent);font-size:.95rem;margin-bottom:1rem}
.hero-art{width:100%;max-width:32rem;justify-self:end}
.guild-logo{display:block;width:100%;height:auto}
.actions{display:flex;gap:1rem;align-items:center;flex-wrap:wrap}
.button{display:inline-flex;align-items:center;justify-content:center;padding:.7rem 1.3rem;border:1px solid #df6650;background:var(--red);color:#fff5e6;text-decoration:none;font-weight:650;min-height:44px}
.button:hover{background:#902318}
.secondary{background:transparent;border-color:var(--line);color:var(--fg)}
.secondary:hover{background:var(--head)}
.ledger-status{display:flex;align-items:center;justify-content:space-between;gap:1rem;flex-wrap:wrap;padding:1rem 1.4rem;background:var(--head);border-block:1px solid var(--line)}
.ledger-status strong{color:var(--accent);font-size:.9rem}
.lede{margin:0;color:var(--muted);font-size:.9rem}
h2{font:700 1.8rem/1.25 Georgia,serif;margin:0 0 1.2rem}
h3{font:700 1.35rem/1.3 Georgia,serif;margin:0 0 1rem}
section{margin-top:3.5rem;min-width:0}
.empty{padding:2rem;border:1px dashed var(--line);color:var(--muted);background:var(--head)}
.empty strong{display:block;color:var(--fg);font-size:1.1rem;margin-bottom:.4rem}
.empty p{margin:0}
.scroll{overflow-x:auto;border:1px solid var(--line)}
:focus-visible{outline:2px solid var(--accent);outline-offset:5px}
table{width:100%;border-collapse:collapse;min-width:30rem}
table.wide{min-width:44rem}
table.attendance{min-width:0;overflow-wrap:anywhere}
caption{text-align:left;padding:.8rem 1rem;color:var(--muted);font-size:.9rem}
th,td{padding:.8rem 1rem;text-align:left;vertical-align:top;border-top:1px solid var(--line)}
thead th{background:var(--head);font-weight:600}
tbody th{font-weight:600}
.num{text-align:right;font-variant-numeric:tabular-nums}
.neg{color:var(--neg)}
.nowrap{white-space:nowrap}
a{color:var(--accent)}
a:hover{text-decoration:underline;text-underline-offset:4px}
code{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;overflow-wrap:anywhere}
ul{padding-left:1.25rem}
li{margin:.35rem 0}
.note,.foot{color:var(--muted);font-size:.9rem}
.foot{margin-top:3rem;padding-top:1.5rem;border-top:1px solid var(--line)}
tr{scroll-margin-top:1rem}
tr:target>*{background:var(--head)}
tr:target>th{color:var(--accent)}
.share{margin-left:.4rem;color:var(--muted);text-decoration:none;font-weight:400}
.share:hover,.share:focus-visible{color:var(--accent);text-decoration:underline}
ul.chars{list-style:none;padding:0;margin:0}
ul.chars li{margin:0 0 .35rem}
.char{font-weight:600}
.spec{margin-left:.45rem;font-size:.88rem}
.pill{display:inline-block;margin-left:.45rem;padding:0 .5rem;border:1px solid var(--line);border-radius:999px;font-size:.78rem;line-height:1.6;white-space:nowrap}
.c-druid{color:#FF7C0A}
.c-hunter{color:#AAD372}
.c-mage{color:#3FC7EB}
.c-paladin{color:#F48CBA}
.c-priest{color:#FFFFFF}
.c-rogue{color:#FFF468}
.c-shaman{color:#3d8fe8}
.c-warlock{color:#8788EE}
.c-warrior{color:#C69B6D}
.role-tank{color:#9cc3ff}
.role-healer{color:#8fe39a}
.role-melee{color:#f0a868}
.role-ranged{color:#d0a8ff}
.loot summary{padding:.35rem 0;white-space:nowrap}
.loot ul{list-style:none;padding:0;margin:.2rem 0 0;min-width:15rem}
.loot li{margin:0 0 .55rem}
.meta{display:block;color:var(--muted);font-size:.85rem}
a.item{text-decoration:none;font-weight:600}
a.item:hover{text-decoration:underline;text-underline-offset:3px}
a.item img{width:18px;height:18px;margin-right:.4rem;vertical-align:-3px;border:1px solid var(--line)}
a.item.q0{color:#9d9d9d}
a.item.q1{color:#ffffff}
a.item.q2{color:#1eff00}
a.item.q3{color:#4a9eff}
a.item.q4{color:#b65cff}
a.item.q5{color:#ff8000}
a.item.q6{color:#e6cc80}
a.item.q7{color:#00ccff}
.carousel-bar{display:flex;flex-wrap:wrap;align-items:center;justify-content:space-between;gap:1rem;margin-bottom:1rem}
.gallery-filters{display:flex;flex-wrap:wrap;gap:.6rem}
.gallery-filters input{position:absolute;width:1px;height:1px;margin:0;opacity:0}
.gallery-filters label{display:inline-flex;align-items:center;min-height:44px;padding:0 1.1rem;border:1px solid var(--line);color:var(--muted);cursor:pointer}
.gallery-filters label:hover{color:var(--fg);border-color:var(--muted)}
.gallery-filters input:checked+label{color:var(--fg);background:var(--head);border-color:var(--accent)}
.gallery-filters input:focus-visible+label{outline:2px solid var(--accent);outline-offset:3px}
.carousel-nav{display:flex;gap:.6rem;margin-left:auto}
.step{width:44px;height:44px;border:1px solid var(--line);background:var(--head);color:var(--fg);font:inherit;font-size:1.1rem;cursor:pointer}
.step:hover:not(:disabled){border-color:var(--accent);color:var(--accent)}
.step:disabled{opacity:.4;cursor:default}
.track{display:grid;grid-auto-flow:column;grid-auto-columns:minmax(15rem,21rem);gap:1rem;margin:0;padding:0 0 1rem;list-style:none;overflow-x:auto;overscroll-behavior-x:contain;scroll-snap-type:x mandatory}
.slide{margin:0;scroll-snap-align:start;background:var(--head);border:1px solid var(--line)}
.slide figure{margin:0}
.slide img{display:block;width:100%;height:auto;aspect-ratio:4/3;object-fit:cover;background:var(--bg)}
.slide figcaption{padding:.8rem 1rem 1rem}
.kill{display:flex;flex-direction:column;justify-content:flex-end;min-height:15rem;padding:1.2rem;background:var(--ember);border-color:var(--emberline)}
.kill h3{font-size:1.6rem;margin:0 0 .4rem;overflow-wrap:anywhere}
.kill h3 a{color:var(--fg);text-decoration:none}
.kill h3 a:hover{text-decoration:underline}
.kill p{margin:0;color:var(--muted)}
.zoom{display:block;position:relative;cursor:zoom-in;color:inherit}
.zoom::after{content:"Enlarge";position:absolute;right:.6rem;bottom:.6rem;padding:.15rem .65rem;background:rgba(16,15,13,.88);border:1px solid var(--line);color:var(--fg);font-size:.78rem;line-height:1.6}
.zoom:hover::after,.zoom:focus-visible::after{border-color:var(--accent);color:var(--accent)}
.zoom:focus-visible{outline-offset:-4px}
.lightbox{position:fixed;inset:0;width:100%;height:100%;max-width:none;max-height:none;margin:0;padding:3.5rem 5rem 1.5rem;border:0;background:transparent;color:var(--fg);overflow:hidden}
.lightbox[open]{display:flex;flex-direction:column;align-items:center;justify-content:center}
.lightbox::backdrop{background:rgba(8,7,6,.98)}
html:has(.lightbox[open]){overflow:hidden}
.lb-figure{display:flex;flex-direction:column;align-items:center;gap:.9rem;max-width:100%;margin:0}
.lb-figure img{display:block;width:auto;height:auto;max-width:100%;max-height:calc(100vh - 10rem);max-height:calc(100dvh - 10rem);object-fit:contain;border:1px solid var(--line);background:var(--head);box-shadow:0 1.5rem 4rem rgba(0,0,0,.55)}
.lb-figure figcaption{padding:0;text-align:center;font:600 1.1rem/1.4 Georgia,serif}
.lb-figure .meta{font:400 .85rem/1.5 system-ui,-apple-system,"Segoe UI",sans-serif}
.lb-close,.lb-step{position:absolute}
.lb-close{top:.9rem;right:.9rem;font-size:1.5rem;line-height:1}
.lb-step{top:50%;margin-top:-22px}
.lb-prev{left:.9rem}
.lb-next{right:.9rem}
@media (prefers-reduced-motion:no-preference){.lightbox[open]{animation:lb-in .24s cubic-bezier(.16,1,.3,1)}.lightbox[open]::backdrop{animation:lb-fade .24s ease-out}}
@keyframes lb-in{from{opacity:0;transform:scale(.985)}}
@keyframes lb-fade{from{opacity:0}}
@media (max-width:40rem){.lightbox{padding:3.5rem .75rem 5rem}.lb-figure img{max-height:calc(100vh - 13rem);max-height:calc(100dvh - 13rem)}.lb-step{top:auto;bottom:.9rem;margin-top:0}}
.gallery:has(#gf-memory:checked) .slide:not(.cat-memory),.gallery:has(#gf-event:checked) .slide:not(.cat-event),.gallery:has(#gf-kill:checked) .slide:not(.cat-kill){display:none}
.raids{list-style:none;margin:0;padding:0;border-top:1px solid var(--line)}
.raids li{display:grid;grid-template-columns:11rem minmax(0,1fr) auto;gap:.3rem 1.2rem;align-items:baseline;margin:0;padding:1rem 0;border-bottom:1px solid var(--line)}
.raid-when{color:var(--accent);font-variant-numeric:tabular-nums}
.raid-title{font-weight:650;overflow-wrap:anywhere}
.raid-count{text-align:right;font-variant-numeric:tabular-nums;white-space:nowrap}
.raid-roles{grid-column:2/-1;display:flex;flex-wrap:wrap;gap:.2rem 1rem;font-size:.88rem}
.positions{display:grid;grid-template-columns:minmax(0,1.3fr) minmax(0,1fr);gap:2.5rem;align-items:start}
.openings{list-style:none;margin:0;padding:0;display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:0 2rem;border-top:1px solid var(--line)}
.openings>li{margin:0;padding:1rem 0;border-bottom:1px solid var(--line)}
.cls{display:block;font:700 1.25rem/1.3 Georgia,serif}
.openings .specs{list-style:none;margin:.4rem 0 0;padding:0;display:flex;flex-wrap:wrap;gap:.45rem 1.4rem}
.openings .specs li{margin:0;display:inline-flex;align-items:center;gap:.5rem}
.prio{display:inline-block;padding:0 .45rem;border:1px solid;font-size:.75rem;font-weight:700;letter-spacing:.08em;line-height:1.6;text-transform:uppercase}
.prio-high{background:var(--red);border-color:#df6650;color:#fff5e6}
.prio-mid{border-color:var(--accent);color:var(--accent)}
.prio-low{border-color:var(--line);color:var(--muted)}
.vh{position:absolute;width:1px;height:1px;overflow:hidden;clip-path:inset(50%);white-space:nowrap}
.ask{margin:1rem 0 0;color:var(--muted);font-size:.95rem}
.expect{padding:1.6rem;background:var(--ember);border:1px solid var(--emberline)}
.expect ul{margin:0 0 1.4rem;padding-left:1.1rem}
.expect .actions{justify-content:flex-start}
.guild-links{display:grid;grid-template-columns:1fr 1fr 1fr;gap:2.5rem;padding:2.5rem;background:var(--ember);border-block:1px solid var(--emberline)}
.guild-links ul{list-style:none;padding:0;margin:0}
.guild-links li{margin:0}
.guild-links li a{display:block;padding:.65rem 0;border-bottom:1px solid #53372e;text-decoration:none}
.guild-links li a:hover{color:#fff5e6;text-decoration:underline}
.guild-links p{color:var(--muted);font-size:.95rem}
.community .actions{display:grid;grid-template-columns:1fr;gap:.75rem}
.roster-list{list-style:none;padding:0;display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:0 2rem}
.roster-list li{margin:0;padding:.55rem 0;border-bottom:1px solid var(--line)}
.roster-list a{display:inline-block;padding:.1rem 0;font-weight:600;overflow-wrap:anywhere;text-underline-offset:3px}
.who{display:block;color:var(--muted);font-size:.85rem}
.profile-links{display:flex;flex-wrap:wrap;gap:.2rem 1rem;margin-top:.25rem;font-size:.85rem}
.profile-links a{min-height:44px;display:inline-flex;align-items:center;font-weight:400}
.guild-facts{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:0 2rem;margin:0}
.guild-facts div{padding:1rem 0;border-bottom:1px solid var(--line);min-width:0}
.guild-facts dt{color:var(--muted);font-size:.85rem}
.guild-facts dd{margin:.35rem 0 0;font-weight:600;overflow-wrap:anywhere}
.progress-list{list-style:none;padding:0;border-top:1px solid var(--line)}
.progress-list>li{padding:1rem 0;margin:0;border-bottom:1px solid var(--line)}
.progress-heading{display:flex;justify-content:space-between;align-items:baseline;gap:1rem;flex-wrap:wrap}
.progress-heading h3{margin:0}
.progress-heading p{margin:0;color:var(--muted);font-variant-numeric:tabular-nums}
.kill-records{list-style:none;padding:0}
.kill-records li{display:flex;justify-content:space-between;gap:1rem;flex-wrap:wrap;padding:.3rem 0}
.rules-intro,.rules-detail{max-width:72ch}
.rules-detail{border-bottom:1px solid var(--line)}
.rules-detail summary{font-weight:600}
.rules-detail p{margin:.4rem 0 1rem}
.rules-detail ol{padding-left:1.4rem}
@media (max-width:40rem){.guild-facts{grid-template-columns:repeat(2,minmax(0,1fr));gap:0 1rem}}
.roster-stats{padding:1.4rem;background:var(--head);border:1px solid var(--line);margin:1.5rem 0}
.roster-stats h3{font:600 .95rem/1.4 system-ui,-apple-system,"Segoe UI",sans-serif;margin:1.7rem 0 .25rem}
.roster-stats h3:first-child{margin-top:0}
.stat-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(8rem,1fr));gap:.65rem;align-items:start;margin:0;padding:0;list-style:none}
.stat-classes{grid-template-columns:repeat(5,minmax(0,1fr))}
.stat-tile{min-width:0;margin:0;border:1px solid var(--line);border-radius:.4rem;background:var(--bg)}
.stat-main{display:block;position:relative;padding:.85rem .9rem 1rem}
.stat-tile summary.stat-main{min-height:44px;margin:0;color:inherit;cursor:pointer;list-style:none}
.stat-tile summary.stat-main::-webkit-details-marker{display:none}
.stat-tile summary.stat-main::after{content:"";position:absolute;top:1.1rem;right:.95rem;width:.45rem;height:.45rem;border:solid var(--muted);border-width:0 2px 2px 0;transform:rotate(45deg)}
.stat-tile summary.stat-main:hover::after{border-color:var(--accent)}
.stat-tile details[open]>summary.stat-main::after{top:1.3rem;transform:rotate(-135deg)}
.stat-tile summary.stat-main:focus-visible{outline-offset:2px}
.stat-label{display:block;padding-right:1.2rem;font-size:.85rem;font-weight:600}
.stat-count{display:block;margin:.15rem 0 0;font-size:1.7rem;font-weight:700;line-height:1.2;font-variant-numeric:tabular-nums;color:var(--fg)}
.stat-tile img{width:32px;height:32px;object-fit:contain;vertical-align:middle;margin-right:.4rem}
.stat-bar{display:block;height:4px;background:var(--line);margin-top:.65rem}
.stat-bar span{display:block;height:100%;background:currentColor}
.stat-zero{color:var(--muted)}
.stat-neutral{color:var(--muted)}
.stat-detail{margin:0;padding:.35rem .9rem .75rem;border-top:1px solid var(--line);list-style:none;font-size:.85rem;color:var(--muted)}
.stat-detail li{display:flex;justify-content:space-between;gap:.75rem;margin:0;padding:.3rem 0}
.stat-detail strong{font-variant-numeric:tabular-nums;color:var(--fg)}
.roster-stats .note{margin:.7rem 0 0}
.roster-stats .stat-hint{margin:0 0 .7rem}
.spec-counts{display:grid;grid-template-columns:repeat(auto-fit,minmax(13rem,1fr));gap:.3rem 1.5rem;margin:.6rem 0;padding:0;list-style:none}
.spec-counts li{display:flex;justify-content:space-between;gap:1rem;border-bottom:1px solid var(--line);padding:.35rem 0;margin:0}
.spec-counts span{overflow-wrap:anywhere}
.spec-counts strong{font-variant-numeric:tabular-nums}
summary{cursor:pointer;min-height:44px;color:var(--accent);padding:.65rem 0}
.roster-stats>details>summary{margin-top:.7rem}
@media (max-width:50rem){.stat-classes{grid-template-columns:repeat(3,minmax(0,1fr))}}
@media (max-width:40rem){.roster-stats{padding:1rem}.stat-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.stat-tile img{display:block;margin:0 0 .3rem}}
.skip{position:absolute;left:1rem;top:-5rem;background:var(--fg);color:var(--bg);padding:.6rem;z-index:20}
.skip:focus{top:1rem}
@media (max-width:50rem){.hero{grid-template-columns:1fr 1fr;gap:1rem}.guild-links{grid-template-columns:1fr 1fr}.community{grid-column:1/-1}.roster-list{grid-template-columns:repeat(2,minmax(0,1fr))}.positions{grid-template-columns:1fr}}
@media (max-width:40rem){.wrap{padding:0 1rem 2rem}.topbar{align-items:flex-start;flex-direction:column;gap:.2rem}.navlinks{gap:0 1.1rem}.hero{grid-template-columns:1fr;padding:2rem 0;gap:.7rem}.hero-art{grid-row:1;max-width:20rem;justify-self:center}.hero-copy{text-align:center}.hero p{margin-left:auto;margin-right:auto}.actions{justify-content:center}.expect .button{width:100%}.guild-links{grid-template-columns:1fr;padding:1.5rem;gap:2rem}.community{grid-column:auto}.roster-list{grid-template-columns:1fr}section{margin-top:2.5rem}table{min-width:24rem}table.wide{min-width:0}th,td{padding:.5rem .6rem}.col-record{display:none}.raids li{grid-template-columns:minmax(0,1fr) auto}.raid-when,.raid-roles{grid-column:1/-1}.openings{grid-template-columns:1fr}.track{grid-auto-columns:82%}table.standings,table.standings caption,table.standings tbody{display:block;min-width:0}table.standings thead{position:absolute;width:1px;height:1px;overflow:hidden;clip-path:inset(50%);white-space:nowrap}table.standings tr{display:grid;grid-template-columns:minmax(0,1fr) auto auto;align-items:baseline;gap:.3rem 1rem;padding:.8rem 1rem;border-top:1px solid var(--line)}table.standings tr:target{background:var(--head)}table.standings tr>*{padding:0;border:0}table.standings td:nth-child(n+4){grid-column:1/-1}table.standings td[data-label]::before{content:attr(data-label);margin-right:.35rem;color:var(--muted);font-size:.8rem}}
"""

GUILD_LINKS = (
    ("Apply", (
        ("Guilds of WoW", "https://guildsofwow.com/peons-with-benefits"),
        ("Guilds Forever", "https://guildsforever.com/guilds/peons-with-benefits"),
    )),
    ("Roster & progress", (
        ("Blizzard Armory", "https://worldofwarcraft.blizzard.com/en-gb/forever/eu/armory/guild/peons-with-benefits"),
        ("Raider.IO", "https://forever.raider.io/guilds/eu/pvp/Peons%20with%20Benefits"),
        ("Warcraft Logs", "https://forever.warcraftlogs.com/guild/id/833455"),
    )),
)
DISCORD_INVITE = "https://discord.gg/Cahah6u4yZ"
ADDON_URL = "https://www.curseforge.com/wow/addons/pwb-dkp"
UPLOADER_URL = "https://github.com/Dfintz/PeonsWithBenefits/releases/latest"
PROFILE_PREFIX = "https://worldofwarcraft.blizzard.com/en-gb/forever/eu/armory/character/"
ROSTER_FILE = "pwb-roster.json"
ROSTER_BYTES = 1024 * 1024
# What capped_dkp_community.py fetch may save for a character. specChecked and signupSeen are its bookkeeping and are
# never shown; signupRole and signupSpec are the role and spec the player declared in a Raid-Helper sign-up.
ROSTER_FIELDS = frozenset({"name", "url", "level", "class", "spec", "rank", "specChecked", "signupRole", "signupSpec",
                           "signupSeen"})


def brand_asset(name):
    try:
        return (Path(_TOOLS) / name).read_bytes()
    except OSError as error:
        raise ToolError(f"Cannot read branding asset {name}: {error}") from None


def armory_roster(snapshot=None):
    """A dated, public Armory snapshot, separate from DKP membership and authority.

    Uses the given snapshot (such as the one capped_dkp_community.py fetch refreshes) or the bundled one.
    Returns the members to show, the snapshot time and how many members a hidden rank left out."""
    try:
        if snapshot is None:
            snapshot = json.loads(brand_asset(ROSTER_FILE))
        members = snapshot["members"]
        stamp = datetime.fromisoformat(snapshot["retrievedAt"].replace("Z", "+00:00"))
        if not isinstance(members, list) or not members or stamp.tzinfo is None:
            raise ValueError("no members")
        seen, shown = set(), []
        for member in members:
            name, url = member["name"], member["url"]
            if (not isinstance(name, str) or not name.strip() or len(name) > NAME_LIMIT
                    or not isinstance(url, str) or not url.startswith(PROFILE_PREFIX)
                    or not re.fullmatch(r"(?:[a-z0-9-]|%[0-9A-Fa-f]{2})+", url[len(PROFILE_PREFIX):]) or url in seen):
                raise ValueError("invalid or repeated character")
            if set(member) - ROSTER_FIELDS:
                raise ValueError(f"unknown field for {name}")
            if "level" in member and not is_whole(member["level"], 1, LEVEL_MAX):
                raise ValueError(f"level for {name}")
            if "class" in member and member["class"] not in CLASSES:
                raise ValueError(f"class for {name}")
            if "signupRole" in member and member["signupRole"] not in ROLES:
                raise ValueError(f"signupRole for {name}")
            for field in ("specChecked", "signupSeen"):
                if field in member and not is_whole(member[field]):
                    raise ValueError(f"{field} for {name}")
            for field in ("spec", "signupSpec", "rank"):
                value = member.get(field, "x")
                if not isinstance(value, str) or not value.strip() or len(value) > 40 or clean(value, 40) != value:
                    raise ValueError(f"{field} for {name}")
            seen.add(url)
            if member.get("rank") not in HIDDEN_RANKS:
                shown.append(member)
        if not shown:
            raise ValueError("every member is hidden")
    except (ValueError, KeyError, TypeError, AttributeError) as error:
        raise ToolError(f"Invalid public Armory snapshot: {error}") from None
    return shown, stamp.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M UTC"), len(members) - len(shown)


def roster_specs(standings):
    """The ledger's class/spec text by character name without its realm, skipping names that disagree."""
    found = {}
    for player in standings["players"]:
        for character, spec in (player.get("specs") or {}).items():
            key = character.rsplit("-", 1)[0].casefold()
            found[key] = spec if found.get(key, spec) == spec else None
    return {key: spec for key, spec in found.items() if spec}


def compatible_spec(text, klass):
    """A spec text that fits the Armory class, with the class added when the text lacks it. None when it names another
    class or no spec at all: a class alone says nothing about a spec, so it never substitutes for one."""
    if not text:
        return None
    named = {name for name in CLASSES if name.lower() in spec_words(text)}
    if klass:
        if named and named != {klass}:
            return None
        text = text if named else f"{text} {klass}"
    return text if spec_words(text) - CLASS_WORDS else None


def named_role(spec):
    """The raid role a spec text names, or None, including the fixed class/spec roles."""
    klass = spec_class(spec)
    if klass in CLASS_ROLES:
        return CLASS_ROLES[klass]
    tokens = spec_words(spec) - CLASS_WORDS
    named = spec_role(" ".join(tokens))
    if "survival" in tokens and klass == "Hunter":
        return "Melee"
    return named


def roster_choice(member, specs):
    """A member's spec text and raid role, shared by character details and counts.

    The first source with anything to say decides the role: the officers' ledger, then the spec or role the player
    declared in a raid sign-up, then the talent tree read from the Armory profile. Mage and Warlock are always
    Ranged, Rogue is always Melee, and Survival Hunter is Melee. The spec shown is the first source's own spec.
    A source that names another class is skipped."""
    klass = member.get("class")
    sources = ((specs.get(member["name"].casefold()), None),
               (member.get("signupSpec"), member.get("signupRole")),
               (member.get("spec"), None))
    spec, role, decided = None, None, False
    for text, declared in sources:
        text = compatible_spec(text, klass)
        spec = spec or text
        if not decided and (text or declared):
            decided, role = True, declared or (named_role(text) if text else None)
    if klass in CLASS_ROLES:
        role = CLASS_ROLES[klass]
    return spec, role


def roster_detail(member, specs):
    """Level, then a compatible spec, else the Armory class alone."""
    klass, spec = member.get("class"), roster_choice(member, specs)[0]
    parts = [f'Level {member["level"]}'] if "level" in member else []
    if spec or klass:
        parts.append(spec or klass)
    return DOT.join(parts)


def roster_breakdown(members, specs):
    """Counts over the already-filtered roster: characters by class and classes inside each raid role.
    Unrecorded or ambiguous roles stay Unknown."""
    classes = dict.fromkeys((*CLASSES, "Unknown"), 0)
    roles = dict.fromkeys((*ROLES, "Unknown"), 0)
    role_classes = {name: dict.fromkeys(classes, 0) for name in roles}
    recorded, unknown_specs = {}, 0
    for member in members:
        klass = member.get("class", "Unknown")
        spec, role = roster_choice(member, specs)
        role = role or "Unknown"
        classes[klass] += 1
        roles[role] += 1
        role_classes[role][klass] += 1
        if spec:
            key = " ".join(spec.split()).casefold()
            label, count = recorded.get(key, (" ".join(spec.split()), 0))
            recorded[key] = (label, count + 1)
        else:
            unknown_specs += 1
    return {"classes": classes, "roles": roles, "role_classes": role_classes,
            "specs": sorted(recorded.values(), key=lambda entry: entry[0].casefold()), "unknown_specs": unknown_specs}


def stat_tile(title, count, total, colour, rows, panel, icon=""):
    """One breakdown tile. A tile that counts anyone opens, without script, into its own breakdown: rows of
    (label, count, colour class) named by the panel label. An empty tile stays plain."""
    width = count * 100 / total if total else 0
    face = (f'<span class="stat-label">{icon}{esc(title)}</span><span class="stat-count">{count}</span>'
            f'<span class="stat-bar" aria-hidden="true"><span style="width:{width:.2f}%"></span></span>')
    if not count:
        return f'<li class="stat-tile {colour} stat-zero"><div class="stat-main">{face}</div></li>'
    if not rows:
        return f'<li class="stat-tile {colour}"><div class="stat-main">{face}</div></li>'
    items = []
    for label, number, css in rows:
        attribute = f' class="{css}"' if css else ""
        items.append(f'<li><span{attribute}>{esc(label)}</span><strong>{number}</strong></li>')
    return (f'<li class="stat-tile {colour}"><details><summary class="stat-main">{face}</summary>'
            f'<ul class="stat-detail" aria-label="{esc(panel)}">{"".join(items)}</ul></details></li>')


def roster_statistics(members, specs):
    stats = roster_breakdown(members, specs)
    total = len(members)
    declared = any("signupRole" in member or "signupSpec" in member for member in members)
    page = ['<div class="roster-stats">', '<h3>Classes</h3>',
            '<ul class="stat-grid stat-classes" aria-label="Classes breakdown">']
    for name, count in stats["classes"].items():
        if count or name != "Unknown":
            page.append(stat_tile(name, count, total, f"c-{name.lower()}" if name in CLASSES else "stat-neutral",
                                  (), ""))
    page += ['</ul>', '<h3>Raid roles</h3>', '<p class="note stat-hint">Select a role to see its classes.</p>',
             '<ul class="stat-grid" aria-label="Raid roles breakdown">']
    for role, count in stats["roles"].items():
        mix = [("Unknown class" if name == "Unknown" else name, number, f"c-{name.lower()}" if name in CLASSES else "")
               for name, number in stats["role_classes"][role].items() if number]
        icon = (f'<img src="{ROLE_ICONS[role]}" alt="" width="32" height="32" loading="lazy">'
                if role in ROLE_ICONS else "")
        page.append(stat_tile(ROLE_LABELS[role], count, total, f"role-{role.lower()}" if role in ROLES else "stat-neutral",
                              mix, f"{ROLE_LABELS[role]} by class", icon))
    known = total - stats["roles"]["Unknown"]
    dps = stats["roles"]["Melee"] + stats["roles"]["Ranged"]
    sources = ", then ".join(["the ledger's recorded spec",
                              *(["a role or spec declared in a raid sign-up"] if declared else []),
                              "the talent tree with the most points on the Armory profile"])
    page += ['</ul>',
             f'<p class="note">{known} of {total} characters have a known role &middot; {dps} DPS total. '
             f'Roles come from {sources}. Mage and Warlock are always Ranged, Rogue is always Melee, '
             'and Survival Hunters are Melee; other missing or ambiguous specs stay Unknown. '
             'Feral Druids do too, because Bear and Cat share a talent tree.</p>',
             '<details><summary>View spec counts</summary><ul class="spec-counts">']
    for label, count in [*stats["specs"], ("Unknown / not recorded", stats["unknown_specs"])]:
        page.append(f'<li><span>{esc(label)}</span><strong>{count}</strong></li>')
    page.append('</ul></details></div>')
    return page


def guild_sections(specs=None, roster=None, profiles=None):
    members, stamp, hidden = armory_roster(roster)
    specs = specs or {}
    ranks = " or ".join(sorted(HIDDEN_RANKS))
    left_out = f" Characters at the {esc(ranks)} rank are not listed." if hidden else ""
    page = ['<section aria-labelledby="roster"><h2 id="roster">The guild roster</h2>',
            f'<p class="note">{len(members)} characters from the public Blizzard Armory, coloured by class, with '
            f'their spec where one is known. Snapshot: {esc(stamp)}. Not a live feed or a DKP eligibility list.'
            f'{left_out} Select a name to open its Armory profile.</p>']
    page += roster_statistics(members, specs)
    page.append('<p class="note">Raider.IO profiles may not be indexed yet. Warcraft Logs opens a verified '
                'character link where supplied; otherwise it opens the guild logs, not a character profile.</p>')
    page.append(f'<details><summary>View all {len(members)} characters</summary><ul class="roster-list">')
    for member in members:
        klass = member.get("class")
        colour = f' class="c-{klass.lower()}"' if klass else ""
        detail = roster_detail(member, specs)
        logs = (profiles or {}).get(member["url"][len(PROFILE_PREFIX):], {}).get("warcraftLogs")
        links = (f'<span class="profile-links"><a href="{esc(RAIDER_CHARACTER + urllib.parse.quote(member["name"], safe=""))}" '
                 f'aria-label="Raider.IO for {esc(member["name"])}" rel="noopener noreferrer">Raider.IO &nearr;</a>'
                 f'<a href="{esc(logs or GUILD_LOGS)}" rel="noopener noreferrer" '
                 f'aria-label="{esc("Warcraft Logs for " + member["name"] if logs else "Guild logs for Peons with Benefits")}">'
                 f'{"Warcraft Logs" if logs else "Guild logs"} &nearr;</a></span>')
        page.append(f'<li><a href="{esc(member["url"])}"{colour} rel="noopener noreferrer">{esc(member["name"])}</a>'
                    + (f'<span class="who">{esc(detail)}</span>' if detail else "") + links + "</li>")
    return page + ['</ul></details></section>']


def guild_links():
    page = ['<section id="guild-links" class="guild-links" aria-label="Guild links">']
    for heading, links in GUILD_LINKS:
        page.append(f'<div><h2>{esc(heading)}</h2><ul>')
        for label, url in links:
            page.append(f'<li><a href="{esc(url)}" rel="noopener noreferrer">{esc(label)} <span aria-hidden="true">&nearr;</span></a></li>')
        page.append('</ul></div>')
    page += ['<div class="community"><h2>Meet the peons.</h2><p>Peons with Benefits on WoW: Forever. '
             'Find us, apply, or come say hello.</p>',
             '<div class="actions">',
             f'<a class="button" href="{DISCORD_INVITE}" rel="noopener noreferrer">Join our Discord &nearr;</a>',
             f'<a class="button secondary" href="{ADDON_URL}" rel="noopener noreferrer">Get the DKP addon &nearr;</a>',
             '</div><p class="note">Officers and Loot Masters: '
             '<a href="#uploader">get the desktop uploader</a> to submit saved raid and loot records.</p>',
             '</div></section>']
    return page


def uploader_section():
    return [
        '<section aria-labelledby="uploader"><h2 id="uploader">Officer uploader</h2>',
        '<p><strong>For officers and Loot Masters.</strong> The PWB DKP Uploader reads the CappedDKP addon\'s '
        'saved raid, DKP and loot records and submits them to the guild\'s private ledger for review. '
        'Approved records keep this page\'s standings and loot history up to date.</p>',
        '<p>Regular raiders do not need this tool to view standings or receive loot. '
        'It is a separate Windows desktop app, not the in-game addon.</p>',
        f'<div class="actions"><a class="button" href="{UPLOADER_URL}" rel="noopener noreferrer">'
        'Download officer uploader &nearr;</a></div>',
        '<p class="note">Windows 10 or 11 (64-bit). Opens the latest GitHub release; choose the '
        '<code>CappedDKP-Uploader-...-win64.zip</code> asset, not the source-code archives. '
        'No Git or Python installation is required.</p>',
        '<details><summary>Setup &amp; updates</summary>',
        '<p>Extract the whole ZIP and open <code>CappedDKP Uploader.exe</code>. '
        'It looks for your addon\'s SavedVariables file automatically; confirm the correct account in Settings. '
        'Ask guild leadership for the ledger settings and a guild-provided access token. '
        'Enter the token only in the desktop app, never on this public page or in public chat.</p>',
        '<p>The uploader checks for newer releases and keeps your settings and saved token when updating. '
        'Upgrading from 0.1.43.1 or earlier needs one manual update: close the app, back up its folder, replace '
        'the program files in the same location and keep your existing <code>data</code> folder unchanged. '
        'The Windows executable is not code-signed; only download releases you trust.</p>',
        '</details></section>',
    ]


_TAG = re.compile(r"\w{3,32}#[0-9]{3,8}")
_LONG_NUMBER = re.compile(r"[0-9]{17,}")
_DISCORD_STRIP = re.compile(r"[<>@]")
_DISCORD_MARKDOWN = re.compile(r"([\\*_~`|#\[\]()])")


def say(text, stream=None):
    stream = stream or sys.stdout
    encoding = getattr(stream, "encoding", None) or "ascii"
    print(text.encode(encoding, "backslashreplace").decode(encoding), file=stream)


def clean(value, limit=FIELD_LIMIT):
    """Make a journal string safe to publish: printable text only, IDs and BattleTags redacted, bounded."""
    text = "".join(ch if ch.isprintable() else " " for ch in str(value))
    text = _TAG.sub("[tag]", _LONG_NUMBER.sub("[id]", " ".join(text.split())))
    return text if len(text) <= limit else text[: limit - 3].rstrip() + "..."


def is_number(value):
    return isinstance(value, (int, float)) and not isinstance(value, bool)


def number_text(value):
    if isinstance(value, float):
        return f"{value:.2f}".rstrip("0").rstrip(".")
    return str(value)


def signed(value):
    return ("+" if value > 0 else "") + number_text(value)


def scalar(value):
    if isinstance(value, bool):
        return value
    if isinstance(value, int):
        return value if abs(value) <= store.MAX_SAFE_INTEGER else None
    if isinstance(value, float):
        if not math.isfinite(value) or abs(value) > store.MAX_BALANCE:
            return None
        return int(value) if value == int(value) else value
    if isinstance(value, str):
        return clean(value) or None
    return None


def is_whole(value, low=0, high=store.MAX_SAFE_INTEGER):
    return isinstance(value, int) and not isinstance(value, bool) and low <= value <= high


def utc_text(seconds, pattern="%Y-%m-%d %H:%M UTC"):
    try:
        return datetime.fromtimestamp(seconds, timezone.utc).strftime(pattern)
    except (OverflowError, OSError, ValueError, TypeError):
        return "unknown time"


def time_html(seconds, pattern="%Y-%m-%d %H:%M UTC"):
    """A UTC time that the page script rewrites into the reader's own time zone."""
    try:
        stamp = datetime.fromtimestamp(seconds, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    except (OverflowError, OSError, ValueError, TypeError):
        return "unknown time"
    return f'<time datetime="{stamp}" data-local>{esc(utc_text(seconds, pattern))}</time>'


def spec_words(spec):
    return set(re.findall(r"[a-z]+", spec.lower()))


def spec_role(spec):
    """The raid role a class/spec text names, or None when it names none or more than one."""
    words = spec_words(spec)
    roles = {role for role, names in ROLE_WORDS.items() if names & words}
    if "frost" in words and ("deathknight" in words or {"death", "knight"} <= words):
        roles.add("Melee")
    return roles.pop() if len(roles) == 1 else None


def spec_class(spec):
    words = spec_words(spec)
    found = [name for name in CLASSES if name.lower() in words]
    return found[0] if len(found) == 1 else None


def projected_specs(ledger):
    """Each character's current class/spec text, replayed the way the addon stores it."""
    specs = {}
    for event in ledger.events:
        data = event["data"]
        character = data.get("character")
        if event["kind"] in SPEC_KINDS and isinstance(character, str):
            text = clean(data["spec"], 60) if isinstance(data.get("spec"), str) else ""
            if text:
                specs[character] = text
            else:
                specs.pop(character, None)
    return specs


def loot_records(ledger):
    """Awarded items per account, newest first, with later reversals and corrections applied.

    Each award event's result is the award as the addon recorded it; a reversal, improper-Greed report or
    repair carries the corrected award, and a trade award reverses the award it replaces."""
    owners = {row["character"]: row["account"] for row in ledger.rows}
    records = {}
    for event in ledger.events:
        kind, data, result = event["kind"], event["data"], event.get("result")
        if not isinstance(result, dict) or not isinstance(data, dict):
            continue
        target = data.get("award")
        earlier = records.get(target) if is_whole(target, 1) else None
        if kind in AWARD_KINDS:
            item, account = result.get("item"), result.get("account")
            if not is_whole(item, 1, ITEM_MAX) or not isinstance(account, str):
                continue
            if kind == "tradeaward" and earlier is not None:
                earlier.update(cost=0, reversed=True)
            record = {"event": event["id"], "time": event["time"], "item": item, "account": account}
            if isinstance(result.get("mode"), str) and clean(result["mode"], 40):
                record["mode"] = clean(result["mode"], 40)
            cost = scalar(result.get("cost"))
            if is_number(cost):
                record["cost"] = cost
            character = data.get("character")
            if isinstance(character, str) and owners.get(character) == account and clean(character, NAME_LIMIT):
                record["character"] = clean(character, NAME_LIMIT)
            for flag in ("reversed", "corrected"):
                if result.get(flag) is True:
                    record[flag] = True
            records[event["id"]] = record
        elif kind in CHANGE_KINDS and earlier is not None:
            item = result.get("item")
            if isinstance(item, bool) or item != earlier["item"]:
                continue
            cost = scalar(result.get("cost"))
            if is_number(cost):
                earlier["cost"] = cost
            for flag in ("reversed", "corrected"):
                if result.get(flag) is True:
                    earlier[flag] = True
                else:
                    earlier.pop(flag, None)
    by_account = {}
    for record in sorted(records.values(), key=lambda entry: -entry["event"]):
        by_account.setdefault(record.pop("account"), []).append(record)
    return by_account


def boss_kills(events):
    """The newest confirmed boss kills from the public history, newest first."""
    kills = []
    for event in reversed(events):
        if event["kind"] != "boss":
            continue
        fields = event["fields"]
        name = fields.get("encounterName") or (f"Boss {fields['boss']}" if "boss" in fields else "Boss kill")
        kills.append({"id": event["id"], "time": event["time"], "name": clean(name, NAME_LIMIT),
                      "raid": clean(fields["raid"], NAME_LIMIT) if fields.get("raid") else None})
        if len(kills) == KILL_LIMIT:
            break
    return kills


def item_link(item, items):
    """A Wowhead: Forever link. Cached names show at once; otherwise the tooltip script renames the link."""
    entry = items.get(str(item)) or {}
    href = esc(f"{WOWHEAD_ITEM}{item}")
    name = entry.get("name")
    if not name:
        return f'<a class="item" href="{href}" rel="noopener noreferrer">Item #{item}</a>'
    quality = entry.get("quality")
    classes = "item" + (f" q{quality}" if is_whole(quality, 0, 7) else "")
    icon = (f'<img src="{esc(ICON_PREFIX + entry["icon"] + ".jpg")}" alt="" width="18" height="18" loading="lazy">'
            if entry.get("icon") else "")
    return (f'<a class="{classes}" href="{href}" data-wh-rename-link="false" rel="noopener noreferrer">'
            f'{icon}{esc(name)}</a>')


def linked_summary(event, items):
    """The escaped summary with its last "item N" turned into a Wowhead link."""
    text = esc(event["summary"])
    item = event["fields"].get("item")
    if not is_whole(item, 1, ITEM_MAX):
        return text
    marker = f"item {item}"
    at = text.rfind(marker)
    end = at + len(marker)
    if at < 0 or (end < len(text) and text[end].isdigit()) or (at > 0 and text[at - 1].isalnum()):
        return text
    return text[:at] + item_link(item, items) + text[end:]


def event_fields(event, runs):
    kind, data = event["kind"], event["data"]
    result = event.get("result")
    merged = {}
    for source, allowed in ((data, FIELDS), (result if kind != "boss" else None, RESULT_FIELDS)):
        if isinstance(source, dict):
            for key, value in source.items():
                if key in allowed and key not in merged:
                    merged[key] = value
    identifier = data.get("id")
    if kind in ("account", "alt") and "account" not in merged and identifier is not None:
        merged["account"] = identifier
    if kind == "run" and "run" not in merged and identifier is not None:
        merged["run"] = identifier
    fields = {}
    for key in FIELDS:
        value = scalar(merged.get(key))
        if value is not None:
            fields[key] = value
    for key in COUNT_FIELDS:
        if isinstance(data.get(key), list):
            fields[key + "Count"] = len(data[key])
    run = data.get("run")
    if kind == "boss" and "raid" not in fields and isinstance(run, str) and run in runs:
        fields["raid"] = clean(runs[run])
    return fields


def item_text(fields):
    item = fields.get("item")
    if item is None:
        return "an item"
    return f"item {item}" if is_number(item) else str(item)


def summarize(kind, label, fields):
    """One self-contained sentence per record; kinds without a dedicated sentence start with their label."""
    who = fields.get("character") or fields.get("account")
    raid, run = fields.get("raid"), fields.get("run")
    if kind == "boss":
        name = fields.get("encounterName") or (f"Boss {fields['boss']}" if "boss" in fields else "A boss")
        text = f"{name} defeated" + (f" in {raid}" if raid else "")
        return text + (f", {fields['presentCount']} present" if "presentCount" in fields else "")
    if kind in ("award", "tradeaward", "progression"):
        cost = fields.get("cost")
        parts = [fields.get("mode"), f"{number_text(cost)} DKP" if is_number(cost) else None]
        detail = ", ".join(str(part) for part in parts if part)
        return f"{who or 'A player'} received {item_text(fields)}" + (f" ({detail})" if detail else "")
    if kind == "disenchant":
        return f"{who or 'The enchanter'} disenchanted {item_text(fields)}"
    if kind == "adjust" and who and is_number(fields.get("amount")):
        return f"{who}: DKP adjusted by {signed(fields['amount'])}"
    if kind in ("depart", "returned") and who:
        return f"{who} {'departed' if kind == 'depart' else 'returned'}"
    if kind in ("account", "rosteradd") and who:
        return f"{who} added" + (" as an alt" if fields.get("action") == "alt" else "")
    if kind == "alt" and who and fields.get("account"):
        return f"{who} linked to {fields['account']}"
    if kind == "week" and is_number(fields.get("start")):
        return "Raid week starting " + utc_text(fields["start"], "%Y-%m-%d")
    if kind == "run" and run:
        return f"Run {run} started" + (f" in {raid}" if raid else "")
    if kind == "farm" and raid and isinstance(fields.get("farm"), bool):
        return f"{raid} farm status: {'on' if fields['farm'] else 'off'}"
    if kind == "cap" and is_number(fields.get("value")):
        return f"DKP cap set to {number_text(fields['value'])}"
    parts = [f"{key} {fields[key]}" for key in FIELDS if key in fields and key not in SUMMARY_SKIPPED]
    return label + (": " + ", ".join(parts) if parts else "")


def project_events(ledger):
    """Allowlisted public view of every non-private event, in journal order, plus the omitted count.

    Free-text notes and the characters that recorded, checked or approved an event are never copied."""
    runs, events, omitted = {}, [], 0
    for event in ledger.events:
        kind, data = event["kind"], event["data"]
        if kind == "run" and isinstance(data.get("id"), str) and isinstance(data.get("raid"), str):
            runs[data["id"]] = data["raid"]
        if kind in PRIVATE_KINDS:
            omitted += 1
            continue
        label = LABELS.get(kind) or "Recorded " + clean(kind, 40)
        fields = event_fields(event, runs)
        events.append({
            "id": event["id"], "time": event["time"], "kind": clean(kind, 40), "label": label,
            "summary": clean(summarize(kind, label, fields), SUMMARY_LIMIT), "fields": fields,
        })
    return events, omitted


def status_text(row):
    if row["membershipStatus"] == "legacy":
        return "Not set"
    if row["activeCap"] is None:
        return "Unverified"
    return STATUS_TEXT.get(row["membershipStatus"], "Not set")


def anchor_ids(names):
    """One fragment id per listed name, readable (p-alpha) and unique. A short hash is added only when
    the readable form is empty or shared, and a counter when even that repeats."""
    folded = [re.sub(r"[^a-z0-9]+", "-", unicodedata.normalize("NFKD", name).encode("ascii", "ignore")
                     .decode("ascii").lower()).strip("-") for name in names]
    counts = Counter(folded)
    ids, seen = [], set()
    for name, base in zip(names, folded):
        text = base if base and counts[base] == 1 else (
            base + "-" if base else "") + hashlib.sha256(name.encode("utf-8")).hexdigest()[:8]
        candidate, number = "p-" + text, 1
        while candidate in seen:
            number += 1
            candidate = f"p-{text}-{number}"
        seen.add(candidate)
        ids.append(candidate)
    return ids


def raid_attendance(ledger):
    """Public counts only: one opportunity per raid/reset, not per group, run, character or boss.

    A registered account is eligible when a recorded kill occurred during its membership. Presence at any such
    kill counts as attendance, even at the DKP cap. Wipes, bench time and unrecorded raids cannot be measured.
    Membership intervals use event times so late-entered boss records still respect joining and departure."""
    owners = {row["character"]: row["account"] for row in ledger.rows}
    windows, active, runs, kills = {}, {}, {}, []
    week = None
    for event in ledger.events:
        kind, data, stamp = event["kind"], event["data"], event["time"]
        account = owners.get(data.get("character"))
        if kind in ("account", "rosteradd") and account and account not in windows:
            windows[account], active[account] = [], stamp
        elif kind == "depart" and account in active:
            windows[account].append((active.pop(account), stamp))
        elif kind == "returned" and account in windows and account not in active:
            active[account] = stamp
        elif kind == "week":
            start, finish = data.get("start"), data.get("finish")
            week = ((start, finish) if is_whole(start) and is_whole(finish, start + 1) else None)
        elif kind == "run" and week and isinstance(data.get("id"), str) and isinstance(data.get("raid"), str):
            runs[data["id"]] = (RAID_ALIASES.get(data["raid"], data["raid"]), week)
        elif kind == "boss" and data.get("run") in runs and isinstance(data.get("present"), list):
            raid, (start, finish) = runs[data["run"]]
            killed = data.get("killed", stamp)
            if is_number(killed) and start <= killed < finish:
                present = {owners[name] for name in data["present"] if isinstance(name, str) and name in owners}
                kills.append(((start, raid), killed, present))
    for account, start in active.items():
        windows[account].append((start, math.inf))
    counts = {}
    for account, periods in windows.items():
        eligible, attended = set(), set()
        for key, killed, present in kills:
            if any(start <= killed < finish for start, finish in periods):
                eligible.add(key)
                if account in present:
                    attended.add(key)
        counts[account] = {"attended": len(attended), "eligible": len(eligible)}
    return counts


def standings_document(ledger):
    """One public row per active account. Returns the document and how many names needed cleaning."""
    accounts = {}
    for row in ledger.rows:
        accounts.setdefault(row["account"], []).append(row)
    specs, loot, attendance = projected_specs(ledger), loot_records(ledger), raid_attendance(ledger)
    players, departed, changed = [], 0, 0
    for name, rows in accounts.items():
        first = rows[0]
        if first["departed"]:
            departed += 1
            continue
        shown = clean(name, NAME_LIMIT)
        names = [clean(row["character"], NAME_LIMIT) for row in rows]
        changed += (shown != name) + sum(text != row["character"] for text, row in zip(names, rows))
        player = {
            "account": shown, "balance": first["balance"], "cap": first["activeCap"],
            "characters": sorted(names, key=lambda text: (text.lower(), text)), "status": status_text(first),
        }
        if name in attendance:
            player["attendance"] = attendance[name]
        shown_specs = {text: specs[row["character"]] for text, row in zip(names, rows) if row["character"] in specs}
        if shown_specs:
            player["specs"] = dict(sorted(shown_specs.items()))
        awarded = loot.get(name, [])
        if awarded:
            player["loot"] = awarded[:LOOT_LIMIT]
            player["lootTotal"] = len(awarded)
        players.append(player)
    players.sort(key=lambda player: (-player["balance"], player["account"].lower(), player["account"]))
    # Anchors follow the name order, not the balance order, so a player's link survives balance changes.
    by_name = sorted(range(len(players)), key=lambda at: (players[at]["account"].lower(), players[at]["account"]))
    for at, anchor in zip(by_name, anchor_ids([players[at]["account"] for at in by_name])):
        players[at]["anchor"] = anchor
    document = {
        "format": STANDINGS_FORMAT, "version": SITE_VERSION, "lastEventId": ledger.count,
        "lastEventTime": ledger.manifest["lastEventTime"], "chainHead": ledger.heads[-1],
        "departedCount": departed, "players": players,
    }
    return document, changed


def esc(value):
    return html.escape(str(value), quote=True)


def dkp_html(value):
    text = number_text(abs(value))
    return f'<span class="neg">&minus;{text}</span>' if value < 0 else text


def table(caption, headings, rows, wide=False, kind=""):
    head = "".join(
        f'<th scope="col" class="{classes}">{esc(name)}</th>' if classes else f'<th scope="col">{esc(name)}</th>'
        for name, classes in headings)
    label = esc(caption)
    style = " ".join(word for word in ("wide" if wide else "", kind) if word)
    return "\n".join([
        f'<div class="scroll" role="region" aria-label="{label}" tabindex="0">',
        f'<table class="{style}">' if style else "<table>",
        f"<caption>{label}</caption>",
        f"<thead><tr>{head}</tr></thead>",
        "<tbody>", *rows, "</tbody>", "</table>", "</div>",
    ])


def plural(count, singular, many):
    return f"{count} {singular if count == 1 else many}"


DOT = " \u00b7 "


def empty_state(heading, *lines):
    """Trusted copy only: callers escape any data they pass in."""
    return f'<div class="empty"><strong>{heading}</strong>' + "".join(f"<p>{line}</p>" for line in lines) + "</div>"


def class_name(text):
    return next((name for name in CLASSES if name.lower() == str(text).strip().lower()), None)


def characters_html(player):
    specs = player.get("specs") or {}
    lines = []
    for name in player["characters"]:
        parts = [f'<span class="char">{esc(name)}</span>']
        spec = specs.get(name)
        if isinstance(spec, str) and spec:
            klass = spec_class(spec)
            colour = f" c-{klass.lower()}" if klass else ""
            parts.append(f'<span class="spec{colour}">{esc(spec)}</span>')
            role = spec_role(spec)
            if role:
                parts.append(f'<span class="pill role role-{role.lower()}">{role}</span>')
        lines.append("<li>" + "".join(parts) + "</li>")
    return '<ul class="chars">' + "".join(lines) + "</ul>"


def loot_html(player, items):
    loot = player.get("loot") or []
    if not loot:
        return "&mdash;"
    lines = []
    for entry in loot:
        link, meta = item_link(entry["item"], items), []
        mode = entry.get("mode")
        if mode:
            meta.append(MODE_LABELS.get(mode, mode) + (" (corrected)" if entry.get("corrected") else ""))
        if is_number(entry.get("cost")):
            meta.append(f"{number_text(entry['cost'])} DKP")
        if entry.get("character"):
            meta.append(entry["character"])
        meta.append(utc_text(entry["time"], "%Y-%m-%d"))
        if entry.get("reversed"):
            link = f"<del>{link}</del>"
            meta.append("reversed")
        lines.append(f'<li>{link}<span class="meta">{esc(DOT.join(meta))}</span></li>')
    total = player.get("lootTotal", len(loot))
    if total > len(loot):
        lines.append(f'<li class="meta">+{total - len(loot)} older in history.json</li>')
    return (f'<details class="loot"><summary>{plural(total, "item", "items")}</summary>'
            "<ul>" + "".join(lines) + "</ul></details>")


def gallery_section(gallery, kills, linked):
    slides, present = [], set()
    for entry in gallery:
        date = f'<span class="meta">{esc(entry["date"])}</span>' if entry.get("date") else ""
        image = f'gallery/{esc(entry["image"])}'
        slides.append(f'<li class="slide cat-{entry["category"]}"><figure>'
                      f'<a class="zoom" href="{image}" data-zoom target="_blank" rel="noopener" '
                      f'aria-label="Enlarge photo: {esc(entry["caption"])}">'
                      f'<img src="{image}" alt="{esc(entry["alt"])}" loading="lazy"></a>'
                      f'<figcaption>{esc(entry["caption"])}{date}</figcaption></figure></li>')
        present.add(entry["category"])
    for kill in kills:
        name = esc(kill["name"])
        if kill["id"] in linked:
            name = f'<a href="#e-{kill["id"]}">{name}</a>'
        raid = f'{esc(kill["raid"])} &middot; ' if kill.get("raid") else ""
        slides.append(f'<li class="slide kill cat-kill"><h3>{name}</h3>'
                      f'<p>{raid}{time_html(kill["time"], "%Y-%m-%d")}</p></li>')
        present.add("kill")
    page = ['<section class="gallery" aria-labelledby="gallery"><h2 id="gallery">Memories, events and raid kills</h2>']
    if not slides:
        page.append(empty_state("Nothing in the gallery yet.",
                                "Raid screenshots, guild events and confirmed boss kills will appear here."))
        return page + ["</section>"]
    bar = []
    kinds = [(kind, label) for kind, label in GALLERY_LABELS if kind in present]
    if len(kinds) > 1:
        bar.append('<div class="gallery-filters" role="group" aria-label="Show in the gallery">'
                   '<input type="radio" name="gf" id="gf-all" checked><label for="gf-all">All</label>')
        bar += [f'<input type="radio" name="gf" id="gf-{kind}"><label for="gf-{kind}">{label}</label>'
                for kind, label in kinds]
        bar.append("</div>")
    bar.append('<div class="carousel-nav" hidden>'
               '<button class="step" type="button" data-dir="-1" aria-label="Previous slides">&larr;</button>'
               '<button class="step" type="button" data-dir="1" aria-label="Next slides">&rarr;</button></div>')
    return page + ['<div class="carousel" data-carousel>', '<div class="carousel-bar">' + "".join(bar) + "</div>",
                   '<ul class="track" tabindex="0" aria-label="Gallery slides">', *slides, "</ul>", "</div>",
                   *([LIGHTBOX] if gallery else []), "</section>"]


def raids_section(extras):
    community, days = extras["community"], extras["raid_days"]
    raid = community["raidHelper"] if community else None
    page = ['<section aria-labelledby="raids"><h2 id="raids">Upcoming raids</h2>']
    if extras["raid"] is None or (raid is not None and raid["status"] == "unconfigured"):
        page.append(empty_state("Raid-Helper isn't connected yet.",
                                "Upcoming raids and sign-up counts will show here once officers link the guild's "
                                "Raid-Helper server."))
    elif raid is None:
        page.append(empty_state("Sign-ups haven't been checked yet.", "The next scheduled update fills this in."))
    elif raid["status"] == "error":
        page.append(empty_state("Couldn't reach Raid-Helper on the last check.",
                                "Sign-ups are in the events channel on Discord until the next update."))
    elif not raid["events"]:
        page.append(empty_state(f"No raids scheduled in the next {plural(days, 'day', 'days')}.",
                                "New events posted in Discord appear here after the next update."))
    else:
        page.append('<ul class="raids">')
        for event in raid["events"]:
            title = esc(event["title"])
            if event.get("url"):
                title = f'<a href="{esc(event["url"])}" rel="noopener noreferrer">{title}</a>'
            roles = "".join(f'<span class="role-{role.lower()}">{role} {event["roles"][role]}</span>' for role in ROLES)
            page.append(f'<li><span class="raid-when">{time_html(event["start"], "%a %d %b, %H:%M UTC")}</span>'
                        f'<span class="raid-title">{title}</span>'
                        f'<span class="raid-count">{plural(event["total"], "sign-up", "sign-ups")}</span>'
                        f'<span class="raid-roles">{roles}</span></li>')
        page.append("</ul>")
    checked = f" Checked {time_html(raid['checked'])}." if raid and raid["checked"] else ""
    page += [f'<p class="note">Sign-ups are shown as counts by role; names stay in Discord.{checked} '
             f'<a href="{DISCORD_INVITE}" rel="noopener noreferrer">Join the Discord</a> to sign up.</p>', "</section>"]
    return page


def recruitment_status(recruitment):
    snapshot = recruitment.get("snapshot")
    if not snapshot:
        return ""
    status = snapshot["status"]
    if status == "ok":
        return "Open positions verified from the public Guilds of WoW listing."
    if status == "stale":
        return "Recruitment sync error: showing stale, last-known-good openings. Check the source before applying."
    return "Recruitment sync unavailable: manual openings below are not verified against the source."


def positions_section(recruitment):
    links = recruitment.get("apply") or [GUILD_LINKS[0][1][0][1]]
    updated = (f' Updated <span class="nowrap">{esc(recruitment["updated"])}</span>.'
               if recruitment.get("updated") else "")
    ranked = any(spec.get("priority") for opening in recruitment["openings"] for spec in opening["specs"])
    note = ("Recruitment need reflects urgency, not DKP loot priority."
            if ranked else "Roles the raid team is recruiting for.")
    page = ['<section aria-labelledby="recruiting"><h2 id="recruiting">Open positions</h2>',
            f'<p class="note">{note}{updated}</p>']
    snapshot = recruitment.get("snapshot")
    if snapshot:
        from capped_dkp_recruitment import ERRORS
        message = recruitment_status(recruitment)
        if snapshot.get("error"):
            message += " " + ERRORS[snapshot["error"]]
        checked = f" Last attempted {time_html(snapshot['checked'])}."
        verified = f" Last verified {time_html(snapshot['updated'])}." if snapshot["updated"] is not None else ""
        page.append(f'<p class="note" role="status">{esc(message)}{verified}{checked} '
                    f'<a href="{esc(snapshot["source"])}" rel="noopener noreferrer">Public recruitment source</a>.</p>')
    page.append('<div class="positions">')
    if recruitment["openings"]:
        page.append('<ul class="openings">')
        for opening in recruitment["openings"]:
            klass = class_name(opening["class"])
            colour = f" c-{klass.lower()}" if klass else ""
            specs = []
            for spec in opening["specs"]:
                level = spec.get("priority")
                tag = (f' <span class="prio prio-{level}">{PRIORITY_LABELS[level]}</span>'
                       if level in PRIORITY_LABELS else "")
                specs.append(f"<li>{esc(spec['name'])}{tag}</li>")
            page.append(f'<li><span class="cls{colour}">{esc(opening["class"])}</span>'
                        f'<ul class="specs">{"".join(specs)}</ul></li>')
        page.append("</ul>")
    else:
        if snapshot and snapshot["status"] == "error":
            page.append(empty_state("Open positions could not be verified.", "Check the public recruitment source."))
        elif snapshot and snapshot["status"] == "stale":
            page.append(empty_state("No positions in the last verified listing.", "Current openings are unknown."))
        else:
            page.append(empty_state("No open positions right now.", "Good company is always welcome; say hello on Discord."))
    page.append('<div class="expect"><h3>What we expect</h3>')
    if recruitment["expectations"]:
        page.append("<ul>" + "".join(f"<li>{esc(line)}</li>" for line in recruitment["expectations"]) + "</ul>")
    page.append('<div class="actions">')
    for at, link in enumerate(links):
        host = (urllib.parse.urlsplit(link).hostname or "").removeprefix("www.")
        label = APPLY_LABELS.get(host) or f"Apply on {esc(host)}"
        page.append(f'<a class="button{" secondary" if at else ""}" href="{esc(link)}" rel="noopener noreferrer">'
                    f'{label} &nearr;</a>')
    page += ["</div>", f'<p class="ask">Questions first? <a href="{DISCORD_INVITE}" rel="noopener noreferrer">'
             "Ask on Discord</a>.</p>", "</div>", "</div>", "</section>"]
    return page


def guild_overview(guild):
    facts = GUILD_FACTS | guild
    fields = [("Loot system", '<a href="#rules">Capped DKP</a>'),
              *[(label, esc(facts[key])) for key, label in (
                  ("raidSize", "Raid focus"), ("language", "Language"), ("voice", "Voice chat"),
                  ("attendance", "Attendance expectation"), ("atmosphere", "Atmosphere"))]]
    page = ['<section aria-labelledby="guild"><h2 id="guild">Guild at a glance</h2><dl class="guild-facts">']
    page += [f"<div><dt>{label}</dt><dd>{value}</dd></div>" for label, value in fields]
    page += ['</dl><p class="note">Our raid focus is not a limit: the loot rules cover 10-player Deeps, '
             '20-player Hyjal and 40-player Onyxia.</p>']
    if facts.get("source"):
        page.append(f'<p class="note"><a href="{esc(facts["source"])}" rel="noopener noreferrer">'
                    f'Guild listing</a> &middot; Details checked {esc(facts["updated"])}.</p>')
    return page + ["</section>"]


def progression_section(events, reports):
    """All recorded bosses, not the gallery's newest twelve or the activity table's newest 250."""
    raids = {key: {} for key in RAID_INFO}
    run_raids = {}
    for event in events:
        fields = event["fields"]
        raid = fields.get("raid")
        if event["kind"] != "boss" or not isinstance(raid, str) or not is_whole(fields.get("boss"), 1):
            continue
        key = RAID_ALIASES.get(raid, raid)
        total = RAID_INFO.get(key, (key, None))[1]
        if total and fields["boss"] > total:
            continue
        killed = fields.get("killed", event["time"])
        if not is_number(killed):
            killed = event["time"]
        bosses = raids.setdefault(key, {})
        previous = bosses.get(fields["boss"])
        if previous is None or killed > previous["time"]:
            bosses[fields["boss"]] = {
                "name": fields.get("encounterName") or f'Boss {fields["boss"]}', "time": killed}
        if isinstance(fields.get("run"), str):
            run_raids[fields["run"]] = key
    page = ['<section aria-labelledby="progress"><h2 id="progress">Raid progression</h2>',
            '<p class="note">Unique bosses in the published ledger, across all recorded resets and groups. '
            'Repeated kills count once. Missing records do not mean a boss is undefeated; this is not live '
            'Armory or Warcraft Logs progression.</p><ul class="progress-list">']
    for raid, bosses in raids.items():
        name, total = RAID_INFO.get(raid, (raid, None))
        count = (f'{len(bosses)} / {total} bosses recorded' if total else f'{len(bosses)} bosses recorded')
        page.append(f'<li><div class="progress-heading"><h3>{esc(name)}</h3><p>'
                    f'{count if bosses else "No kills recorded"}</p></div>')
        if bosses:
            page.append('<details><summary>Recorded kills &amp; reports</summary><ul class="kill-records">')
            for _, boss in sorted(bosses.items()):
                page.append(f'<li><span>{esc(boss["name"])}</span>'
                            f'<span class="meta">Last recorded {time_html(boss["time"])}</span></li>')
            page.append("</ul>")
            matched = [report for report in reports if run_raids.get(report["run"]) == raid]
            for report in matched:
                page.append(f'<p><a href="{esc(report["url"])}" rel="noopener noreferrer">'
                            f'Warcraft Logs report &middot; {esc(report["run"])}</a></p>')
            if not matched:
                page.append('<p class="note">No Warcraft Logs report linked to these runs yet.</p>')
            page.append("</details>")
        page.append("</li>")
    return page + [f'</ul><p><a href="{GUILD_LOGS}" rel="noopener noreferrer">'
                    'Browse the guild on Warcraft Logs &nearr;</a></p></section>']


def attendance_section(players):
    page = ['<section aria-labelledby="attendance"><h2 id="attendance">Recorded raid attendance</h2>',
            '<p class="rules-intro">The share of recorded raids an account attended while registered in the '
            'ledger. Each raid counts once per official weekly reset, even with multiple groups or nights. '
            'Presence at any confirmed boss kill counts; linked characters count as one account.</p>',
            '<p class="note">This is participation, not full-night attendance or a guild requirement. '
            'It excludes time before registration and while departed. Wipes, bench time, cancelled raids and '
            'unrecorded raids are not measured. Being at the DKP cap does not reduce attendance.</p>']
    recorded = [player for player in players if player.get("attendance", {}).get("eligible")]
    if not recorded:
        page.append(empty_state("Attendance is not available yet.",
                                "It appears after the ledger publishes membership, reset and boss-presence records. "
                                "No records is not 0% attendance."))
    else:
        rows = []
        for player in sorted(recorded, key=lambda value: value["account"].casefold()):
            counts = player["attendance"]
            percentage = 100 * counts["attended"] / counts["eligible"]
            rows.append(f'<tr><th scope="row"><a href="#{esc(player["anchor"])}">{esc(player["account"])}</a></th>'
                        f'<td class="num">{counts["attended"]} / {counts["eligible"]}</td>'
                        f'<td class="num">{percentage:.0f}%</td></tr>')
        page.append(table("Since each account's ledger registration; recorded raids only",
                          [("Account", ""), ("Attended / recorded", "num"), ("Attendance", "num")], rows,
                          kind="attendance"))
        if len(recorded) < len(players):
            page.append('<p class="note">Accounts without a recorded opportunity are not assigned a percentage.</p>')
    return page + ["</section>"]


def loot_rules_section():
    """Member-facing summary of the Capped DKP Loot Rules as the guild runs them, checked 2026-11-21."""
    return [
        '<section aria-labelledby="rules"><h2 id="rules">How our loot works</h2>',
        '<p class="rules-intro">One person, one DKP balance across linked characters and raids. '
        'Fixed prices, not bidding. This is a member guide: the guild\'s formal Capped DKP Loot Rules '
        'cover the details and exceptions.</p>',
        '<details class="rules-detail" open><summary>Earn DKP &amp; spend at fixed prices</summary>',
        '<p>Earn 5 DKP per boss, 10 for the final boss instead, and a 5-DKP non-farm full-clear bonus once per '
        'raid per reset. Full-clear credit requires every boss with one group. Late arrivals earn from their '
        'next kill; bench time does not earn boss credit. Credit the kill before its loot.</p>',
        '<p>Full members have a 280-DKP cap; Trials have a 100-DKP cap. Excess earnings are permanently '
        'forfeited, not saved for later. New accounts start at 0; there is no DKP decay.</p>',
        table("Fixed item prices in DKP", [("Item", ""), ("Need", "num"), ("Greed", "num")], [
            f'<tr><th scope="row">{name}</th><td class="num">{need}</td><td class="num">{greed}</td></tr>'
            for name, need, greed in (("Weapon", 100, 20), ("Trinket or tier token", 75, 15),
                                     ("All other gear", 50, 10))]),
        '<p>The Loot Master records the price from the item type when the item is opened. Losing a claim costs '
        'nothing. Resolve items in the announced loot-window order (ascending item ID if unavailable), updating '
        'balances and Need status before the next item.</p></details>',
        '<details class="rules-detail"><summary>Need: five priority groups, then highest DKP</summary>',
        '<p>Only Full members may Need, and only for the main spec of the character they are playing in the '
        'raid: items are bind on pickup, so nothing goes to an alt outside the raid. An off-spec item is Greed. '
        'Duplicate tier items are not legitimate Need. The Loot Master checks each claim and an uninvolved officer '
        'verifies the award. Use the first eligible group in this order:</p><ol>',
        '<li>Nonnegative DKP, no Need win this week, can afford the full price.</li>',
        '<li>Nonnegative DKP, no Need win this week, cannot afford the full price.</li>',
        '<li>Nonnegative DKP, already won Need this week, can afford the full price.</li>',
        '<li>Nonnegative DKP, already won Need this week, cannot afford the full price.</li>',
        '<li>Negative DKP, regardless of earlier Need wins.</li></ol>',
        '<p>Within that group, the highest current balance wins; in debt, that means the least negative. '
        'Only exact balance ties roll. Zero is nonnegative. Priority group always comes before balance.</p>',
        '<p>Ordinary Need may reach &minus;100 DKP. An item the Loot Master marks as a major upgrade when opening '
        'it may take Need down to &minus;200, never below, and keeps priority over Greed. Skip withdrawn or '
        'floor-blocked claims. A Need win lowers priority account-wide until the official weekly reset; it does '
        'not forbid another Need win. Trials cannot Need.</p></details>',
        '<details class="rules-detail"><summary>Greed, rolls &amp; unclaimed items</summary>',
        '<p>After awardable Need, resolve eligible off-spec Greed. Need-eligible items cannot be claimed as Greed. '
        'Full members resolve before Trials: affordable Full claims roll. If none can afford it, the '
        'highest-balance eligible Full claimant wins fallback, provided the charge stays at or above '
        '&minus;100; exact balance ties roll. Only if no Full award is possible do affordable Trials roll. '
        'Trials must stay at or above 0 and have no fallback. Greed never changes weekly Need status.</p>',
        '<p>Rolls use /roll 1-100 with a shared 30-second window. Winning ties reroll among the tied players. '
        'Missed claimants get one extra shared 30-second call; existing valid rolls stand. A second miss or '
        'an explicit pass withdraws the claim. Reapply priority after withdrawals.</p>',
        '<p>Never force an award. Unclaimed gear is disenchanted or vendored for the guild bank; '
        'disenchanting costs 0 and does not change Need status. Items that are not gear (tier tokens count as '
        'gear) are free and rolled among eligible claimants unless a bank rule was announced before claims.'
        '</p></details>',
        '<details class="rules-detail"><summary>Farm raids, progression exceptions &amp; safeguards</summary>',
        '<p>Farm status needs one week\'s notice. Farm raids give no full-clear bonus: halve each account\'s '
        'weekly boss-credit total for that raid and round up, crediting the increase before each loot award. '
        'Two 5-DKP bosses give +3 then +2, not +3 each. First earning group locks raid/reset credit; approved '
        'reassignment must not double-count it.</p>',
        '<p>A rare Progression Exception needs an announced encounter/role reason and approval from an '
        'uninvolved officer. Full members only: legitimate Need pays full price, may reach &minus;200 and sets '
        'Need status. A non-Need Progression Allocation pays half the Need price rounded up, may reach '
        '&minus;150 and leaves Need status unchanged.</p>',
        '<p>Improper Greed is corrected to the full Need charge and Need status through the next reset, '
        'even if that correction crosses a floor; the item is not taken back. Honest mistakes receive the '
        'correction only. Disciplinary decisions and appeals follow the formal rules; private disciplinary records '
        'are not published here.</p>',
        '<p>An uninvolved officer verifies Loot Master claims. Unknown membership is not silently treated as '
        'Trial: paid awards wait for verification and reconciliation of pending credits. The spreadsheet '
        'remains authoritative until formal addon cutover. If the addon is unavailable, the same rules and '
        'independent checks apply; if Master Loot or its equivalent is unavailable, pause for an approved process.</p>',
        '</details>',
        f'<p class="note">Summary checked 2026-11-21. Ask in <a href="{DISCORD_INVITE}" '
        'rel="noopener noreferrer">Discord</a> for the full policy and appeal process. '
        f'The guild\'s <a href="{ADDON_URL}" rel="noopener noreferrer">PWB DKP addon</a> is on CurseForge. '
        'This page does not itself enforce in-game loot.</p></section>',
    ]


def structured_data(title, site_url):
    """schema.org JSON-LD naming the guild and its official profiles. It is inert data, so the CSP need not allow it."""
    guild = f"{site_url}#guild"
    data = {"@context": "https://schema.org", "@graph": [
        {"@type": "WebSite", "@id": f"{site_url}#website", "url": site_url, "name": title, "inLanguage": "en",
         "description": GUILD_SUMMARY, "publisher": {"@id": guild}},
        {"@type": "Organization", "@id": guild, "name": GUILD_NAME, "url": site_url, "logo": site_url + LOGO_FILE,
         "description": GUILD_SUMMARY,
         "sameAs": [url for _, links in GUILD_LINKS for _, url in links] + [DISCORD_INVITE]},
    ]}
    text = json.dumps(data, ensure_ascii=True, separators=(",", ":"))
    return text.replace("&", "\\u0026").replace("<", "\\u003c").replace(">", "\\u003e")


def md_text(value):
    return re.sub(r"([\\`*_\[\]<>])", r"\\\1", " ".join(str(value).split()))


def md_url(url):
    return "".join(f"%{ord(ch):02X}" if ch in "()<> " else ch for ch in url)


def llms_text(title, site_url, pending, recruitment):
    """llms.txt (llmstxt.org): a plain-text guide to the public page for AI assistants. Public facts and links only."""
    lines = [f"# {md_text(title)}", "", f"> {md_text(GUILD_SUMMARY)}", "",
             f"{GUILD_NAME} is a Horde guild in World of Warcraft: Forever (EU). The guild page shows the open "
             "positions, the raid calendar, the roster with class and raid-role counts, a screenshot gallery and the "
             "guild's Capped DKP loot standings and history.", "", "## Guild page", "",
             f"- [{md_text(title)}]({md_url(site_url)}): the guild's home page",
             f"- [Guild at a glance]({md_url(site_url)}#guild): language, voice, raid focus and expectations",
             f"- [Loot rules]({md_url(site_url)}#rules): the Capped DKP member guide, not in-game enforcement",
             f"- [Recorded progression]({md_url(site_url)}#progress): unique bosses in the published ledger",
             f"- [Recorded attendance]({md_url(site_url)}#attendance): account participation by raid and weekly reset"]
    if not pending:
        lines += [f"- [Capped DKP standings]({md_url(site_url)}standings.json): public DKP balances and loot, as JSON",
                  f"- [Loot and DKP history]({md_url(site_url)}history.json): the public ledger records, as JSON"]
    lines += ["", "## Join", "", f"- [Discord]({DISCORD_INVITE}): questions and raid sign-ups",
              f"- [PWB DKP addon]({ADDON_URL}): the guild's DKP addon on CurseForge",
              f"- [Officer uploader]({UPLOADER_URL}): Windows desktop tool for officers and Loot Masters to "
              "submit saved addon records for review; not required for regular raiders"]
    listed = {DISCORD_INVITE}
    for link in recruitment.get("apply") or [GUILD_LINKS[0][1][0][1]]:
        host = (urllib.parse.urlsplit(link).hostname or "").removeprefix("www.")
        lines.append(f"- [{md_text(APPLY_LABELS.get(host) or f'Apply on {host}')}]({md_url(link)})")
        listed.add(link)
    status = recruitment_status(recruitment)
    if status:
        lines += ["", status]
        snapshot = recruitment["snapshot"]
        lines.append(f"Source: {snapshot['source']}; last attempt: {snapshot['checked']}; "
                     f"last verified: {snapshot['updated']}.")
    if recruitment["openings"]:
        updated = f" (updated {md_text(recruitment['updated'])})" if recruitment.get("updated") else ""
        lines += ["", f"## Open positions{updated}", ""]
        for opening in recruitment["openings"]:
            specs = ", ".join(md_text(spec["name"]) + (f" ({PRIORITY_LABELS[spec['priority']]})"
                                                       if spec.get("priority") in PRIORITY_LABELS else "")
                              for spec in opening["specs"])
            lines.append(f"- {md_text(opening['class'])}" + (f": {specs}" if specs else ""))
    lines += ["", "## Optional", ""]
    lines += [f"- [{md_text(name)}]({md_url(url)})" for _, links in GUILD_LINKS for name, url in links
              if url not in listed]
    return "\n".join(lines) + "\n"


def discovery_files(title, site_url, pending, recruitment):
    """sitemap.xml and llms.txt for the served page, plus robots.txt when the page is the root of its host: crawlers
    read robots.txt only from there, and a project page under a shared host is already allowed by its absence."""
    if not site_url:
        return {}
    files = {
        "sitemap.xml": ('<?xml version="1.0" encoding="UTF-8"?>\n'
                        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
                        f"<url><loc>{esc(site_url)}</loc></url>\n</urlset>\n").encode("utf-8"),
        "llms.txt": llms_text(title, site_url, pending, recruitment).encode("utf-8"),
    }
    if urllib.parse.urlsplit(site_url).path == "/":
        files["robots.txt"] = f"User-agent: *\nAllow: /\n\nSitemap: {site_url}sitemap.xml\n".encode("utf-8")
    return files


def render_page(title, standings, recent, omitted, source_url=None, *, pending=False, site_url=None, extras=None,
                verification=None, history_events=None):
    """Six progressively enhanced tabs; all content remains in the HTML for crawlers and no-script readers.

    With site_url the page asks to be indexed and carries its canonical address; verification is a Google
    Search Console HTML-tag token. Existing section, player and event fragments remain intact."""
    players = standings["players"]
    items = extras["items"] if extras else {}
    if standings["lastEventId"]:
        lede_text = (f'Standings after event {standings["lastEventId"]}, '
                     f'recorded {utc_text(standings["lastEventTime"])}.')
    else:
        lede_text = "No events are recorded yet."
    nav = [("overview", "Overview"), ("raids", "Raids"), ("roster", "Roster"),
           ("standings", "DKP & loot"), ("rules", "Loot rules"), ("gallery", "Gallery")]
    overview = [
        '<div class="hero" id="overview"><div class="hero-copy">',
        f"<h1>{esc(title)}</h1>", '<p class="realm">WoW: Forever &nbsp;/&nbsp; Horde &nbsp;/&nbsp; EU PvP</p>',
        f"<p>{esc(GUILD_SUMMARY)}</p>",
        '<div class="actions"><a class="button" href="#standings">View standings &rarr;</a>'
        f'<a class="button secondary" href="{DISCORD_INVITE}" rel="noopener noreferrer">Join Discord &nearr;</a></div></div>',
        f'<div class="hero-art"><img class="guild-logo" src="{LOGO_FILE}" width="{LOGO_SIZE[0]}" height="{LOGO_SIZE[1]}" '
        f'alt="{esc(LOGO_ALT)}"></div></div>',
        *guild_overview(extras.get("guild", {}) if extras else {}),
    ]
    if extras:
        overview += positions_section(extras["recruitment"])
    overview += guild_links()
    loot = [
        '<div class="ledger-status">',
        '<strong>Awaiting first publication</strong>' if pending else '<strong>Public ledger</strong>',
        f'<p class="lede">{esc(lede_text)}</p></div>',
        '<section aria-labelledby="standings"><h2 id="standings">Standings</h2>',
    ]
    if players:
        rows = []
        for player in players:
            cap = "&mdash;" if player["cap"] is None else number_text(player["cap"])
            rows.append(
                f'<tr id="{esc(player["anchor"])}"><th scope="row">{esc(player["account"])}'
                f'<a class="share" href="#{esc(player["anchor"])}" aria-label="Link to {esc(player["account"])}">#</a></th>'
                f'<td class="num" data-label="DKP">{dkp_html(player["balance"])}</td>'
                f'<td class="num" data-label="Cap">{cap}</td>'
                f'<td>{esc(player["status"])}</td><td>{characters_html(player)}</td>'
                f'<td>{loot_html(player, items)}</td></tr>')
        loot.append(table("Active players by DKP balance",
                          [("Player", ""), ("DKP", "num"), ("Cap", "num"), ("Status", ""), ("Characters", ""),
                           ("Loot", "")], rows, kind="standings"))
    else:
        loot.append(empty_state("The first standings are still to come.", "No active players are recorded yet.",
                                "DKP balances appear here after an officer-reviewed ledger is published."))
    if standings["departedCount"]:
        loot.append(f'<p class="note">{plural(standings["departedCount"], "departed player is", "departed players are")}'
                    " not listed.</p>")
    loot.append('</section><section aria-labelledby="activity"><h2 id="activity">Recent activity</h2>')
    if recent:
        rows = [
            f'<tr id="e-{event["id"]}"><td class="num"><a href="#e-{event["id"]}" '
            f'aria-label="Link to event {event["id"]}">{event["id"]}</a></td>'
            f'<td>{esc(utc_text(event["time"])).replace(" UTC", "&nbsp;UTC")}</td>'
            f'<td class="col-record">{esc(event["label"])}</td><td>{linked_summary(event, items)}</td></tr>'
            for event in recent]
        loot.append(table(f"Latest {plural(len(recent), 'public record', 'public records')}, newest first",
                          [("Event", "num"), ("When", ""), ("Record", "col-record"), ("Details", "")], rows, wide=True))
    else:
        loot.append(empty_state("Every drop has a story.", "No public records yet.",
                                "Published loot and DKP changes will appear here, newest first."))
    loot.append("</section>")
    loot += uploader_section()
    if not pending:
        loot += ['<footer class="foot ledger-footer">',
                 f'<p id="fingerprint">Ledger fingerprint: <code>{esc(standings["chainHead"])}</code>.</p>',
                 '<p>Raw data: <a href="standings.json">standings.json</a>, <a href="history.json">history.json</a>.</p>',
                 '</footer>']
    all_events = history_events if history_events is not None else recent
    raids = raids_section(extras or {"community": None, "raid": None, "raid_days": RAID_DAYS})
    raids += progression_section(all_events, extras.get("reports", []) if extras else [])
    raids += attendance_section(players)
    panels = {
        "overview": overview, "raids": raids,
        "roster": guild_sections(roster_specs(standings), extras.get("roster") if extras else None,
                                 extras.get("profiles") if extras else None),
        "standings": loot, "rules": loot_rules_section(),
        "gallery": gallery_section(extras["gallery"] if extras else [],
                                   extras["kills"] if extras else boss_kills(all_events),
                                   {event["id"] for event in recent}),
    }
    body = [
        '<!-- THESIS: one guild destination at a time, not an endless feed. '
        'OWN-WORLD: Horde red, iron charcoal, parchment type and the supplied guild crest. '
        'STORY: choose the guild overview, raid plans, roster, DKP, rules or memories. '
        'FIRST VIEWPORT: compact tab navigation above the Overview hero; other tabs begin with their content. '
        'FORM: existing Horde identity, accessible hash-linked tabs, native disclosures and one hashed script. -->',
        '<a class="skip" href="#standings">Skip to standings</a>', '<div class="wrap">',
        f'<header class="topbar"><a class="wordmark" href="#" aria-label="{GUILD_NAME}">'
        f'<img src="{LOGO_FILE}" alt="" width="48" height="42">PWB</a>',
        '<nav class="navlinks" aria-label="Guild sections" data-tabs>'
        + "".join(f'<a id="tab-{anchor}" href="#{anchor}" data-panel="panel-{anchor}">{esc(label)}</a>'
                  for anchor, label in nav) + "</nav></header>", '<main>',
    ]
    for anchor, _ in nav:
        body += [f'<div class="tab-panel" id="panel-{anchor}">', *panels[anchor], "</div>"]
    has_items = 'class="item' in "\n".join(body)
    body.append('<footer class="foot">')
    if source_url:
        body.append(f'<p>Source: <a href="{esc(source_url)}" rel="noopener noreferrer">'
                    f"{esc(urllib.parse.urlsplit(source_url).hostname)}</a></p>")
    body += [f'<p>{GUILD_NAME} &middot; WoW: Forever &middot; For the Horde.</p></footer>', "</main>",
             "</div>"]
    body.append(f"<script>{INLINE_SCRIPT}</script>")
    if has_items:
        body.append(f'<script src="{WOWHEAD_SCRIPT}"></script>')
    head = [
        "<!doctype html>", '<html lang="en">', "<head>", '<meta charset="utf-8">',
        '<meta name="viewport" content="width=device-width, initial-scale=1">',
        '<meta name="color-scheme" content="dark">', '<meta name="theme-color" content="#b52d20">',
        '<meta name="referrer" content="no-referrer">',
        f'<meta name="robots" content="{INDEX_ROBOTS if site_url else PRIVATE_ROBOTS}">',
        f'<meta name="description" content="{esc(GUILD_SUMMARY)}">',
        '<meta property="og:type" content="website">', f'<meta property="og:site_name" content="{GUILD_NAME}">',
        f'<meta property="og:title" content="{esc(title)}">',
        f'<meta property="og:description" content="{esc(GUILD_SUMMARY)}">',
    ]
    if site_url:
        head += [f'<link rel="canonical" href="{esc(site_url)}">',
                 f'<meta property="og:url" content="{esc(site_url)}">',
                 f'<meta property="og:image" content="{esc(site_url + LOGO_FILE)}">',
                 f'<meta property="og:image:width" content="{LOGO_SIZE[0]}">',
                 f'<meta property="og:image:height" content="{LOGO_SIZE[1]}">',
                 f'<meta property="og:image:alt" content="{esc(LOGO_ALT)}">',
                 '<meta name="twitter:card" content="summary_large_image">']
    else:
        head.append('<meta name="twitter:card" content="summary">')
    if verification:
        head.append(f'<meta name="google-site-verification" content="{esc(verification)}">')
    head += [f'<meta http-equiv="Content-Security-Policy" content="{CSP}">',
             f'<link rel="icon" type="image/png" href="{LOGO_FILE}">',
             f"<title>{esc(title)}</title>", f"<style>\n{CSS}</style>"]
    if site_url:
        head.append(f'<script type="application/ld+json">{structured_data(title, site_url)}</script>')
    head += ["</head>", "<body>"]
    return "\n".join(head + body + ["</body>", "</html>"]) + "\n"


def public_documents(ledger):
    """The same allowlisted data for workflow and desktop publication."""
    events, omitted = project_events(ledger)
    standings, changed = standings_document(ledger)
    history = {
        "format": HISTORY_FORMAT, "version": SITE_VERSION, "lastEventId": ledger.count,
        "chainHead": ledger.heads[-1], "omitted": omitted, "events": events,
    }
    return standings, history, changed


def build_site(ledger, title, source_url=None, site_url=None):
    standings, history, changed = public_documents(ledger)
    events, omitted = history["events"], history["omitted"]
    recent = [event for event in reversed(events) if event["kind"] in PAGE_ACTIVITY][:RECENT_EVENTS]
    files = {
        "index.html": render_page(title, standings, recent, omitted, source_url, site_url=site_url,
                                  history_events=events).encode("utf-8"),
        "standings.json": store.indented(standings),
        "history.json": (store.canonical(history) + "\n").encode("ascii"),
        **{name: brand_asset(name) for name in PAGE_ASSETS},
    }
    return files, standings, history, changed


def separate_folders(private, out, label):
    private_path, out_path = Path(private).resolve(), Path(out).resolve()
    if out_path.exists() and not out_path.is_dir():
        raise ToolError("--out is a file; give a folder for the public site")
    if out_path == private_path or private_path in out_path.parents or out_path in private_path.parents:
        raise ToolError(f"The public site folder must be separate from the {label} folder")


def check_out_dir(ledger_dir, out):
    separate_folders(ledger_dir, out, "private ledger")


def check_title(value):
    text = clean(value, 80)
    if not text:
        raise ToolError("--title needs some visible text")
    return text


def check_source_url(value):
    if value is None:
        return None
    try:
        parts = urllib.parse.urlsplit(value)
    except ValueError:
        raise ToolError("--source-url must be a plain https:// link") from None
    if (len(value) > 200 or parts.scheme != "https" or not parts.hostname or parts.username or parts.password
            or any(ch.isspace() or not ch.isprintable() for ch in value)):
        raise ToolError("--source-url must be a plain https:// link")
    return value


def check_site_url(value):
    """The page's own address, used for link previews, the canonical link and search discovery."""
    if value is None:
        return None
    problem = "--site-url must be the page's own https:// address ending in /, without ? or #"
    try:
        parts = urllib.parse.urlsplit(value)
        port = parts.port
    except ValueError:
        raise ToolError(problem) from None
    if (len(value) > 200 or parts.scheme != "https" or not parts.hostname or parts.username or parts.password
            or port is not None or not re.fullmatch(r"[a-z0-9.-]+", parts.hostname) or not value.endswith("/")
            or "?" in value or "#" in value or any(ch.isspace() or not ch.isprintable() for ch in value)):
        raise ToolError(problem)
    return value


def check_verification(value):
    """The content value of Google Search Console's HTML-tag verification, for a page that cannot use DNS."""
    if value is None:
        return None
    if not VERIFICATION_TOKEN.fullmatch(value):
        raise ToolError("--google-site-verification must be the content value from Google's HTML tag: "
                        "10 to 100 letters, digits, - or _")
    return value


def check_public(standings, history):
    """Accept only the shapes `site` writes, so a hand-edited or damaged data folder cannot reach the page."""
    def need(ok, what):
        if not ok:
            raise IntegrityError(f"Published data is malformed: {what}")

    def keys(value, required, optional, what):
        need(isinstance(value, dict) and set(required) <= set(value) <= set(required) | set(optional), what)

    def text(value, limit=NAME_LIMIT):
        return isinstance(value, str) and 0 < len(value) <= limit and value == clean(value, limit)

    keys(standings, ("format", "version", "lastEventId", "lastEventTime", "chainHead", "departedCount", "players"), (),
         "standings.json fields")
    keys(history, ("format", "version", "lastEventId", "chainHead", "omitted", "events"), (), "history.json fields")
    need(standings["format"] == STANDINGS_FORMAT and history["format"] == HISTORY_FORMAT
         and standings["version"] == history["version"] == SITE_VERSION, "file format or version")
    last = standings["lastEventId"]
    need(is_whole(last) and history["lastEventId"] == last, "lastEventId differs between the two files")
    need(isinstance(standings["chainHead"], str) and re.fullmatch(r"[0-9a-f]{64}", standings["chainHead"])
         and history["chainHead"] == standings["chainHead"], "chainHead differs between the two files")
    need(is_number(standings["lastEventTime"]) and is_whole(standings["departedCount"]) and is_whole(history["omitted"]),
         "lastEventTime, departedCount or omitted")
    need(isinstance(standings["players"], list) and isinstance(history["events"], list), "players or events list")
    anchors, statuses = set(), set(STATUS_TEXT.values()) | {"Not set", "Unverified"}
    for player in standings["players"]:
        keys(player, ("account", "balance", "cap", "characters", "status", "anchor"),
             ("specs", "loot", "lootTotal", "attendance"),
             "player fields")
        need(text(player["account"]) and is_number(player["balance"])
             and (player["cap"] is None or is_number(player["cap"])) and player["status"] in statuses, "player row")
        need(isinstance(player["anchor"], str) and re.fullmatch(r"p-[a-z0-9-]{1,140}", player["anchor"])
             and player["anchor"] not in anchors, "player anchor")
        anchors.add(player["anchor"])
        if "attendance" in player:
            counts = player["attendance"]
            keys(counts, ("attended", "eligible"), (), "attendance fields")
            need(is_whole(counts["eligible"], 0, last)
                 and is_whole(counts["attended"], 0, counts["eligible"]), "attendance counts")
        characters = player["characters"]
        need(isinstance(characters, list) and characters and all(text(name) for name in characters), "characters")
        specs = player.get("specs", {})
        need(isinstance(specs, dict) and all(name in characters and text(spec, 60) for name, spec in specs.items()),
             "class/spec text")
        loot = player.get("loot", [])
        need(isinstance(loot, list) and len(loot) <= LOOT_LIMIT and ("loot" in player) == ("lootTotal" in player)
             and (not loot or is_whole(player["lootTotal"], len(loot))), "loot list")
        for entry in loot:
            keys(entry, ("event", "time", "item"), ("mode", "cost", "character", "reversed", "corrected"), "loot fields")
            need(is_whole(entry["event"], 1, last) and is_number(entry["time"]) and is_whole(entry["item"], 1, ITEM_MAX)
                 and (("mode" not in entry) or text(entry["mode"], 40))
                 and (("cost" not in entry) or is_number(entry["cost"]))
                 and (("character" not in entry) or text(entry["character"]))
                 and all(entry.get(flag, True) is True for flag in ("reversed", "corrected")), "loot entry")
    previous = 0
    for event in history["events"]:
        keys(event, ("id", "time", "kind", "label", "summary", "fields"), (), "history event fields")
        need(is_whole(event["id"], previous + 1, last) and is_number(event["time"]) and text(event["kind"], 40)
             and text(event["label"]) and text(event["summary"], SUMMARY_LIMIT) and isinstance(event["fields"], dict),
             "history event")
        need(all(key in FIELDS or (key.endswith("Count") and key[:-5] in COUNT_FIELDS) for key in event["fields"])
             and all(isinstance(value, (str, bool)) or is_number(value) for value in event["fields"].values()),
             "history event fields")
        previous = event["id"]


def escape_discord(text):
    return _DISCORD_MARKDOWN.sub(r"\\\1", _DISCORD_STRIP.sub("", text))


def announce_line(event):
    return escape_discord(clean(f"Event {event['id']} - {event['summary']}", LINE_LIMIT))


def batch_lines(lines):
    batches, current, size = [], [], 0
    for item in lines:
        cost = len(item[1]) + 1
        if current and size + cost > MESSAGE_LIMIT:
            batches.append(current)
            current, size = [], 0
        current.append(item)
        size += cost
    if current:
        batches.append(current)
    return batches


def webhook_url(environ):
    url = environ.get(WEBHOOK_VARIABLE, "").strip()
    if not url:
        raise ToolError(f"Set {WEBHOOK_VARIABLE} first; the webhook URL is never accepted on the command line")
    if not WEBHOOK_PATTERN.fullmatch(url):
        raise ToolError(f"{WEBHOOK_VARIABLE} is not a Discord webhook URL (https://discord.com/api/webhooks/ID/TOKEN)")
    return url


def check_username(value):
    text = value.strip()
    if (not 1 <= len(text) <= 80 or any(not ch.isprintable() for ch in text)
            or any(ch in text for ch in "@#:`")
            or any(word in text.lower() for word in ("discord", "clyde"))):
        raise ToolError("--username must be 1-80 printable characters without @ # : ` and not contain 'discord' or 'clyde'")
    return text


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def default_opener():
    return urllib.request.build_opener(NoRedirect)


def retry_hint(error):
    value = error.headers.get("Retry-After", "") if getattr(error, "headers", None) else ""
    value = str(value).strip()
    return f" Retry after {value} seconds." if value.isdigit() and len(value) <= 5 else ""


def post_webhook(opener, url, content, username):
    body = store.canonical({"content": content, "username": username, "allowed_mentions": {"parse": []}})
    request = urllib.request.Request(url + "?wait=true", data=body.encode("ascii"), method="POST")
    request.add_header("Content-Type", "application/json")
    request.add_header("User-Agent", USER_AGENT)
    try:
        with opener.open(request, timeout=TIMEOUT_SECONDS) as response:
            status = getattr(response, "status", None) or getattr(response, "code", 200)
            response.read(1)
    except urllib.error.HTTPError as error:
        if error.code == 429:
            raise RemoteError("Discord is rate limiting this webhook (HTTP 429)." + retry_hint(error)) from None
        raise RemoteError(f"Discord answered HTTP {error.code}") from None
    except (urllib.error.URLError, OSError) as error:
        raise RemoteError(f"Could not reach Discord: {type(error).__name__}") from None
    if status not in (200, 204):
        raise RemoteError(f"Discord answered HTTP {status}")


def read_cursor(folder, ledger):
    path = Path(folder) / store.CURSOR
    if not path.exists():
        return None
    document = store.read_json(path, CURSOR_BYTES, store.CURSOR)
    keys = {"format", "version", "lastEventId", "chainHead"}
    if not isinstance(document, dict) or set(document) != keys or document["format"] != CURSOR_FORMAT \
            or document["version"] != 1:
        raise IntegrityError(f"{store.CURSOR} is not an announce cursor; restore it from Git")
    last = document["lastEventId"]
    if isinstance(last, bool) or not isinstance(last, int) or not 0 <= last <= ledger.count \
            or document["chainHead"] != ledger.heads[last]:
        raise IntegrityError("The ledger history changed since the last announcement; nothing was posted. "
                             "Restore the ledger or announced.json from Git")
    return last


def write_cursor(folder, ledger, last):
    store.write_atomic(Path(folder) / store.CURSOR, store.indented({
        "format": CURSOR_FORMAT, "version": 1, "lastEventId": last, "chainHead": ledger.heads[last]}))


def replay_note(replayed):
    return ("Balances were replayed through the addon rules." if replayed
            else "NOTE: --no-replay was used; balances and caps were NOT independently verified.")


def run_ingest(args, opener, environ, sleep):
    result = store.ingest(args.ledger, args.export, args.characters, store.replay_from_args(args))
    if result["status"] == "unchanged":
        say("No new events; ledger unchanged.")
        return
    if result["status"] == "created":
        say(f"Ledger created: {result['events']} events, chain head {result['chainHead']}.")
    else:
        say(f"Ledger updated: {result['added']} new events ({result['events']} total), "
            f"chain head {result['chainHead']}.")
    say(replay_note(result["replayed"]))
    say("Review the diff: a correct update only adds lines to journal.json. "
        "Commit it through a pull request that a second officer approves.")


def run_verify(args, opener, environ, sleep):
    replay = store.replay_from_args(args)
    ledger = store.verify_ledger(args.ledger, replay, args.previous)
    say(f"Ledger verified: {ledger.count} events, chain head {ledger.heads[-1]}.")
    say(replay_note(replay.enabled))
    if args.previous:
        say("The history extends the previous ledger without any change.")


def run_site(args, opener, environ, sleep):
    ledger = store.load_ledger(args.ledger)
    check_out_dir(args.ledger, args.out)
    files, standings, history, changed = build_site(ledger, check_title(args.title), check_source_url(args.source_url),
                                                    check_site_url(args.site_url))
    for name, data in files.items():
        store.write_atomic(Path(args.out) / name, data)
    say(f"Site written to {args.out}: {', '.join(files)} "
        f"({plural(len(standings['players']), 'player', 'players')}, {plural(len(history['events']), 'record', 'records')}). "
        "Nothing was uploaded.")
    if changed:
        say(f"Warning: {plural(changed, 'name was', 'names were')} shortened, cleaned or redacted for the public page "
            "(IDs and BattleTag-like text are never published).")
    if history["omitted"]:
        say(f"{plural(history['omitted'], 'private record was', 'private records were')} left out of the history.")


def run_render(args, opener, environ, sleep):
    """The full guild page from already-published JSON plus the community files. Nothing is fetched here."""
    import capped_dkp_community as community
    title, source_url = check_title(args.title), check_source_url(args.source_url)
    site_url = check_site_url(args.site_url)
    verification = check_verification(args.google_site_verification)
    data = Path(args.data)
    separate_folders(data, args.out, "published data")
    if args.gallery:
        separate_folders(args.gallery, args.out, "gallery")
    config = community.load_config(args.config) if args.config else community.empty_config()
    items = community.load_items(args.items) if args.items else {}
    gallery = community.load_gallery(args.gallery) if args.gallery else []
    feed = community.load_data(args.community) if args.community else None
    recruitment = community.resolved_recruitment(config, feed)
    roster = None
    if args.roster and Path(args.roster).is_file():
        roster = store.read_json(args.roster, ROSTER_BYTES, Path(args.roster).name)
        armory_roster(roster)
    present = [name for name in ("standings.json", "history.json") if (data / name).is_file()]
    if len(present) == 1:
        raise ToolError(f"{data} holds {present[0]} without its partner file; publish both together with `site`")
    files = {}
    if present:
        standings = store.read_json(data / "standings.json", PUBLIC_JSON_BYTES, "standings.json")
        history = store.read_json(data / "history.json", PUBLIC_JSON_BYTES, "history.json")
        check_public(standings, history)
        files["standings.json"] = store.indented(standings)
        files["history.json"] = (store.canonical(history) + "\n").encode("ascii")
        events = history["events"]
    else:
        standings = {"lastEventId": 0, "lastEventTime": 0, "chainHead": "", "departedCount": 0, "players": []}
        history, events = {"omitted": 0}, []
    recent = [event for event in reversed(events) if event["kind"] in PAGE_ACTIVITY][:RECENT_EVENTS]
    raid = config["raidHelper"]
    extras = {"items": items, "gallery": gallery, "kills": boss_kills(events), "community": feed, "raid": raid,
              "raid_days": raid["days"] if raid else community.RAID_DAYS, "recruitment": recruitment,
              "roster": roster, "guild": config["guild"], "reports": config["reports"], "profiles": config["profiles"]}
    page = render_page(title, standings, recent, history["omitted"], source_url, pending=not present,
                       site_url=site_url, extras=extras, verification=verification, history_events=events)
    files = {"index.html": page.encode("utf-8"), **{name: brand_asset(name) for name in PAGE_ASSETS},
             **discovery_files(title, site_url, not present, recruitment), **files}
    for entry in gallery:
        files[f"gallery/{entry['image']}"] = entry["data"]
    for name, content in files.items():
        store.write_atomic(Path(args.out) / name, content)
    state = "awaiting first publication" if not present else plural(len(standings["players"]), "player", "players")
    say(f"Page rendered to {args.out}: {plural(len(files), 'file', 'files')} ({state}, "
        f"{plural(len(gallery), 'gallery image', 'gallery images')}). Nothing was fetched or uploaded.")


def check_announce_flags(args):
    if args.baseline and args.send:
        raise ToolError("--baseline never posts anything; run it without --send")
    if args.baseline and args.from_event is not None:
        raise ToolError("Use either --baseline or --from-event, not both")


def starting_point(args, folder, ledger):
    """Return the event id the announcement starts after, or None when --baseline already finished the run."""
    cursor = read_cursor(folder, ledger)
    if cursor is not None:
        if args.baseline or args.from_event is not None:
            raise ToolError("An announce cursor exists; --baseline and --from-event are only for the first run")
        return cursor
    if args.baseline:
        write_cursor(folder, ledger, ledger.count)
        say(f"Baseline set: the {ledger.count} existing events will never be announced. Nothing was sent.")
        return None
    if args.from_event is None:
        raise ToolError("No announce cursor yet: run once with --baseline to skip the existing history, "
                        "or --from-event N to announce from event N")
    if not 1 <= args.from_event <= ledger.count:
        raise ToolError(f"--from-event must be between 1 and {ledger.count}")
    return args.from_event - 1


def run_announce(args, opener, environ, sleep):
    check_announce_flags(args)
    ledger = store.load_ledger(args.ledger)
    folder = Path(args.ledger)
    username = check_username(args.username)
    url = webhook_url(environ) if args.send else None
    start = starting_point(args, folder, ledger)
    if start is None:
        return
    events, _ = project_events(ledger)
    lines = [(event["id"], announce_line(event)) for event in events
             if event["id"] > start and event["kind"] in DISCORD_ACTIVITY]
    batches = batch_lines(lines)
    selected, leftover = batches[:args.max_messages], batches[args.max_messages:]
    if not args.send:
        for number, batch in enumerate(selected, 1):
            say(f"--- message {number} of {len(selected)} (events {batch[0][0]}-{batch[-1][0]}) ---")
            say("\n".join(text for _, text in batch))
        if not selected:
            say(f"Nothing to announce after event {start}.")
        if leftover:
            say(f"{plural(len(leftover), 'more message waits', 'more messages wait')} for the next run.")
        say("Dry run: nothing was sent and no cursor was written. "
            f"Add --send (with {WEBHOOK_VARIABLE} set) to post these.")
        return
    if not selected:
        if start < ledger.count:
            write_cursor(folder, ledger, ledger.count)
        say(f"Nothing to announce; the cursor is at event {ledger.count}.")
        return
    opener = opener or default_opener()
    for number, batch in enumerate(selected, 1):
        if number > 1:
            sleep(args.delay)
        post_webhook(opener, url, "\n".join(text for _, text in batch), username)
        write_cursor(folder, ledger, ledger.count if number == len(selected) and not leftover else batch[-1][0])
        say(f"Posted message {number} of {len(selected)} (events {batch[0][0]}-{batch[-1][0]}).")
    if leftover:
        say(f"{plural(len(leftover), 'more message waits', 'more messages wait')} for the next run.")


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise ToolError(message)


def bounded_int(low, high):
    def parse(text):
        try:
            value = int(text)
        except ValueError:
            raise argparse.ArgumentTypeError(f"{text!r} is not a whole number") from None
        if not low <= value <= high:
            raise argparse.ArgumentTypeError(f"must be between {low} and {high}")
        return value
    return parse


def bounded_float(low, high):
    def parse(text):
        try:
            value = float(text)
        except ValueError:
            raise argparse.ArgumentTypeError(f"{text!r} is not a number") from None
        if not low <= value <= high:
            raise argparse.ArgumentTypeError(f"must be between {low} and {high}")
        return value
    return parse


def build_parser():
    root = Parser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = root.add_subparsers(dest="command", required=True)

    ingest = commands.add_parser("ingest", help="copy an addon export into the ledger folder")
    ingest.add_argument("--ledger", required=True, metavar="DIR", help="private ledger folder")
    ingest.add_argument("--export", required=True, metavar="FILE", help="output of /cdkp export|json")
    ingest.add_argument("--characters", required=True, metavar="FILE", help="output of /cdkp characters|json")
    store.add_replay_arguments(ingest)

    verify = commands.add_parser("verify", help="re-check the ledger")
    verify.add_argument("--ledger", required=True, metavar="DIR")
    verify.add_argument("--previous", metavar="DIR", help="earlier approved ledger; the history must extend it unchanged")
    store.add_replay_arguments(verify)

    site = commands.add_parser("site", help="write the static public page and JSON files")
    site.add_argument("--ledger", required=True, metavar="DIR")
    site.add_argument("--out", required=True, metavar="DIR", help="public site folder, separate from the ledger")
    site.add_argument("--title", default=DEFAULT_TITLE)
    site.add_argument("--source-url", metavar="URL", help="optional https link shown in the page footer")
    site.add_argument("--site-url", metavar="URL",
                      help="the page's own https address, for link previews and search engines")

    render = commands.add_parser("render", help="build the full guild page from published JSON and community files")
    render.add_argument("--data", required=True, metavar="DIR", help="folder holding standings.json and history.json")
    render.add_argument("--out", required=True, metavar="DIR", help="output folder, separate from --data and --gallery")
    render.add_argument("--config", metavar="FILE", help="community.json: Raid-Helper server and open positions")
    render.add_argument("--community", metavar="FILE", help="community data written by capped_dkp_community.py fetch")
    render.add_argument("--items", metavar="FILE", help="item-cache.json with Wowhead item names")
    render.add_argument("--gallery", metavar="DIR", help="folder with gallery.json and its images")
    render.add_argument("--roster", metavar="FILE",
                        help="Armory roster saved by capped_dkp_community.py fetch; if absent, the bundled snapshot")
    render.add_argument("--site-url", metavar="URL",
                        help="the page's own https address: link previews, search indexing, sitemap.xml and llms.txt")
    render.add_argument("--google-site-verification", metavar="TOKEN",
                        help="content value of Google Search Console's HTML-tag verification")
    render.add_argument("--source-url", metavar="URL", help="optional https link shown in the page footer")
    render.add_argument("--title", default=DEFAULT_TITLE)

    announce = commands.add_parser("announce", help="print or post new events to a Discord webhook")
    announce.add_argument("--ledger", required=True, metavar="DIR")
    announce.add_argument("--send", action="store_true", help=f"post to the webhook in {WEBHOOK_VARIABLE} (default: dry run)")
    announce.add_argument("--baseline", action="store_true", help="first run: mark every existing event as announced")
    announce.add_argument("--from-event", type=bounded_int(1, 10 ** 9), metavar="N",
                          help="first run: announce from event N onward")
    announce.add_argument("--max-messages", type=bounded_int(1, 50), default=10, metavar="N")
    announce.add_argument("--delay", type=bounded_float(0, 60), default=1.0, metavar="SECONDS")
    announce.add_argument("--username", default=DEFAULT_USERNAME)
    return root


def fail(message, code, secrets):
    for secret in secrets:
        if secret:
            message = message.replace(secret, "***")
    say(f"ERROR: {message}", sys.stderr)
    return code


def secret_values(argv, environ):
    """Webhook URLs and tokens that must never be printed, whether they came from the environment or a mistaken argument."""
    url = environ.get(WEBHOOK_VARIABLE, "").strip()
    secrets = [url, url.rsplit("/", 1)[-1]]
    for text in argv:
        for match in WEBHOOK_PATTERN.finditer(text):
            secrets += [match.group(0), match.group(0).rsplit("/", 1)[-1]]
    return [secret for secret in secrets if len(secret) >= 16]


def main(argv=None, opener=None, environ=None, sleep=time.sleep):
    environ = os.environ if environ is None else environ
    argv = sys.argv[1:] if argv is None else list(argv)
    secrets = secret_values(argv, environ)
    handlers = {"ingest": run_ingest, "verify": run_verify, "site": run_site, "render": run_render,
                "announce": run_announce}
    try:
        args = build_parser().parse_args(argv)
        handlers[args.command](args, opener, environ, sleep)
    except ToolError as error:
        return fail(str(error), error.code, secrets)
    except OSError as error:
        return fail(f"File operation failed: {type(error).__name__}: {error.strerror or error}", 1, secrets)
    return 0


if __name__ == "__main__":
    sys.exit(main())
