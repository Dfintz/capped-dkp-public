# SPDX-License-Identifier: Apache-2.0
"""Original offline store for the approved Capped DKP journal. No network, game or SavedVariables access.

The store keeps one approved journal export (journal.json), the projected character rows
(characters.json) and a manifest carrying a hash chain. It records what officers approved; it does not
authorise anything. The chain and digests detect accidental, partial or inconsistent edits, not a
forger who rewrites every file consistently, so review journal diffs: a correct ingest only adds lines.
"""

import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

_TOOLS = str(Path(__file__).resolve().parent)
if _TOOLS not in sys.path:
    sys.path.insert(0, _TOOLS)

import capped_dkp_snapshot as snapshot  # noqa: E402

FORMAT = "capped-dkp-ledger"
VERSION = 1
ZERO_HEAD = "0" * 64
JOURNAL, ROWS, MANIFEST, CURSOR = "journal.json", "characters.json", "manifest.json", "announced.json"
MAX_ROWS = 5000
MAX_ROWS_BYTES = 8 * 1024 * 1024
MAX_BALANCE = 1_000_000_000
MAX_SAFE_INTEGER = 2 ** 53
CHUNK_EVENTS = 100
REPLAY_TIMEOUT_SECONDS = 120
REPLAY_SCRIPT = Path(__file__).resolve().with_name("capped_dkp_replay.lua")
LUA_MODULES = (
    "Bootstrap.lua", "Models/PointInfo.lua", "Models/Loot.lua", "Dispatcher.lua",
    "Rules.lua", "Rolls.lua", "Teams.lua", "Policy.lua", "Ledger.lua",
)
ROW_KEYS = ("account", "activeCap", "balance", "character", "departed", "discordID", "membershipStatus")
IDENTITY_KINDS = ("account", "rosteradd", "alt", "discord", "depart", "returned")
DISCORD_ID = re.compile(r"[0-9]{17,20}")
DIFFERENCE_LIMIT = 5


class ToolError(Exception):
    """Usage problem: the command cannot run as given (exit 1)."""
    code = 1


class IntegrityError(ToolError):
    """Data is invalid, inconsistent or unsafe to publish (exit 2)."""
    code = 2


class RemoteError(ToolError):
    """A remote service stopped or answered unexpectedly (exit 3)."""
    code = 3


@dataclass(frozen=True)
class Replay:
    addon: Optional[Path] = None
    lua: Optional[str] = None

    @property
    def enabled(self):
        return self.addon is not None


@dataclass(frozen=True)
class Ledger:
    events: list
    rest: dict
    rows: list
    manifest: dict
    heads: list

    @property
    def count(self):
        return len(self.events)


def canonical(value) -> str:
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    except (TypeError, ValueError) as error:
        raise IntegrityError(f"Value cannot be written as canonical JSON: {error}") from None


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("ascii")).hexdigest()


def chain_heads(events: list) -> list:
    heads = [ZERO_HEAD]
    for event in events:
        heads.append(sha256_text(heads[-1] + "\n" + canonical(event)))
    return heads


def write_atomic(path: Path, data: bytes, durable: bool = True) -> None:
    """Replace path with data. durable=False skips fsync (slow on some Windows disks) for scratch or cache files."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, name = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(data)
            if durable:
                stream.flush()
                os.fsync(stream.fileno())
        os.replace(name, path)
    except BaseException:
        try:
            os.unlink(name)
        except OSError:
            pass
        raise


def indented(value) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def read_json(path, limit: int, label: str):
    try:
        content = snapshot.bounded_read(Path(path), limit)
    except (OSError, ValueError) as error:
        raise ToolError(f"Cannot read {label}: {error}") from None
    if content.startswith(b"\xef\xbb\xbf"):
        content = content[3:]
    try:
        return json.loads(
            content.decode("utf-8"), object_pairs_hook=snapshot.unique_object,
            parse_constant=snapshot.invalid_number, parse_float=snapshot.finite_float,
        )
    except (ValueError, RecursionError) as error:
        raise IntegrityError(f"{label} is not valid JSON: {error}") from None


def journal_bytes(events: list, rest: dict) -> bytes:
    """One canonical event per line (leading comma) so an append only adds lines to the diff."""
    lines = ['{"database":{"events":[']
    for index, event in enumerate(events):
        lines.append(("," if index else "") + canonical(event))
    tail = canonical(rest)[1:-1]
    lines.append("]" + ("," + tail if tail else "") + '},"exportVersion":1,"format":"CappedDKP"}')
    return ("\n".join(lines) + "\n").encode("ascii")


def check_envelope(document: dict) -> None:
    if set(document) != {"database", "exportVersion", "format"}:
        extra = sorted(set(document) ^ {"database", "exportVersion", "format"})
        raise IntegrityError("The export has unexpected top-level keys: " + ", ".join(extra))


def number_value(value, label: str):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise IntegrityError(f"{label} must be a number")
    if isinstance(value, float) and not math.isfinite(value):
        raise IntegrityError(f"{label} must be finite")
    if abs(value) > MAX_BALANCE:
        raise IntegrityError(f"{label} is outside the supported range")
    if isinstance(value, float) and value == int(value):
        return int(value)
    return value


def project_row(row, position: int) -> dict:
    label = f"Character row {position}"
    if not isinstance(row, dict):
        raise IntegrityError(f"{label} is not an object")

    def text(key, limit):
        value = row.get(key)
        if not isinstance(value, str) or not value.strip() or len(value) > limit:
            raise IntegrityError(f"{label} has no valid {key}")
        return value

    discord = row.get("discordID")
    if not isinstance(discord, str) or (discord and not DISCORD_ID.fullmatch(discord)):
        raise IntegrityError(f"{label} has an invalid discordID")
    if not isinstance(row.get("departed"), bool):
        raise IntegrityError(f"{label} has an invalid departed flag")
    cap = row.get("activeCap")
    return {
        "account": text("account", 120),
        "activeCap": None if cap in (None, "") else number_value(cap, f"{label} activeCap"),
        "balance": number_value(row.get("balance"), f"{label} balance"),
        "character": text("character", 120),
        "departed": row["departed"],
        "discordID": discord,
        "membershipStatus": text("membershipStatus", 40),
    }


def validate_rows(rows) -> list:
    """Project to the minimal public-safe columns and enforce account-level consistency."""
    if not isinstance(rows, list):
        raise IntegrityError(
            "Character rows must be a JSON array: use /cdkp characters|json on the official ledger, "
            "not a practice export")
    if len(rows) > MAX_ROWS:
        raise IntegrityError(f"More than {MAX_ROWS} character rows")
    projected = sorted((project_row(row, index) for index, row in enumerate(rows, 1)),
                       key=lambda row: row["character"])
    seen, accounts, owners = set(), {}, {}
    for row in projected:
        if row["character"] in seen:
            raise IntegrityError(f"Character {row['character']} appears twice")
        seen.add(row["character"])
        first = accounts.setdefault(row["account"], row)
        for key in ("balance", "departed", "discordID", "activeCap", "membershipStatus"):
            if first[key] != row[key]:
                raise IntegrityError(f"Characters of account {row['account']} disagree on {key}")
        if row["discordID"] and owners.setdefault(row["discordID"], row["account"]) != row["account"]:
            raise IntegrityError("One Discord ID is linked to two accounts")
    return projected


def identity_rows(events: list) -> list:
    """Replay only the identity handlers (account, rosteradd, alt, discord, depart, returned)."""
    characters, accounts = {}, {}

    def need(event, key):
        value = event["data"].get(key)
        if not isinstance(value, str) or not value:
            raise IntegrityError(f"Event {event['id']} ({event['kind']}) has no valid {key}")
        return value

    def known(event, character):
        if character not in characters:
            raise IntegrityError(f"Event {event['id']} ({event['kind']}) refers to unknown character {character}")
        return accounts[characters[character]]

    for event in events:
        kind = event["kind"]
        if kind not in IDENTITY_KINDS:
            continue
        if kind == "account":
            account, character = need(event, "id"), need(event, "character")
            if account in accounts or character in characters:
                raise IntegrityError(f"Event {event['id']} registers an existing account or character")
            accounts[account] = {"discord": None, "departed": False}
            characters[character] = account
        elif kind == "rosteradd":
            account, character = need(event, "account"), need(event, "character")
            action = need(event, "action")
            if character in characters or action not in ("new", "alt"):
                raise IntegrityError(f"Event {event['id']} has an invalid roster registration")
            if action == "new":
                if account in accounts:
                    raise IntegrityError(f"Event {event['id']} registers an existing account")
                accounts[account] = {"discord": None, "departed": False}
            elif account not in accounts:
                raise IntegrityError(f"Event {event['id']} links an alt to an unknown account")
            characters[character] = account
        elif kind == "alt":
            account, character = need(event, "id"), need(event, "character")
            if account not in accounts or character in characters:
                raise IntegrityError(f"Event {event['id']} has an invalid alt link")
            characters[character] = account
        elif kind == "discord":
            character, value = need(event, "character"), need(event, "id")
            state = known(event, character)
            if value != "-" and not DISCORD_ID.fullmatch(value):
                raise IntegrityError(f"Event {event['id']} has an invalid Discord ID")
            if value != "-" and any(
                    key != characters[character] and other["discord"] == value for key, other in accounts.items()):
                raise IntegrityError(f"Event {event['id']} reuses a Discord ID of another account")
            state["discord"] = None if value == "-" else value
        else:
            known(event, need(event, "character"))["departed"] = kind == "depart"
    return [
        {"account": account, "character": character, "departed": accounts[account]["departed"],
         "discordID": accounts[account]["discord"] or ""}
        for character, account in sorted(characters.items())
    ]


def row_differences(stored: list, replayed: list, keys=ROW_KEYS) -> list:
    left = {row["character"]: row for row in stored}
    right = {row["character"]: row for row in replayed}
    problems = []
    for name in sorted(set(left) | set(right)):
        if name not in right:
            problems.append(f"{name}: listed in characters.json but absent from the replay")
        elif name not in left:
            problems.append(f"{name}: produced by the replay but absent from characters.json")
        else:
            for key in keys:
                if left[name][key] != right[name][key]:
                    problems.append(
                        f"{name}: {key} is {left[name][key]!r} in characters.json but {right[name][key]!r} in the replay")
    return problems


def report(problems: list, headline: str) -> None:
    if problems:
        shown = "; ".join(problems[:DIFFERENCE_LIMIT])
        more = f" (+{len(problems) - DIFFERENCE_LIMIT} more)" if len(problems) > DIFFERENCE_LIMIT else ""
        raise IntegrityError(f"{headline}: {shown}{more}")


def check_identity(events: list, rows: list) -> None:
    keys = ("account", "departed", "discordID")
    report(row_differences(rows, identity_rows(events), keys), "Character rows disagree with the journal identity events")


def build_manifest(events: list, rows: list, heads: list) -> dict:
    return {
        "format": FORMAT, "version": VERSION, "eventCount": len(events),
        "lastEventTime": events[-1]["time"] if events else 0, "chainHead": heads[-1],
        "characterCount": len(rows), "charactersDigest": sha256_text(canonical(rows)),
    }


def lua_string(text: str) -> str:
    try:
        encoded = text.encode("utf-8")
    except UnicodeEncodeError:
        raise IntegrityError("A journal string is not valid Unicode text") from None
    out = ['"']
    for byte in encoded:
        if byte in (0x22, 0x5C):
            out.append("\\" + chr(byte))
        elif 32 <= byte < 127:
            out.append(chr(byte))
        else:
            out.append("\\%03d" % byte)
    out.append('"')
    return "".join(out)


def lua_value(value) -> str:
    if value is None:
        raise IntegrityError("The journal contains null, which the addon never writes")
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        if abs(value) > MAX_SAFE_INTEGER:
            raise IntegrityError("A journal integer is too large for exact replay")
        return "%d" % value
    if isinstance(value, float):
        return "%.17g" % value
    if isinstance(value, str):
        return lua_string(value)
    if isinstance(value, list):
        return "{" + ",".join(lua_value(item) for item in value) + "}"
    return "{" + ",".join("[%s]=%s" % (lua_string(key), lua_value(item)) for key, item in value.items()) + "}"


def lua_journal(events: list, rest: dict) -> str:
    """Chunked so no Lua function exceeds the 5.1 per-function constant limit."""
    parts = ["local events = {}\n"]
    for start in range(0, len(events), CHUNK_EVENTS):
        body = "".join("events[#events+1]=%s\n" % lua_value(event) for event in events[start:start + CHUNK_EVENTS])
        parts.append("do local function chunk()\n%send chunk() end\n" % body)
    fields = ["events=events"] + ["[%s]=%s" % (lua_string(key), lua_value(item)) for key, item in sorted(rest.items())]
    parts.append("return {%s}\n" % ",".join(fields))
    return "".join(parts)


def lua_command(candidate):
    if str(candidate).lower().endswith(".dll"):
        return [sys.executable, "-B", str(Path(__file__).with_name("capped_dkp_lua.py")), str(candidate)]
    return [candidate]


def find_lua(explicit) -> str:
    candidate = explicit or shutil.which("lua")
    if not candidate:
        raise ToolError("Lua 5.1 interpreter not found; pass --lua PATH")
    try:
        probe = subprocess.run([*lua_command(candidate), "-v"], capture_output=True, text=True, timeout=20,
                               check=False)
    except (OSError, subprocess.SubprocessError) as error:
        raise ToolError(
            f"Cannot run the Lua interpreter ({type(error).__name__}); pass --lua PATH to a Lua 5.1 interpreter"
        ) from None
    found = (probe.stdout + probe.stderr).strip()
    if probe.returncode or "Lua 5.1" not in found:
        raise ToolError(f"Lua 5.1 is required to replay the journal; found: {found[:60] or 'nothing'}")
    return candidate


def clip(text: str, limit: int = 300) -> str:
    return "".join(ch if ch.isprintable() else " " for ch in text.strip())[:limit]


def lua_rows(addon: Path, lua: str, events: list, rest: dict) -> list:
    """Replay the journal through the real addon rules (plain Lua 5.1, no WoW API) and return projected rows."""
    folder = Path(addon)
    for module in LUA_MODULES:
        if not (folder / module).is_file():
            raise ToolError(f"{folder} is not the CappedDKP addon folder (missing {module})")
    with tempfile.TemporaryDirectory(prefix="cdkp-replay-") as scratch:
        journal, output = Path(scratch) / "journal.lua", Path(scratch) / "rows.json"
        journal.write_bytes(lua_journal(events, rest).encode("ascii"))
        try:
            run = subprocess.run(
                [*lua_command(lua), str(REPLAY_SCRIPT), str(folder), str(journal), str(output)],
                capture_output=True, text=True, timeout=REPLAY_TIMEOUT_SECONDS, check=False)
        except subprocess.TimeoutExpired:
            raise IntegrityError(f"The addon replay did not finish within {REPLAY_TIMEOUT_SECONDS} seconds") from None
        except OSError as error:
            raise ToolError(f"Cannot run the Lua interpreter: {type(error).__name__}") from None
        if run.returncode != 0 or not output.is_file():
            raise IntegrityError("The addon rejected the journal during replay: " + clip(run.stderr or run.stdout))
        return validate_rows(read_json(output, MAX_ROWS_BYTES, "the replay output"))


def check_replay(ledger: Ledger, replay: Replay) -> None:
    if replay.enabled:
        actual = lua_rows(replay.addon, replay.lua, ledger.events, ledger.rest)
        report(row_differences(ledger.rows, actual), "Balances or caps differ from an independent addon replay")


def load_ledger(folder) -> Ledger:
    """Check manifest, hash chain, character digest and identity events. Does not run the addon replay."""
    folder = Path(folder)
    for name in (JOURNAL, ROWS, MANIFEST):
        if not (folder / name).is_file():
            raise IntegrityError(
                f"{folder} is missing {name}; restore the folder from Git (git checkout -- <folder>)")
    try:
        _, document = snapshot.read_export(folder / JOURNAL)
    except (OSError, ValueError, RecursionError) as error:
        raise IntegrityError(f"{JOURNAL} is invalid: {error}") from None
    check_envelope(document)
    events = document["database"]["events"]
    rest = {key: value for key, value in document["database"].items() if key != "events"}
    stored = read_json(folder / ROWS, MAX_ROWS_BYTES, ROWS)
    rows = validate_rows(stored)
    if canonical(rows) != canonical(stored):
        raise IntegrityError(f"{ROWS} is not in the minimal projected form")
    heads = chain_heads(events)
    expected = build_manifest(events, rows, heads)
    recorded = read_json(folder / MANIFEST, MAX_ROWS_BYTES, MANIFEST)
    if canonical(recorded) != canonical(expected):
        found = recorded if isinstance(recorded, dict) else {}
        names = sorted(key for key in set(expected) | set(found)
                       if canonical(found.get(key)) != canonical(expected.get(key)))
        raise IntegrityError(f"{MANIFEST} does not match the journal and rows (differs in: {', '.join(names)})")
    check_identity(events, rows)
    return Ledger(events, rest, rows, expected, heads)


def check_extends(old: Ledger, new: Ledger) -> None:
    if new.count < old.count:
        raise IntegrityError(f"History shrank: {old.count} events before, {new.count} now")
    if canonical(old.rest) != canonical(new.rest):
        raise IntegrityError("Database metadata changed")
    for index, (before, after) in enumerate(zip(old.events, new.events), 1):
        if canonical(before) != canonical(after):
            raise IntegrityError(f"History changed: event {index} differs from the previous ledger")


def verify_ledger(folder, replay: Replay, previous=None) -> Ledger:
    ledger = load_ledger(folder)
    check_replay(ledger, replay)
    if previous is not None:
        check_extends(load_ledger(previous), ledger)
    return ledger


def ingest(folder, export_path, characters_path, replay: Replay, durable: bool = True) -> dict:
    folder = Path(folder)
    try:
        _, document = snapshot.read_export(Path(export_path))
    except (OSError, ValueError, RecursionError) as error:
        raise IntegrityError(f"The journal export is not usable: {error}") from None
    check_envelope(document)
    events = document["database"]["events"]
    rest = {key: value for key, value in document["database"].items() if key != "events"}
    if not events:
        raise ToolError("The export has no events; nothing to ingest")
    rows = validate_rows(read_json(characters_path, MAX_ROWS_BYTES, "the character export"))
    check_identity(events, rows)
    heads = chain_heads(events)
    present = [name for name in (JOURNAL, ROWS, MANIFEST) if (folder / name).exists()]
    if present and len(present) != 3:
        raise IntegrityError(f"The ledger folder is incomplete; restore it with git checkout -- {folder}")
    added, status = len(events), "created"
    if present:
        existing = load_ledger(folder)
        if len(events) < existing.count:
            raise IntegrityError(
                f"Stale export: the ledger already has {existing.count} events but this export has {len(events)}")
        if canonical(rest) != canonical(existing.rest):
            raise IntegrityError("The export's database metadata differs from the ledger")
        for index, (old, new) in enumerate(zip(existing.events, events), 1):
            if canonical(old) != canonical(new):
                raise IntegrityError(
                    f"Conflicting history: event {index} differs from the approved ledger. Nothing was written")
        added, status = len(events) - existing.count, "updated"
        if added == 0:
            if canonical(rows) != canonical(existing.rows):
                raise IntegrityError(
                    "The export has the same events as the ledger but different character rows. Nothing was written")
            return {"status": "unchanged", "added": 0, "events": len(events), "chainHead": heads[-1],
                    "replayed": False}
    if replay.enabled:
        report(row_differences(rows, lua_rows(replay.addon, replay.lua, events, rest)),
               "Balances or caps differ from an independent addon replay. Nothing was written")
    manifest = build_manifest(events, rows, heads)
    write_atomic(folder / ROWS, indented(rows), durable)
    write_atomic(folder / JOURNAL, journal_bytes(events, rest), durable)
    write_atomic(folder / MANIFEST, indented(manifest), durable)
    return {"status": status, "added": added, "events": len(events), "chainHead": heads[-1],
            "replayed": replay.enabled}


def add_replay_arguments(parser) -> None:
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--replay-addon", metavar="DIR",
                       help="CappedDKP addon folder; replays the journal through the addon rules and compares balances")
    group.add_argument("--no-replay", action="store_true",
                       help="skip the replay; balances and caps are then NOT independently verified")
    parser.add_argument("--lua", metavar="PATH", help="Lua 5.1 interpreter for the replay (default: lua on PATH)")


def replay_from_args(args) -> Replay:
    if args.no_replay:
        return Replay()
    return Replay(Path(args.replay_addon), find_lua(args.lua))
