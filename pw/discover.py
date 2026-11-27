"""Look after the places of the facts a project has declared.

    python -m pw.discover [--repo DIR] [--model claude-opus-5-5] [--budget 5] [--apply] [--new]

The scope is what has been declared in pw-facts.json. For those facts an agent, which can read
files and nothing else, is asked two things:

  repair    a declared place that can no longer be read as declared (its file or part was
            removed or renamed, its pattern does not find what it should): where is that
            statement now?
  further   which other places of the repository state the fact, that the declaration misses?

What nobody declared is not looked at. Only with --new is the agent also asked to propose things
stated in several places that are not declared yet: bringing something into scope is a step of
its own, taken on request.

The agent reports through tools, and each report is checked against the files before it is
kept: the place has to exist, the quote has to be in it word for word, the value has to be in
the quote, and a pattern has to compute the value. What passes is a proposal, not a reading:
the agent saw every place at once, so nothing it says about what a place reads as is recorded.

Is a proposed place about the same thing? The searcher is the wrong one to ask: it has seen the
other places, and a number that happens to be the same looks like the same thing. So every
proposed place is shown, alone, to a blind reader with the fact's one-sentence description. A
place is kept if that reader reads a value off it (for a place with a pattern: the value the
pattern computes). A place the reader says does not state the thing is dropped, with the
reader's reason. A place whose reading differs from the other places is kept: that is a finding.
The agent may say a declared place is gone for good; taking it out of the declaration is left
to a person.

A search that failed must not look like a search that found nothing:
  - the agent has to say, per fact, that it finished searching; a session that does not is
    reported as incomplete, as is one whose tools never started or that ended in an error;
  - one known place of each declared fact is left out of what the agent is told. If the search
    does not come back with it, the search for that fact is reported as doubtful;
  - a proposed place the blind reader neither read nor declined is reported as unanswered and
    is not written.

With --apply the kept places are written into pw-facts.json and their blind readings are in the
record. Without it everything runs against a copy of the record and is only printed. How many
missing places this finds was measured by hiding declared ones: experiments/discovery/RESULTS.md.
"""
import argparse
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

from .check import FACTS
from .kernel import CALIBRATION, LOG, Kernel, KernelError, _anchored, _json_part, _md_section, _py_part, _read_pattern, compute, locate, pattern, reader

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TYPES = {"String": str, "Nat": int, "Int": int, "List String": str, "List Nat": int}
OWN = (FACTS, LOG, CALIBRATION)       # the list of places, the record and the measurements are not places themselves

HOW = """You are looking through a project's files for places that state the same thing, so that the
project can be told when they stop agreeing. You change nothing: you can read files (Read, Grep,
Glob) and report with the tools named below.

What a place is
  A place is where a file states the thing as it is now in this project: a default or constant in
  code, a pinned version in a configuration file, a sentence or table row in documentation that
  says what the value is.
  The test: if the value were changed on purpose, would this place have to change with it for the
  project to stay consistent? If yes, it is a place.
  Not a place: a dated record of what was the case once (results of an experiment, a changelog
  entry, a log), an example that merely happens to use the value, a test's input data.

  A list can also be stated in part. An example configuration uses some of the keys there are; a
  list of highlights names some of the commands. Such a place does not have to list everything,
  but whatever it lists has to exist: report it with `some` set to true, and as its value give
  the entries it mentions. An example that uses a key the code does not know is exactly what
  the project wants to hear about.

How to name a place
  "path" for a whole file, or "path::part" for the smallest part that holds the statement:
    Markdown   the text of a heading, exactly as written, without the #'s    docs/guide.md::3. Limits
    Python     the dotted name of a function, class, method or assignment    app/server.py::Server.__init__
    JSON       a dotted key                                                  package.json::engines.node
  Any other kind of file is named whole.

What to report for a place
  value   what the place says, as JSON: "fast", 14, ["a", "b"]
  quote   the line or sentence of the place that says it, copied character for character
  For code and configuration, also give a pattern that reads the value off the place, so that
  nobody has to read it again:
    find      a regular expression with exactly one group that matches exactly once in the place;
              the group is the value
    find_all  the same, where every match is one entry of a list
    kind      "string", "nat", "int", or "permille" (a decimal such as 0.9, read as 900)
    within    optional: a regular expression with one group that matches exactly once; `find` or
              `find_all` then looks only inside that group. Use it when the place holds several
              things of the same shape and you mean one of them (the choices next to "--format",
              the fields of one struct, the entries of one list).
    rewrite   optional: [pattern, replacement], applied to each piece found. The pattern has to
              match the piece as a whole; the replacement may use \\1 ... \\9. Use it when the
              place writes the value another way than the other places (["py(\\d)(\\d+)", "\\1.\\2"]
              turns py310 into 3.10).
  No look-around, back-references or named groups. Leave the pattern out for prose.
  For a Python file, and for a TOML or JSON file, prefer `structure` to a pattern: it reads the
  place by what it is, so quotes, spacing and line breaks do not matter and an entry added in
  another style is still seen. Give it instead of find/find_all, as an object:
    {"python": "value"}     the literal a name is assigned (name the assignment: path::NAME)
    {"python": "strings"}   every string literal in what a name is assigned (a set, a tuple, ...)
    {"python": "keys"}      the keys of the dictionary a name is assigned
    {"python": "names"}     the functions defined directly in the place (a module, or path::Class);
                            add "public": true to leave out _names, "decorator": "app.route" to keep
                            only those carrying that decorator
    {"python": "keyword", "call": "add_argument", "with": "--mode", "keyword": "default"}
                            the literal passed as that keyword to the one such call
    {"data": "package.version"}   a dotted path into a .toml or .json file, named whole; a step may
                            be * (every entry) or name[key=value]; add "keys": true for the keys
  with "as" (string, nat, int, permille), and "sort": true for a list, as needed.
  Read the place that really determines the thing, even if it writes the value differently:
  do not settle for another line that merely happens to spell it the same way.
  Never spell the value itself in the pattern. Write what stands around it, and let the group
  take any value of its kind: "topic == \"([a-z.]+)\"", not "topic == \"(system\\.return)\"". A pattern
  that fits only the present value cannot tell that the value has changed.

Each report is checked against the file, and you are told what is wrong: fix it and report again.
Ignore pw-facts.json, pw-log.jsonl, pw-calibration.json and anything under .git.
"""

FURTHER = """
Task. The project has declared the things below, and for each the places known to state it. The
lists may be incomplete. For each thing, search the whole repository for every further place that
states it and report each one with `add_place(fact, at, value, quote, ...)`. Report a place even
if it states a different value from the known ones: that is exactly what the project wants to
hear about. Search for the value itself, for other ways of writing it, and for the words that
describe it; look in documentation, code, configuration and build files alike. Do not report a
place that is already listed. When you have finished searching for a thing, call
`finished(fact, searched)` for it, whether or not you found anything: a thing you do not call
it for counts as not searched. Then reply with one line per thing: how you searched and what
you found.

Declared:
"""

REPAIR = """
Task. The project declared the things below and where each is stated. Some of those places can
no longer be read as declared: the file or the part was removed or renamed, or the pattern does
not find exactly what it should any more. They are marked CANNOT BE READ. For each of them, find
where that same statement is now and report it with `replace_place(fact, old, at, value, quote, ...)`:
`old` is the place as it is listed, `at` where the statement is now (the same place, if only
the pattern has to change). It has to be the statement that was declared, moved or reworded,
not another one that happens to give the same value. If the project no longer makes that
statement anywhere, say so with `gone(fact, old, why)`; do not put something else in its
place. When you are done with a thing, call `finished(fact, searched)`. Then reply with one
line per place.

Declared:
"""

NEW = """
Task. Find things this project states in two or more places and has not declared yet, and report
each with `new_fact(name, type, gloss, places)`. Where to look: defaults, limits and thresholds
that documentation describes and code sets; versions pinned in more than one configuration file;
lists (of commands, options, names, states) that documentation enumerates and code defines;
constants copied between files. Report a thing even if its places do not agree right now: that is
exactly what the project wants to hear about. Prefer things whose places could really drift
apart and would mislead someone if they did; leave out anything stated only once.

  name   a short name for the thing
  type   one of String, Nat, Int, List String, List Nat
  gloss  one sentence saying exactly what the value is, precise enough that someone shown a
         single place and nothing else could read the value off it (for a list: what the entries
         are, and that they are sorted). Say what the value is, not how it is used elsewhere:
         each place is shown alone to a reader who has to recognise it as stating this, and
         "the words a response starts with, which the client parses" cannot be checked from
         the one file that defines the words. "the status words of a response" can.
  places at least two, each {"at", "value", "quote"} and, for code and configuration, a pattern

When you have finished, call `finished("", searched)` saying where you looked, whether or not
you found anything, and reply with one line per thing you reported.
"""


class Refused(ValueError):
    pass


def _part(at, repo):
    """The text a place names. Unlike `locate`, a part that cannot be found is an error."""
    path, _, part = at.partition("::")
    if os.path.isabs(path) or ".." in path.split("/") or path.split("/")[0] == ".git" or path in OWN:
        raise Refused(f"{path} is not a file of the project that can be a place")
    full = os.path.join(repo, path)
    if not os.path.isfile(full):
        raise Refused(f"there is no file {path}")
    with open(full, "rb") as fh:
        raw = fh.read()
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        raise Refused(f"{path} is not text")
    if not part:
        return text
    found = None
    try:
        if path.endswith((".md", ".markdown")):
            found = _md_section(text, part)
            if found is None:
                heads = [m.group(1) for m in re.finditer(r"^#+\s+(.*?)\s*#*\s*$", text, re.M)]
                raise Refused(f"{path} has no heading {part!r}; its headings are {heads[:60]}")
        elif path.endswith(".json"):
            found = _json_part(text, part)
        elif path.endswith(".py"):
            found = _py_part(text, part)
        else:
            raise Refused(f"only Markdown, JSON and Python files have parts; name {path} whole")
    except (ValueError, SyntaxError, KeyError, IndexError, TypeError) as e:
        if isinstance(e, Refused):
            raise
        found = None
    if found is None:
        raise Refused(f"{path} has no part {part!r}")
    return found


def _json_value(typ, value):
    """The value as Python data, checked against the fact's type."""
    if typ not in TYPES:
        raise Refused(f"a type is one of {sorted(TYPES)}, not {typ!r}")
    if isinstance(value, str):
        try:
            value = json.loads(value)
        except ValueError:
            if typ != "String":
                raise Refused(f"the value has to be JSON of type {typ}, e.g. " + ('["a", "b"]' if "List" in typ else "14"))
    items = value if isinstance(value, list) else [value]
    if isinstance(value, list) != typ.startswith("List") or not all(type(x) is TYPES[typ] for x in items):
        raise Refused(f"{json.dumps(value, ensure_ascii=False)[:80]} is not a value of type {typ}")
    if typ.endswith("Nat") and any(x < 0 for x in items):
        raise Refused("a Nat is not negative")
    return value


def _reads_another(read, text):
    """Does the pattern still read the place when the value there is another one of its kind?
    A pattern that spells the value out can only ever find that one value."""
    found = text
    start = 0
    for step in [*read.get("within", []), read.get("find") or read["find_all"]]:
        m = re.search(step, found, re.M)
        if m is None:
            return True                                  # (not for this check to say)
        start, found = start + m.start(1), m.group(1)
    old = found
    if re.fullmatch(r"\d+", old):
        others = [str(int(old) + 1), str(int(old) + 10)]
    elif re.fullmatch(r"[\d.]*\d", old):
        others = [re.sub(r"\d$", lambda d: str((int(d.group(0)) + 1) % 10), old)]
    else:
        last = old[-1:]
        others = [old[:-1] + ("Q" if last.isupper() else "q" if last != "q" else "z"), old + "x", old + "X", old + "_x", old + "9",
                  re.sub(r"[A-Za-z]", lambda c: "Q" if c.group(0).isupper() else "q", old)]
    for new in others:
        try:
            got = json.loads(_read_pattern(read, text[:start] + new + text[start + len(old):]))
        except KernelError:
            continue
        want = new if read["as"] == "string" else None
        if want is None or got == want or (isinstance(got, list) and want in got):
            return True
    return False


def screen(repo, typ, at, value, quote, find=None, find_all=None, kind=None, within=None, rewrite=None, structure=None):
    """Check one reported place against the files. Returns the place as pw-facts.json lists it,
    with the value and quote kept alongside for whoever looks at the proposal."""
    text = _part(at, repo)
    value = _json_value(typ, value)
    if not quote or not _anchored(quote, at, repo):
        raise Refused("the quote is not in the place word for word")
    read = None
    if structure:
        if find or find_all:
            raise Refused("give a pattern or `structure`, not both")
        if not isinstance(structure, dict):
            raise Refused('`structure` is an object such as {"python": "keys"} or {"data": "package.version"}')
        try:
            term = compute(reader(structure, at), text)
            computed = json.loads(re.sub(r"\((-\d+)\)", r"\1", term))
        except KernelError as e:
            raise Refused(f"this way of reading does not work on the place: {e}")
        same = sorted(computed) == sorted(value) if isinstance(value, list) and isinstance(computed, list) else computed == value
        if not same:
            raise Refused(f"read that way the place gives {json.dumps(computed, ensure_ascii=False)[:200]}, not the value you gave")
        read = {**structure, **({"sort": True} if isinstance(computed, list) else {})}      # (a list is compared in one order, as with find_all)
    elif find or find_all:
        try:
            read = pattern(find or None, find_all or None, kind or ("nat" if typ.endswith("Nat") else "int" if typ == "Int" else "string"),
                           sort=bool(find_all), unique=False, within=within or None, rewrite=rewrite or None)
            term = _read_pattern(read, text)
            computed = json.loads(term.replace("(", "").replace(")", "") if read["as"] == "int" else term)
        except KernelError as e:
            raise Refused(f"the pattern does not work on this place: {e}")
        same = sorted(computed) == sorted(value) if isinstance(value, list) else computed == value
        if not same:
            raise Refused(f"the pattern reads {json.dumps(computed, ensure_ascii=False)[:200]} off the place, not the value you gave")
        if not rewrite and not _reads_another(read, text):
            raise Refused("the pattern fits only the value that is there now: were the value to change, the place would count as "
                          "unreadable instead of as saying something else. Do not spell the value in the pattern; write what is "
                          "around it and let the group take any value of its kind, e.g. \"([a-z.]+)\" or (\\d+)")
        read = {k: v for k, v in read.items() if k in ("find", "find_all", "as", "within", "rewrite") or (k == "sort" and v)}
    else:
        where = text if isinstance(value, list) else quote
        missing = [x for x in (value if isinstance(value, list) else [value]) if str(x) not in where]
        if missing:
            raise Refused(f"{json.dumps(missing, ensure_ascii=False)[:120]} does not occur in the {'place' if isinstance(value, list) else 'quote'}; "
                          "a value that has to be computed from the text needs a pattern")
    return {"at": at, "read": read, "value": value, "quote": " ".join(quote.split())}


def _agree(places):
    key = lambda v: json.dumps(sorted(v) if isinstance(v, list) else v, ensure_ascii=False)
    return len({key(p["value"]) for p in places}) == 1


# ---- the server the agent reports to -----------------------------------------------------------

def serve():
    try:  # mcp 2.x
        from mcp.server.mcpserver import MCPServer as FastMCP
    except ImportError:  # mcp 1.x
        from mcp.server.fastmcp import FastMCP

    repo, out = os.environ["PW_WORKDIR"], os.environ["PW_DISCOVER_OUT"]
    with open(os.environ["PW_DISCOVER_FACTS"], encoding="utf-8") as fh:
        facts = {f["name"]: f for f in json.load(fh)}
    mcp = FastMCP("find")

    def keep(entry):
        with open(out, "a", encoding="utf-8") as fh:
            fh.write(json.dumps(entry, ensure_ascii=False) + "\n")

    keep({"started": True})                    # without this line, nothing the session says about finding nothing counts

    @mcp.tool()
    def finished(fact: str = "", searched: str = "") -> dict:
        """Say that you have finished searching: for one declared fact (its name exactly as
        listed), or, with `fact` empty, for things not declared yet. `searched` says what you
        searched for and where. Call it even when you found nothing."""
        if fact and fact not in facts:
            return {"error": f"no declared fact is named {fact!r}; the names are {sorted(facts)}"}
        if not searched.strip():
            return {"error": "say what you searched for and where"}
        keep({"finished": fact, "searched": " ".join(searched.split())[:600]})
        return {"noted": fact or "new facts"}

    @mcp.tool()
    def add_place(fact: str, at: str, value: str | int | list, quote: str, find: str = "", find_all: str = "", kind: str = "",
                  some: bool = False, within: str = "", rewrite: list[str] | None = None, structure: dict | None = None) -> dict:
        """Report a further place that states a declared fact. `fact` is the fact's name exactly
        as listed, `at` the place ("path" or "path::part"), `value` what the place says as JSON
        text ("\\"fast\\"", "14", "[\\"a\\", \\"b\\"]"), `quote` the line of the place that says it,
        copied character for character. For code and configuration give `find` (or `find_all`
        for a list) and `kind` as well, and `within` or `rewrite` where needed; or, for Python, TOML
        and JSON, `structure` instead of a pattern. Set `some` for a
        place that lists only some entries of a list (an example, an excerpt): `value` is then
        the entries it mentions."""
        if fact not in facts:
            return {"error": f"no declared fact is named {fact!r}; the names are {sorted(facts)}"}
        known = [p if isinstance(p, str) else p["at"] for p in facts[fact]["places"]]
        if at in known:
            return {"error": f"{at} is already listed for this fact"}
        if some and not facts[fact]["type"].startswith("List "):
            return {"error": "only a list can be stated in part"}
        try:
            place = {**screen(repo, facts[fact]["type"], at, value, quote, find, find_all, kind, within, rewrite, structure), "some": bool(some)}
        except Refused as e:
            return {"error": str(e)}
        keep({"fact": fact, "place": place})
        facts[fact]["places"].append(at)
        return {"kept": at}

    @mcp.tool()
    def replace_place(fact: str, old: str, at: str, value: str | int | list, quote: str, find: str = "", find_all: str = "",
                      kind: str = "", within: str = "", rewrite: list[str] | None = None, structure: dict | None = None) -> dict:
        """Report where a declared place that can no longer be read is now. `old` is the place
        exactly as listed; `at`, `value`, `quote` and the pattern are as for `add_place`. `at`
        may equal `old` when only the pattern has to change."""
        if fact not in facts:
            return {"error": f"no declared fact is named {fact!r}; the names are {sorted(facts)}"}
        listed = {(p if isinstance(p, str) else p["at"]): p for p in facts[fact]["places"]}
        if old not in listed:
            return {"error": f"{old} is not listed for this fact; its places are {sorted(listed)}"}
        if at != old and at in listed:
            return {"error": f"{at} is already listed for this fact"}
        some = isinstance(listed[old], dict) and bool(listed[old].get("some"))
        try:
            place = {**screen(repo, facts[fact]["type"], at, value, quote, find, find_all, kind, within, rewrite, structure), "some": some}
        except Refused as e:
            return {"error": str(e)}
        keep({"replace": {"fact": fact, "old": old}, "place": place})
        return {"kept": f"{old} -> {at}"}

    @mcp.tool()
    def gone(fact: str, old: str, why: str) -> dict:
        """Say that a declared place cannot be repaired because the project no longer makes that
        statement there or anywhere it moved to. `why` says what happened to it."""
        if fact not in facts:
            return {"error": f"no declared fact is named {fact!r}; the names are {sorted(facts)}"}
        if old not in [p if isinstance(p, str) else p["at"] for p in facts[fact]["places"]]:
            return {"error": f"{old} is not listed for this fact"}
        if not why.strip():
            return {"error": "say what happened to the statement"}
        keep({"gone": {"fact": fact, "old": old, "why": " ".join(why.split())[:400]}})
        return {"noted": old}

    @mcp.tool()
    def new_fact(name: str, type: str, gloss: str, places: list[dict]) -> dict:
        """Report a thing stated in two or more places that is not declared yet. Each place is
        {"at": ..., "value": ..., "quote": ...} plus, for code and configuration, "find" or
        "find_all" and "kind" (and "within", "rewrite" where needed) or "structure", and "some": true for a place
        that lists only some entries of a list. `value` is what that place says, as JSON; places that state different values are
        reported as they are. At least one place has to state the whole of it."""
        if name in facts:
            return {"error": f"{name!r} is already declared; use add_place for further places"}
        if not gloss.strip():
            return {"error": "say in one sentence exactly what the value is"}
        kept, wrong = [], {}
        for p in places:
            try:
                extra = set(p) - {"at", "value", "quote", "find", "find_all", "kind", "some", "within", "rewrite", "structure"}
                if extra or not {"at", "value", "quote"} <= set(p):
                    raise Refused(f"a place has at, value, quote and optionally find, find_all, kind, within, rewrite, structure, some; not {sorted(extra)}")
                if p.get("some") and not type.startswith("List "):
                    raise Refused("only a list can be stated in part")
                kept.append({**screen(repo, type, p["at"], p["value"], p["quote"], p.get("find"), p.get("find_all"), p.get("kind"),
                                      p.get("within"), p.get("rewrite"), p.get("structure")),
                             "some": bool(p.get("some"))})
            except Refused as e:
                wrong[str(p.get("at"))] = str(e)
        if wrong:
            return {"error": "nothing was kept; fix these places and report the thing again", "places": wrong}
        if len({p["at"] for p in kept}) < 2:
            return {"error": "a thing stated in one place has nothing to disagree with; give at least two different places"}
        if all(p["some"] for p in kept):
            return {"error": "every place is marked as stating only some entries; one place has to state the whole list"}
        keep({"new": {"name": name, "type": type, "gloss": " ".join(gloss.split())}, "places": kept})
        facts[name] = {"type": type, "places": [p["at"] for p in kept]}      # further places can be added to it
        return {"kept": name, "the places that state the whole agree": _agree([p for p in kept if not p["some"]])}

    mcp.run()


# ---- running the agent -------------------------------------------------------------------------

def same_place(a, b, repo):
    """Same file, and one part contains the other."""
    if a.partition("::")[0] != b.partition("::")[0]:
        return False
    x, y = locate(a, repo), locate(b, repo)
    return x is not None and y is not None and (x in y or y in x)


def session(repo, model, prompt, facts, budget, expect):
    """One agent with read access to `repo`. Returns what it proposed and how the session went.

    `expect` lists what the agent has to say it finished ("" stands for the search for new
    facts). run["problems"] is empty only if the tools started, the session ended normally and
    everything expected was finished: only then does "nothing proposed" mean nothing was found.
    """
    work = tempfile.mkdtemp(prefix="pw-discover-")
    out, known, cfg = (os.path.join(work, n) for n in ("proposals.jsonl", "facts.json", "mcp.json"))
    with open(known, "w", encoding="utf-8") as fh:
        json.dump(facts, fh, ensure_ascii=False)
    with open(cfg, "w") as fh:
        json.dump({"mcpServers": {"find": {"command": sys.executable, "args": ["-P", "-m", "pw.discover", "--serve"], "env": {     # -P: not the pw of the repository being searched
            "PW_WORKDIR": repo, "PW_DISCOVER_OUT": out, "PW_DISCOVER_FACTS": known, "PYTHONPATH": ROOT}}}}, fh)
    r = subprocess.run(["claude", "-p", prompt, "--model", model, "--tools", "Read,Grep,Glob", "--mcp-config", cfg, "--strict-mcp-config",
                        "--allowedTools", "Read,Grep,Glob," + ",".join(
                            f"mcp__find__{t}" for t in ("add_place", "new_fact", "replace_place", "gone", "finished")),
                        "--output-format", "json", "--max-budget-usd", str(budget)],
                       cwd=repo, capture_output=True, text=True)
    lines = []
    if os.path.exists(out):
        with open(out, encoding="utf-8") as fh:
            lines = [json.loads(line) for line in fh]
    proposals = [x for x in lines if "fact" in x or "new" in x or "replace" in x or "gone" in x]
    done = {x["finished"] for x in lines if "finished" in x}
    run = {"model": model, "problems": []}
    if not any("started" in x for x in lines):
        run["problems"].append("the reporting tools never started, so the agent could not report anything")
    try:
        info = json.loads(r.stdout)
        run.update(turns=info.get("num_turns"), cost_usd=round(info.get("total_cost_usd", 0), 2), said=info.get("result", ""))
        if info.get("is_error") or info.get("subtype", "success") != "success":
            run["problems"].append(f"the session ended with {info.get('subtype') or 'an error'}")
    except ValueError:
        run["problems"].append("the session gave no result: " + (r.stdout + r.stderr)[-300:])
    missing = [e for e in expect if e not in done]
    if missing:
        run["problems"].append("the agent did not say it finished searching for: " + ", ".join(e or "new facts" for e in missing))
    run["unfinished"] = missing
    return proposals, run


def listing(facts, places=True):
    out = ""
    for f in facts:
        out += f'\n- "{f["name"]}" (type {f["type"]}): {f.get("gloss") or f["name"]}\n'
        if places:
            known = [p if isinstance(p, str) else p["at"] for p in f["places"]]
            out += "".join(f"    known place: {at}\n" for at in known) or "    known places: none yet\n"
    return out


def _at(p):
    return p if isinstance(p, str) else p["at"]


def further(repo, model, facts, budget, hide=None):
    """Search for further places of the declared facts.

    `hide` maps a fact's name to one of its places: that place is left out of what the agent is
    told, as a control with a known answer. A proposal that names it shows the search works
    and is not returned; run["controls"] says which controls came back.
    """
    hide = hide or {}
    shown = [{**f, "places": [p for p in f["places"] if _at(p) != hide.get(f["name"])]} for f in facts]
    proposals, run = session(repo, model, HOW + FURTHER + listing(shown), shown, budget, [f["name"] for f in facts])
    back = lambda p: "fact" in p and p["fact"] in hide and same_place(hide[p["fact"]], p["place"]["at"], repo)
    run["controls"] = {name: {"at": at, "found": any(back(p) and p["fact"] == name for p in proposals)} for name, at in hide.items()}
    return [p for p in proposals if not back(p)], run


def repair(repo, model, facts, broken, budget):
    """Look for where declared places that can no longer be read have gone.

    `broken` is [(fact name, place, why it cannot be read)]. Only the facts concerned are shown.
    """
    why = {(name, at): reason for name, at, reason in broken}
    shown = [f for f in facts if any(name == f["name"] for name, _, _ in broken)]
    text = ""
    for f in shown:
        text += f'\n- "{f["name"]}" (type {f["type"]}): {f.get("gloss") or f["name"]}\n'
        for p in f["places"]:
            at = _at(p)
            read = f'   read by: {json.dumps(p["read"], ensure_ascii=False)}' if isinstance(p, dict) and p.get("read") else ""
            part = "   (states only some entries)" if isinstance(p, dict) and p.get("some") else ""
            mark = f'    CANNOT BE READ: {why[(f["name"], at)]}\n      listed as: {at}{read}{part}\n' if (f["name"], at) in why else f"    place: {at}{part}\n"
            text += mark
    return session(repo, model, HOW + REPAIR + text, shown, budget, [f["name"] for f in shown])


def new(repo, model, facts, budget):
    declared = "\nAlready declared (do not report these again):\n" + listing(facts, places=False) if facts else ""
    return session(repo, model, HOW + NEW + declared, facts, budget, [""])


def confirm(repo, lean_dir, facts, proposals, model, budget, record):
    """Show every proposed place, alone, to a blind reader, and keep what it reads.

    Returns (facts with the kept places, one verdict per proposed place, reader sessions).
    A verdict is {"fact", "at", "kept", "why"}; "answered" is False where the reader did
    neither read nor decline, which says nothing about the place.
    """
    from .maintain import read_blind                      # (maintain imports nothing from here)
    from .lean_gate import LeanGate
    merged, added = merge(facts, proposals)
    if not added:
        return facts, [], []
    work = tempfile.mkdtemp(prefix="pw-confirm-")
    with open(os.path.join(work, FACTS), "w", encoding="utf-8") as fh:
        json.dump(merged, fh, ensure_ascii=False)
    kernel = Kernel(record, gate=LeanGate(lean_dir), actor="discover")
    kernel.sync_facts(os.path.join(work, FACTS))
    decisions = {d["fact"]: d for d in kernel.recheck(repo)["decisions"]}
    args = argparse.Namespace(lean_dir=lean_dir, budget=budget)
    runs = read_blind(kernel, repo, args, [(decisions[name], place["at"]) for name, place in added], model, "proposed")
    actors = {r["actor"] for r in runs}
    said = {}
    for e in kernel.events():
        if e.get("actor") in actors and e["type"] in ("reading", "decline"):
            said[(e["h"], e["place"])] = e
    decisions = {d["fact"]: d for d in kernel.recheck(repo)["decisions"]}
    verdicts = []
    for name, place in added:
        d = decisions[name]
        e = said.get((d["h"], place["at"]))
        v = {"fact": name, "at": place["at"], "kept": False, "answered": e is not None}
        if e is None:
            v["why"] = "the blind reader neither read it nor declined: not checked"
        elif e["type"] == "decline":
            v["why"] = "a blind reader says the place does not state this: " + e["why"]
        else:
            read = e["obj"]["text"]
            computed = next((p["reads as"] for p in d["places"] if p["at"] == place["at"] and p["by"] == "reader"), None)
            agree = computed is None or _same_term(read, computed)
            v.update(kept=agree, why=f"a blind reader reads {read[:80]} off it" + (
                "" if agree else f", but the pattern computes {computed[:80]}: the pattern is not reading what the place says"))
        verdicts.append(v)
    kept = {(v["fact"], v["at"]) for v in verdicts if v["kept"]}
    name = lambda p: p["replace"]["fact"] if "replace" in p else p.get("fact")
    final, _ = merge(facts, [{**p, "places": [q for q in p["places"] if (p["new"]["name"], q["at"]) in kept]} if "new" in p else p
                             for p in proposals if "new" in p or ("place" in p and (name(p), p["place"]["at"]) in kept)])
    declared = {f["name"] for f in facts}
    partial = lambda p: isinstance(p, dict) and p.get("some")
    for f in [f for f in final if f["name"] not in declared and (len(f["places"]) < 2 or all(partial(p) for p in f["places"]))]:
        final.remove(f)                                    # nothing left to compare, or nothing that states the whole of it
        for v in verdicts:
            if v["fact"] == f["name"] and v["kept"]:
                v.update(kept=False, why=v["why"] + "; but what was kept of this thing is one place, or only places that state it in part")
    return final, verdicts, runs


def _same_term(a, b):
    try:
        return json.loads(a) == json.loads(b)
    except ValueError:
        return " ".join(a.split()) == " ".join(b.split())


def merge(facts, proposals):
    """The declared facts with the proposals added. Returns (facts, what was added)."""
    facts = json.loads(json.dumps(facts))
    by_name = {f["name"]: f for f in facts}
    added = []

    def put(f, place):
        if place["at"] in [p if isinstance(p, str) else p["at"] for p in f["places"]]:
            return
        entry = {"at": place["at"], **({"read": place["read"]} if place["read"] else {}), **({"some": True} if place.get("some") else {})}
        f["places"].append(entry if len(entry) > 1 else place["at"])
        added.append((f["name"], place))

    for p in proposals:
        if "gone" in p:
            continue                               # taking a declared place away is for a person
        if "replace" in p:
            f, place = by_name[p["replace"]["fact"]], p["place"]
            at = [q if isinstance(q, str) else q["at"] for q in f["places"]]
            entry = {"at": place["at"], **({"read": place["read"]} if place["read"] else {}), **({"some": True} if place.get("some") else {})}
            if p["replace"]["old"] in at and (place["at"] == p["replace"]["old"] or place["at"] not in at):
                f["places"][at.index(p["replace"]["old"])] = entry if len(entry) > 1 else place["at"]
                added.append((f["name"], place))
        elif "fact" in p:
            put(by_name[p["fact"]], p["place"])
        elif p["new"]["name"] not in by_name:
            f = by_name[p["new"]["name"]] = {**p["new"], "places": []}
            facts.append(f)
            for place in p["places"]:
                put(f, place)
    return facts, added


def broken_places(repo, lean_dir, facts):
    """The declared places that can no longer be read as declared: [(fact name, place, why)].
    Found by holding the facts against the files, on a copy of the record."""
    from .lean_gate import LeanGate
    work = tempfile.mkdtemp(prefix="pw-discover-")
    record = os.path.join(work, LOG)
    if os.path.exists(os.path.join(repo, LOG)):
        shutil.copy(os.path.join(repo, LOG), record)
    with open(os.path.join(work, FACTS), "w", encoding="utf-8") as fh:
        json.dump(facts, fh, ensure_ascii=False)
    kernel = Kernel(record, gate=LeanGate(lean_dir), actor="discover")
    kernel.sync_facts(os.path.join(work, FACTS))
    return [(d["fact"], u["at"], u["why"]) for d in kernel.recheck(repo)["decisions"] for u in d.get("unread", []) if u.get("broken")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir")
    ap.add_argument("--model", default="claude-opus-5-5", help="the model that searches")
    ap.add_argument("--confirm-model", default="claude-sonnet-5-5",
                    help="the model that is shown each proposed place alone; it should be a measured reader")
    ap.add_argument("--budget", type=float, default=5.0)
    ap.add_argument("--new", action="store_true",
                    help="also have the agent propose things that are not declared yet. Without this, only what is declared is looked after")
    ap.add_argument("--only", choices=("repair", "further", "new"),
                    help="do one thing only: repair declared places that cannot be read, look for further places of declared facts, or propose new facts")
    ap.add_argument("--no-controls", action="store_true", help="tell the agent every known place, hiding none as a control")
    ap.add_argument("--seed", type=int, help="which known places are hidden as controls")
    ap.add_argument("--apply", action="store_true", help="write the places a blind reader confirmed into pw-facts.json")
    ap.add_argument("--serve", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args()
    if args.serve:
        return serve()
    from .maintain import ready
    ready(own_tools=True)
    from .lean_gate import LEAN_DIR
    lean_dir = args.lean_dir or LEAN_DIR
    repo = os.path.abspath(args.repo)
    path = os.path.join(repo, FACTS)
    facts = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
    want_new = args.new or args.only == "new"
    if not facts and not want_new:
        print(f"No facts are declared in {FACTS}, so there is nothing to look after. With --new the agent proposes some.")
        return
    broken = broken_places(repo, lean_dir, facts) if facts and args.only in (None, "repair") else []
    for name, at, why in broken:
        print(f"cannot be read as declared: {name} at {at}: {why[:160]}")
    lost = {(name, at) for name, at, _ in broken}
    rng = random.Random(args.seed)
    hide = {}
    if not args.no_controls:                                # a known place that can be read, left out as a control
        for f in facts:
            good = [_at(p) for p in f["places"] if (f["name"], _at(p)) not in lost]
            if len(good) > 1:
                hide[f["name"]] = rng.choice(good)
    jobs = [j for j in (
        ("repair", lambda: repair(repo, args.model, facts, broken, args.budget)) if broken else None,
        ("further", lambda: further(repo, args.model, facts, args.budget, hide)) if facts and args.only in (None, "further") else None,
        ("new", lambda: new(repo, args.model, facts, args.budget)) if want_new and args.only in (None, "new") else None) if j]
    if not jobs:
        print("nothing to do: every declared place can be read")
        return
    what = {"repair": "where unreadable places went", "further": "further places of declared facts", "new": "new facts"}
    print(f"looking for {', '.join(what[n] for n, _ in jobs)} with {args.model}", flush=True)
    with ThreadPoolExecutor(3) as pool:
        ran = list(pool.map(lambda j: j[1](), jobs))
    proposals = [p for ps, _ in ran for p in ps]
    failed = False
    for (name, _), (_, run) in zip(jobs, ran):
        print(f"   {name}: {run.get('turns')} turns, ${run.get('cost_usd')}")
        for problem in run["problems"]:
            failed = True
            print(f"   {name}: INCOMPLETE: {problem}")
        controls = run.get("controls", {})
        if controls:
            missed = [f"{n} at {c['at']}" for n, c in controls.items() if not c["found"]]
            print(f"   {name}: {len(controls) - len(missed)} of {len(controls)} hidden known places came back")
            for m in missed:
                print(f"   {name}: the search did not come back with {m}: it may have missed other places of that fact too")

    was = {(p["replace"]["fact"], p["place"]["at"]): p["replace"]["old"] for p in proposals if "replace" in p}
    for p in proposals:
        if "gone" in p:
            g = p["gone"]
            print(f"\nthe agent says the project no longer states {g['fact']} at {g['old']}: {g['why'][:300]}\n"
                  f"   taking a declared place away is for a person: remove it from {FACTS} if that is so")
    _, added = merge(facts, proposals)
    verdicts, kept, unanswered, runs, final = [], [], [], [], facts
    if added:
        record = os.path.join(repo, LOG)
        if not args.apply:                                  # look, but leave the project's record alone
            record = os.path.join(tempfile.mkdtemp(prefix="pw-discover-"), LOG)
            if os.path.exists(os.path.join(repo, LOG)):
                shutil.copy(os.path.join(repo, LOG), record)
        final, verdicts, runs = confirm(repo, lean_dir, facts, proposals, args.confirm_model, args.budget, record)
        by = {(v["fact"], v["at"]): v for v in verdicts}
        declared = {f["name"] for f in facts}
        for name in dict.fromkeys(n for n, _ in added):
            places = [p for n, p in added if n == name]
            print(f"\n{'place(s) of' if name in declared else 'new fact'}: {name}")
            for p in places:
                v = by[(name, p["at"])]
                mark = "keep" if v["kept"] else "drop" if v["answered"] else "????"
                moved = f"  (instead of {was[(name, p['at'])]})" if (name, p["at"]) in was else ""
                print(f"   {mark} {p['at']}{moved}  {'lists in part' if p.get('some') else 'says'} {json.dumps(p['value'], ensure_ascii=False)[:100]}"
                      + ("  (computed)" if p["read"] else ""))
                print(f"        {p['quote'][:160]}")
                print(f"        {v['why'][:300]}")
            if name not in declared and not _agree([p for p in places if by[(name, p['at'])]['kept'] and not p.get("some")]):
                print("   the kept places do not state the same value")
        unanswered = [v for v in verdicts if not v["answered"]]
        kept = [v for v in verdicts if v["kept"]]
        failed = failed or bool(unanswered) or any(r.get("error") for r in runs)
        print(f"\n{len(kept)} of {len(verdicts)} proposed place(s) kept, {len(verdicts) - len(kept) - len(unanswered)} dropped, "
              f"{len(unanswered)} not checked")
        if args.apply and kept:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(final, fh, ensure_ascii=False, indent=1)
                fh.write("\n")
            from .lean_gate import LeanGate
            Kernel(record, gate=LeanGate(lean_dir), actor="discover").sync_facts(path)
            print(f"written to {FACTS}; their blind readings are in the record. Then: python -m pw.maintain")
        elif not args.apply:
            print(f"nothing was written (--apply writes the kept places to {FACTS})")
    else:
        print("\nnothing proposed" + (" (but the search was incomplete: this does not mean there is nothing)" if failed else ""))
    repaired = {(v["fact"], was[(v["fact"], v["at"])]) for v in kept if (v["fact"], v["at"]) in was}
    still = [(name, at) for name, at, _ in broken if (name, at) not in repaired]
    for name, at in still:
        print(f"still cannot be read as declared: {name} at {at}")
    if failed:
        print("part of this run failed (marked INCOMPLETE or ???? above): that is not a finding, run it again")
    sys.exit(1 if failed or still else 0)


if __name__ == "__main__":
    from .kernel import cli
    cli(main)
