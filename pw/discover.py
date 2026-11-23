"""Find where the project states the same thing more than once.

    python -m pw.discover [--repo DIR] [--model claude-opus-5-5] [--budget 5] [--apply]

`pw.check` only holds together the places someone listed in pw-facts.json. A place nobody listed
can drift without a word. This asks an agent to look for what the list is missing:

  further places   for each declared fact, other places in the repository that state it
  new facts        things stated in two or more places that are not declared at all

The agent can read files and nothing else. It reports through two tools, and each report is
checked against the files before it is kept: the place has to exist, the quote has to be in it
word for word, the value has to be in the quote, and a pattern has to compute the value. What
passes is a proposal, not a reading: the agent saw every place at once, so nothing it says about
what a place reads as is recorded. With --apply the proposals are written into pw-facts.json;
`python -m pw.maintain` then has the new places read blind, and `pw.check` compares them.

Without --apply the proposals are only printed. How many missing places this finds was measured
by hiding declared ones: experiments/discovery/RESULTS.md.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

from .check import FACTS
from .kernel import CALIBRATION, LOG, KernelError, _anchored, _json_part, _md_section, _py_part, _read_pattern, locate, pattern

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
  No look-around, back-references or named groups. Leave the pattern out for prose.

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
place that is already listed. When you are done, reply with one line per thing: how you searched
and what you found.

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
         are, and that they are sorted)
  places at least two, each {"at", "value", "quote"} and, for code and configuration, a pattern

When you are done, reply with one line per thing you reported.
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


def screen(repo, typ, at, value, quote, find=None, find_all=None, kind=None):
    """Check one reported place against the files. Returns the place as pw-facts.json lists it,
    with the value and quote kept alongside for whoever looks at the proposal."""
    text = _part(at, repo)
    value = _json_value(typ, value)
    if not quote or not _anchored(quote, at, repo):
        raise Refused("the quote is not in the place word for word")
    read = None
    if find or find_all:
        try:
            read = pattern(find or None, find_all or None, kind or ("nat" if typ.endswith("Nat") else "int" if typ == "Int" else "string"),
                           sort=bool(find_all), unique=False)
            term = _read_pattern(read, text)
            computed = json.loads(term.replace("(", "").replace(")", "") if read["as"] == "int" else term)
        except KernelError as e:
            raise Refused(f"the pattern does not work on this place: {e}")
        same = sorted(computed) == sorted(value) if isinstance(value, list) else computed == value
        if not same:
            raise Refused(f"the pattern reads {json.dumps(computed, ensure_ascii=False)[:200]} off the place, not the value you gave")
        read = {k: v for k, v in read.items() if k in ("find", "find_all", "as") or (k == "sort" and v)}
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

    @mcp.tool()
    def add_place(fact: str, at: str, value: str | int | list, quote: str, find: str = "", find_all: str = "", kind: str = "") -> dict:
        """Report a further place that states a declared fact. `fact` is the fact's name exactly
        as listed, `at` the place ("path" or "path::part"), `value` what the place says as JSON
        text ("\\"fast\\"", "14", "[\\"a\\", \\"b\\"]"), `quote` the line of the place that says it,
        copied character for character. For code and configuration give `find` (or `find_all`
        for a list) and `kind` as well."""
        if fact not in facts:
            return {"error": f"no declared fact is named {fact!r}; the names are {sorted(facts)}"}
        known = [p if isinstance(p, str) else p["at"] for p in facts[fact]["places"]]
        if at in known:
            return {"error": f"{at} is already listed for this fact"}
        try:
            place = screen(repo, facts[fact]["type"], at, value, quote, find, find_all, kind)
        except Refused as e:
            return {"error": str(e)}
        keep({"fact": fact, "place": place})
        return {"kept": at}

    @mcp.tool()
    def new_fact(name: str, type: str, gloss: str, places: list[dict]) -> dict:
        """Report a thing stated in two or more places that is not declared yet. Each place is
        {"at": ..., "value": ..., "quote": ...} plus, for code and configuration, "find" or
        "find_all" and "kind". `value` is what that place says, as JSON; places that state
        different values are reported as they are."""
        if name in facts:
            return {"error": f"{name!r} is already declared; use add_place for further places"}
        if not gloss.strip():
            return {"error": "say in one sentence exactly what the value is"}
        kept, wrong = [], {}
        for p in places:
            try:
                extra = set(p) - {"at", "value", "quote", "find", "find_all", "kind"}
                if extra or not {"at", "value", "quote"} <= set(p):
                    raise Refused(f"a place has at, value, quote and optionally find, find_all, kind; not {sorted(extra)}")
                kept.append(screen(repo, type, p["at"], p["value"], p["quote"], p.get("find"), p.get("find_all"), p.get("kind")))
            except Refused as e:
                wrong[str(p.get("at"))] = str(e)
        if wrong:
            return {"error": "nothing was kept; fix these places and report the thing again", "places": wrong}
        if len({p["at"] for p in kept}) < 2:
            return {"error": "a thing stated in one place has nothing to disagree with; give at least two different places"}
        keep({"new": {"name": name, "type": type, "gloss": " ".join(gloss.split())}, "places": kept})
        return {"kept": name, "the places agree": _agree(kept)}

    mcp.run()


# ---- running the agent -------------------------------------------------------------------------

def session(repo, model, prompt, facts, budget):
    """One agent with read access to `repo`. Returns what it proposed and how the session went."""
    work = tempfile.mkdtemp(prefix="pw-discover-")
    out, known, cfg = (os.path.join(work, n) for n in ("proposals.jsonl", "facts.json", "mcp.json"))
    with open(known, "w", encoding="utf-8") as fh:
        json.dump(facts, fh, ensure_ascii=False)
    with open(cfg, "w") as fh:
        json.dump({"mcpServers": {"find": {"command": sys.executable, "args": ["-P", "-m", "pw.discover", "--serve"], "env": {     # -P: not the pw of the repository being searched
            "PW_WORKDIR": repo, "PW_DISCOVER_OUT": out, "PW_DISCOVER_FACTS": known, "PYTHONPATH": ROOT}}}}, fh)
    r = subprocess.run(["claude", "-p", prompt, "--model", model, "--tools", "Read,Grep,Glob", "--mcp-config", cfg, "--strict-mcp-config",
                        "--allowedTools", "Read,Grep,Glob,mcp__find__add_place,mcp__find__new_fact",
                        "--output-format", "json", "--max-budget-usd", str(budget)],
                       cwd=repo, capture_output=True, text=True)
    proposals = []
    if os.path.exists(out):
        with open(out, encoding="utf-8") as fh:
            proposals = [json.loads(line) for line in fh]
    try:
        info = json.loads(r.stdout)
        run = {"model": model, "turns": info.get("num_turns"), "cost_usd": round(info.get("total_cost_usd", 0), 2), "said": info.get("result", "")}
    except ValueError:
        run = {"model": model, "error": (r.stdout + r.stderr)[-500:]}
    return proposals, run


def listing(facts, places=True):
    out = ""
    for f in facts:
        out += f'\n- "{f["name"]}" (type {f["type"]}): {f.get("gloss") or f["name"]}\n'
        if places:
            known = [p if isinstance(p, str) else p["at"] for p in f["places"]]
            out += "".join(f"    known place: {at}\n" for at in known) or "    known places: none yet\n"
    return out


def further(repo, model, facts, budget):
    return session(repo, model, HOW + FURTHER + listing(facts), facts, budget)


def new(repo, model, facts, budget):
    declared = "\nAlready declared (do not report these again):\n" + listing(facts, places=False) if facts else ""
    return session(repo, model, HOW + NEW + declared, facts, budget)


def merge(facts, proposals):
    """The declared facts with the proposals added. Returns (facts, what was added)."""
    facts = json.loads(json.dumps(facts))
    by_name = {f["name"]: f for f in facts}
    added = []

    def put(f, place):
        if place["at"] in [p if isinstance(p, str) else p["at"] for p in f["places"]]:
            return
        f["places"].append({"at": place["at"], "read": place["read"]} if place["read"] else place["at"])
        added.append((f["name"], place))

    for p in proposals:
        if "fact" in p:
            put(by_name[p["fact"]], p["place"])
        elif p["new"]["name"] not in by_name:
            f = by_name[p["new"]["name"]] = {**p["new"], "places": []}
            facts.append(f)
            for place in p["places"]:
                put(f, place)
    return facts, added


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--budget", type=float, default=5.0)
    ap.add_argument("--only", choices=("further", "new"), help="look only for further places of declared facts, or only for new facts")
    ap.add_argument("--apply", action="store_true", help="write the proposals into pw-facts.json")
    ap.add_argument("--serve", action="store_true", help=argparse.SUPPRESS)
    args = ap.parse_args()
    if args.serve:
        return serve()
    repo = os.path.abspath(args.repo)
    path = os.path.join(repo, FACTS)
    facts = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else []
    jobs = [j for j in ((further, "further") if facts else None, (new, "new")) if j and args.only in (None, j[1])]
    print(f"looking for {' and '.join('further places' if n == 'further' else 'new facts' for _, n in jobs)} with {args.model}", flush=True)
    with ThreadPoolExecutor(2) as pool:
        ran = list(pool.map(lambda j: j[0](repo, args.model, facts, args.budget), jobs))
    proposals = [p for ps, _ in ran for p in ps]
    for (_, name), (_, run) in zip(jobs, ran):
        print(f"   {name}: " + (run.get("error") or f"{run['turns']} turns, ${run['cost_usd']}"))
    merged, added = merge(facts, proposals)
    values = {}
    for name, place in added:
        values.setdefault(name, []).append(place)
    for name, places in values.items():
        is_new = name not in [f["name"] for f in facts]
        print(f"\n{'new fact' if is_new else 'further place(s) of'}: {name}")
        for p in places:
            print(f"   {p['at']}  says {json.dumps(p['value'], ensure_ascii=False)[:100]}" + ("  (pattern)" if p["read"] else ""))
            print(f"      {p['quote'][:160]}")
        if is_new and not _agree(places):
            print("   these places do not state the same value")
    if not added:
        print("\nnothing proposed")
    elif args.apply:
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(merged, fh, ensure_ascii=False, indent=1)
            fh.write("\n")
        print(f"\n{len(added)} place(s) written to {FACTS}. Commit, then: python -m pw.maintain")
    else:
        print(f"\n{len(added)} place(s) proposed; nothing was written (--apply writes them to {FACTS})")


if __name__ == "__main__":
    main()
