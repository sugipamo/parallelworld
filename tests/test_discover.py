"""pw discover: an agent that looks for the places of declared facts, and the checks that stand
between what it reports and the declaration. Driven from outside, through the executable only:
the screening of a reported place (`pw kernel` op screen_place), the tools the agent reports
through (`pw mcp` with PW_TOOLS=find), and whole runs of `pw discover` with a stand-in for claude
(PW_CLAUDE) that says what a plan tells it to, through the same tools a real session has."""
import json
import os
import subprocess
import sys

import pytest

from test_rust import PW, pw  # noqa: F401  (the fixture that makes the build)


class Refused(Exception):
    pass


def screen(repo, typ, at, value, quote, **how):
    """Check one reported place against the files, as the find tools do before keeping it."""
    req = {"op": "screen_place", "cwd": repo, "type": typ, "at": at, "value": value, "quote": quote, **how}
    r = json.loads(subprocess.run([PW, "kernel"], input=json.dumps(req), capture_output=True, text=True).stdout)
    if "error" in r:
        assert r["kind"] == "Refused"
        raise Refused(r["error"])
    return r["ok"]


def refused(*a, **kw):
    with pytest.raises(Refused) as e:
        screen(*a, **kw)
    return str(e.value)


# ---- screening a reported place ------------------------------------------------------------------

def test_a_proposed_place_is_checked_against_the_file(pw, tmp_path):
    repo = str(tmp_path)
    (tmp_path / "guide.md").write_text("# Guide\n\n## Limits\n\nAt most 14 atoms are solved. The class is `fast`.\n\n## Other\n\nNothing.\n")
    (tmp_path / "app.py").write_text('LIMIT = 14\n\ndef run(threshold=0.9, mode="fast"):\n    return threshold\n\nNAMES = ["b", "a"]\n')
    (tmp_path / "pw-log.jsonl").write_text("{}\n")

    p = screen(repo, "Nat", "guide.md::Limits", 14, "At most 14 atoms are solved.")
    assert p == {"at": "guide.md::Limits", "read": None, "value": 14, "quote": "At most 14 atoms are solved."}
    assert screen(repo, "Nat", "guide.md::Limits", "14", "At most 14 atoms are solved.")["value"] == 14      # JSON text is accepted too
    assert "word for word" in refused(repo, "Nat", "guide.md::Limits", 14, "At most 14 atoms can be solved.")
    assert "word for word" in refused(repo, "Nat", "guide.md::Other", 14, "At most 14 atoms are solved.")          # the quote is in another part
    assert "does not occur in the quote" in refused(repo, "Nat", "guide.md::Limits", 15, "At most 14 atoms are solved.")
    assert refused(repo, "Nat", "guide.md::Limit", 14, "x") == "guide.md has no heading 'Limit'; its headings are ['Guide', 'Limits', 'Other']"
    assert "no file" in refused(repo, "Nat", "missing.md", 14, "x")
    assert "not a value of type Nat" in refused(repo, "Nat", "guide.md::Limits", '"14"', "At most 14 atoms are solved.")
    assert refused(repo, "Bool", "guide.md::Limits", 14, "x") == "a type is one of ['Int', 'List Nat', 'List String', 'Nat', 'String'], not 'Bool'"
    assert "a Nat is not negative" == refused(repo, "Nat", "guide.md::Limits", -1, "At most 14 atoms are solved.")
    for own in ("pw-log.jsonl", "../guide.md", ".git/config", "/etc/hostname"):
        assert "not a file of the project" in refused(repo, "Nat", own, 14, "x")

    p = screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"LIMIT = (\d+)")
    assert p["read"] == {"find": r"LIMIT = (\d+)", "as": "nat"}
    p = screen(repo, "Nat", "app.py::run", 900, "def run(threshold=0.9", find=r"threshold=([0-9.]+)", kind="permille")
    assert p["read"]["as"] == "permille"                                             # a computed value need not be in the quote
    assert "needs a pattern" in refused(repo, "Nat", "app.py::run", 900, "def run(threshold=0.9")
    assert "not the value you gave" in refused(repo, "Nat", "app.py::LIMIT", 15, "LIMIT = 14", find=r"LIMIT = (\d+)")
    assert "does not work" in refused(repo, "Nat", "app.py", 14, "LIMIT = 14", find=r"(\d+)")                      # matches more than once
    assert "inline flags" in refused(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"(?m)^LIMIT = (\d+)")   # not common to all engines
    # a pattern can be confined to one part of the place, and a piece can be rewritten into the other places' spelling
    (tmp_path / "tox.ini").write_text("[tox]\nenvlist = lint,py{310,311,315t},docs\n\n[gh]\npython =\n    3.10 = py310\n")
    (tmp_path / "cli.py").write_text('quote = Choice(["always", "never"])\nfmt = option("--format", Choice(["simple", "json"]))\n')
    p = screen(repo, "List String", "tox.ini", ["3.10", "3.11"], "envlist = lint,py{310,311,315t},docs",
               find_all=r"(\d+)(?:,|$)", within=r"^envlist = .*py\{([^}]+)\}", rewrite=[r"(\d)(\d+)", r"\1.\2"])
    assert p["read"] == {"find_all": r"(\d+)(?:,|$)", "as": "string", "sort": True,
                         "within": [r"^envlist = .*py\{([^}]+)\}"], "rewrite": [r"(\d)(\d+)", r"\1.\2"]}
    p = screen(repo, "List String", "cli.py", ["json", "simple"], 'fmt = option("--format", Choice(["simple", "json"]))',
               find_all=r'"(\w+)"', within=r'"--format", Choice\(\[([^\]]+)\]')
    assert p["read"]["within"] == [r'"--format", Choice\(\[([^\]]+)\]']
    assert "`within` matches 2 times" in refused(repo, "List String", "cli.py", ["json"], 'quote = Choice(["always", "never"])',
                                                 find_all=r'"(\w+)"', within=r"Choice\(\[([^\]]+)\]")
    assert "does not match '315t' as a whole" in refused(repo, "List String", "tox.ini", ["3.10"], "envlist = lint,py{310,311,315t},docs",
                                                        find_all=r"(\w+)(?:,|$)", within=r"py\{([^}]+)\}", rewrite=[r"(\d)(\d+)", r"\1.\2"])
    for bad in ([r"(\d)", r"\2"], [r"(\d)", r"\n"], [r"(?=x)(\d)", r"\1"]):
        assert "does not work" in refused(repo, "List String", "tox.ini", ["3.10"], "envlist = lint,py{310,311,315t},docs", find_all=r"(\d+),", rewrite=bad)
    assert screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"^(?:LIMIT) = (\d+)")["read"]         # (?: ) is fine
    p = screen(repo, "List String", "app.py::NAMES", ["a", "b"], 'NAMES = ["b", "a"]', find_all=r'"(\w)"')
    assert p["read"] == {"find_all": r'"(\w)"', "as": "string", "sort": True}
    (tmp_path / "notes.txt").write_text("14\n")
    assert "only Markdown, JSON and Python" in refused(repo, "Nat", "notes.txt::x", 14, "14")
    # or by its structure, which has to give the value too
    p = screen(repo, "List String", "app.py::NAMES", ["b", "a"], 'NAMES = ["b", "a"]', structure={"python": "strings"})
    assert p["read"] == {"python": "strings", "sort": True}
    assert "read that way the place gives 14, not the value you gave" in refused(repo, "Nat", "app.py::LIMIT", 15, "LIMIT = 14", structure={"python": "value", "as": "nat"})
    assert "not both" in refused(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", structure={"python": "value"}, find="x")
    assert "does not work on the place" in refused(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", structure={"python": "nope"})


def test_a_proposed_pattern_must_not_spell_out_the_value(pw, tmp_path):
    """A pattern that fits only the present value turns a changed value into an unreadable place."""
    (tmp_path / "ch.rs").write_text('fn topics() -> Vec<&str> {\n    vec!["system.return"]\n}\nconst LIMIT: u32 = 14;\n')
    repo = str(tmp_path)
    assert "fits only the value" in refused(repo, "String", "ch.rs", "system.return", 'vec!["system.return"]', find=r'vec!\["(system\.return)"')
    assert "fits only the value" in refused(repo, "Nat", "ch.rs", 14, "const LIMIT: u32 = 14;", find=r"LIMIT: u32 = (14);", kind="nat")
    kept = screen(repo, "String", "ch.rs", "system.return", 'vec!["system.return"]', find=r'vec!\["(system\.[a-z]+)"')
    assert kept["read"]["find"] == r'vec!\["(system\.[a-z]+)"'
    assert screen(repo, "Nat", "ch.rs", 14, "const LIMIT: u32 = 14;", find=r"LIMIT: u32 = (\d+);", kind="nat")["read"]["as"] == "nat"
    assert screen(repo, "List String", "ch.rs", ["system.return"], 'vec!["system.return"]', find_all=r'"([a-z.]+)"')["read"]["find_all"]


# ---- the tools the agent reports through -----------------------------------------------------------

def find_session(env, calls):
    """Start `pw mcp` with the find tools, make the calls; return the tool names and what each call said."""
    msgs = [{"jsonrpc": "2.0", "id": 0, "method": "initialize", "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                                                                            "clientInfo": {"name": "test", "version": "0"}}},
            {"jsonrpc": "2.0", "method": "notifications/initialized"},
            {"jsonrpc": "2.0", "id": 1, "method": "tools/list"}]
    msgs += [{"jsonrpc": "2.0", "id": n + 2, "method": "tools/call", "params": {"name": name, "arguments": a}} for n, (name, a) in enumerate(calls)]
    r = subprocess.run([PW, "mcp"], input="".join(json.dumps(m) + "\n" for m in msgs), capture_output=True, text=True,
                       env={**os.environ, "PW_TOOLS": "find", **env}, timeout=60)
    replies = {m["id"]: m for m in map(json.loads, r.stdout.splitlines())}
    return replies[1]["result"]["tools"], [replies[n + 2]["result"]["structuredContent"] for n in range(len(calls))]


def test_what_the_searching_agent_can_report(pw, tmp_path):
    """finished, add_place, replace_place, gone, new_fact: what is kept (one line each in PW_OUT),
    what is refused and why. The server remembers what was reported while it runs."""
    for name, text in {"guide.md": "## Limits\n\nAt most 14 atoms are solved. The class is `fast`.\n",
                       "app.py": 'LIMIT = 14\n\ndef run(mode="fast"):\n    pass\n\nNAMES = ["b", "a"]\n',
                       "notes.md": "Try `a`.\n", "other.md": "Mode: slow\n"}.items():
        (tmp_path / name).write_text(text)
    told = tmp_path / "told.json"
    told.write_text(json.dumps([{"name": "limit", "type": "Nat", "places": ["guide.md::Limits"]}]))
    out = tmp_path / "out.jsonl"
    run = {"at": "app.py::run", "value": "fast", "quote": 'mode="fast"', "find": r'mode="(\w+)"'}
    calls = [("finished", {"fact": "nope", "searched": "x"}),
             ("finished", {"fact": "limit", "searched": "  "}),
             ("finished", {"searched": "  everywhere,\n  twice "}),
             ("add_place", {"fact": "nope", "at": "app.py::LIMIT", "value": 14, "quote": "LIMIT = 14"}),
             ("add_place", {"fact": "limit", "at": "guide.md::Limits", "value": 14, "quote": "At most 14 atoms are solved."}),
             ("add_place", {"fact": "limit", "at": "app.py::LIMIT", "value": 14, "quote": "LIMIT = 14", "some": True}),
             ("add_place", {"fact": "limit", "at": "app.py::LIMIT", "value": "15", "quote": "LIMIT = 14", "find": r"LIMIT = (\d+)"}),
             ("add_place", {"fact": "limit", "at": "app.py::LIMIT", "value": "14", "quote": "LIMIT = 14", "find": r"LIMIT = (\d+)"}),
             ("add_place", {"fact": "limit", "at": "app.py::LIMIT", "value": 14, "quote": "LIMIT = 14", "find": r"LIMIT = (\d+)"}),   # (it is listed now)
             ("add_place", {"fact": "limit", "at": "app.py::LIMIT", "value": 14}),
             ("replace_place", {"fact": "limit", "old": "nope.md", "at": "guide.md::Limits", "value": 14, "quote": "x"}),
             ("replace_place", {"fact": "limit", "old": "guide.md::Limits", "at": "app.py::LIMIT", "value": 14, "quote": "LIMIT = 14"}),
             ("replace_place", {"fact": "limit", "old": "guide.md::Limits", "at": "guide.md::Limits", "value": 14, "quote": "At most 14 atoms are solved."}),
             ("gone", {"fact": "limit", "old": "x.md", "why": "w"}),
             ("gone", {"fact": "limit", "old": "guide.md::Limits", "why": " "}),
             ("gone", {"fact": "limit", "old": "guide.md::Limits", "why": "the  section\nwas cut"}),
             ("new_fact", {"name": "limit", "type": "Nat", "gloss": "g", "places": []}),
             ("new_fact", {"name": "mode", "type": "String", "gloss": " ", "places": []}),
             ("new_fact", {"name": "mode", "type": "String", "gloss": "the mode", "places": [run]}),
             ("new_fact", {"name": "mode", "type": "String", "gloss": "the mode", "places": [
                 run, {"at": "guide.md::Limits", "value": "fast", "quote": "The class is `fast`.", "bogus": 1}, {"value": 1}]}),
             ("new_fact", {"name": "names", "type": "List String", "gloss": "the names", "places": [
                 {"at": "app.py::NAMES", "value": ["a"], "quote": 'NAMES = ["b", "a"]', "some": True},
                 {"at": "notes.md", "value": ["a"], "quote": "Try `a`.", "some": True}]}),
             ("new_fact", {"name": "mode", "type": "String", "gloss": "the mode", "places": [
                 {"at": "app.py::run", "value": "fast", "quote": 'mode="fast"', "some": True}, run]}),
             ("new_fact", {"name": "mode", "type": "String", "gloss": "the  mode", "places": [run, {"at": "other.md", "value": "slow", "quote": "Mode: slow"}]}),
             ("add_place", {"fact": "mode", "at": "guide.md::Limits", "value": "fast", "quote": "The class is `fast`."}),
             ("nothing", {})]
    tools, said = find_session({"PW_WORKDIR": str(tmp_path), "PW_OUT": str(out), "PW_DISCOVER_FACTS": str(told)}, calls)
    assert [t["name"] for t in tools] == ["finished", "add_place", "replace_place", "gone", "new_fact"]
    assert tools[1]["inputSchema"]["required"] == ["fact", "at", "value", "quote"] and "structure" in tools[1]["inputSchema"]["properties"]
    assert said[0] == {"error": "no declared fact is named 'nope'; the names are ['limit']"}
    assert said[1] == {"error": "say what you searched for and where"} and said[2] == {"noted": "new facts"}
    assert said[3]["error"].startswith("no declared fact is named 'nope'")
    assert said[4] == {"error": "guide.md::Limits is already listed for this fact"}
    assert said[5] == {"error": "only a list can be stated in part"}
    assert said[6] == {"error": "the pattern reads 14 off the place, not the value you gave"}
    assert said[7] == {"kept": "app.py::LIMIT"} and said[8] == {"error": "app.py::LIMIT is already listed for this fact"}
    assert "quote" in said[9]["error"]
    assert said[10] == {"error": "nope.md is not listed for this fact; its places are ['app.py::LIMIT', 'guide.md::Limits']"}
    assert said[11] == {"error": "app.py::LIMIT is already listed for this fact"}
    assert said[12] == {"kept": "guide.md::Limits -> guide.md::Limits"}
    assert said[13] == {"error": "x.md is not listed for this fact"} and said[14] == {"error": "say what happened to the statement"}
    assert said[15] == {"noted": "guide.md::Limits"}
    assert said[16] == {"error": "'limit' is already declared; use add_place for further places"}
    assert said[17] == {"error": "say in one sentence exactly what the value is"}
    assert said[18] == {"error": "a thing stated in one place has nothing to disagree with; give at least two different places"}
    assert said[19] == {"error": "nothing was kept; fix these places and report the thing again", "places": {
        "guide.md::Limits": "a place has at, value, quote and optionally find, find_all, kind, within, rewrite, structure, some; not ['bogus']",
        "None": "a place has at, value, quote and optionally find, find_all, kind, within, rewrite, structure, some; not []"}}
    assert said[20] == {"error": "every place is marked as stating only some entries; one place has to state the whole list"}
    assert said[21] == {"error": "nothing was kept; fix these places and report the thing again", "places": {"app.py::run": "only a list can be stated in part"}}
    assert said[22] == {"kept": "mode", "the places that state the whole agree": False}       # reported as they are
    assert said[23] == {"kept": "guide.md::Limits"}                                          # a proposed fact takes further places
    assert "error" in said[24]

    lines = [json.loads(x) for x in out.read_text().splitlines()]
    assert lines[0] == {"started": True}
    assert lines[1] == {"finished": "", "searched": "everywhere, twice"}
    assert lines[2] == {"fact": "limit", "place": {"at": "app.py::LIMIT", "read": {"as": "nat", "find": r"LIMIT = (\d+)"}, "value": 14, "quote": "LIMIT = 14", "some": False}}
    assert lines[3] == {"replace": {"fact": "limit", "old": "guide.md::Limits"},
                        "place": {"at": "guide.md::Limits", "read": None, "value": 14, "quote": "At most 14 atoms are solved.", "some": False}}
    assert lines[4] == {"gone": {"fact": "limit", "old": "guide.md::Limits", "why": "the section was cut"}}
    assert lines[5]["new"] == {"name": "mode", "type": "String", "gloss": "the mode"} and [p["at"] for p in lines[5]["places"]] == ["app.py::run", "other.md"]
    assert lines[6]["fact"] == "mode" and len(lines) == 7


# ---- whole runs, with a stand-in for claude --------------------------------------------------------

FAKE = r'''
"""Stands in for `claude -p`: says through the session's own tools what the plan (FAKE_PLAN) says.
A searching session (PW_TOOLS=find) writes the plan's lines to PW_OUT, or makes its calls; a blind
reader reads or declines each place it is shown as the plan's "read" says. Every session is logged."""
import json, os, re, subprocess, sys
args = sys.argv[1:]
prompt = args[args.index("-p") + 1]
cfg = json.load(open(args[args.index("--mcp-config") + 1]))["mcpServers"]["pw"]
env = cfg["env"]
plan = json.load(open(os.environ["FAKE_PLAN"]))
entry = {"argv": args, "cwd": os.getcwd(), "env": env, "prompt": prompt}

def serve(calls):
    msgs = [{"jsonrpc": "2.0", "id": 0, "method": "initialize", "params": {"protocolVersion": "2025-06-18", "capabilities": {}, "clientInfo": {"name": "fake", "version": "0"}}},
            {"jsonrpc": "2.0", "method": "notifications/initialized"}]
    msgs += [{"jsonrpc": "2.0", "id": n + 1, "method": "tools/call", "params": {"name": c[0], "arguments": c[1]}} for n, c in enumerate(calls)]
    r = subprocess.run([cfg["command"], *cfg["args"]], input="".join(json.dumps(m) + "\n" for m in msgs), capture_output=True, text=True, env={**os.environ, **env})
    replies = {m["id"]: m for m in map(json.loads, r.stdout.splitlines())}
    return [replies[n + 1]["result"]["structuredContent"] for n in range(len(calls))]

result = {"num_turns": 3, "total_cost_usd": 0.1, "result": "done", "subtype": "success", "is_error": False}
if env.get("PW_TOOLS") == "find":
    job = "repair" if "CANNOT BE READ" in prompt else "new" if "Task. Find things" in prompt else "further"
    step = plan.get(job, {})
    told = json.load(open(env["PW_DISCOVER_FACTS"]))
    entry.update(job=job, told=told)
    # the place left out of what the session was told, as a control: the file it is in
    declared = json.load(open("pw-facts.json")) if os.path.exists("pw-facts.json") else []
    shown = {p if isinstance(p, str) else p["at"] for f in told for p in f["places"]}
    hidden = [at for f in declared for at in (p if isinstance(p, str) else p["at"] for p in f["places"]) if at not in shown]
    step = json.loads(json.dumps(step).replace("HIDDEN-FILE", hidden[0].split("::")[0] if hidden else "?"))
    if "lines" in step:
        with open(env["PW_OUT"], "w") as fh:
            fh.writelines(json.dumps(x) + "\n" for x in step["lines"])
    if "calls" in step:
        entry["replies"] = serve(step["calls"])
    result = step.get("result", result)
else:
    calls = []
    for h, place, typ in re.findall(r"^=== h: (\S+)   place: (.+)\nAsked: .*\(type (.+)\)$", prompt, re.M):
        said = plan.get("read", {}).get(place)
        if said and "by type" in said:                    # (a place of two facts)
            said = said["by type"].get(typ)
        if said is not None:
            calls.append(("not_stated", {"h": h, "place": place, "why": said["why"]}) if "why" in said else
                         ("read_place", {"h": h, "place": place, "object": said["object"], "quote": said["quote"]}))
    entry["replies"] = serve(calls)
with open(os.environ["FAKE_LOG"], "a") as fh:
    fh.write(json.dumps(entry) + "\n")
print("boom" if result is None else json.dumps(result))
'''

OK = {"num_turns": 3, "total_cost_usd": 0.1, "result": "found nothing", "subtype": "success", "is_error": False}


@pytest.fixture
def run(pw, tmp_path):
    """Run `pw discover` on tmp_path/repo with the stand-in for claude following `plan`.
    Returns (the completed process, the sessions the stand-in was asked to run)."""
    fake = tmp_path / "claude"
    fake.write_text(f"#!{sys.executable}\n" + FAKE)
    fake.chmod(0o755)
    (tmp_path / "repo").mkdir()

    def go(plan, *args):
        (tmp_path / "plan.json").write_text(json.dumps(plan))
        log = tmp_path / "log.jsonl"
        if log.exists():
            log.unlink()
        r = subprocess.run([PW, "discover", "--repo", str(tmp_path / "repo"), "--model", "m", "--confirm-model", "r", "--budget", "1", *args],
                           capture_output=True, text=True, timeout=300,
                           env={**os.environ, "PW_CLAUDE": str(fake), "FAKE_PLAN": str(tmp_path / "plan.json"), "FAKE_LOG": str(log),
                                "XDG_CACHE_HOME": str(tmp_path / "cache")})
        assert "Traceback" not in r.stdout + r.stderr, r.stdout + r.stderr
        return r, [json.loads(x) for x in log.read_text().splitlines()] if log.exists() else []
    return go


def files(tmp_path, facts=None, **texts):
    repo = tmp_path / "repo"
    for name, text in texts.items():
        (repo / name).write_text(text)
    if facts is not None:
        (repo / "pw-facts.json").write_text(json.dumps(facts))
    return repo


def incomplete(out):
    return [line.split("INCOMPLETE: ", 1)[1] for line in out.splitlines() if "INCOMPLETE: " in line]


def test_a_search_that_failed_does_not_look_like_one_that_found_nothing(run, tmp_path):
    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits", "app.py::LIMIT"]}]
    files(tmp_path, facts, **{"guide.md": "## Limits\n\nAt most 14 atoms are solved.\n", "app.py": "LIMIT = 14\n", "other.py": "LIMIT = 14\n"})
    place = lambda at: {"fact": "limit", "place": {"at": at, "read": None, "value": 14, "quote": "LIMIT = 14"}}

    r, sessions = run({"further": {"lines": [], "result": OK}}, "--only", "further", "--no-controls")   # the tools never came up: the agent only talked
    assert incomplete(r.stdout) == ["the reporting tools never started, so the agent could not report anything",
                                    "the agent did not say it finished searching for: limit"]
    assert "nothing proposed (but the search was incomplete: this does not mean there is nothing)" in r.stdout
    assert r.stdout.rstrip().endswith("part of this run failed (marked INCOMPLETE or ???? above): that is not a finding, run it again") and r.returncode == 1
    # how the session was run: reading the repository and reporting through our tools, nothing else
    (s,) = sessions
    argv = s["argv"]
    assert argv[argv.index("--tools") + 1] == "Read,Grep,Glob" and argv[argv.index("--model") + 1] == "m"
    assert argv[argv.index("--allowedTools") + 1] == "Read,Grep,Glob," + ",".join(f"mcp__pw__{t}" for t in ("add_place", "new_fact", "replace_place", "gone", "finished"))
    assert os.path.realpath(s["cwd"]) == os.path.realpath(tmp_path / "repo") and s["env"]["PW_TOOLS"] == "find"
    assert s["prompt"].startswith("You are looking through a project's files") and "    known place: guide.md::Limits\n    known place: app.py::LIMIT\n" in s["prompt"]
    assert s["told"] == facts and "   further: 3 turns, $0.1" in r.stdout

    r, _ = run({"further": {"lines": [{"started": True}]}}, "--only", "further", "--no-controls")     # tools up, but the agent never said it was done
    assert incomplete(r.stdout) == ["the agent did not say it finished searching for: limit"]
    r, _ = run({"further": {"lines": [{"started": True}, {"finished": "limit"}], "result": {**OK, "subtype": "error_max_budget_usd", "is_error": True}}},
               "--only", "further", "--no-controls")
    assert incomplete(r.stdout) == ["the session ended with error_max_budget_usd"]
    r, _ = run({"further": {"lines": [{"started": True}, {"finished": "limit"}], "result": None}}, "--only", "further", "--no-controls")
    assert incomplete(r.stdout) == ["the session gave no result: boom"]
    assert "   further: None turns, $None" in r.stdout
    r, sessions = run({"new": {"lines": [{"started": True}, {"finished": ""}]}}, "--only", "new")
    assert incomplete(r.stdout) == [] and r.returncode == 0 and "looking for new facts with m" in r.stdout
    assert 'Already declared (do not report these again):\n\n- "limit" (type Nat): limit\n' in sessions[0]["prompt"] and "known place" not in sessions[0]["prompt"]
    r, _ = run({"further": {"lines": [{"started": True}, {"finished": "limit"}]}}, "--only", "further", "--no-controls")   # only now does nothing mean nothing
    assert incomplete(r.stdout) == [] and "hidden known places" not in r.stdout and r.returncode == 0
    assert r.stdout.splitlines()[-1] == "nothing proposed"

    # a known place left out as a control: coming back with it shows the search works, and is not a proposal
    r, sessions = run({"further": {"lines": [{"started": True}, place("HIDDEN-FILE"), place("other.py::LIMIT"), {"finished": "limit"}]},
                       "read": {"other.py::LIMIT": {"object": "14", "quote": "LIMIT = 14"}}}, "--only", "further", "--seed", "3")
    hidden = next(at for at in ("guide.md::Limits", "app.py::LIMIT") if at not in sessions[0]["prompt"])
    assert [p if isinstance(p, str) else p["at"] for p in sessions[0]["told"][0]["places"]] == [at for at in facts[0]["places"] if at != hidden]
    assert "   further: 1 of 1 hidden known places came back" in r.stdout and r.returncode == 0, r.stdout
    assert "   keep other.py::LIMIT  says 14\n        LIMIT = 14\n        a blind reader reads 14 off it\n" in r.stdout
    assert "1 of 1 proposed place(s) kept, 0 dropped, 0 not checked" in r.stdout
    assert "nothing was written. To write the kept places as shown, without searching again: pw discover --apply-last" in r.stdout
    reader = sessions[1]["argv"]                                     # the blind reader: the place alone, and nothing to read files with
    assert reader[reader.index("--tools") + 1] == "" and reader[reader.index("--allowedTools") + 1] == "mcp__pw__read_place,mcp__pw__not_stated"
    assert reader[reader.index("--model") + 1] == "r" and "place: other.py::LIMIT" in sessions[1]["prompt"]
    assert not (tmp_path / "repo" / "pw-log.jsonl").exists() and json.loads((tmp_path / "repo" / "pw-facts.json").read_text()) == facts
    # the search that does not come back with it is doubtful; a place nobody answered for is not checked
    r, _ = run({"further": {"lines": [{"started": True}, place("other.py::LIMIT"), {"finished": "limit"}]}}, "--only", "further", "--seed", "3")
    assert "   further: 0 of 1 hidden known places came back" in r.stdout
    assert f"   further: the search did not come back with limit at {hidden}: it may have missed other places of that fact too" in r.stdout
    assert "   ???? other.py::LIMIT  says 14\n" in r.stdout and "the blind reader neither read it nor declined: not checked" in r.stdout
    assert "0 of 1 proposed place(s) kept, 0 dropped, 1 not checked" in r.stdout and r.returncode == 1
    assert "part of this run failed" in r.stdout


def kernel(req):
    return json.loads(subprocess.run([PW, "kernel"], input=json.dumps(req), capture_output=True, text=True).stdout)


def test_a_declared_place_that_cannot_be_read_is_said_and_can_be_repaired(run, tmp_path):
    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits", {"at": "app.py::LIMIT", "read": {"find": "LIMIT = (\\d+)", "as": "nat"}}]},
             {"name": "other", "type": "Nat", "places": ["notes.md"]}]
    repo = files(tmp_path, facts, **{"guide.md": "## Limits\n\nAt most 14 atoms are solved.\n", "app.py": "LIMIT = 14\n", "notes.md": "14\n"})
    db = str(repo / "pw-log.jsonl")
    (h, _) = kernel({"db": db, "actor": "t", "op": "sync", "path": str(repo / "pw-facts.json")})["ok"]
    kernel({"db": db, "actor": "t", "op": "read", "h": h, "place": "guide.md::Limits", "obj": "14", "cwd": str(repo), "quote": "At most 14 atoms are solved."})
    assert kernel({"db": db, "actor": "t", "op": "recheck", "cwd": str(repo)})["ok"]["decisions"][0]["state"] == "current"
    r, _ = run({}, "--only", "repair")
    assert r.stdout == "nothing to do: every declared place can be read\n" and r.returncode == 0

    # the heading is renamed, the constant is renamed: neither place is where it was declared
    (repo / "guide.md").write_text("## Bounds\n\nAt most 14 atoms are solved.\n")
    (repo / "app.py").write_text("MAX_ATOMS = 14\n")
    record = (repo / "pw-log.jsonl").read_text()
    fix = {"repair": {"calls": [
        ["replace_place", {"fact": "limit", "old": "guide.md::Limits", "at": "guide.md::Bounds", "value": 14, "quote": "At most 14 atoms are solved."}],
        ["replace_place", {"fact": "limit", "old": "app.py::LIMIT", "at": "app.py::MAX_ATOMS", "value": 14, "quote": "MAX_ATOMS = 14", "find": r"MAX_ATOMS = (\d+)"}],
        ["gone", {"fact": "limit", "old": "guide.md::Limits", "why": "x"}],
        ["finished", {"fact": "limit", "searched": "the guide and the code"}]]},
        "read": {"guide.md::Bounds": {"object": "14", "quote": "At most 14 atoms are solved."}, "app.py::MAX_ATOMS": {"object": "14", "quote": "MAX_ATOMS = 14"}}}
    r, sessions = run(fix, "--only", "repair")
    out = r.stdout
    assert out.startswith("cannot be read as declared: limit at guide.md::Limits: guide.md no longer has a part named 'Limits'\n"
                          "cannot be read as declared: limit at app.py::LIMIT: ")
    assert "looking for where unreadable places went with m" in out and sessions[0]["job"] == "repair"
    assert sessions[0]["replies"][:2] == [{"kept": "guide.md::Limits -> guide.md::Bounds"}, {"kept": "app.py::LIMIT -> app.py::MAX_ATOMS"}]
    # the agent is told which places cannot be read, and only about the facts concerned
    prompt = sessions[0]["prompt"]
    assert "CANNOT BE READ: guide.md no longer has a part named 'Limits'\n      listed as: guide.md::Limits\n" in prompt and '"other"' not in prompt
    assert '      listed as: app.py::LIMIT   read by: {"find": "LIMIT = (\\\\d+)", "as": "nat"}\n' in prompt
    assert [f["name"] for f in sessions[0]["told"]] == ["limit"]
    assert "the agent says the project no longer states limit at guide.md::Limits: x\n   taking a declared place away is for a person: remove it from pw-facts.json if that is so" in out
    assert "\nplace(s) of: limit\n   keep guide.md::Bounds  (instead of guide.md::Limits)  says 14\n" in out
    assert "   keep app.py::MAX_ATOMS  (instead of app.py::LIMIT)  says 14  (computed)\n        MAX_ATOMS = 14\n        read: {\"as\": \"nat\", \"find\": \"MAX_ATOMS = (\\\\d+)\"}\n" in out, out   # the way of reading, as it would be written (#21)
    assert "2 of 2 proposed place(s) kept, 0 dropped, 0 not checked" in out and "nothing was written" in out
    assert "still cannot be read" not in out and r.returncode == 0
    assert (repo / "pw-log.jsonl").read_text() == record and json.loads((repo / "pw-facts.json").read_text()) == facts   # (without --apply: only looked)

    merged = [{"name": "limit", "type": "Nat", "places": ["guide.md::Bounds", {"at": "app.py::MAX_ATOMS", "read": {"as": "nat", "find": r"MAX_ATOMS = (\d+)"}}]},
              facts[1]]
    # what was shown is written as it was shown, with no search (#21); not once a file it read has changed
    (repo / "app.py").write_text("MAX_ATOMS = 14\n# touched\n")
    r, sessions = run({}, "--apply-last")
    assert r.returncode == 2 and "app.py changed since that run" in r.stderr and sessions == []
    (repo / "app.py").write_text("MAX_ATOMS = 14\n")
    r, sessions = run({}, "--apply-last")
    assert sessions == [] and r.returncode == 0, r.stdout + r.stderr
    assert "kept: limit at guide.md::Bounds\nkept: limit at app.py::MAX_ATOMS\n" in r.stdout and "with its 2 blind reading(s) in the record; nothing was searched again" in r.stdout
    assert (repo / "pw-facts.json").read_text() == json.dumps(merged, ensure_ascii=False, indent=1) + "\n"
    events = [json.loads(x) for x in (repo / "pw-log.jsonl").read_text().splitlines()]
    assert {(e["place"], e["blind"]) for e in events if e["type"] == "reading" and e["actor"].startswith("proposed-")} == {("guide.md::Bounds", True), ("app.py::MAX_ATOMS", True)}
    check = subprocess.run([PW, "check", "--repo", str(repo), "--unconfirmed", "warn"], capture_output=True, text=True)
    assert "cannot be read as declared" not in check.stdout
    r, _ = run({}, "--apply-last")
    assert r.returncode == 2 and "there is no result of a run without --apply" in r.stderr       # (taken once)

    (repo / "pw-facts.json").write_text(json.dumps(facts))
    (repo / "pw-log.jsonl").write_text(record)
    r, _ = run(fix, "--only", "repair", "--apply")
    assert "written to pw-facts.json; their blind readings are in the record. Then: pw maintain" in r.stdout and r.returncode == 0
    assert (repo / "pw-facts.json").read_text() == json.dumps(merged, ensure_ascii=False, indent=1) + "\n"
    events = [json.loads(x) for x in (repo / "pw-log.jsonl").read_text().splitlines()]
    assert {(e["place"], e["blind"]) for e in events if e["type"] == "reading" and e["actor"].startswith("proposed-")} == {("guide.md::Bounds", True), ("app.py::MAX_ATOMS", True)}
    check = subprocess.run([PW, "check", "--repo", str(repo), "--unconfirmed", "warn"], capture_output=True, text=True)
    assert "cannot be read as declared" not in check.stdout and "pw.discover" not in check.stdout

    # a place the agent cannot find again stays unreadable, and the run says so
    (repo / "pw-facts.json").write_text(json.dumps(facts))
    r, _ = run({"repair": {"lines": [{"started": True}, {"gone": {"fact": "limit", "old": "app.py::LIMIT", "why": "removed"}}, {"finished": "limit"}]}}, "--only", "repair")
    assert "nothing proposed\n" in r.stdout and r.returncode == 1
    assert r.stdout.endswith("still cannot be read as declared: limit at guide.md::Limits\nstill cannot be read as declared: limit at app.py::LIMIT\n")


def test_what_a_blind_reader_confirms_is_merged_into_the_declaration(run, tmp_path):
    """The places kept are added as pw-facts.json lists places (a name, or with its way of reading
    and "some"); a place a reader declines is dropped, and a new thing left with one place is not
    declared. What is written is a declaration that can be checked."""
    repo = files(tmp_path, [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits"]}], **{
        "guide.md": "## Limits\n\nAt most 14 atoms are solved. The class is `fast`.\n\n## Names\n\nThe names are `a` and `b`.\n\n## Threshold\n\nThe threshold is 0.9.\n",
        "app.py": 'LIMIT = 14\n\ndef run(threshold=0.9, mode="fast"):\n    return threshold\n\nNAMES = ["b", "a"]\n',
        "notes.md": "Try `a`.\n", "other.md": "## Budget\n\nThe budget is 14 dollars.\n"})
    plan = {
        "further": {"calls": [
            ["add_place", {"fact": "limit", "at": "app.py::LIMIT", "value": 14, "quote": "LIMIT = 14", "find": r"LIMIT = (\d+)"}],
            ["add_place", {"fact": "limit", "at": "other.md::Budget", "value": 14, "quote": "The budget is 14 dollars."}],
            ["finished", {"fact": "limit", "searched": "everywhere"}]]},
        "new": {"calls": [
            ["new_fact", {"name": "class", "type": "String", "gloss": "the class", "places": [
                {"at": "guide.md::Limits", "value": "fast", "quote": "The class is `fast`."},
                {"at": "app.py::run", "value": "fast", "quote": 'mode="fast"', "find": r'mode="(\w+)"'}]}],
            ["new_fact", {"name": "names", "type": "List String", "gloss": "the names, sorted", "places": [
                {"at": "app.py::NAMES", "value": ["a", "b"], "quote": 'NAMES = ["b", "a"]', "structure": {"python": "strings"}},
                {"at": "notes.md", "value": ["a"], "quote": "Try `a`.", "some": True}]}],
            ["add_place", {"fact": "names", "at": "guide.md::Names", "value": ["a", "b"], "quote": "The names are `a` and `b`."}],
            ["new_fact", {"name": "threshold", "type": "Nat", "gloss": "the threshold, in thousandths", "places": [
                {"at": "app.py::run", "value": 900, "quote": "def run(threshold=0.9", "find": r"threshold=([0-9.]+)", "kind": "permille"},
                {"at": "guide.md::Threshold", "value": 900, "quote": "The threshold is 0.9.", "find": r"threshold is (\d+\.\d+)", "kind": "permille"}]}],
            ["finished", {"searched": "everywhere"}]]},
        "read": {"app.py::LIMIT": {"object": "14", "quote": "LIMIT = 14"},
                 "other.md::Budget": {"why": "it is about the budget"},
                 "guide.md::Limits": {"object": '"fast"', "quote": "The class is `fast`."},
                 "app.py::run": {"by type": {"String": {"object": '"fast"', "quote": 'mode="fast"'},
                                             "Nat": {"object": "900", "quote": "def run(threshold=0.9"}}},
                 "app.py::NAMES": {"object": '["a", "b"]', "quote": 'NAMES = ["b", "a"]'},
                 "notes.md": {"object": '["a"]', "quote": "Try `a`."},
                 "guide.md::Names": {"object": '["a", "b"]', "quote": "The names are `a` and `b`."},
                 "guide.md::Threshold": {"why": "it is about another threshold"}}}
    r, sessions = run(plan, "--new", "--apply")
    out = r.stdout
    assert {s.get("job") for s in sessions} == {"further", "new", None}
    assert "looking for further places of declared facts, new facts with m" in out and "hidden known places" not in out   # (one place: no control)
    assert all("error" not in x for s in sessions for x in s.get("replies", [])), [s.get("replies") for s in sessions]
    assert "   drop other.md::Budget  says 14\n        The budget is 14 dollars.\n        a blind reader says the place does not state this: it is about the budget\n" in out
    assert "\nnew fact: names\n   keep app.py::NAMES  says [\"a\", \"b\"]  (computed)\n" in out and '   keep notes.md  lists in part ["a"]\n' in out
    # the reader declines one place of a new thing: what is left of it is one place, which is not declared
    assert "   drop app.py::run  says 900  (computed)\n" in out and "; but what was kept of this thing is one place, or only places that state it in part" in out
    assert "\nnew fact: threshold\n" in out and out.split("new fact: threshold")[1].count("the kept places do not state the same value") == 1
    assert "6 of 9 proposed place(s) kept, 3 dropped, 0 not checked" in out and r.returncode == 0
    written = json.loads((repo / "pw-facts.json").read_text())
    assert written == [
        {"name": "limit", "type": "Nat", "places": ["guide.md::Limits", {"at": "app.py::LIMIT", "read": {"as": "nat", "find": r"LIMIT = (\d+)"}}]},
        {"name": "class", "type": "String", "gloss": "the class", "places": ["guide.md::Limits", {"at": "app.py::run", "read": {"as": "string", "find": r'mode="(\w+)"'}}]},
        {"name": "names", "type": "List String", "gloss": "the names, sorted",
         "places": [{"at": "app.py::NAMES", "read": {"python": "strings", "sort": True}}, {"at": "notes.md", "some": True}, "guide.md::Names"]}]
    check = subprocess.run([PW, "check", "--repo", str(repo), "--unconfirmed", "warn"], capture_output=True, text=True)
    assert check.returncode in (0, 1) and "could not" not in check.stdout + check.stderr, check.stdout + check.stderr


def test_what_there_is_nothing_to_do_for(run, tmp_path):
    r, sessions = run({})
    assert r.stdout == "No facts are declared in pw-facts.json, so there is nothing to look after. With --new the agent proposes some.\n"
    assert r.returncode == 0 and sessions == []
    r = subprocess.run([PW, "discover", "--repo", str(tmp_path / "repo")], capture_output=True, text=True, env={**os.environ, "PW_CLAUDE": str(tmp_path / "none")})
    assert r.returncode == 2 and "the `claude` command is not on PATH" in r.stderr           # before anything is paid for
    r = subprocess.run([PW, "discover", "--only", "everything"], capture_output=True, text=True)
    assert r.returncode == 2 and "--only is one of repair, further, new" in r.stderr
    assert subprocess.run([PW, "discover", "--help"], capture_output=True, text=True).stdout.startswith("pw discover:")
