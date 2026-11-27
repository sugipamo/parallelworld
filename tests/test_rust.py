"""The Rust check (rust/) has to judge as the Python check does: the same declaration, record
and files give the same verdicts, by the same rules. Skipped when it is not built and cargo is
not there to build it."""
import json
import os
import shutil
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "experiments", "history"))
from rust import trimmed      # noqa: E402

PW = os.path.join(ROOT, "rust", "target", "release", "pw")


@pytest.fixture(scope="module")
def pw():
    if not os.path.exists(PW):
        if not shutil.which("cargo"):
            pytest.skip("the Rust check is not built and cargo is not installed")
        subprocess.run(["cargo", "build", "--release", "--locked"], cwd=os.path.join(ROOT, "rust"), check=True, capture_output=True)
    return PW


def both(pw, repo, *args):
    py = subprocess.run([sys.executable, "-m", "pw.check", "--repo", repo, *args], capture_output=True, text=True, env={**os.environ, "PYTHONPATH": ROOT})
    rs = subprocess.run([pw, "check", "--repo", repo, *args], capture_output=True, text=True)
    return py, rs


def declare(tmp_path, facts, **files):
    for name, text in files.items():
        (tmp_path / name).write_text(text)
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    return str(tmp_path)


LIMIT = {"name": "limit", "type": "Nat", "places": [{"at": "k.py::LIMIT", "read": {"python": "value", "as": "nat"}},
                                                     {"at": "doc.md::Limits", "read": {"find": r"most (\d+)", "as": "nat"}}]}
MODES = {"name": "modes", "type": "List String", "places": [{"at": "k.py::MODES", "read": {"python": "keys", "sort": True}},
                                                            {"at": "cfg.toml", "read": {"data": "mode.*.name", "sort": True}},
                                                            {"at": "doc.md::Modes", "read": {"find_all": "`(\\w+)`", "sort": True}, "some": True}]}
FILES = {"k.py": "LIMIT = 14\nMODES = {'fast': 1,\n         \"safe\": 2}\n", "doc.md": "## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`\n",
         "cfg.toml": '[[mode]]\nname = "fast"\n\n[[mode]]\nname = "safe"\n'}


@pytest.mark.parametrize("change", [
    {},                                                                    # everything agrees
    {"k.py": "LIMIT = 15\nMODES = {'fast': 1, 'safe': 2}\n"},              # a value differs
    {"doc.md": "## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`, `bogus`\n"},  # an example lists what the whole does not have
    {"cfg.toml": '[[mode]]\nname = "fast"\n'},                             # the lists differ
    {"k.py": "LIMIT = N\nMODES = {'fast': 1, 'safe': 2}\n"},               # not written out: cannot be read
    {"doc.md": "## Limit\n\nAt most 14.\n\n## Modes\n\n`fast`\n"},         # the heading is gone
])
def test_the_same_verdicts_and_the_same_words(pw, tmp_path, change):
    repo = declare(tmp_path, [LIMIT, MODES], **{**FILES, **change})
    py, rs = both(pw, repo, "--json", "--unconfirmed", "warn")
    assert py.returncode == rs.returncode and trimmed(json.loads(py.stdout)) == trimmed(json.loads(rs.stdout))
    py, rs = both(pw, repo, "--unconfirmed", "warn")
    same = lambda out: [line for line in out.splitlines() if "cannot be read" not in line and "not written out" not in line and ": the place is not" not in line]
    assert same(py.stdout) == same(rs.stdout)                              # (what a parser says when it fails is its own wording)


def test_what_people_laid_down(pw, tmp_path):
    laid = {**LIMIT, "instructions": [{"is": 14, "by": "ann"}]}
    for facts, files in [([laid, MODES], {**FILES, "k.py": "LIMIT = 15\nMODES = {'fast': 1, 'safe': 2}\n"}),
                         ([{**LIMIT, "instructions": [{"is": 14, "by": "ann"}, {"is": 15, "by": "bob", "said": "make it 15"}]}, MODES], FILES)]:
        repo = declare(tmp_path, facts, **files)
        py, rs = both(pw, repo, "--unconfirmed", "warn")
        assert py.returncode == rs.returncode == 1 and py.stdout == rs.stdout


LAKE = os.environ.get("PW_LAKE") or shutil.which("lake")
lean = pytest.mark.skipif(not LAKE, reason="Lean not installed (set PW_LAKE)")


@lean
@pytest.mark.parametrize("args", [(), ("--lean", "always"), ("--verify",)])
def test_this_repository(pw, args):
    """Its one definition is worked out by Lean; with --lean always every comparison is; --verify runs the record's proofs again."""
    py, rs = both(pw, ROOT, "--json", *args)
    assert py.returncode == rs.returncode == 0 and py.stdout == rs.stdout          # the same JSON, byte for byte (the question asked included)
    py, rs = both(pw, ROOT, *args)
    assert py.stdout == rs.stdout and py.returncode == rs.returncode == 0
    assert both(pw, ROOT, "--needs-lean")[1].stdout == both(pw, ROOT, "--needs-lean")[0].stdout == "yes\n"


@lean
@pytest.mark.parametrize("change", [{}, {"k.py": "LIMIT = 15\nMODES = {'fast': 1, 'safe': 2}\n"},
                                    {"doc.md": "## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`, `bogus`\n"}])
def test_every_comparison_put_to_lean(pw, tmp_path, change):
    """With no proof in the record, both ask Lean the same propositions and come to the same verdicts."""
    repo = declare(tmp_path, [LIMIT, MODES], **{**FILES, **change})
    py, rs = both(pw, repo, "--json", "--unconfirmed", "warn", "--lean", "always")
    assert py.returncode == rs.returncode and trimmed(json.loads(py.stdout)) == trimmed(json.loads(rs.stdout))


@lean
def test_definitions(pw, tmp_path):
    """A count and a first entry worked out from other facts: agreeing, differing, waiting, following an instruction."""
    modes = {"name": "modes", "type": "List String", "places": [{"at": "app.py::MODES", "read": {"find_all": '"(\\w+)"', "sort": True}}]}
    versions = {"name": "versions", "type": "List String", "places": [
        {"at": "app.py::VERSIONS", "read": {"find_all": '"([0-9.]+)"', "sort": True}},
        {"at": "pyproject.toml", "read": {"within": "versions = \\[([^\\]]*)\\]", "find_all": '"([0-9.]+)"', "sort": True}}]}
    count = {"name": "number of modes", "type": "Nat", "defined": {"from": ["modes"], "as": "fun ms => ms.length"},
             "places": [{"at": "doc.md::Modes", "read": {"find": "There are (\\d+) modes", "as": "nat"}}]}
    oldest = {"name": "oldest version", "type": "String", "defined": {"from": ["versions"], "as": 'fun vs => vs.headD ""'},
              "places": [{"at": "pyproject.toml", "read": {"find": 'requires-python = ">=([0-9.]+)"'}}]}
    twice = {"name": "twice the modes", "type": "Nat", "defined": {"from": ["number of modes"], "as": "fun n => 2 * n"},
             "places": [{"at": "doc.md::Modes", "read": {"find": "There are (\\d+) modes", "as": "nat"}}]}
    app, doc = 'MODES = ["fast", "safe"]\nVERSIONS = ["3.10", "3.11"]\n', "## Modes\n\nThere are 2 modes.\n"
    toml = 'requires-python = ">=3.10"\nversions = ["3.10", "3.11"]\n'
    laid = {**versions, "instructions": [{"is": ["3.9", "3.10", "3.11"], "by": "alice"}]}
    states = []
    for facts, files in [
        ([count, modes, versions, oldest], {}),                                                       # all agree
        ([count, modes, versions, oldest], {"app.py": app.replace('"safe"]', '"safe", "turbo"]')}),   # the count is now wrong
        ([count, modes, versions, oldest], {"pyproject.toml": toml.replace('["3.10"', '["3.9", "3.10"')}),   # what it is built on disagrees
        ([count, modes, laid, oldest], {"pyproject.toml": toml.replace('["3.10"', '["3.9", "3.10"')}),       # a person settles it
        ([count, modes, twice], {"doc.md": doc.replace("2 modes", "4 modes")}),                       # a definition of a definition
        ([count, modes, twice], {}),
    ]:
        repo = declare(tmp_path, facts, **{"app.py": app, "doc.md": doc, "pyproject.toml": toml, **files})
        py, rs = both(pw, repo, "--json", "--unconfirmed", "warn")
        a, b = trimmed(json.loads(py.stdout)), trimmed(json.loads(rs.stdout))
        assert py.returncode == rs.returncode and a == b, (files, a, b)
        py, rs = both(pw, repo, "--unconfirmed", "warn")
        assert py.stdout == rs.stdout
        states.append(sorted((n, d["state"]) for n, d in b.items()))
    assert ("number of modes", "violated") in states[1] and ("oldest version", "waits") in states[2] and ("oldest version", "violated") in states[3]
    assert ("number of modes", "violated") in states[4] and ("twice the modes", "current") in states[4]
    assert ("number of modes", "current") in states[5] and ("twice the modes", "violated") in states[5]


@lean
def test_definitions_that_cannot_be_used(pw, tmp_path):
    modes = {"name": "modes", "type": "List String", "places": [{"at": "app.py::MODES", "read": {"find_all": '"(\\w+)"'}}]}
    count = {"name": "count", "type": "Nat", "defined": {"from": ["modes"], "as": "fun ms => ms.length"}, "places": ["doc.md"]}
    twice = {"name": "twice", "type": "Nat", "defined": {"from": ["count"], "as": "fun n => 2 * n"}, "places": ["doc.md"]}
    for bad in ({**count, "defined": {"from": ["nothing"], "as": "fun ms => ms.length"}},     # from a fact that is not declared
                {**count, "defined": {"from": ["modes"], "as": "fun ms => ms"}},               # not a Nat
                {**count, "defined": {"from": ["count"], "as": "fun n => n"}},                 # from itself
                {**count, "instructions": [{"is": 2, "by": "alice"}]},                         # a definition takes no instruction
                {**count, "defined": {"from": ["twice"], "as": "fun n => n"}},                 # in a circle
                {**count, "defined": {"from": ["modes"], "as": "fun ms => by sorry"}}):        # not Lean we take
        repo = declare(tmp_path, [bad, modes, twice], **{"app.py": 'MODES = ["a"]\n', "doc.md": "1\n"})
        py, rs = both(pw, repo)
        assert py.returncode == rs.returncode == 2 and rs.stderr.startswith("pw: "), (bad, py.stderr, rs.stderr)


def test_without_lean_what_needs_it_is_not_checked(pw, tmp_path):
    """Where Lean is needed and is not there, neither judges anything: the check could not be made."""
    count = {"name": "count", "type": "Nat", "defined": {"from": ["limit"], "as": "fun n => n"}, "places": [LIMIT["places"][1]]}
    repo = declare(tmp_path, [LIMIT, count], **FILES)
    env = {**os.environ, "PW_LAKE": str(tmp_path / "no-lake")}
    py = subprocess.run([sys.executable, "-m", "pw.check", "--repo", repo], capture_output=True, text=True, env={**env, "PYTHONPATH": ROOT})
    rs = subprocess.run([pw, "check", "--repo", repo], capture_output=True, text=True, env=env)
    assert py.returncode == rs.returncode == 2 and py.stderr == rs.stderr, (py.stderr, rs.stderr)
    for args in [(), ("--verify",)]:                     # ...while what is written out is still compared as written
        py = subprocess.run([sys.executable, "-m", "pw.check", "--repo", declare(tmp_path, [LIMIT], **FILES), *args], capture_output=True, text=True, env={**env, "PYTHONPATH": ROOT})
        rs = subprocess.run([pw, "check", "--repo", str(tmp_path), *args], capture_output=True, text=True, env=env)
        assert py.returncode == rs.returncode and py.stdout == rs.stdout


def test_a_declaration_that_cannot_be_used(pw, tmp_path):
    for text in ["[{", '{"name": "x"}', '[{"name": "x", "places": ["a"]}]', '[{"name": "x", "type": "Nat", "place": ["a"]}]',
                 json.dumps([{"name": "x", "type": "Nat", "places": ["a"]}] * 2), '[{"name": "x", "type": "Nat", "places": [{"at": "a", "reader": 1}]}]']:
        (tmp_path / "pw-facts.json").write_text(text)
        py, rs = both(pw, str(tmp_path))
        assert py.returncode == rs.returncode == 2 and rs.stderr.startswith("pw: ")
    os.remove(tmp_path / "pw-facts.json")
    py, rs = both(pw, str(tmp_path))
    assert py.returncode == rs.returncode == 2 and py.stderr == rs.stderr


def test_what_is_wrong_is_said_alike(pw, tmp_path):
    """A key nobody reads, and a record cut off in the middle of a line: the same words, and the
    project's record named (not the copy a check works on)."""
    for facts in ([{**LIMIT, "glos": "x"}], [{**LIMIT, "places": [{**LIMIT["places"][0], "read": {**LIMIT["places"][0]["read"], "sortt": True}}]}]):
        py, rs = both(pw, declare(tmp_path, facts, **FILES))
        assert py.returncode == rs.returncode == 2 and py.stderr == rs.stderr, (py.stderr, rs.stderr)
    repo = declare(tmp_path, [LIMIT], **FILES)
    (tmp_path / "pw-log.jsonl").write_text('{"type": "withdraw", "h": "H:1", "justification": "x"}\n{"type": "rea')
    py, rs = both(pw, repo)
    cut = lambda e: e.split(" (")[0]                       # (what the JSON parser says is its own)
    assert py.returncode == rs.returncode == 2 and cut(py.stderr) == cut(rs.stderr) == f"pw: {tmp_path}/pw-log.jsonl, line 2: not a readable event"


# ---- what each appends to the record -------------------------------------------------------------

def appended(pw, repo, *args, cmd="check"):
    """Run each implementation on its own copy of `repo`; return the lines each appended, without their times."""
    out = []
    for impl in ("python", "rust"):
        copy = repo + "-" + impl
        shutil.rmtree(copy, ignore_errors=True)
        shutil.copytree(repo, copy, ignore=shutil.ignore_patterns(".git", "target", "__pycache__", ".pytest_cache"))
        log = os.path.join(copy, "pw-log.jsonl")
        before = open(log, encoding="utf-8").read() if os.path.exists(log) else ""
        if impl == "python":
            r = subprocess.run([sys.executable, "-m", f"pw.{cmd}", "--repo", copy, *args], capture_output=True, text=True, env={**os.environ, "PYTHONPATH": ROOT})
        else:
            r = subprocess.run([pw, cmd, "--repo", copy, *args], capture_output=True, text=True)
        after = open(log, encoding="utf-8").read() if os.path.exists(log) else ""
        assert after.startswith(before), impl
        lines = [json.loads(x) for x in after[len(before):].splitlines()]
        out.append(([{k: v for k, v in e.items() if k != "ts"} for e in lines], r.returncode, r.stdout))
        assert all(after[len(before):].splitlines()[n] == json.dumps(e, ensure_ascii=False) for n, e in enumerate(lines))     # written as Python writes it
    return out


@pytest.mark.parametrize("args", [(), ("--lean", "always")])
def test_what_check_records(pw, tmp_path, args):
    """--record appends the same events: the facts claimed and withdrawn, what was computed, and (with Lean) what was agreed and proved."""
    if args and not LAKE:
        pytest.skip("Lean not installed")
    (tmp_path / "a").mkdir()
    repo = declare(tmp_path / "a", [LIMIT, MODES], **FILES)
    (py, pc, po), (rs, rc, ro) = appended(pw, repo, "--record", "--unconfirmed", "warn", *args)
    assert py == rs and pc == rc and po == ro and {e["type"] for e in py} >= {"claim", "reading"}, (py, rs)
    # and again on top of that: a fact taken out, a description changed, a value changed
    first = subprocess.run([pw, "check", "--repo", repo, "--record", *args], capture_output=True, text=True)
    assert first.returncode in (0, 1)
    with open(os.path.join(repo, "pw-facts.json"), "w") as fh:
        json.dump([{**LIMIT, "gloss": "the most there may be"}], fh)
    with open(os.path.join(repo, "k.py"), "w") as fh:
        fh.write("LIMIT = 15\nMODES = {'fast': 1, 'safe': 2}\n")
    (py, pc, po), (rs, rc, ro) = appended(pw, repo, "--record", *args)
    assert py == rs and pc == rc and po == ro and [e["type"] for e in py][:2] == ["claim", "withdraw"], (py, rs)


@lean
def test_what_check_records_here(pw, tmp_path):
    """This repository, with its definition: nothing new to record, or the same new lines."""
    repo = str(tmp_path / "here")
    shutil.copytree(ROOT, repo, ignore=shutil.ignore_patterns(".git", "target", "__pycache__", ".pytest_cache"))
    (py, pc, po), (rs, rc, ro) = appended(pw, repo, "--record", "--verify")
    assert py == rs and pc == rc == 0 and po == ro


def test_confirming(pw, tmp_path):
    """A person confirms and rejects readings: the same lines; the same refusal of saying both."""
    repo = declare(tmp_path, [{**LIMIT, "places": [LIMIT["places"][0], "doc.md::Limits"]}], **FILES)
    m = "M:" + "0" * 10
    py = subprocess.run([sys.executable, "-c", f"""
import sys; sys.path.insert(0, {ROOT!r})
from pw.kernel import Kernel
k = Kernel({repo!r} + "/pw-log.jsonl", actor="reader")
k.sync_facts({repo!r} + "/pw-facts.json")
h = next(iter(k.state().facts))
print(k.read_place(h, "doc.md::Limits", "14", cwd={repo!r}, quote="At most 14.")["m"])
"""], capture_output=True, text=True)
    m = py.stdout.strip()
    assert m.startswith("M:"), py.stderr
    (a, ac, ao), (b, bc, bo) = appended(pw, repo, "--who", "ann", m, cmd="confirm")
    assert a == b and ac == bc == 0 and ao == bo and a[0]["type"] == "observe" and a[0]["outcome"] == "confirmed"
    (a, ac, _), (b, bc, _) = appended(pw, repo, "--who", "ann", "--reject", m, cmd="confirm")
    assert a == b and ac == bc == 0
    (a, ac, _), (b, bc, _) = appended(pw, repo, "--who", "ann", "M:nothing", cmd="confirm")
    assert a == b == [] and ac == bc == 2
    (a, ac, ao), (b, bc, bo) = appended(pw, repo, cmd="confirm")          # the list: nothing written
    assert a == b == [] and ac == bc == 0 and ao == bo and m in ao


# ---- what a reader can say, through the MCP server -----------------------------------------------

def mcp_session(pw, env, calls):
    """Start `pw mcp`, initialize, make the calls; return what each said back."""
    msgs = [{"jsonrpc": "2.0", "id": 0, "method": "initialize", "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                                                                            "clientInfo": {"name": "test", "version": "0"}}},
            {"jsonrpc": "2.0", "method": "notifications/initialized"},
            {"jsonrpc": "2.0", "id": 1, "method": "tools/list"}]
    msgs += [{"jsonrpc": "2.0", "id": n + 2, "method": "tools/call", "params": {"name": name, "arguments": a}} for n, (name, a) in enumerate(calls)]
    r = subprocess.run([pw, "mcp"], input="".join(json.dumps(m) + "\n" for m in msgs), capture_output=True, text=True, env={**os.environ, **env}, timeout=60)
    replies = {m["id"]: m for m in map(json.loads, r.stdout.splitlines())}
    assert replies[0]["result"]["serverInfo"]["name"] == "pw"
    assert [t["name"] for t in replies[1]["result"]["tools"]] == ["read_place", "not_stated"]
    return [replies[n + 2]["result"]["structuredContent"] for n in range(len(calls))]


def test_what_a_reader_says(pw, tmp_path):
    """read_place and not_stated: the same answers and the same lines as the Python kernel's, refusals included."""
    from pw.kernel import Kernel, KernelError
    from pw.lean_gate import GateError, LeanGate
    facts = [{"name": "limit", "type": "Nat", "places": ["doc.md::Limits", LIMIT["places"][0]]},
             {"name": "modes", "type": "List String", "places": ["doc.md::Modes", {"at": "notes.md", "some": True}]}]
    repo = declare(tmp_path, facts, **FILES, **{"notes.md": "Try `fast`.\n"})
    Kernel(str(tmp_path / "pw-log.jsonl")).sync_facts(str(tmp_path / "pw-facts.json"))
    hs = {f["name"]: h for h, f in Kernel(str(tmp_path / "pw-log.jsonl")).state().facts.items()}
    L, M = hs["limit"], hs["modes"]
    calls = [("read_place", {"h": L, "place": "doc.md::Limits", "object": "14", "quote": "At most 14."}),
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "14", "quote": "At most 14."}),          # the same again: nothing new
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "15", "quote": "At most 15."}),          # not in the place
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "7 + 7", "quote": "At most 14."}),       # not written out
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "14 #", "quote": "At most 14."}),        # not Lean we take
             ("read_place", {"h": L, "place": "doc.md::Nothing", "object": "14", "quote": "x"}),                   # not a place of the fact
             ("read_place", {"h": "H:nothing", "place": "doc.md::Limits", "object": "14", "quote": "x"}),
             ("read_place", {"h": M, "place": "doc.md::Modes", "object": '["fast"]', "quote": "`fast`"}),
             ("read_place", {"h": M, "place": "notes.md", "object": '["fast"]', "quote": "Try `fast`."}),
             ("not_stated", {"h": L, "place": "k.py::LIMIT", "why": "  it is   the code  "}),
             ("not_stated", {"h": L, "place": "k.py::LIMIT", "why": " "})]
    for blind, model in (("1", "claude-opus-5-5"), ("1", ""), ("0", "claude-opus-5-5")):
        env = {"PW_AGENT": "reader", "PW_WORKDIR": repo, "PW_BLIND": blind, "PW_MODEL": model}
        lines, said = [], []
        for impl in ("python", "rust"):
            db = str(tmp_path / f"log-{impl}-{blind}{model}.jsonl")
            shutil.copy(tmp_path / "pw-log.jsonl", db)
            if impl == "python":
                k = Kernel(db, gate=LeanGate(), actor="reader")
                who = {"blind": blind == "1", "model": model or None}
                out = []
                for name, a in calls:
                    try:
                        out.append(k.read_place(a["h"], a["place"], a["object"], cwd=repo, quote=a["quote"], **who) if name == "read_place"
                                   else k.decline(a["h"], a["place"], a["why"], repo, **who))
                    except (KernelError, GateError) as e:
                        out.append({"error": f"{type(e).__name__}: {e}"})
            else:
                out = mcp_session(pw, {**env, "PW_DB": db, "PW_MODEL": model}, calls) if model else \
                      mcp_session(pw, {k: v for k, v in {**env, "PW_DB": db}.items() if k != "PW_MODEL"}, calls)
            said.append(out)
            with open(db, encoding="utf-8") as fh:
                lines.append([{k: v for k, v in json.loads(x).items() if k != "ts"} for x in fh.read().splitlines()])
        assert said[0] == said[1], (blind, model, said)
        assert lines[0] == lines[1], (blind, model)
    assert [o.get("error", "")[:11] for o in said[1]][2:7] == ["KernelError", "KernelError", "GateError: ", "KernelError", "KernelError"]
