"""The Rust build (rust/) is the kernel: it judges, it keeps the record, it runs Lean. These tests
are about what it shows from outside: the check, the readers' tools over MCP, a person's
confirmation, what it does with a place's text, what it says when a check cannot be made.
Skipped when the build is not there and cargo is not there to make it."""
import json
import os
import shutil
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PW = os.path.join(ROOT, "rust", "target", "release", "pw")
LAKE = os.environ.get("PW_LAKE") or shutil.which("lake")


@pytest.fixture(scope="module")
def pw():
    if not os.path.exists(PW):
        if not shutil.which("cargo"):
            pytest.skip("the Rust build is not there and cargo is not installed")
        subprocess.run(["cargo", "build", "--release", "--locked"], cwd=os.path.join(ROOT, "rust"), check=True, capture_output=True)
    return PW


def declare(tmp_path, facts, **files):
    for name, text in files.items():
        (tmp_path / name).write_text(text)
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    return str(tmp_path)


def check(pw, repo, *args, env=None):
    return subprocess.run([pw, "check", "--repo", repo, *args], capture_output=True, text=True, env={**os.environ, **(env or {})})


LIMIT = {"name": "limit", "type": "Nat", "places": [{"at": "k.py::LIMIT", "read": {"python": "value", "as": "nat"}},
                                                     {"at": "doc.md::Limits", "read": {"find": r"most (\d+)", "as": "nat"}}]}
MODES = {"name": "modes", "type": "List String", "places": [{"at": "k.py::MODES", "read": {"python": "keys", "sort": True}},
                                                            {"at": "cfg.toml", "read": {"data": "mode.*.name", "sort": True}},
                                                            {"at": "doc.md::Modes", "read": {"find_all": "`(\\w+)`", "sort": True}, "some": True}]}
FILES = {"k.py": "LIMIT = 14\nMODES = {'fast': 1,\n         \"safe\": 2}\n", "doc.md": "## Limits\n\nAt most 14.\n\n## Modes\n\n`fast`\n",
         "cfg.toml": '[[mode]]\nname = "fast"\n\n[[mode]]\nname = "safe"\n'}


# ---- reading a place, and what is done with its text ----------------------------------------------

def test_this_repositorys_places_are_read(pw):
    from pwt.kernel import compute, locate, reader
    with open(os.path.join(ROOT, "pw-facts.json"), encoding="utf-8") as fh:
        facts = json.load(fh)
    places = [p for f in facts for p in f["places"] if isinstance(p, dict) and "read" in p]
    assert len(places) >= 10
    for p in places:
        assert compute(reader(p["read"], p["at"]), locate(p["at"], ROOT).decode())


def test_a_value_is_written_back_only_where_it_reads_back(pw):
    from pwt.kernel import KernelError, pattern, write_pattern
    rd = pattern(find=r"LIMIT = (\d+)", kind="nat")
    assert write_pattern(rd, "LIMIT = 14\nOTHER = 14\n", "15") == "LIMIT = 15\nOTHER = 14\n"
    assert write_pattern(pattern(find=r"ratio: ([0-9.]+)", kind="permille"), "ratio: 0.85\n", "900") == "ratio: 0.9\n"
    for text, term in (("LIMIT = 14\nLIMIT = 3\n", "15"), ("LIMIT = 14\n", '"x"')):
        with pytest.raises(KernelError):
            write_pattern(rd, text, term)
    with pytest.raises(KernelError, match="only a single value"):
        write_pattern(pattern(find_all=r"(\d+)"), "1 2", "[3]")


def test_what_a_reader_is_shown(pw, tmp_path):
    """A long place: the lines its way of reading looks at. A small one: what surrounds it, in
    characters, whatever the script (Python's version cut after it by bytes)."""
    from pwt.kernel import context, excerpt, pattern
    text = "x\n" * 2000 + "MODES = [\"a\", \"b\"]\n" + "y\n" * 2000
    rd = pattern(find_all=r'"(\w+)"', within=r"MODES = \[([^\]]*)\]")
    assert excerpt(rd, text) == 'MODES = ["a", "b"]\n' and excerpt(rd, "short") is None
    (tmp_path / "doc.md").write_text("# 設定\n\n## 上限 🚀\n\n最大 14。\n\n## 次\n\n説明。\n")
    around = context("doc.md::上限 🚀", str(tmp_path))
    assert around == "# 設定\n\n## 上限 🚀\n\n最大 14。\n\n## 次\n\n説明。\n", around


def test_measured_bounds_are_exact():
    """The bounds a reader's measurement allows decide whether its readings count: to machine precision."""
    from pwt.kernel import interval
    lo, hi = interval(27, 27)
    assert abs(lo - 0.025 ** (1 / 27)) < 1e-12 and hi == 1.0                # Beta(27, 1): the bound has a closed form
    lo, hi = interval(0, 40)
    assert lo == 0.0 and abs(hi - (1 - 0.025 ** (1 / 40))) < 1e-12


# ---- the check -------------------------------------------------------------------------------------

def test_this_repository(pw):
    r = check(pw, ROOT, "--json")
    assert r.returncode == 0 and all(d["state"] == "current" for d in json.loads(r.stdout)["decisions"]), r.stdout[-500:]
    assert check(pw, ROOT, "--needs-lean").stdout == "yes\n"                 # (it declares a definition)
    if LAKE:
        r = check(pw, ROOT, "--verify")
        assert r.returncode == 0 and " refused" in r.stdout and r.stdout.strip().endswith("0 refused")


def test_a_declaration_that_cannot_be_used(pw, tmp_path):
    for text in ["[{", '{"name": "x"}', '[{"name": "x", "places": ["a"]}]', '[{"name": "x", "type": "Nat", "place": ["a"]}]',
                 json.dumps([{"name": "x", "type": "Nat", "places": ["a"]}] * 2), '[{"name": "x", "type": "Nat", "places": [{"at": "a", "reader": 1}]}]',
                 json.dumps([{"name": "x", "type": "Nat", "places": ["a"], "value": 1}])]:
        (tmp_path / "pw-facts.json").write_text(text)
        r = check(pw, str(tmp_path))
        assert r.returncode == 2 and r.stderr.startswith("pw: ") and r.stdout == "", (text, r.stderr)
    os.remove(tmp_path / "pw-facts.json")
    r = check(pw, str(tmp_path))
    assert r.returncode == 2 and "nothing is declared here" in r.stderr


def test_what_is_wrong_is_said_in_a_line(pw, tmp_path):
    """A key nobody reads, and a record cut off in the middle of a line: said in a line, naming the project's record."""
    r = check(pw, declare(tmp_path, [{**LIMIT, "glos": "x"}], **FILES))
    assert r.returncode == 2 and "unknown keys ['glos']" in r.stderr
    repo = declare(tmp_path, [LIMIT], **FILES)
    (tmp_path / "pw-log.jsonl").write_text('{"type": "withdraw", "h": "H:1", "justification": "x"}\n{"type": "rea')
    r = check(pw, repo)
    assert r.returncode == 2 and r.stderr.startswith(f"pw: {tmp_path}/pw-log.jsonl, line 2: not a readable event")


def test_without_lean_what_needs_it_is_not_checked(pw, tmp_path):
    """Where Lean is needed and is not there, nothing is judged; what is written out is still compared as written."""
    no = {"PW_LAKE": str(tmp_path / "no-lake")}
    count = {"name": "count", "type": "Nat", "defined": {"from": ["limit"], "as": "fun n => n"}, "places": [LIMIT["places"][1]]}
    r = check(pw, declare(tmp_path, [LIMIT, count], **FILES), env=no)
    assert r.returncode == 2 and "Lean" in r.stderr and r.stdout == ""
    r = check(pw, declare(tmp_path, [LIMIT], **FILES), "--verify", "--unconfirmed", "warn", env=no)
    assert r.returncode == 0 and "not run again: Lean (lake) is not installed" in r.stdout and "nothing declared needs Lean" in r.stdout


def test_checking_writes_nothing_and_recording_writes_once(pw, tmp_path):
    repo = declare(tmp_path, [LIMIT, MODES], **FILES)
    log = tmp_path / "pw-log.jsonl"
    check(pw, repo, "--unconfirmed", "warn")
    assert not log.exists()
    check(pw, repo, "--record", "--unconfirmed", "warn")
    lines = log.read_text().splitlines()
    assert [json.loads(x)["type"] for x in lines].count("claim") == 2 and all(json.loads(x)["actor"] == "check" for x in lines)
    assert all(line == json.dumps(json.loads(line), ensure_ascii=False) for line in lines)       # written as JSON lines, Python's spacing
    check(pw, repo, "--record", "--unconfirmed", "warn")
    assert log.read_text().splitlines() == lines                                                 # nothing new to say


# ---- a person's confirmation --------------------------------------------------------------------

def test_confirming(pw, tmp_path):
    """A person confirms and rejects readings; the same person cannot say both; listing writes nothing."""
    from pwt.core import Kernel
    repo = declare(tmp_path, [{**LIMIT, "places": [LIMIT["places"][0], "doc.md::Limits"]}], **FILES)
    k = Kernel(str(tmp_path / "pw-log.jsonl"), actor="reader")
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    m = k.read_place(next(iter(k.state().facts)), "doc.md::Limits", "14", cwd=repo, quote="At most 14.")["m"]
    confirm = lambda *a: subprocess.run([pw, "confirm", "--repo", repo, *a], capture_output=True, text=True)
    before = (tmp_path / "pw-log.jsonl").read_text()
    r = confirm()
    assert r.returncode == 0 and m in r.stdout and "because it says: At most 14." in r.stdout
    assert (tmp_path / "pw-log.jsonl").read_text() == before
    assert confirm("--who", "ann", m).stdout == f"confirmed {m}\n"
    e = json.loads((tmp_path / "pw-log.jsonl").read_text().splitlines()[-1])
    assert (e["type"], e["actor"], e["target"], e["outcome"]) == ("observe", "ann", m, "confirmed")
    assert confirm("--who", "ann", m).returncode == 0 and (tmp_path / "pw-log.jsonl").read_text().count('"observe"') == 1   # said again: nothing new
    r = confirm("--who", "ann", "--reject", m)
    assert r.returncode == 2 and "already recorded this reading as confirmed" in r.stderr
    assert confirm("--who", "ann", "M:nothing").returncode == 2
    assert "0 reading(s) nobody has confirmed" in confirm().stdout


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
    """read_place and not_stated over MCP: what is taken, what is refused and why, and what is recorded."""
    from pwt.core import Kernel
    from pwt.kernel import INSTRUCTIONS
    facts = [{"name": "limit", "type": "Nat", "places": ["doc.md::Limits", LIMIT["places"][0]]},
             {"name": "modes", "type": "List String", "places": ["doc.md::Modes", {"at": "notes.md", "some": True}]}]
    repo = declare(tmp_path, facts, **FILES, **{"notes.md": "Try `fast`.\n"})
    k = Kernel(str(tmp_path / "pw-log.jsonl"))
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    hs = {f["name"]: h for h, f in k.state().facts.items()}
    L, M = hs["limit"], hs["modes"]
    calls = [("read_place", {"h": L, "place": "doc.md::Limits", "object": "14", "quote": "At most 14."}),
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "14", "quote": "At most 14."}),          # the same again: nothing new
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "15", "quote": "At most 15."}),          # not in the place
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "7 + 7", "quote": "At most 14."}),       # not written out
             ("read_place", {"h": L, "place": "doc.md::Limits", "object": "14 #", "quote": "At most 14."}),        # not Lean we take
             ("read_place", {"h": L, "place": "doc.md::Nothing", "object": "14", "quote": "x"}),                   # not a place of the fact
             ("read_place", {"h": "H:nothing", "place": "doc.md::Limits", "object": "14", "quote": "x"}),
             ("read_place", {"h": M, "place": "notes.md", "object": '["fast"]', "quote": "Try `fast`."}),
             ("not_stated", {"h": L, "place": "k.py::LIMIT", "why": "  it is   the code  "}),
             ("not_stated", {"h": L, "place": "k.py::LIMIT", "why": " "})]
    said = mcp_session(pw, {"PW_DB": str(tmp_path / "pw-log.jsonl"), "PW_AGENT": "reader", "PW_WORKDIR": repo, "PW_BLIND": "1",
                            "PW_MODEL": "claude-opus-5-5", "PW_INSTRUCTIONS": "given-these"}, calls)
    assert said[0] == said[1] and said[0]["read as"] == "14" and said[0]["m"].startswith("M:")
    assert [x.get("error", "").split(":")[0] for x in said[2:7]] == ["KernelError", "KernelError", "GateError", "KernelError", "KernelError"]
    assert "the quote is not in the place" in said[2]["error"] and "state the value itself" in said[3]["error"] and "forbidden token" in said[4]["error"]
    assert said[8] == {"declined": "k.py::LIMIT"} and "say what the place is about" in said[9]["error"]
    events = [json.loads(x) for x in (tmp_path / "pw-log.jsonl").read_text().splitlines() if '"claim"' not in x]
    assert [e["type"] for e in events] == ["reading", "reading", "decline"]
    first, part, no = events
    assert (first["actor"], first["blind"], first["model"], first["instructions"], first["literal"], first["anchor"]) == ("reader", True, "claude-opus-5-5", "given-these", True, True)
    assert part["anchor"] is False and part["asked"] != first["asked"]                       # a place that states some entries is asked another question
    assert no["why"] == "it is the code"
    # without being told, the server records the instructions this build has: pw/reader.txt
    mcp_session(pw, {"PW_DB": str(tmp_path / "pw-log.jsonl"), "PW_AGENT": "reader-2", "PW_WORKDIR": repo, "PW_BLIND": "1",
                     "PW_MODEL": "claude-opus-5-5"}, calls[:1])
    assert json.loads((tmp_path / "pw-log.jsonl").read_text().splitlines()[-1])["instructions"] == INSTRUCTIONS


# ---- ways of reading by structure: Markdown tables, YAML, Rust ------------------------------------

def test_a_markdown_table_is_read_by_its_columns(pw, tmp_path):
    from pwt.kernel import KernelError, compute, reader
    text = ("## Modes\n\nSome prose with `fast` in it.\n\n| Mode | Limit | Notes |\n|:-----|------:|-------|\n"
            "| `fast` | 14 | the default \\| quick |\n|  safe  |  3 |  |\n\n```\n| Mode |\n|---|\n| fake |\n```\n")
    read = lambda r, **kw: compute(reader({"table": r, **kw}, "doc.md::Modes"), text)
    assert read("Mode") == '["fast", "safe"]' and read("Mode", sort=True) == '["fast", "safe"]'
    assert read("Limit", row="safe", **{"as": "nat"}) == "3" and read("Notes", row="fast") == '"the default | quick"'
    realigned = text.replace("| `fast` | 14 |", "|`fast`|14|").replace("|:-----|------:|", "|---|---|")
    assert compute(reader({"table": "Mode"}, "doc.md"), realigned) == '["fast", "safe"]'   # spacing and alignment do not matter
    for bad in ({"table": "Nothing"}, {"table": "Limit", "row": "turbo"}):
        with pytest.raises(KernelError):
            compute(reader(bad, "doc.md"), text)
    with pytest.raises(KernelError, match="Markdown"):
        reader({"table": "Mode"}, "doc.txt")


def test_a_yaml_file_is_read_by_a_path(pw):
    from pwt.kernel import compute, reader
    text = "jobs:\n  test:\n    strategy:\n      matrix:\n        python: ['3.12', \"3.13\"]\n    runs-on: ubuntu-24.04\nlimit: 14\n"
    at = ".github/workflows/ci.yml"
    assert compute(reader({"data": "jobs.test.strategy.matrix.python"}, at), text) == '["3.12", "3.13"]'
    assert compute(reader({"data": "jobs.*.runs-on"}, at), text) == '["ubuntu-24.04"]'
    assert compute(reader({"data": "limit", "as": "nat"}, at), text) == "14"
    assert compute(reader({"data": "jobs", "keys": True}, at), text) == '["test"]'


def test_a_rust_file_is_read_by_its_items(pw):
    from pwt.kernel import KernelError, compute, reader
    text = ('pub const LIMIT: u32 = 14;\nconst NAMES: [&str; 2] = ["b", "a"];\nstatic NEG: i64 = -3;\n'
            'pub enum Mode { Fast, Safe }\nstruct Config { limit: u32, mode: Mode }\n'
            'mod tools { pub fn read() {} pub fn not_stated() {} pub const X: u8 = 1; }\n'
            'impl Config { fn new() -> Self { todo!() } fn check(&self) {} }\n'
            'fn names() -> Vec<String> { vec!["x".into(), format!("{}", "y")] }\n')
    read = lambda **r: compute(reader({"as": "string", **r}, "src/lib.rs"), text)
    assert read(rust="value", item="LIMIT", **{"as": "nat"}) == "14" and read(rust="value", item="NEG", **{"as": "int"}) == "(-3)"
    assert read(rust="value", item="NAMES", sort=True) == '["a", "b"]'
    assert read(rust="names", item="Mode") == '["Fast", "Safe"]' and read(rust="names", item="Config") == '["limit", "mode"]'
    assert read(rust="names", item="impl Config") == '["new", "check"]'                 # a type, and its impl blocks, apart
    assert read(rust="names", item="tools") == '["read", "not_stated", "X"]' and read(rust="value", item="tools::X", **{"as": "nat"}) == "1"
    assert read(rust="strings", item="names") == '["x", "{}", "y"]'
    reformatted = text.replace("pub const LIMIT: u32 = 14;", "pub const LIMIT: u32 =\n    14; // the most")
    assert compute(reader({"rust": "value", "item": "LIMIT", "as": "nat"}, "src/lib.rs"), reformatted) == "14"
    for bad in ({"rust": "value", "item": "Mode"}, {"rust": "value", "item": "nothing"}, {"rust": "value", "item": "names"}):
        with pytest.raises(KernelError):
            compute(reader(bad, "src/lib.rs"), text)
    with pytest.raises(KernelError, match="item"):
        reader({"rust": "value"}, "src/lib.rs")


def test_a_first_step_writes_what_is_missing_and_keeps_the_rest(pw, tmp_path):
    pin = "0123456789abcdef0123456789abcdef01234567"
    (tmp_path / ".gitattributes").write_text("*.png binary")
    init = lambda *a: subprocess.run([pw, "init", "--repo", str(tmp_path), *a], capture_output=True, text=True)
    r = init("--pin", pin)
    assert r.returncode == 0 and "wrote    pw-facts.json" in r.stdout
    assert (tmp_path / "pw-facts.json").read_text() == "[]\n"
    assert (tmp_path / ".gitattributes").read_text() == "*.png binary\npw-log.jsonl merge=union\n"
    flow = (tmp_path / ".github" / "workflows" / "facts.yml").read_text()
    assert f"uses: sugipamo/parallelworld@{pin}" in flow and "permissions:\n  contents: read" in flow
    (tmp_path / "pw-facts.json").write_text(json.dumps([LIMIT]))
    r = init("--pin", pin)                                        # again: nothing is changed
    assert r.stdout.count("kept") == 3 and json.loads((tmp_path / "pw-facts.json").read_text()) == [LIMIT]
    assert init("--pin", "main").returncode == 2                  # a name can be moved: a commit id only
    (tmp_path / "fresh").mkdir()
    assert init("--pin", pin).returncode == 0 and check(pw, declare(tmp_path / "fresh", [])).returncode == 0     # an empty declaration passes


def test_what_was_read_blind_is_the_way_of_reading(pw, tmp_path):
    """A computed place stands by a blind reading of an earlier text: said as such, not as a reading of this value (#15)."""
    from pwt.core import Kernel
    from pwt.kernel import INSTRUCTIONS, pattern
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    (tmp_path / "pw-calibration.json").write_text(json.dumps([{"model": "opus", "instructions": INSTRUCTIONS, "planted": {"n": 27, "read": 27, "stuck": 0},
                                                                "decoys": {"n": 27, "accepted": 0}}]))
    k = Kernel(str(tmp_path / "pw-log.jsonl"), actor="reader")
    h = k.claim_fact("limit", "Nat", [{"at": "k.py", "reader": pattern(find=r"LIMIT = (\d+)", kind="nat")}], gloss="the limit")["h"]
    k.read_place(h, "k.py", cwd=str(tmp_path))
    k.read_place(h, "k.py", "14", cwd=str(tmp_path), quote="LIMIT = 14", blind=True, model="opus")
    place = lambda: k.recheck(str(tmp_path))["decisions"][0]["places"][0]
    assert place()["stands"] and place()["read the same blind on"] == "this text"
    (tmp_path / "k.py").write_text("LIMIT = 15\n")
    p = place()
    assert p["stands"] and p["has"] == {"read the same blind": True} and p["read the same blind on"] == "an earlier text"


def test_help_is_asked_for_not_an_error(pw):
    """pw, pw --help, pw help check: the usage, exit 0, every command a user types named (#16)."""
    for args in ([], ["--help"], ["-h"], ["help"]):
        r = subprocess.run([pw, *args], capture_output=True, text=True)
        assert r.returncode == 0 and all(f"pw {c}" in r.stdout for c in ("start", "check", "confirm", "init", "version", "maintain", "calibrate", "discover", "propagate")), args
    for c in ("check", "confirm", "init", "start", "maintain", "calibrate", "propagate"):
        assert subprocess.run([pw, c, "--help"], capture_output=True, text=True).stdout.startswith(f"pw {c}:")
        assert subprocess.run([pw, "help", c], capture_output=True, text=True).stdout.startswith(f"pw {c}:")


def test_rust_struct_fields_as_serde_has_them_and_the_strings_a_match_takes(pw):
    from pwt.kernel import compute, reader
    text = ('#[derive(Deserialize)]\npub struct TaskConfig {\n    #[serde(rename = "task_name")]\n    pub name: String,\n'
            '    #[serde(default)]\n    pub view: bool,\n    // not in the file\n    #[serde(skip)]\n    pub internal: bool,\n}\n'
            'impl std::fmt::Display for Status {\n    fn fmt(&self, f: &mut F) -> R { match self { Status::A => write!(f, "ok"), Status::B => write!(f, "error") } }\n}\n'
            'pub enum Status { A, B }\n'
            'fn route(key: &str) -> u8 {\n    match key {\n        "system.status" => 1,\n        "system.stop" | "system.halt" => 2,\n'
            '        _ if key.starts_with("system.") => 3,\n        _ => 0,\n    }\n}\n')
    read = lambda **r: compute(reader({"sort": True, **r}, "src/lib.rs"), text)
    assert read(rust="fields", item="TaskConfig") == '["task_name", "view"]'
    assert read(rust="strings", item="impl Status") == '["error", "ok"]'
    assert read(rust="arms", item="route") == '["system.halt", "system.status", "system.stop"]'    # (a guard is not a string it matches)


def test_entries_in_another_order_are_said_to_be_that(pw, tmp_path):
    """Two lists with the same entries in another order differ; what to do about it is said (#18)."""
    facts = [{"name": "modes", "type": "List String", "places": [{"at": "a.py", "read": {"find_all": '"(\\w+)"'}},
                                                                 {"at": "b.py", "read": {"find_all": '"(\\w+)"'}}]}]
    r = check(pw, declare(tmp_path, facts, **{"a.py": 'M = ["fast", "safe"]\n', "b.py": 'M = ["safe", "fast"]\n'}), "--unconfirmed", "warn")
    assert r.returncode == 1 and 'the same entries in another order: give the ways of reading "sort": true' in r.stdout


def test_the_version_says_what_it_was_built_from(pw):
    out = subprocess.run([pw, "version"], capture_output=True, text=True).stdout.splitlines()
    assert out[0].startswith("parallelworld ") and (len(out) == 1 or (out[1].startswith("built from ") and len(out[1].split()[-1]) == 40))


def test_the_lean_project_is_built_in(pw, tmp_path):
    """An executable with no lean/ next to it (published, or installed on its own) still runs the
    record's proofs again: the Lean project is built into it (#17)."""
    if not LAKE:
        pytest.skip("Lean not installed")
    r = check(pw, ROOT, "--verify", env={"PW_LEAN_DIR": ""})          # (the empty path: no project on disk)
    assert r.returncode == 0 and r.stdout.strip().endswith("0 refused") and "verified again" in r.stdout, r.stdout[-300:]


def test_a_place_whose_text_is_unchanged_is_not_sent_to_be_searched_for(pw, tmp_path):
    """The text is as it was read, but the way of reading no longer reads it (a declaration, or this
    tool's version): the way of reading is what to fix, not the place to look for; and "impl NAME" is
    said where that is what was meant (#19)."""
    text = 'pub enum S { A, B }\nimpl std::fmt::Display for S {\n    fn fmt(&self, f: &mut F) -> R { match self { S::A => write!(f, "ok"), S::B => write!(f, "no") } }\n}\n'
    fact = lambda item: [{"name": "words", "type": "List String", "places": [{"at": "s.rs", "read": {"rust": "strings", "item": item, "sort": True}}]}]
    repo = declare(tmp_path, fact("impl S"), **{"s.rs": text})
    assert check(pw, repo, "--record", "--unconfirmed", "warn").returncode == 0
    declare(tmp_path, fact("S"))
    r = check(pw, repo, "--unconfirmed", "warn")
    assert r.returncode == 1 and '"item": "impl S" reads them' in r.stdout
    assert "its text is as it was when last read" in r.stdout and "pw discover" not in r.stdout
    assert "a type's name alone does not)" in r.stdout                                      # the reason is not cut (#20)
    (tmp_path / "s.rs").write_text(text + "// touched\n")                                    # the text changed, the fix is known: that first (#20)
    out = check(pw, repo, "--unconfirmed", "warn").stdout
    assert "says how to fix its way of reading: fix that first; if it still cannot be read, pw discover" in out
    (tmp_path / "s.rs").write_text(text.replace("pub enum S", "pub enum T").replace("for S", "for T"))   # nothing to say how: look for it
    out = check(pw, repo, "--unconfirmed", "warn").stdout
    assert "pw discover (it looks for where the statement went)" in out and "fix that first" not in out


# ---- the agent tools, with a stand-in for claude (tests/fake_claude.py) -------------------------

FAKE = os.path.join(ROOT, "tests", "fake_claude.py")


def agents(tmp_path, told):
    """The environment for a command whose sessions are the stand-in, told what to answer; and its log of sessions."""
    log = tmp_path.parent / f"{tmp_path.name}-sessions.jsonl"
    log.write_text("")
    spec = tmp_path.parent / f"{tmp_path.name}-told.json"
    spec.write_text(json.dumps({**told, "log": str(log)}))
    def sessions():                      # the sessions started since this was last asked
        said = [json.loads(l) for l in log.read_text().splitlines()]
        log.write_text("")
        return said
    return {"PW_CLAUDE": FAKE, "FAKE_CLAUDE": str(spec)}, sessions


def test_maintain_has_each_place_read_once_for_what_it_is_now(pw, tmp_path):
    """pw maintain has a blind reader read what nobody has read, and look at what a pattern reads.
    What it has read, as it is now, is not paid for again; a place that changed is read again."""
    repo = declare(tmp_path, [{"name": "limit", "type": "Nat", "gloss": "the most atoms", "places": [
                       "doc.md::Limits", {"at": "k.py", "read": {"find": r"LIMIT = (\d+)", "as": "nat"}}]}],
                   **{"k.py": "LIMIT = 14\n", "doc.md": "## Limits\n\nAt most 14 atoms.\n"})
    maintain = lambda env: subprocess.run([pw, "maintain", "--repo", repo, "--model", "opus", "--second-model", ""],
                                          capture_output=True, text=True, env={**os.environ, **env})
    r = maintain({"PW_CLAUDE": str(tmp_path / "no-claude")})
    assert r.returncode == 2 and "Nothing was read" in r.stderr and "claude" in r.stderr
    assert '"blind": true' not in (tmp_path / "pw-log.jsonl").read_text()       # nobody was asked

    env, sessions = agents(tmp_path, {"read": {"doc.md::Limits": {"object": "14", "quote": "At most 14 atoms."},
                                               "k.py": {"object": "14", "quote": "LIMIT = 14"}}})
    r = maintain(env)
    said = [s for s in sessions()]
    assert len(said) == 2 and all(s["env"]["PW_MODEL"] == "opus" and s["env"]["PW_BLIND"] == "1" for s in said), r.stdout
    assert "place: doc.md::Limits" in said[0]["prompt"] and "place: k.py" in said[1]["prompt"]
    assert "not measured" in r.stdout or "unmeasured" in r.stdout, r.stdout     # read, but by a reader nobody measured here

    r = maintain(env)
    assert sessions() == [], r.stdout                                           # nothing new to read: no session at all
    (tmp_path / "k.py").write_text("# the limit\nLIMIT = 14\n")
    r = maintain(env)
    assert [("place: k.py" in s["prompt"]) for s in sessions()] == [True]       # the pattern's place changed: looked at again


def test_start_takes_each_step_not_done_yet_and_goes_on_from_where_it_stopped(pw, tmp_path):
    """pw start: set up, then (facts being declared here) measure, read, check. Without --yes and
    with nobody to answer, it stops before the first step that spends money, having spent nothing."""
    with open(os.path.join(ROOT, "pw", "reader.txt"), encoding="utf-8") as fh:
        instructions = __import__("hashlib").sha256(fh.read().encode()).hexdigest()[:10]
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    env, sessions = agents(tmp_path, {"read": {"doc.md::Limits": {"object": "14", "quote": "At most 14 atoms."},
                                               "k.py": {"object": "14", "quote": "LIMIT = 14"}}})
    start = lambda *a: subprocess.run([pw, "start", "--repo", str(tmp_path), "--model", "opus", *a], capture_output=True, text=True,
                                      stdin=subprocess.DEVNULL, env={**os.environ, **env})
    r = start()
    assert "1. Setting up" in r.stdout and (tmp_path / "pw-facts.json").read_text().strip() == "[]" and (tmp_path / ".gitattributes").exists()
    assert "propose facts" in r.stdout and "Stopped before it" in r.stdout and r.returncode == 1 and sessions() == []

    (tmp_path / "pw-facts.json").write_text(json.dumps([{"name": "limit", "type": "Nat", "gloss": "the most atoms", "places": [
        "doc.md::Limits", {"at": "k.py", "read": {"find": r"LIMIT = (\d+)", "as": "nat"}}]}]))
    r = start()
    assert "Set up already" in r.stdout and "Facts declared already: 1" in r.stdout
    assert "opus is not measured here" in r.stdout and "Stopped before it" in r.stdout and sessions() == []

    (tmp_path / "pw-calibration.json").write_text(json.dumps([{"model": "opus", "instructions": instructions,      # (as if measured)
        "planted": {"n": 27, "read": 27, "stuck": 0}, "decoys": {"n": 27, "accepted": 0}}]))
    r = start()
    assert "Reader measured already" in r.stdout and "blind reader read" in r.stdout and "Stopped before it" in r.stdout and sessions() == []
    r = start("--yes")
    assert len(sessions()) >= 1 and "5. The check" in r.stdout, r.stdout + r.stderr
    assert "FAIL" not in r.stdout and r.returncode == 0 and "Done." in r.stdout, r.stdout
    r = start()
    assert "Every place is read as it is now" in r.stdout and r.returncode == 0 and sessions() == []
