import os
import shutil

import pytest

from pwt.core import Kernel
from pwt.kernel import KernelError
from pwt.core import GateError, LeanGate

LAKE = os.environ.get("PW_LAKE") or shutil.which("lake")


@pytest.fixture
def k(tmp_path):
    return Kernel(str(tmp_path / "e.db"))


def test_gate_is_the_only_way_in(tmp_path, monkeypatch):
    """Where every comparison is put to Lean: without it nothing is accepted as agreeing or
    differing, and only what Lean settled is recorded."""
    monkeypatch.setattr(Kernel, "compare", "always")
    (tmp_path / "a.txt").write_text("v = 1\n")
    (tmp_path / "b.txt").write_text("v = 1\n")
    from pwt.kernel import pattern
    places = [{"at": name, "reader": pattern(find=r"v = (\d+)", kind="nat")} for name in ("a.txt", "b.txt")]
    k = Kernel(str(tmp_path / "e.db"))
    k.claim_fact("v", "Nat", places)
    monkeypatch.setenv("PW_LAKE", str(tmp_path / "no-lake"))
    with pytest.raises(KernelError, match="Lean"):
        k.recheck(str(tmp_path))                                  # no Lean: the equation cannot be settled
    assert not k.state().proofs
    monkeypatch.delenv("PW_LAKE")
    if not LAKE:
        pytest.skip("the rest needs Lean")
    assert k.recheck(str(tmp_path))["decisions"][0]["state"] == "current"
    f, = k.state().props
    with pytest.raises(KernelError):
        k.prove("iff", f, "rfl")                                  # a proposition holds, or does not
    with pytest.raises(KernelError):
        k.prove("holds", "F:unknown", "rfl")
    with open(tmp_path / "e.db", "a") as fh:                      # a line of a kind the kernel does not know is not skipped
        fh.write('{"type": "ground", "h": "H:x"}\n')
    with pytest.raises(KernelError):
        k.state()


def test_gate_screening_and_axiom_judgement():
    gate = LeanGate()
    for bad in ("sorry", "exact foo\naxiom cheat : False", "simp\n#eval 1", "native_decide"):
        with pytest.raises(GateError):
            gate.render("holds", [("Prop", "True")], bad)
    # a string is data: the name of a tool is not a command. But nothing may pose as a string.
    gate.render("holds", [("Prop", 'x = ["declare_independent", "open", "theorem"]')], "rfl")
    for bad in ('"a\\" axiom cheat : False "', "'\"' axiom cheat : False '\"'", '"unterminated axiom cheat : False'):
        with pytest.raises(GateError):
            gate.render("holds", [("Prop", bad)], "rfl")
    src = gate.render("not", [("Prop", "1 = 2")], "simp")
    assert "theorem pw_goal : _root_.Not PWStmt.S0" in src and "#print" not in src
    with pytest.raises((GateError, KeyError)):
        gate.render("iff", [("Prop", "1 = 1"), ("Prop", "2 = 2")], "simp")
    assert LeanGate.judge(0, "'pw_goal' depends on axioms: [propext, Quot.sound]", "g")["ok"]
    assert LeanGate.judge(0, "'pw_goal' does not depend on any axioms", "g")["axioms"] == []
    assert not LeanGate.judge(0, "'pw_goal' depends on axioms: [sorryAx]", "g")["ok"]
    assert not LeanGate.judge(1, "error: unsolved goals", "g")["ok"]
    forged = "'pw_goal' does not depend on any axioms\n'pw_goal' depends on axioms: [sorryAx]"
    assert not LeanGate.judge(0, forged, "g")["ok"]
    assert not LeanGate.judge(0, "", "g")["ok"]


def test_a_subject_is_a_file_or_a_part_of_one(tmp_path):
    """A reading is tied to the content it is about, not to the rest of the file."""
    from pwt.kernel import locate, subject_id
    cwd = str(tmp_path)
    md = "# Title\n\nintro\n\n## Rules\n\n- one\n\n```\n# not a heading\n```\n\n### Detail\n\nmore\n\n## Other\n\ntext\n"
    (tmp_path / "doc.md").write_text(md)
    assert locate("doc.md::Rules", cwd).decode() == "## Rules\n\n- one\n\n```\n# not a heading\n```\n\n### Detail\n\nmore\n\n"
    before = subject_id("doc.md::Rules", cwd)
    (tmp_path / "doc.md").write_text(md.replace("text", "changed elsewhere"))
    assert subject_id("doc.md::Rules", cwd) == before != subject_id("doc.md::Other", cwd)
    (tmp_path / "doc.md").write_text(md.replace("- one", "- two"))
    assert subject_id("doc.md::Rules", cwd) != before

    (tmp_path / "c.json").write_text('{"a": {"x": [1, 2]}, "b": 3}')
    v = subject_id("c.json::a.x", cwd)
    (tmp_path / "c.json").write_text('{"b": 4,   "a": {"x": [1, 2]}}')            # other key, order, spacing
    assert subject_id("c.json::a.x", cwd) == v and locate("c.json::a.x.1", cwd) == b"2"

    py = "LIMIT = 3\n\nclass K:\n    def f(self, n):\n        return n + LIMIT\n\ndef g():\n    return 1\n"
    (tmp_path / "m.py").write_text(py)
    f, lim = subject_id("m.py::K.f", cwd), subject_id("m.py::LIMIT", cwd)
    (tmp_path / "m.py").write_text(py.replace("return 1", "return 2").replace("LIMIT = 3", "LIMIT = 4"))
    assert subject_id("m.py::K.f", cwd) == f and subject_id("m.py::LIMIT", cwd) != lim

    (tmp_path / "blob.bin").write_bytes(b"\x00\xff\x10")                         # any file at all
    assert subject_id("blob.bin", cwd).startswith("blob.bin@") and subject_id("blob.bin::x", cwd).startswith("blob.bin::x@")
    assert subject_id("doc.md::No such heading", cwd) == "doc.md::No such heading@" + subject_id("doc.md", cwd).split("@")[1]
    assert subject_id("missing.txt::a", cwd) == "missing.txt::a"


def test_a_place_is_read_by_a_description_not_by_code():
    from pwt.kernel import _read_pattern, pattern
    text = 'def __init__(self, max_atoms=14, dependence="pqd"):\nALLOWED = {"propext", "Quot.sound", "propext", "Classical.choice"}\nthreshold 0.9 and -3\n'
    assert _read_pattern(pattern(find=r'dependence="(\w+)"'), text) == '"pqd"'
    assert _read_pattern(pattern(find=r"max_atoms=(\d+)", kind="nat"), text) == "14"
    assert _read_pattern(pattern(find=r"threshold ([0-9.]+)", kind="permille"), text) == "900"
    assert _read_pattern(pattern(find=r"and (-?\d+)", kind="int"), text) == "(-3)"
    names = r'"([^"]+)"'
    part = text.splitlines()[1]
    assert _read_pattern(pattern(find_all=names), part) == '["propext", "Quot.sound", "propext", "Classical.choice"]'
    assert _read_pattern(pattern(find_all=names, sort=True, unique=True), part) == '["Classical.choice", "Quot.sound", "propext"]'
    assert _read_pattern(pattern(find_all=r"(\d+)", kind="nat", sort=True), "9 10 2") == "[2, 9, 10]"       # by size, not as text
    with pytest.raises(KernelError):                 # nothing found is not "an empty list": the pattern may no longer fit the text
        _read_pattern(pattern(find_all=r"zzz(\d)", kind="nat"), text)
    assert _read_pattern(pattern(find=r"^ALLOWED = (.)"), text) == '"{"'                                    # ^ is a line start
    for found, why in ((r'"(\w+)"', "matches 3 times"), (r"nothing (here)", "matches 0 times")):
        with pytest.raises(KernelError, match=why):
            _read_pattern(pattern(find=found), text)
    with pytest.raises(KernelError):
        _read_pattern(pattern(find=r"threshold ([0-9.]+)", kind="nat"), text)                               # 0.9 is not a natural number
    with pytest.raises(KernelError):
        _read_pattern(pattern(find=r"(0\.[0-9]+)", kind="permille"), "0.9005")                              # not a whole number of thousandths
    for bad in (dict(find="no group"), dict(find="(a)(b)"), dict(find="(a)", find_all="(b)"), dict(), dict(find="(a)", kind="float"),
                dict(find=r"(?<=x)(a)"), dict(find=r"(a)\1"), dict(find=r"(?P<n>a)"), dict(find="(a")):
        with pytest.raises(KernelError):
            pattern(**bad)


def test_a_measured_rate_is_held_by_its_bounds():
    """(How the planted changes are made, and the decoys: rust/src/calibrate.rs, cargo test.)"""
    from pwt.kernel import interval
    lo, hi = interval(30, 30)
    assert 0.88 < lo < 0.89 and hi == 1.0                                           # thirty out of thirty: at least 0.88
    lo, hi = interval(0, 30)
    assert lo == 0.0 and 0.11 < hi < 0.12


def test_a_pattern_reads_the_same_whatever_the_line_ends():
    from pwt.kernel import _read_pattern, pattern
    text = '@tool()\ndef read(x):\n    pass\n\n@tool()\ndef decline(x):\n    pass\n'
    rd = pattern(find_all=r"@tool\(\)\ndef (\w+)\(", sort=True)
    assert _read_pattern(rd, text) == _read_pattern(rd, text.replace("\n", "\r\n")) == '["decline", "read"]'


def test_a_reader_states_a_value_not_a_computation(tmp_path):
    """What a reader says a place states goes into a Lean file. For the types a value is written
    out in (numbers, strings, lists of them) nothing but a written-out value is taken."""
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 15 atoms.\n")
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    cwd = str(tmp_path)
    k = Kernel(str(tmp_path / "pw-log.jsonl"), actor="reader")

    def says(typ, value):
        h = k.claim_fact(f"thing {typ}", typ, ["doc.md::Limits"])["h"]
        return k.read_place(h, "doc.md::Limits", value, cwd=cwd, quote="At most 15 atoms.")["read as"]

    assert says("Nat", "15") == "15" and says("Int", "-3") == "-3" and says("Int", "(-3)") == "(-3)"
    assert says("String", '"fast"') == '"fast"' and says("List String", '["a", "b"]') == '["a", "b"]' and says("List Nat", "[]") == "[]"
    for typ, value in [("Nat", "15 - 1"), ("Nat", "Nat.pred 15"), ("Nat", "by exact 14"), ("Nat", "14 /- x -/"), ("Nat", "-1"), ("Nat", "14.0"),
                       ("Nat", "true"), ("Nat", '"14"'), ("String", '"fa" ++ "st"'), ("String", "fast"), ("List String", '["a" ++ "b"]'),
                       ("List String", '"a"'), ("List Nat", '[1, "2"]'), ("Int", "(-3) + 1")]:
        with pytest.raises(KernelError):
            says(typ, value)


def test_a_place_can_be_read_by_its_structure():
    """By the syntax of Python or a path into TOML or JSON: spelling does not matter, an entry
    added in another style is seen, and what is not written out as a literal is not guessed."""
    from pwt.kernel import compute, reader
    py = lambda read, text: compute(reader(read, "m.py"), text)
    assert py({"python": "value"}, 'MODE = "fast"') == py({"python": "value"}, "MODE='fast'  # x") == '"fast"'
    assert py({"python": "value", "as": "nat"}, "LIMIT: int = 14") == "14"
    assert py({"python": "strings", "sort": True}, 'A = frozenset({"b",\n  \'a\'})') == '["a", "b"]'
    assert py({"python": "keys", "sort": True}, 'D = {"b": 1,\n     \'a\':2, "c" : 3}') == '["a", "b", "c"]'
    src = "@mcp.tool()\ndef read(x): pass\n\n\n@mcp.tool()\nasync def decline(x): pass\n\ndef _helper(): pass\ndef other(): pass\n"
    assert py({"python": "names", "decorator": "mcp.tool", "sort": True}, src) == '["decline", "read"]'
    assert py({"python": "names", "public": True, "sort": True}, src) == '["decline", "other", "read"]'
    assert py({"python": "names", "public": True}, "class C:\n    def a(self): pass\n    def _b(self): pass\n") == '["a"]'
    call = {"python": "keyword", "call": "add_argument", "with": "--model", "keyword": "default"}
    assert py(call, 'ap.add_argument("--n", default=3)\nap.add_argument(\n  "--model",\n  default = \'opus\')') == '"opus"'
    for read, text in [({"python": "value"}, "MODE = DEFAULT"), ({"python": "value"}, 'A = 1\nB = 2'), (call, 'ap.add_argument("--model", default=M)'),
                       (call, 'ap.add_argument("--model")'), ({"python": "strings"}, "A = frozenset()"), ({"python": "keys"}, "D = dict(a=1)"),
                       ({"python": "value"}, "def f(:")]:
        with pytest.raises(KernelError):
            py(read, text)

    toml = '[package]\nname = "x"\nversion = "0.1.0"\n\n[[tasks]]\nname = "a"\ncommand = "c"\n\n[[tasks]]\nname = "b"\nargs = []\n'
    data = lambda read, text, at="f.toml": compute(reader(read, at), text)
    assert data({"data": "package.version"}, toml) == '"0.1.0"'
    assert data({"data": "tasks.*", "keys": True, "sort": True, "unique": True}, toml) == '["args", "command", "name"]'
    assert data({"data": "tasks[name=b].name"}, toml) == '"b"' and data({"data": "tasks.*.name"}, toml) == '["a", "b"]'
    js = '{"bar": {"read at least": 0.85}, "rules": [["a", "b"], ["b"]]}'
    assert data({"data": "bar.read at least", "as": "permille"}, js, "r.json") == "850"
    assert data({"data": "rules.*", "sort": True, "unique": True}, js, "r.json") == '["a", "b"]'
    for read, text in [({"data": "package.license"}, toml), ({"data": "tasks.name"}, toml), ({"data": "package", "keys": True}, "x = ["), ({"data": "package.version", "as": "nat"}, toml)]:
        with pytest.raises(KernelError):
            data(read, text)
    for read, at in [({"data": "a.b"}, "f.ini"), ({"python": "value"}, "f.toml"), ({"data": "a"}, "f.json::a"), ({"python": "nope"}, "f.py"),
                     ({"python": "value", "find": "x"}, "f.py"), ({"data": "a..b"}, "f.toml"), ({"python": "value", "public": True}, "f.py")]:
        with pytest.raises(KernelError):
            reader(read, at)


def test_what_differs_between_lists_is_named(tmp_path):
    """Where lists do not agree, the check names the entries that are not everywhere, and where they are."""
    import json
    from pwt import check
    read = {"find_all": '"(\\w+)"', "sort": True}
    files = {"README.md": '"a" "b" "z"', "m.py": '"a" "b" "c" "z"', "all.py": '"a" "b" "c" "z"', "start.md": '"a"'}
    for name, text in files.items():
        (tmp_path / name).write_text(text + "\n")
    def output(fact, capsys_text=None):
        (tmp_path / "pw-facts.json").write_text(json.dumps([fact]))
        import io
        import contextlib
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            check.run(str(tmp_path), str(tmp_path / "pw-log.jsonl"), unconfirmed="warn")
        return out.getvalue()
    places = [{"at": n, "read": read} for n in ("README.md", "m.py", "all.py")] + [{"at": "start.md", "read": read, "some": True}]
    assert "       only in all.py, m.py: c\n" in output({"name": "modes", "type": "List String", "places": places})
    laid = {"name": "modes", "type": "List String", "places": places[:2], "instructions": [{"is": ["a", "b", "c", "z"], "by": "ann"}]}
    (tmp_path / "README.md").write_text('"a" "x" "c" "z"\n')
    got = output(laid)
    assert "README.md has, beyond what was laid down: x" in got and "README.md lacks, of what was laid down: b" in got, got


def test_the_documents_are_there_and_point_at_things_that_exist():
    """The files a reader is sent to are not empty, and what they link to is in the repository."""
    import os
    import re
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for name in ("README.md", "CHANGES.md", "docs/spec.md", "experiments/README.md"):
        path = os.path.join(root, name)
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        assert len(text) > 200, f"{name} is all but empty"
        for target in re.findall(r"\]\(([^)#\s]+)(?:#[^)]*)?\)", text):
            if "://" not in target:
                there = os.path.join(os.path.dirname(path), target)
                assert os.path.exists(there) and (os.path.isdir(there) or os.path.getsize(there) > 0), f"{name} links to {target}, which is not there"


def test_the_action_has_its_parts():
    """action.yml is read by GitHub, not by anything here: a slip in it shows only in another
    repository's CI. Its top level has to be these keys, and its steps the ones the README names."""
    import os
    import re
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    with open(os.path.join(root, "action.yml"), encoding="utf-8") as fh:
        text = fh.read()
    assert re.findall(r"^([a-z]+):", text, re.M) == ["name", "description", "inputs", "runs"]
    assert re.findall(r"^  ([a-z]+):", text.split("\ninputs:", 1)[1].split("\nruns:", 1)[0], re.M) == ["repo", "args", "build"]
    runs = text.split("\nruns:", 1)[1]
    assert "\n  using: composite\n  steps:\n" in runs and len(re.findall(r"^    - name: ", runs, re.M)) == 3
    assert "ci/pw.sh" in runs and '"$PW_BIN" check' in runs


def test_a_declaration_that_cannot_be_used_is_said_in_a_line(tmp_path):
    import json
    k = Kernel(str(tmp_path / "pw-log.jsonl"))
    path = tmp_path / "pw-facts.json"
    with pytest.raises(KernelError, match="there is no pw-facts.json"):
        k.sync_facts(str(path))
    for text, said in [("[{", "is not JSON"), ('{"name": "x"}', "is a list of facts"), ('[{"type": "Nat", "places": ["a"]}]', 'object with a "name"'),
                       ('[{"name": "x", "places": ["a"]}]', 'needs a "type"'), ('[{"name": "x", "type": "Nat", "place": ["a"]}]', 'needs "places"'),
                       ('[{"name": "x", "type": "Nat", "places": ["a"], "glos": "y"}]', "unknown keys"),
                       (json.dumps([{"name": "x", "type": "Nat", "places": ["a"]}] * 2), "declared more than once")]:
        path.write_text(text)
        with pytest.raises(KernelError, match=said):
            k.sync_facts(str(path))
    path.write_text("[]")
    assert k.sync_facts(str(path)) == set()


def test_a_long_place_read_by_structure_is_shown_in_part():
    from pwt.kernel import excerpt, reader
    lock = "version = 4\n\n" + "".join(f'[[package]]\nname = "dep{i}"\nversion = "1.{i}.0"\ndependencies = [\n "a",\n]\n\n' for i in range(40))
    lock += '[[package]]\nname = "mine"\nversion = "0.1.0"\n'
    shown = excerpt(reader({"data": "package[name=mine].version"}, "Cargo.lock"), lock)
    assert shown == '[[package]]\nname = "mine"\nversion = "0.1.0"\n' and shown in lock
    assert excerpt(reader({"data": "package[name=mine].version"}, "Cargo.lock"), shown) is None          # short: shown whole
    assert excerpt(reader({"data": "package.*.version"}, "Cargo.lock"), lock) is None                    # needs every table: nothing to leave out
    src = "import os\n\n" + "".join(f"@route('/{i}')\ndef page{i}(request,\n          flag=False):\n    return {i} * [\n        os.sep,\n        os.linesep,\n        os.pathsep,\n        os.curdir,\n    ]\n\n\n" for i in range(30))
    shown = excerpt(reader({"python": "names"}, "app.py"), src)
    assert shown.startswith("@route('/0')\ndef page0(request,\n          flag=False):\n@route('/1')") and "return" not in shown
    assert excerpt(reader({"python": "value"}, "app.py"), "X = " + repr(list(range(900)))) is None        # no smaller part can be told
    assert excerpt({"language": "pattern", "find": "(x)", "as": "string"}, "x" * 5000) is None


def test_the_published_executable_is_named_for_its_source():
    """rust/release.txt names one executable by version, source digest, place and SHA-256; ci/pw.sh
    computes the digest the same way the release did (it is the release's own definition)."""
    import os
    import re
    import subprocess
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    with open(os.path.join(root, "rust", "release.txt"), encoding="utf-8") as fh:
        said = dict(line.split("=", 1) for line in fh.read().split("\n") if line)
    assert set(said) == {"version", "source", "url", "sha256"}
    assert re.fullmatch(r"[0-9a-f]{64}", said["source"]) and re.fullmatch(r"[0-9a-f]{64}", said["sha256"])
    assert said["url"] == f"https://github.com/sugipamo/parallelworld/releases/download/v{said['version']}/pw-{said['version']}-linux-x86_64"
    digest = subprocess.run([os.path.join(root, "ci", "pw.sh"), "--source-digest"], capture_output=True, text=True, check=True).stdout.strip()
    assert re.fullmatch(r"[0-9a-f]{64}", digest)          # (equal to said["source"] only while the source is what was released)
