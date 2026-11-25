import pytest

from pw.kernel import Kernel, KernelError
from pw.lean_gate import GateError, LeanGate


class FakeGate(LeanGate):
    """Accepts every proof. Stands in for Lean so kernel semantics can be tested alone."""
    def check(self, relation, items, proof):
        self.render(relation, items, proof)
        return {"ok": True, "axioms": [], "gamma": "fake"}

    def typecheck(self, items):
        return {"ok": True, "reason": ""}


@pytest.fixture
def k(tmp_path):
    return Kernel(str(tmp_path / "e.db"), gate=FakeGate())


def test_gate_is_the_only_way_in(tmp_path):
    """Without Lean nothing is accepted as agreeing or differing; and only what Lean settled is recorded."""
    (tmp_path / "a.txt").write_text("v = 1\n")
    (tmp_path / "b.txt").write_text("v = 1\n")
    from pw.kernel import pattern
    places = [{"at": name, "reader": pattern(find=r"v = (\d+)", kind="nat")} for name in ("a.txt", "b.txt")]
    k = Kernel(str(tmp_path / "e.db"))
    k.claim_fact("v", "Nat", places)
    with pytest.raises(KernelError):
        k.recheck(str(tmp_path))                                  # no gate: the equation cannot be settled
    k = Kernel(str(tmp_path / "e.db"), gate=FakeGate())
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
    from pw.kernel import locate, subject_id
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
    from pw.kernel import _read_pattern, pattern
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


def test_planted_changes_have_known_answers():
    import random
    from pw.calibrate import interval, mutants, same
    rng = random.Random(0)
    text = "## Model\n\nThe default class is `pqd`; `pqd` is positive dependence. Not `pqdx`.\nAt most 14 atoms, range 0-15, 114 in total.\n"
    made = mutants(text, "pqd", rng, 3)
    assert len(made) == 3 and all(k == "value replaced" for k, _, _ in made)
    for _, changed, planted in made:
        assert planted != "pqd" and changed.count(f"`{planted}`") == 2 and "`pqdx`" in changed and "`pqd`" not in changed
    (_, changed, planted), = mutants(text, 14, rng, 1)
    assert planted != 14 and f"At most {planted} atoms" in changed and "114 in total" in changed and "0-15" in changed
    assert mutants(text, "frechet", rng, 3) == []                                   # not in the words: cannot be planted

    table = "| `claim(text)` | registers |\n| `prove(r)` | proves |\n| `claim_formal` | other |\n| `status()` | shows |\n"
    made = mutants(table, ["claim", "prove", "status"], random.Random(1), 3)
    assert {k for k, _, _ in made} == {"entry renamed", "row removed"}
    for kind, changed, planted in made:
        assert len(planted) == (2 if kind == "row removed" else 3) and "claim_formal" in changed
        for e in planted:
            assert f"`{e}" in changed                                               # every planted entry is in the changed text
    (_, changed, planted), = mutants("`blind` and `read blind` and `computed`", ["blind", "computed", "read blind"], random.Random(3), 1)
    assert all(f"`{e}`" in changed for e in planted) and len(planted) == 3          # an entry inside another entry changes with it
    assert same(["b", "a"], ["a", "b"]) and not same(["a"], ["a", "b"]) and same(14, 14) and not same("14", 14)
    lo, hi = interval(30, 30)
    assert 0.88 < lo < 0.89 and hi == 1.0                                           # thirty out of thirty: at least 0.88
    lo, hi = interval(0, 30)
    assert lo == 0.0 and 0.11 < hi < 0.12


def test_a_proposed_place_is_checked_against_the_file(tmp_path):
    import json
    from pw.discover import Refused, _agree, merge, screen
    repo = str(tmp_path)
    (tmp_path / "guide.md").write_text("# Guide\n\n## Limits\n\nAt most 14 atoms are solved. The class is `fast`.\n\n## Other\n\nNothing.\n")
    (tmp_path / "app.py").write_text('LIMIT = 14\n\ndef run(threshold=0.9, mode="fast"):\n    return threshold\n\nNAMES = ["b", "a"]\n')
    (tmp_path / "pw-log.jsonl").write_text("{}\n")

    def refused(*a, **kw):
        with pytest.raises(Refused) as e:
            screen(repo, *a, **kw)
        return str(e.value)

    p = screen(repo, "Nat", "guide.md::Limits", 14, "At most 14 atoms are solved.")
    assert p == {"at": "guide.md::Limits", "read": None, "value": 14, "quote": "At most 14 atoms are solved."}
    assert screen(repo, "Nat", "guide.md::Limits", "14", "At most 14 atoms are solved.")["value"] == 14      # JSON text is accepted too
    assert "word for word" in refused("Nat", "guide.md::Limits", 14, "At most 14 atoms can be solved.")
    assert "word for word" in refused("Nat", "guide.md::Other", 14, "At most 14 atoms are solved.")          # the quote is in another part
    assert "does not occur in the quote" in refused("Nat", "guide.md::Limits", 15, "At most 14 atoms are solved.")
    assert "no heading" in refused("Nat", "guide.md::Limit", 14, "At most 14 atoms are solved.")
    assert "no file" in refused("Nat", "missing.md", 14, "x")
    assert "not a value of type Nat" in refused("Nat", "guide.md::Limits", '"14"', "At most 14 atoms are solved.")
    for own in ("pw-log.jsonl", "../guide.md", ".git/config"):
        assert "not a file of the project" in refused("Nat", own, 14, "x")

    p = screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"LIMIT = (\d+)")
    assert p["read"] == {"find": r"LIMIT = (\d+)", "as": "nat"}
    p = screen(repo, "Nat", "app.py::run", 900, "def run(threshold=0.9", find=r"threshold=([0-9.]+)", kind="permille")
    assert p["read"]["as"] == "permille"                                             # a computed value need not be in the quote
    assert "needs a pattern" in refused("Nat", "app.py::run", 900, "def run(threshold=0.9")
    assert "not the value you gave" in refused("Nat", "app.py::LIMIT", 15, "LIMIT = 14", find=r"LIMIT = (\d+)")
    assert "does not work" in refused("Nat", "app.py", 14, "LIMIT = 14", find=r"(\d+)")                      # matches more than once
    assert "inline flags" in refused("Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"(?m)^LIMIT = (\d+)")   # not common to all engines
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
    assert "`within` matches 2 times" in refused("List String", "cli.py", ["json"], 'quote = Choice(["always", "never"])',
                                                 find_all=r'"(\w+)"', within=r"Choice\(\[([^\]]+)\]")
    assert "does not match '315t' as a whole" in refused("List String", "tox.ini", ["3.10"], "envlist = lint,py{310,311,315t},docs",
                                                        find_all=r"(\w+)(?:,|$)", within=r"py\{([^}]+)\}", rewrite=[r"(\d)(\d+)", r"\1.\2"])
    for bad in ([r"(\d)", r"\2"], [r"(\d)", r"\n"], [r"(?=x)(\d)", r"\1"]):
        assert "does not work" in refused("List String", "tox.ini", ["3.10"], "envlist = lint,py{310,311,315t},docs", find_all=r"(\d+),", rewrite=bad)
    assert screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"^(?:LIMIT) = (\d+)")["read"]         # (?: ) is fine
    p = screen(repo, "List String", "app.py::NAMES", ["a", "b"], 'NAMES = ["b", "a"]', find_all=r'"(\w)"')
    assert p["read"] == {"find_all": r'"(\w)"', "as": "string", "sort": True}
    (tmp_path / "notes.txt").write_text("14\n")
    assert "only Markdown, JSON and Python" in refused("Nat", "notes.txt::x", 14, "14")

    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits"]}]
    merged, added = merge(facts, [
        {"fact": "limit", "place": screen(repo, "Nat", "app.py::LIMIT", 14, "LIMIT = 14", find=r"LIMIT = (\d+)")},
        {"fact": "limit", "place": screen(repo, "Nat", "guide.md::Limits", 14, "At most 14 atoms are solved.")},     # already listed
        {"new": {"name": "class", "type": "String", "gloss": "the class"}, "places": [
            screen(repo, "String", "guide.md::Limits", "fast", "The class is `fast`."),
            screen(repo, "String", "app.py::run", "fast", 'mode="fast"', find=r'mode="(\w+)"')]}])
    assert facts[0]["places"] == ["guide.md::Limits"]                                # the input is left alone
    assert merged[0]["places"] == ["guide.md::Limits", {"at": "app.py::LIMIT", "read": {"find": r"LIMIT = (\d+)", "as": "nat"}}]
    assert merged[1] == {"name": "class", "type": "String", "gloss": "the class",
                         "places": ["guide.md::Limits", {"at": "app.py::run", "read": {"find": r'mode="(\w+)"', "as": "string"}}]}
    assert len(added) == 3 and _agree([p for _, p in added[1:]]) and not _agree([{"value": 1}, {"value": 2}])
    # a place that states only some entries of a list is declared as such
    part = {**screen(repo, "List String", "app.py::NAMES", ["a"], 'NAMES = ["b", "a"]'), "some": True}
    merged2, _ = merge([{"name": "names", "type": "List String", "places": ["guide.md::Limits"]}], [{"fact": "names", "place": part}])
    assert merged2[0]["places"] == ["guide.md::Limits", {"at": "app.py::NAMES", "some": True}]
    k = Kernel(str(tmp_path / "e.db"), gate=FakeGate())
    (tmp_path / "facts.json").write_text(json.dumps(merged))
    assert len(k.sync_facts(str(tmp_path / "facts.json"))) == 2                      # what is merged is a valid declaration


def test_a_search_that_failed_does_not_look_like_one_that_found_nothing(tmp_path, monkeypatch):
    import json
    from pw import discover
    (tmp_path / "guide.md").write_text("## Limits\n\nAt most 14 atoms are solved.\n")
    (tmp_path / "app.py").write_text("LIMIT = 14\n")
    (tmp_path / "other.py").write_text("LIMIT = 14\n")
    repo = str(tmp_path)
    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits", "app.py::LIMIT"]}]
    place = lambda at: {"fact": "limit", "place": {"at": at, "read": None, "value": 14, "quote": "LIMIT = 14"}}

    def agent(lines, result):
        """Stand in for the agent: what its tools wrote, and how the session ended."""
        def run(cmd, **kw):
            with open(cmd[cmd.index("--mcp-config") + 1]) as fh:
                env = json.load(fh)["mcpServers"]["find"]["env"]
            with open(env["PW_DISCOVER_OUT"], "w") as fh:
                fh.writelines(json.dumps(x) + "\n" for x in lines)
            return type("R", (), {"stdout": json.dumps(result) if result is not None else "boom", "stderr": ""})()
        monkeypatch.setattr(discover.subprocess, "run", run)

    ok = {"num_turns": 3, "total_cost_usd": 0.1, "result": "found nothing", "subtype": "success", "is_error": False}
    agent([], ok)                                                    # the tools never came up: the agent only talked
    proposals, run = discover.further(repo, "m", facts, 1.0)
    assert proposals == [] and "never started" in run["problems"][0] and "did not say it finished" in run["problems"][1]
    agent([{"started": True}], ok)                                   # tools up, but the agent never said it was done
    assert discover.further(repo, "m", facts, 1.0)[1]["problems"] == ["the agent did not say it finished searching for: limit"]
    agent([{"started": True}, {"finished": "limit"}], {**ok, "subtype": "error_max_budget_usd", "is_error": True})
    assert discover.further(repo, "m", facts, 1.0)[1]["problems"] == ["the session ended with error_max_budget_usd"]
    agent([{"started": True}, {"finished": "limit"}], None)
    assert "gave no result" in discover.further(repo, "m", facts, 1.0)[1]["problems"][0]
    agent([{"started": True}, {"finished": ""}], ok)
    assert discover.new(repo, "m", facts, 1.0)[1]["problems"] == []
    agent([{"started": True}, {"finished": "limit"}], ok)            # only now does nothing mean nothing
    proposals, run = discover.further(repo, "m", facts, 1.0)
    assert proposals == [] and run["problems"] == [] and run["controls"] == {}

    # a known place left out as a control: coming back with it shows the search works, and is not a proposal
    agent([{"started": True}, place("app.py"), place("other.py::LIMIT"), {"finished": "limit"}], ok)
    proposals, run = discover.further(repo, "m", facts, 1.0, hide={"limit": "app.py::LIMIT"})
    assert [p["place"]["at"] for p in proposals] == ["other.py::LIMIT"] and run["controls"] == {"limit": {"at": "app.py::LIMIT", "found": True}}
    agent([{"started": True}, place("other.py::LIMIT"), {"finished": "limit"}], ok)
    assert discover.further(repo, "m", facts, 1.0, hide={"limit": "app.py::LIMIT"})[1]["controls"]["limit"]["found"] is False


def test_a_declared_place_that_cannot_be_read_is_said_and_can_be_repaired(tmp_path, monkeypatch):
    import json
    from pw import discover
    from pw.kernel import unreadable
    (tmp_path / "guide.md").write_text("## Limits\n\nAt most 14 atoms are solved.\n")
    (tmp_path / "app.py").write_text("LIMIT = 14\n")
    repo = str(tmp_path)
    facts = [{"name": "limit", "type": "Nat", "places": ["guide.md::Limits", {"at": "app.py::LIMIT", "read": {"find": "LIMIT = (\\d+)", "as": "nat"}}]}]
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=FakeGate())
    h, = k.sync_facts(str(tmp_path / "pw-facts.json"))
    k.read_place(h, "guide.md::Limits", "14", cwd=repo, quote="At most 14 atoms are solved.")
    assert k.recheck(repo)["decisions"][0]["state"] == "current" and unreadable("guide.md::Limits", repo) is None

    # the heading is renamed, the constant is renamed: neither place is where it was declared
    (tmp_path / "guide.md").write_text("## Bounds\n\nAt most 14 atoms are solved.\n")
    (tmp_path / "app.py").write_text("MAX_ATOMS = 14\n")
    r = k.recheck(repo)["decisions"][0]
    assert r["state"] == "stale" and [(u["at"], u["broken"]) for u in r["unread"]] == [("guide.md::Limits", True), ("app.py::LIMIT", True)]
    assert "no longer has a part named 'Limits'" in r["unread"][0]["why"]            # not quietly read off the whole file instead
    from pw.lean_gate import LEAN_DIR
    broken = discover.broken_places(repo, LEAN_DIR, facts)                           # (nothing is put to Lean while a place is unread)
    assert [(n, at) for n, at, _ in broken] == [("limit", "guide.md::Limits"), ("limit", "app.py::LIMIT")]

    # what the agent would report, and what becomes of the declaration
    proposals = [
        {"replace": {"fact": "limit", "old": "guide.md::Limits"},
         "place": {**discover.screen(repo, "Nat", "guide.md::Bounds", 14, "At most 14 atoms are solved."), "some": False}},
        {"replace": {"fact": "limit", "old": "app.py::LIMIT"},
         "place": {**discover.screen(repo, "Nat", "app.py::MAX_ATOMS", 14, "MAX_ATOMS = 14", find=r"MAX_ATOMS = (\d+)"), "some": False}},
        {"gone": {"fact": "limit", "old": "guide.md::Limits", "why": "x"}}]
    merged, added = discover.merge(facts, proposals)
    assert merged[0]["places"] == ["guide.md::Bounds", {"at": "app.py::MAX_ATOMS", "read": {"find": r"MAX_ATOMS = (\d+)", "as": "nat"}}]
    assert [at["at"] for _, at in added] == ["guide.md::Bounds", "app.py::MAX_ATOMS"] and facts[0]["places"][0] == "guide.md::Limits"
    (tmp_path / "pw-facts.json").write_text(json.dumps(merged))
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    r = k.recheck(repo)["decisions"][0]
    assert r["state"] == "stale" and [(u["at"], u.get("broken")) for u in r["unread"]] == [("guide.md::Bounds", None)]   # found again; to be read

    # the agent is told which places cannot be read, and only about the facts concerned
    seen = {}
    def run(cmd, **kw):
        seen["prompt"] = cmd[cmd.index("-p") + 1]
        with open(cmd[cmd.index("--mcp-config") + 1]) as fh:
            env = json.load(fh)["mcpServers"]["find"]["env"]
        with open(env["PW_DISCOVER_OUT"], "w") as fh:
            fh.writelines(json.dumps(x) + "\n" for x in [{"started": True}, proposals[0], {"finished": "limit"}])
        return type("R", (), {"stdout": json.dumps({"num_turns": 1, "total_cost_usd": 0, "result": "", "subtype": "success"}), "stderr": ""})()
    monkeypatch.setattr(discover.subprocess, "run", run)
    other = {"name": "other", "type": "Nat", "places": ["guide.md::Bounds"]}
    got, info = discover.repair(repo, "m", facts + [other], broken, 1.0)
    assert got == [proposals[0]] and info["problems"] == []
    assert "CANNOT BE READ: guide.md no longer has a part named 'Limits'" in seen["prompt"] and '"other"' not in seen["prompt"]


def test_a_pattern_reads_the_same_whatever_the_line_ends():
    from pw.kernel import _read_pattern, pattern
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
