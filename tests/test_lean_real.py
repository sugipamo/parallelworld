"""Runs the real Lean kernel. Skipped when Lean is not installed."""
import os
import shutil
import subprocess

import pytest

from pwt.core import Kernel
from pwt.kernel import KernelError
from pwt.core import LeanGate

LAKE = os.environ.get("PW_LAKE") or shutil.which("lake")
pytestmark = pytest.mark.skipif(not LAKE, reason="Lean not installed (set PW_LAKE)")

@pytest.fixture(autouse=True)
def every_comparison_by_lean(monkeypatch):
    """These tests are about what Lean is asked and what is done with its answers: here every
    comparison is put to it. (By default only what has to be worked out is; tests/test_plain.py.)"""
    monkeypatch.setattr(Kernel, "compare", "always")


COMM = "∀ a b : Nat, a + b = b + a"
P = lambda *texts: [("Prop", t) for t in texts]


@pytest.fixture(scope="module")
def gate():
    return LeanGate()


def test_accepts_valid_proofs(gate):
    v = gate.check("holds", P(COMM), "intro a b\nexact Nat.add_comm a b")
    assert v["ok"] and v["axioms"] == [], v
    assert gate.check("not", P("(1 : Nat) < 1"), "decide")["ok"]
    assert gate.check("holds", P('(("a" : String) = ("a" : String)) ∧ (("a" : String) = ("a" : String))'), "decide")["ok"]
    assert gate.check("not", P('((["a", "b"] : List String) = (["a"] : List String))'), "decide")["ok"]


def test_classical_axioms_are_reported_and_allowed(gate):
    v = gate.check("holds", P("∀ p : Prop, p ∨ ¬p"), "intro p\nexact Classical.em p")
    assert v["ok"] and "Classical.choice" in v["axioms"], v


def test_rejects_wrong_and_incomplete_proofs(gate):
    assert not gate.check("holds", P("∀ a b : Nat, a + b = a"), "intro a b\nrfl")["ok"]
    assert not gate.check("holds", P(COMM), "intro a b")["ok"]            # unsolved goal
    assert not gate.check("not", P("(1 : Nat) = 1"), "decide")["ok"]
    assert not gate.check("holds", P("this is not lean"), "trivial")["ok"]


@pytest.mark.parametrize("proof", [
    "exact sorryAx _",                                    # sorry without the keyword
    "exact sorryAx _ false",
    "exact (Lean.ofReduceBool true true rfl ▸ trivial)",  # native axiom
    "exact Lean.trustCompiler ▸ trivial",
])
def test_rejects_unapproved_axioms(gate, proof):
    assert not gate.check("holds", P("(1 : Nat) = 2"), proof)["ok"]


def test_forged_axiom_report_is_not_believed(gate):
    forged = "trace \"'pw_goal' does not depend on any axioms\"\nexact sorryAx _"
    v = gate.check("holds", P("(1 : Nat) = 2"), forged)
    assert not v["ok"] and "sorryAx" in v["reason"], v


def test_a_statement_settled_by_unfolding_alone_is_accepted(gate):
    """An equation between two equal literals leaves nothing for the caller's tactics to do."""
    v = gate.check("holds", [("Prop", '(fun l => l = ["declare_independent", "prove"]) ["declare_independent", "prove"]')], "rfl")
    assert v["ok"], v
    assert gate.check("holds", [("Prop", "(fun n => n = 14) 14")], "decide")["ok"]
    assert not gate.check("holds", [("Prop", "(fun n => n = 14) 16")], "rfl")["ok"]
    assert gate.check("not", [("Prop", "(fun n => n = 14) 16")], "decide")["ok"]
    assert not gate.check("holds", [("Prop", "(1 : Nat) = 2")], "exact sorryAx _")["ok"]


def test_a_fact_stated_in_several_places(tmp_path):
    """No place is the truth: the decision is that they all say the same thing."""
    from pwt.kernel import pattern
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    repo = tmp_path / "repo"
    repo.mkdir()
    doc = "# Spec\n\n## Model\n\nThe default class is `{a}`.\n\n## Changes\n\n| 9 | classes | `{b}` (default) |\n"
    code = 'class K:\n    def __init__(self, dependence="{c}"):\n        self.d = dependence\n'
    def write(a, b, c):
        (repo / "doc.md").write_text(doc.format(a=a, b=b))
        (repo / "k.py").write_text(code.format(c=c))
    git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a], cwd=repo, check=True, capture_output=True)
    write("pqd", "pqd", "pqd"); git("init", "-q"); git("add", "-A"); git("commit", "-qm", "v1")
    cwd = str(repo)
    places = ["doc.md::Model", "doc.md::Changes",
              {"at": "k.py::K.__init__", "reader": pattern(find=r'dependence="(\w+)"')}]
    h = k.claim_fact("default dependence class", "String", places)["h"]
    assert k.claim_fact("default dependence class", "String", places)["h"] == h

    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and [u["at"] for u in r["unread"]] == ["doc.md::Model", "doc.md::Changes"], r
    assert len(r["places"]) == 1 and {k: r["places"][0][k] for k in ("at", "reads as", "by", "stands", "has")} == {
        "at": "k.py::K.__init__", "reads as": '"pqd"', "by": "reader", "stands": False, "has": {"read the same blind": False}}
    with pytest.raises(KernelError):
        k.read_place(h, "doc.md::Model", "14", cwd=cwd)                     # not a value of the fact's type
    with pytest.raises(KernelError):
        k.read_place(h, "doc.md::Elsewhere", '"pqd"', cwd=cwd)              # not one of its places
    with pytest.raises(KernelError):
        k.read_place(h, "doc.md::Model", '"pqd"', cwd=cwd, quote="The default is pqd.")     # not what is written there
    a = k.read_place(h, "doc.md::Model", '"pqd"', cwd=cwd, quote="The default class is `pqd`.")
    b = k.read_place(h, "doc.md::Changes", '"pqd"', cwd=cwd)
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "current" and [p["stands"] for p in r["places"]] == [False, False, False], r  # they agree; nothing stands yet
    k.sign_off(a["m"], "reviewer"); k.sign_off(b["m"], "reviewer")
    assert all(p["stands"] for p in k.recheck(cwd)["decisions"][0]["places"] if p["by"] == "stated")   # now on a person's word

    # an edit elsewhere in the quoted place leaves its reading alone; the unquoted one must be read again
    (repo / "doc.md").write_text(doc.format(a="pqd", b="pqd").replace("## Changes\n", "## Changes\n\nA note.\n")
                                 .replace("The default class", "Some remarks first.\n\nThe default class"))
    git("commit", "-qam", "remarks")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and [u["at"] for u in r["unread"]] == ["doc.md::Changes"], r
    b = k.read_place(h, "doc.md::Changes", '"pqd"', cwd=cwd, quote="| 9 | classes | `pqd` (default) |")
    k.sign_off(b["m"], "reviewer")
    assert k.recheck(cwd)["decisions"][0]["state"] == "current"
    write("pqd", "pqd", "pqd"); git("commit", "-qam", "remarks removed")
    assert k.recheck(cwd)["decisions"][0]["state"] == "current"                              # both quotes are still there

    # one place changes its mind
    write("frechet", "pqd", "pqd"); git("commit", "-qam", "the model section now says frechet")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and [u["at"] for u in r["unread"]] == ["doc.md::Model"], r
    k.read_place(h, "doc.md::Model", '"frechet"', cwd=cwd)
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "violated", r
    assert {p["at"]: p["reads as"] for p in r["places"]} == {"doc.md::Model": '"frechet"', "doc.md::Changes": '"pqd"', "k.py::K.__init__": '"pqd"'}

    # everything follows: the fact changed, and no decision had to be rewritten
    write("frechet", "frechet", "frechet"); git("commit", "-qam", "the rest follows")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and [u["at"] for u in r["unread"]] == ["doc.md::Changes"], r     # the code was read mechanically
    k.read_place(h, "doc.md::Changes", '"frechet"', cwd=cwd)
    assert k.recheck(cwd)["decisions"][0]["state"] in ("current", "re-established")

    # the list of facts lives in a file; what is no longer declared no longer stands
    import json
    (repo / "pw-facts.json").write_text(json.dumps([{"name": "default name", "type": "String", "places": [
        {"at": "k.py", "read": {"find": 'dependence="(\\w+)"'}}]}]))
    k.sync_facts(str(repo / "pw-facts.json"))
    rep = k.recheck(cwd)["decisions"]
    assert [(d["fact"], d["state"]) for d in rep] == [("default name", "current")] and rep[0]["places"][0]["reads as"] == '"frechet"'
    (repo / "pw-facts.json").write_text(json.dumps([{"name": "x", "type": "Nat", "places": [{"at": "k.py", "reader": "str(len(data))"}]}]))
    with pytest.raises(KernelError):
        k.sync_facts(str(repo / "pw-facts.json"))                                  # no expressions in a list of facts


def test_a_list_is_read_off_the_whole_place(tmp_path):
    """One quoted row cannot stand for a list: if the table changes, it has to be read again."""
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    (tmp_path / "doc.md").write_text("## Tools\n\n| `a` | first |\n| `b` | second |\n")
    cwd = str(tmp_path)
    h = k.claim_fact("tool names", "List String", ["doc.md::Tools"])["h"]
    k.read_place(h, "doc.md::Tools", '["a", "b"]', cwd=cwd, quote="| `a` | first |")
    assert k.recheck(cwd)["decisions"][0]["state"] == "current"
    (tmp_path / "doc.md").write_text("## Tools\n\n| `a` | first |\n| `b` | second |\n| `c` | third |\n")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and r["unread"][0]["why"] == "it changed since it was read", r


def test_the_record_is_text_in_the_repository_and_is_not_believed_where_it_can_be_checked(tmp_path):
    import json
    from pwt.kernel import pattern
    log = tmp_path / "pw-log.jsonl"
    (tmp_path / "k.py").write_text('LIMIT = 14\n')
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    cwd = str(tmp_path)
    places = ["doc.md::Limits", {"at": "k.py::LIMIT", "reader": pattern(find=r"= (\d+)", kind="nat")}]
    k = Kernel(str(log), gate=LeanGate(), actor="agent")
    h = k.claim_fact("limit", "Nat", places)["h"]
    k.read_place(h, "doc.md::Limits", "14", cwd=cwd, quote="At most 14 atoms.")
    assert k.recheck(cwd)["decisions"][0]["state"] == "current" and k.verify() == []
    lines = log.read_text().splitlines()
    assert all(json.loads(l)["actor"] == "agent" and "ts" in json.loads(l) for l in lines)

    # someone else, somewhere else, with only the files and the record: the same answer
    other = Kernel(str(log), gate=LeanGate(), actor="ci")
    assert other.recheck(cwd)["decisions"][0]["state"] == "current"
    assert log.read_text().splitlines() == lines                                # ...and checking adds nothing to the record

    # two branches appended; merged by keeping both, some lines twice
    log.write_text("\n".join(lines + lines[-2:]) + "\n")
    assert Kernel(str(log), gate=LeanGate()).recheck(cwd)["decisions"][0]["state"] == "current"

    # a line claiming the reader read something else is ignored: the reader is run again
    forged = dict(json.loads(next(l for l in lines if '"binding": {' in l and '"type": "reading"' in l)))
    forged["obj"] = {"id": "O:forged", "type": "Nat", "text": "15"}
    forged["m"] = "M:forged"
    log.write_text("\n".join(lines + [json.dumps(forged)]) + "\n")
    r = Kernel(str(log), gate=LeanGate()).recheck(cwd)["decisions"][0]
    assert r["state"] == "current" and [p["reads as"] for p in r["places"]] == ["14", "14"], r

    # a line claiming a proof Lean never accepted is found out
    st = k.state()
    f = st.facts[h]["agreed"][-1][1]
    fake = {"ts": 0, "actor": "x", "type": "proof", "relation": "not", "args": [f], "proof": "decide", "proof_sha": "x", "axioms": [], "gamma": "x"}
    log.write_text("\n".join(lines + [json.dumps(fake)]) + "\n")
    assert Kernel(str(log), gate=LeanGate()).recheck(cwd)["decisions"][0]["state"] == "contested"   # not silently one or the other
    refused = Kernel(str(log), gate=LeanGate()).verify()
    assert [r["relation"] for r in refused] == ["not"], refused

    log.write_text("\n".join(lines) + "\nnot json\n")
    with pytest.raises(KernelError):
        Kernel(str(log), gate=LeanGate()).state()


def test_a_fact_keeps_its_readings_when_its_declaration_changes(tmp_path):
    """How a place is read, or which places are listed, can change without the fact becoming another one."""
    from pwt.kernel import pattern
    k = Kernel(str(tmp_path / "e.jsonl"), gate=LeanGate())
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    (tmp_path / "c.txt").write_text("limit: 14\n")
    cwd = str(tmp_path)
    h = k.claim_fact("limit", "Nat", ["doc.md::Limits", {"at": "k.py::LIMIT", "reader": pattern(find=r"LIMIT = (\d+)", kind="nat")}])["h"]
    m = k.read_place(h, "doc.md::Limits", "14", cwd=cwd, quote="At most 14 atoms.")["m"]
    k.sign_off(m, "reviewer")
    again = k.claim_fact("limit", "Nat", ["doc.md::Limits", {"at": "k.py::LIMIT", "reader": pattern(find=r"= (\d+)", kind="nat")},
                                          {"at": "c.txt", "reader": pattern(find=r"limit: (\d+)", kind="nat")}])["h"]
    assert again == h
    import json
    (tmp_path / "pw-rules.json").write_text(json.dumps({"a blind reader counts if measured": {},
                                                        "a reading stands if any of": [["computed"], ["confirmed by a person"]]}))
    r = k.recheck(cwd)["decisions"]
    assert len(r) == 1 and r[0]["state"] in ("current", "re-established") and len(r[0]["places"]) == 3, r
    assert [p for p in r[0]["places"] if p["at"] == "doc.md::Limits"][0]["m"] == m and all(p["stands"] for p in r[0]["places"])


def _measure(cwd, keep=False, instructions=None, **readers):
    """Write what pw calibrate would: for each model, how many of 27 planted changes it read
    (and, of 27 decoys, how many it declined). With keep, the runs are added to those there."""
    import json
    from pwt.kernel import INSTRUCTIONS
    path = os.path.join(cwd, "pw-calibration.json")
    runs = json.load(open(path)) if keep and os.path.exists(path) else []
    runs += [{"model": m, "instructions": instructions or INSTRUCTIONS, "planted": {"n": 27, "read": k, "stuck": 27 - k},
              "decoys": {"n": 27, "accepted": 27 - k}} for m, k in readers.items()]
    with open(path, "w") as fh:
        json.dump(runs, fh)


def test_a_reading_stands_by_the_rules_not_by_a_number(tmp_path):
    import json
    from pwt.kernel import pattern
    log = str(tmp_path / "pw-log.jsonl")
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    (tmp_path / "notes.md").write_text("## Size\n\nComponents have up to 14 atoms.\n")
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    cwd = str(tmp_path)
    a, b = Kernel(log, gate=LeanGate(), actor="reader-a"), Kernel(log, gate=LeanGate(), actor="reader-b")
    def place(h, at):
        return next(p for d in a.recheck(cwd)["decisions"] if d["h"] == h for p in d["places"] if p["at"] == at)
    quote = dict(cwd=cwd, quote="At most 14 atoms.")

    # a place the kernel computes says the same
    h = a.claim_fact("limit", "Nat", ["doc.md::Limits", {"at": "k.py::LIMIT", "reader": pattern(find=r"= (\d+)", kind="nat")}])["h"]
    a.read_place(h, "doc.md::Limits", "14", **quote)
    p = place(h, "k.py::LIMIT")
    assert not p["stands"] and p["has"] == {"read the same blind": False}             # computed, but is it about this at all?
    p = place(h, "doc.md::Limits")
    assert not p["stands"] and p["has"]["words occur in the place"] and p["has"]["agrees with a computed place"] and not p["has"]["blind"]
    a.read_place(h, "doc.md::Limits", "14", blind=True, model="opus", **quote)
    p = place(h, "doc.md::Limits")
    assert not p["stands"] and p["unmeasured readers"] == ["opus"]                    # blind, but nobody measured this reader here
    _measure(cwd, opus=20)
    assert not place(h, "doc.md::Limits")["stands"]                                   # measured, and not good enough
    _measure(cwd, opus=27)
    p = place(h, "doc.md::Limits")
    assert p["stands"] and p["why"] == "blind + words occur in the place + agrees with a computed place"

    # a computed place stands once a reader shown only that place reads off it what the pattern computes
    code = dict(cwd=cwd, quote="LIMIT = 14")
    a.decline(h, "k.py::LIMIT", "this is a line count, not a number of atoms", cwd, blind=True, model="opus")
    p = place(h, "k.py::LIMIT")
    assert not p["stands"] and p["declined"][0]["why"].startswith("this is a line count") and p["declined"][0]["model"] == "opus"
    a.read_place(h, "k.py::LIMIT", "15", blind=True, model="opus", cwd=cwd, quote="LIMIT = 14")
    p = place(h, "k.py::LIMIT")
    assert not p["stands"] and p["read blind as"] == ["15"] and p["reads as"] == "14"  # the reader and the pattern differ
    b.read_place(h, "k.py::LIMIT", "14", blind=True, model="haiku", **code)
    assert not place(h, "k.py::LIMIT")["stands"] and place(h, "k.py::LIMIT")["unmeasured readers"] == ["haiku"]
    b.read_place(h, "k.py::LIMIT", "14", blind=True, model="opus", **code)
    assert place(h, "k.py::LIMIT")["why"] == "computed + read the same blind"
    (tmp_path / "k.py").write_text("LIMIT = 14 + 0\n")
    p = place(h, "k.py::LIMIT")                                                       # the pattern was checked once; edits around it
    assert p["stands"] and p["declined"] == [] and p["read blind as"] == []           # do not call for a reader again
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    with open(os.path.join(cwd, "pw-calibration.json")) as fh:
        runs = json.load(fh)
    with open(os.path.join(cwd, "pw-calibration.json"), "w") as fh:
        json.dump([{k: v for k, v in r.items() if k != "decoys"} for r in runs], fh)
    assert not place(h, "k.py::LIMIT")["stands"]                                      # never tried on places about something else
    _measure(cwd, opus=27)
    assert place(h, "k.py::LIMIT")["stands"]

    # measuring again until a run comes out well does not help: the runs are added up
    _measure(cwd, opus=20)
    _measure(cwd, keep=True, opus=27)
    assert not place(h, "k.py::LIMIT")["stands"]                                      # 47 of 54 is still not enough
    _measure(cwd, keep=True, opus=27); _measure(cwd, keep=True, opus=27); _measure(cwd, keep=True, opus=27)
    assert place(h, "k.py::LIMIT")["stands"]                                          # 128 of 135: only more trials outweigh it
    # and what was measured under other instructions says nothing about the readers as they are instructed now
    _measure(cwd, instructions="another text", opus=27)
    assert not place(h, "k.py::LIMIT")["stands"]
    _measure(cwd, opus=27)

    # no computed place: one model is not enough, two are
    g = a.claim_fact("size", "Nat", ["notes.md::Size"])["h"]
    size = dict(cwd=cwd, quote="Components have up to 14 atoms.")
    a.read_place(g, "notes.md::Size", "14", blind=True, model="opus", **size)
    assert not place(g, "notes.md::Size")["stands"]
    b.read_place(g, "notes.md::Size", "14", blind=True, model="opus", **size)
    assert not place(g, "notes.md::Size")["stands"]                                   # a second reader of the same model
    b.read_place(g, "notes.md::Size", "14", blind=True, model="sonnet", **size)
    assert not place(g, "notes.md::Size")["stands"]                                   # the second model is not measured
    _measure(cwd, opus=27, sonnet=27)
    assert place(g, "notes.md::Size")["why"] == "blind + words occur in the place + read the same by a second model"

    # a person's word is a rule too; and the project can decide otherwise
    t = a.claim_fact("unit", "String", ["doc.md::Limits"])["h"]
    m = a.read_place(t, "doc.md::Limits", '"原子"', blind=True, model="opus", **quote)["m"]     # a translation: not in the words
    assert not place(t, "doc.md::Limits")["stands"]
    a.sign_off(m, "reviewer")
    assert place(t, "doc.md::Limits")["why"] == "confirmed by a person"
    (tmp_path / "pw-rules.json").write_text(json.dumps({"a blind reader counts if measured": {"read at least": 0.85, "stuck at most": 0.15},
                                                        "a reading stands if any of": [["computed"]]}))
    assert not place(t, "doc.md::Limits")["stands"] and not place(h, "doc.md::Limits")["stands"]
    (tmp_path / "pw-rules.json").write_text(json.dumps({"a blind reader counts if measured": {}, "a reading stands if any of": [["looks right"]]}))
    with pytest.raises(KernelError):
        a.recheck(cwd)


def test_readers_who_disagree_stop_the_fact(tmp_path):
    log = str(tmp_path / "pw-log.jsonl")
    (tmp_path / "notes.md").write_text("## Size\n\nComponents have up to 14 atoms, sixteen in tests.\n")
    cwd = str(tmp_path)
    a, b = Kernel(log, gate=LeanGate(), actor="reader-a"), Kernel(log, gate=LeanGate(), actor="reader-b")
    g = a.claim_fact("size", "Nat", ["notes.md::Size"])["h"]
    a.read_place(g, "notes.md::Size", "14", cwd=cwd, blind=True, model="opus")
    wrong = b.read_place(g, "notes.md::Size", "16", cwd=cwd, blind=True, model="sonnet")["m"]
    d = a.recheck(cwd)["decisions"][0]
    assert d["state"] == "disputed" and "reader-a" in d["unread"][0]["why"] and "reader-b" in d["unread"][0]["why"], d
    a.sign_off(wrong, "reviewer", confirmed=False)                                    # a person settles it
    assert a.recheck(cwd)["decisions"][0]["state"] == "current"


def test_a_reading_answers_the_question_as_it_was_asked(tmp_path):
    """When a fact's description changes, what was read before answered another question."""
    import json
    from pwt.kernel import pattern
    log = str(tmp_path / "pw-log.jsonl")
    (tmp_path / "doc.md").write_text("## Versions\n\nWe use Lean v4.9.0.\n")
    (tmp_path / "pin.txt").write_text("lean4:v4.9.0\n")
    cwd = str(tmp_path)
    _measure(cwd, opus=27)
    a = Kernel(log, gate=LeanGate(), actor="reader-a")
    places = ["doc.md::Versions", {"at": "pin.txt", "reader": pattern(find=r":v([0-9.]+)")}]
    declare = lambda gloss: a.claim_fact("Lean version", "String", places, gloss=gloss)["h"]
    fact = lambda: a.recheck(cwd)["decisions"][0]
    h = declare("the Lean version")
    lines = len(a.events())
    assert declare("the Lean version") == h and len(a.events()) == lines              # declaring it again records nothing
    assert a.recheck(cwd) and len(a.events()) == lines + 1                            # (the computed reading, once)
    a.recheck(cwd)
    assert len(a.events()) == lines + 1                                               # checking again records nothing either

    quote = dict(cwd=cwd, quote="We use Lean v4.9.0.")
    a.read_place(h, "doc.md::Versions", '"v4.9.0"', blind=True, model="opus", **quote)   # with the v: the description did not say
    a.decline(h, "pin.txt", "a toolchain line, not a version", cwd, blind=True, model="opus")
    r = fact()
    assert r["state"] == "violated" and r["places"][1]["declined"][0]["why"].startswith("a toolchain line")

    assert declare("the Lean version, as a bare number without a leading v") == h        # the same fact, asked more precisely
    r = fact()
    assert r["state"] == "stale" and "description changed" in r["unread"][0]["why"], r   # the old answer is to another question
    assert r["places"][0]["declined"] == []                                              # and so is the old refusal
    m = a.read_place(h, "doc.md::Versions", '"4.9.0"', blind=True, model="opus", **quote)["m"]
    a.read_place(h, "pin.txt", '"4.9.0"', blind=True, model="opus", cwd=cwd, quote="lean4:v4.9.0")
    r = fact()
    assert r["state"] in ("current", "re-established") and all(p["stands"] for p in r["places"]), r

    # a person's confirmation is an answer to the question as it was then, too
    (tmp_path / "pw-rules.json").write_text(json.dumps({"a blind reader counts if measured": {},
                                                        "a reading stands if any of": [["computed"], ["confirmed by a person"]]}))
    assert not fact()["places"][0]["stands"]
    a.sign_off(m, "reviewer")
    assert fact()["places"][0]["why"] == "confirmed by a person"
    declare("the version of Lean, as a bare number without a leading v")
    a.read_place(h, "doc.md::Versions", '"4.9.0"', **quote)                              # the same value, read again: the same reading
    assert not fact()["places"][0]["stands"]                                             # but nobody confirmed it for this question
    a.sign_off(m, "reviewer")
    assert fact()["places"][0]["stands"]

    # a record written before descriptions were tracked: the description in force then is the one that counts
    old = str(tmp_path / "old.jsonl")
    with open(log) as src, open(old, "w") as dst:
        for line in src:
            e = json.loads(line)
            e.pop("asked", None)
            e.get("fact", {}).pop("asked", None)
            dst.write(json.dumps(e, ensure_ascii=False) + "\n")
    b = Kernel(old, gate=LeanGate(), actor="reader-b")
    assert [p["stands"] for p in b.recheck(cwd)["decisions"][0]["places"]] == [True, True]


def test_a_place_that_writes_the_value_another_way_is_still_read_by_a_declaration(tmp_path):
    """A list scoped inside a place and rewritten into the other places' spelling; and a reading
    made before these keys existed is the same reading."""
    import json
    from pwt.kernel import pattern
    (tmp_path / "pyproject.toml").write_text('classifiers = ["Python :: 3.10", "Python :: 3.11"]\n')
    (tmp_path / "tox.ini").write_text("[tox]\nenvlist = lint,py{310,311}\n\n[testenv:lint]\ncommands = check --target=312\n")
    cwd = str(tmp_path)
    assert pattern(find="(a)") == {"language": "pattern", "as": "string", "find": "(a)"}       # nothing new unless used
    with pytest.raises(KernelError):                                                            # one place, one way of reading it
        Kernel(str(tmp_path / "x.jsonl"), gate=LeanGate()).claim_fact("versions", "List String", [
            {"at": "tox.ini", "reader": pattern(find_all=r"py(\d+)")}, {"at": "tox.ini", "reader": pattern(find_all=r"target=(\d+)")}])
    (tmp_path / "pw-facts.json").write_text(json.dumps([{"name": "versions", "type": "List String", "places": [
        {"at": "pyproject.toml", "read": {"find_all": "Python :: ([0-9.]+)", "sort": True}},
        {"at": "tox.ini", "read": {"within": "^envlist = .*py\\{([^}]+)\\}", "find_all": "(\\d+)", "rewrite": ["(\\d)(\\d+)", "\\1.\\2"], "sort": True}}]}]))
    k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate())
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "current" and [p["reads as"] for p in r["places"]] == ['["3.10", "3.11"]'] * 2, r
    (tmp_path / "tox.ini").write_text("[tox]\nenvlist = lint,py{310,311,312}\n\n[testenv:lint]\ncommands = check --target=312\n")
    assert k.recheck(cwd)["decisions"][0]["state"] == "violated"                           # tox now tries a version the metadata does not list
    (tmp_path / "tox.ini").write_text("[tox]\nenvs = lint\n")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and "`within` matches 0 times" in r["unread"][0]["why"], r   # the part it was confined to is gone: said, not guessed


def test_a_small_place_is_shown_with_what_surrounds_it(tmp_path):
    from pwt.kernel import context
    (tmp_path / "rules.json").write_text('{"note": "readers", "bar": {"read at least": 0.85, "stuck at most": 0.15}, "rows": [["a"]]}')
    (tmp_path / "app.py").write_text("# how many atoms a component may have\nLIMIT = 14\n\ndef f():\n    return LIMIT\n")
    (tmp_path / "doc.md").write_text("# Doc\n\n## Limits\n\n" + "A long section. " * 30 + "\n")
    cwd = str(tmp_path)
    around = context("rules.json::bar.read at least", cwd)
    assert '"read at least": 0.85' in around and '"stuck at most": 0.15' in around and "note" not in around   # the enclosing object
    assert "how many atoms" in context("app.py::LIMIT", cwd) and "def f" in context("app.py::LIMIT", cwd)    # the lines around it
    assert context("doc.md::Limits", cwd) is None and context("app.py", cwd) is None                         # big enough, or whole
    assert context("missing.json::a", cwd) is None


def test_changing_a_pattern_keeps_what_a_reader_confirmed_on_the_same_content(tmp_path):
    """A reader read the value off the place; another pattern that computes that value from the same
    content is confirmed by the same reading, at the first check and not only at the second."""
    from pwt.kernel import pattern
    (tmp_path / "pin.toml").write_text('name = "x"\nversion = "0.1.0"\n')
    cwd = str(tmp_path)
    _measure(cwd, opus=27)
    a = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate(), actor="reader-a")
    declare = lambda rx: a.claim_fact("version", "String", [{"at": "pin.toml", "reader": pattern(find=rx)}])["h"]
    h = declare(r'version = "([^"]+)"')
    a.read_place(h, "pin.toml", '"0.1.0"', blind=True, model="opus", cwd=cwd, quote='version = "0.1.0"')
    assert a.recheck(cwd)["decisions"][0]["places"][0]["stands"]
    assert declare(r'^version = "([0-9.]+)"') == h
    assert a.recheck(cwd)["decisions"][0]["places"][0]["stands"]


def test_a_place_may_state_only_some_entries_of_a_list(tmp_path):
    """An example uses some of the keys there are. It need not list all of them; what it lists has to exist."""
    import json
    from pwt.kernel import pattern
    (tmp_path / "config.py").write_text('KEYS = ["args", "command", "env_vars", "name"]\n')
    (tmp_path / "doc.md").write_text("## Format\n\nKeys: `args`, `command`, `env_vars`, `name`.\n\n"
                                     "## Example\n\nA task sets `name` and `command`.\n")
    (tmp_path / "example.toml").write_text('name = "a"\ncommand = "b"\nargs = []\n')
    cwd = str(tmp_path)
    _measure(cwd, opus=27)
    a = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate(), actor="reader-a")
    toml = {"at": "example.toml", "reader": pattern(find_all=r"^(\w+) = ", sort=True), "some": True}
    with pytest.raises(KernelError):
        a.claim_fact("keys", "List String", [{"at": "doc.md::Example", "some": True}, toml])     # nothing states the whole of it
    with pytest.raises(KernelError):
        a.claim_fact("limit", "Nat", ["doc.md::Format", {"at": "doc.md::Example", "some": True}])  # a number is not stated in part
    (tmp_path / "pw-facts.json").write_text(json.dumps([{"name": "keys", "type": "List String", "gloss": "the keys of a task, sorted", "places": [
        {"at": "config.py::KEYS", "read": {"find_all": '"(\\w+)"', "sort": True}}, "doc.md::Format",
        {"at": "doc.md::Example", "some": True}, {"at": "example.toml", "some": True, "read": {"find_all": "^(\\w+) = ", "sort": True}}]}]))
    h, = a.sync_facts(str(tmp_path / "pw-facts.json"))
    fact = lambda: a.recheck(cwd)["decisions"][0]
    place = lambda at: next(p for p in fact()["places"] if p["at"] == at)
    r = fact()
    assert r["state"] == "stale" and [(u["at"], u.get("some", False)) for u in r["unread"]] == [("doc.md::Format", False), ("doc.md::Example", True)]
    assert "only expected to mention some" in r["unread"][1]["question"] and "only expected" not in r["unread"][0]["question"]

    whole = '["args", "command", "env_vars", "name"]'
    a.read_place(h, "doc.md::Format", whole, blind=True, model="opus", cwd=cwd, quote="Keys: `args`, `command`, `env_vars`, `name`.")
    a.read_place(h, "doc.md::Example", '["command", "name"]', blind=True, model="opus", cwd=cwd, quote="A task sets `name` and `command`.")
    r = fact()
    assert r["state"] == "current", r                                    # two of four, three of four: nothing that does not exist
    assert [p.get("contained") for p in r["places"]] == [None, None, True, True]
    assert place("doc.md::Format")["why"] == "blind + words occur in the place + agrees with a computed place"
    p = place("doc.md::Example")
    assert p["why"] == "blind + words occur in the place + contained in a computed place" and "agrees with a computed place" not in p["has"]
    assert not place("example.toml")["stands"]                           # a pattern on an example is checked by a reader like any other
    a.read_place(h, "example.toml", '["args", "command", "name"]', blind=True, model="opus", cwd=cwd, quote='name = "a"')
    assert place("example.toml")["why"] == "computed + read the same blind"

    # an example that uses a key the code does not know
    (tmp_path / "example.toml").write_text('name = "a"\ncommand = "b"\nenvironment = {}\n')
    r = fact()
    assert r["state"] == "violated" and place("example.toml")["not in the whole"] == ["environment"], r
    (tmp_path / "example.toml").write_text('name = "a"\ncommand = "b"\nargs = []\n')
    (tmp_path / "doc.md").write_text("## Format\n\nKeys: `args`, `command`, `env_vars`, `name`.\n\n"
                                     "## Example\n\nA task sets `name` and `cmd`.\n")
    assert fact()["state"] == "stale"                                    # the example changed: read it again
    a.read_place(h, "doc.md::Example", '["cmd", "name"]', blind=True, model="opus", cwd=cwd, quote="A task sets `name` and `cmd`.")
    r = fact()
    p = place("doc.md::Example")
    assert r["state"] == "violated" and p["not in the whole"] == ["cmd"] and not p["stands"] and p["has"]["contained in a computed place"] is False

    # what was read as the whole list is not an answer to "which of them does this mention", nor the other way round
    declared = json.loads((tmp_path / "pw-facts.json").read_text())
    declared[0]["places"][1] = {"at": "doc.md::Format", "some": True}
    (tmp_path / "pw-facts.json").write_text(json.dumps(declared))
    a.sync_facts(str(tmp_path / "pw-facts.json"))
    r = fact()
    assert r["state"] == "stale" and r["unread"][0]["at"] == "doc.md::Format" and "another question" in r["unread"][0]["why"], r


def test_what_a_person_laid_down_is_an_axiom_and_conflicting_axioms_are_set_aside(tmp_path):
    """An instruction cannot be shown wrong by the files: the places are held against it. Two that
    cannot both hold are both set aside, and only that fact waits for a person."""
    import json
    (tmp_path / "a.py").write_text('MODE = "fast"\nLIMIT = 14\n')
    (tmp_path / "b.toml").write_text('mode = "fast"\n')
    (tmp_path / "c.md").write_text("## Example\n\nUse `safe` and `fast`.\n")
    cwd = str(tmp_path)
    rd = lambda rx, **kw: {"find": rx, **kw}
    def declare(*said, extra=()):
        facts = [{"name": "mode", "type": "String", "gloss": "the default mode", "places": [
                      {"at": "a.py", "read": rd('MODE = "(\\w+)"')}, {"at": "b.toml", "read": rd('mode = "(\\w+)"')}],
                  **({"instructions": list(said)} if said else {})},
                 {"name": "limit", "type": "Nat", "places": [{"at": "a.py", "read": rd("LIMIT = (\\d+)", **{"as": "nat"})}]}, *extra]
        (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
        k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate())
        k.sync_facts(str(tmp_path / "pw-facts.json"))
        return {d["fact"]: d for d in k.recheck(cwd)["decisions"]}
    alice = {"is": "fast", "by": "alice", "said": "keep the default on fast", "on": "2026-03-01"}
    bob, carol = {"is": "safe", "by": "bob"}, {"is": "fast", "by": "carol"}

    assert "instructions" not in declare()["mode"]                                       # nobody said anything: the places only have to agree
    r = declare(alice)["mode"]
    assert r["state"] == "current" and r["instructions"] == [{"is": '"fast"', "by": "alice", "said": "keep the default on fast", "on": "2026-03-01"}]

    # the places agree with each other, and both are against what was laid down
    r = declare(bob)["mode"]
    assert r["state"] == "violated" and [p.get("against") for p in r["places"]] == [["bob"], ["bob"]], r
    # the places differ: without an instruction nobody can say which is wrong; with one, the kernel can
    (tmp_path / "b.toml").write_text('mode = "safe"\n')
    assert [p.get("against") for p in declare()["mode"]["places"]] == [None, None] and declare()["mode"]["state"] == "violated"
    r = declare(alice, carol)["mode"]                                                    # two people, one value
    assert r["state"] == "violated" and [p.get("against") for p in r["places"]] == [None, ["alice", "carol"]], r
    (tmp_path / "b.toml").write_text('mode = "fast"\n')

    # two instructions that cannot both hold: both are set aside, whichever came first, however many agree
    r = declare(alice, bob)
    assert r["mode"]["state"] == "conflict" and r["mode"]["without the instructions set aside"] == "current", r["mode"]
    assert [i.get("set aside") for i in r["mode"]["instructions"]] == [["bob"], ["alice"]]
    assert all("against" not in p for p in r["mode"]["places"])                          # nothing is concluded from either
    assert r["limit"]["state"] == "current"                                              # and nothing else is touched
    r = declare(alice, carol, bob)["mode"]
    assert r["state"] == "conflict" and [sorted(i.get("set aside", [])) for i in r["instructions"]] == [["bob"], ["bob"], ["alice", "carol"]]
    assert declare(alice, carol)["mode"]["state"] == "current"                           # bob's is withdrawn: the rest holds again

    # a place that states only some entries is held against an instruction the same way
    part = {"name": "modes", "type": "List String", "places": [{"at": "c.md::Example", "some": True, "read": {"find_all": "`(\\w+)`", "sort": True}},
                                                               {"at": "a.py", "read": {"find_all": 'MODE = "(\\w+)"'}}],
            "instructions": [{"is": ["fast"], "by": "alice"}]}
    r = declare(extra=[part])["modes"]
    assert r["state"] == "violated" and r["places"][0]["not in the whole"] == ["safe"] and r["places"][0]["against"] == ["alice"], r

    # an instruction has an author and a value of the fact's type; the old anonymous "value" is not read
    for bad in ({"is": "fast"}, {"is": 14, "by": "alice"}, {"by": "alice"}):
        with pytest.raises(KernelError):
            declare(bad)
    with pytest.raises(KernelError):
        declare(alice, dict(alice))
    (tmp_path / "pw-facts.json").write_text(json.dumps([{"name": "mode", "type": "String", "places": ["a.py"], "value": '"fast"'}]))
    with pytest.raises(KernelError):
        Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate()).sync_facts(str(tmp_path / "pw-facts.json"))


FAKE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fake_claude.py")
SUPPOSED = "(supposed)"


def propagate(cwd, facts, suppose=None, told=None, apply=False, json_out=True):
    """pw propagate on `cwd`, whose pw-facts.json is `facts`; with `told`, its agents are the
    stand-in of tests/fake_claude.py, told what to answer. The plan it makes, or what it prints."""
    import json
    assert json.loads(open(os.path.join(cwd, "pw-facts.json")).read()) == facts
    from pwt.core import pw_binary
    args = [pw_binary(), "propagate", "--repo", cwd] + ["--json"] * json_out + ["--apply"] * apply
    for name, value in (suppose or {}).items():
        args += ["--suppose", f"{name}={json.dumps(value) if not isinstance(value, str) else value}"]
    env = dict(os.environ)
    if told is not None:
        spec = os.path.join(cwd, "..", "told.json")
        open(spec, "w").write(json.dumps(told))
        env.update(PW_CLAUDE=FAKE, FAKE_CLAUDE=spec)
        args.append("--agent")
    r = subprocess.run(args, capture_output=True, text=True, env=env)
    if r.returncode == 2:
        raise KernelError(r.stderr.strip().removeprefix("pw: "))
    return json.loads(r.stdout) if json_out else r.stdout


def test_what_was_laid_down_is_written_into_the_places_and_read_back(tmp_path):
    """The check in reverse: a place read by a simple pattern gets the instructed value written
    into it, confirmed by reading it back. A value can also be supposed, to see what would follow."""
    import json
    (tmp_path / "app.py").write_text('def run(mode="fast", limit=0.9):\n    return mode\n\nMODES = ["fast", "safe"]\n')
    (tmp_path / "conf.toml").write_text('[a]\nmode = "x"\n\n[b]\nmode = "fast"\n')
    (tmp_path / "doc.md").write_text("## Mode\n\nThe default mode is `fast`.\n")
    cwd = str(tmp_path)
    def facts(*said):
        return [{"name": "mode", "type": "String", "gloss": "the default mode", "instructions": list(said), "places": [
                     {"at": "app.py::run", "read": {"find": 'mode="(\\w+)"'}},
                     {"at": "conf.toml", "read": {"within": "\\[b\\]\\n([^\\[]*)", "find": 'mode = "(\\w+)"'}},
                     "doc.md::Mode"]},
                {"name": "limit", "type": "Nat", "places": [{"at": "app.py::run", "read": {"find": "limit=([0-9.]+)", "as": "permille"}}]},
                {"name": "modes", "type": "List String", "places": [{"at": "app.py::MODES", "read": {"find_all": '"(\\w+)"', "sort": True}}]}]
    def declare(*said):
        fs = [{k: v for k, v in f.items() if k != "instructions" or v} for f in facts(*said)]
        (tmp_path / "pw-facts.json").write_text(json.dumps(fs))
        k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate())
        k.sync_facts(str(tmp_path / "pw-facts.json"))
        return fs, k
    fs, k = declare({"is": "fast", "by": "alice"})
    h = next(h for h, f in k.state().facts.items() if f["name"] == "mode")
    k.read_place(h, "doc.md::Mode", '"fast"', cwd=cwd, quote="The default mode is `fast`.")
    got = propagate(cwd, fs)
    assert got["files"] == {} and not got["written"] and not got["by hand"]            # every place already says it

    # alice changes her mind: the instruction is edited, and the places follow
    fs, k = declare({"is": "safe", "by": "alice"})
    got = propagate(cwd, fs)
    assert [(w["at"], w["to"]) for w in got["written"]] == [("app.py::run", '"safe"'), ("conf.toml", '"safe"')]
    assert [(b["at"], "reader" in b["why"]) for b in got["by hand"]] == [("doc.md::Mode", True)]   # prose is not written by a pattern
    assert sorted(got["files"]) == ["app.py", "conf.toml"]
    assert got["files"]["app.py"][1] == 'def run(mode="safe", limit=0.9):\n    return mode\n\nMODES = ["fast", "safe"]\n'   # that piece and nothing else
    assert got["files"]["conf.toml"][1] == '[a]\nmode = "x"\n\n[b]\nmode = "safe"\n'                                     # the one inside [b]
    shown = propagate(cwd, fs, json_out=False)
    assert '-def run(mode="fast"' in shown and '+def run(mode="safe"' in shown and "nothing was written" in shown
    assert (tmp_path / "app.py").read_text().startswith('def run(mode="fast"')                # looking writes nothing
    for path, (_, new) in got["files"].items():
        (tmp_path / path).write_text(new)
    r = next(d for d in k.recheck(cwd)["decisions"] if d["fact"] == "mode")
    assert [p.get("against") for p in r["places"]] == [None, None, ["alice"]]                 # only the prose is left

    # a hypothesis: nobody laid it down, nothing is added to the declaration, but what would follow is shown
    fs, _ = declare({"is": "safe", "by": "alice"})
    got = propagate(cwd, fs, {"limit": 850, "modes": ["fast"]})
    assert got["files"]["app.py"][1].startswith('def run(mode="safe", limit=0.85):') and got["written"][0]["by"] == [SUPPOSED]
    assert [b["fact"] for b in got["by hand"]] == ["mode", "modes"] and "find" in got["by hand"][1]["why"]   # a list is not written back
    assert json.loads((tmp_path / "pw-facts.json").read_text()) == fs
    # supposing something against what a person laid down is refused, and nothing is written for that fact
    got = propagate(cwd, fs, {"mode": "turbo"})
    assert got["files"] == {} and got["refused"][0]["supposed"] and {i["by"] for i in got["refused"][0]["instructions"]} == {"alice", SUPPOSED}
    with pytest.raises(KernelError):
        propagate(cwd, fs, {"no such fact": 1})
    # what the pattern cannot confirm is not written: "so safe" is not a word the pattern reads
    got = propagate(cwd, declare()[0], {"mode": "so safe"})
    assert got["files"] == {} and all("can no longer be read" in b["why"] for b in got["by hand"] if b["at"] != "doc.md::Mode")


def test_a_definition_takes_its_value_from_other_facts(tmp_path):
    """A count, a first entry: nothing new is claimed, only what follows from facts already declared."""
    import json
    (tmp_path / "app.py").write_text('MODES = ["fast", "safe"]\nVERSIONS = ["3.10", "3.11"]\n')
    (tmp_path / "doc.md").write_text("## Modes\n\nThere are 2 modes.\n")
    (tmp_path / "pyproject.toml").write_text('requires-python = ">=3.10"\nversions = ["3.10", "3.11"]\n')
    cwd = str(tmp_path)
    modes = {"name": "modes", "type": "List String", "places": [{"at": "app.py::MODES", "read": {"find_all": '"(\\w+)"', "sort": True}}]}
    versions = {"name": "versions", "type": "List String", "places": [
        {"at": "app.py::VERSIONS", "read": {"find_all": '"([0-9.]+)"', "sort": True}},
        {"at": "pyproject.toml", "read": {"within": "versions = \\[([^\\]]*)\\]", "find_all": '"([0-9.]+)"', "sort": True}}]}
    count = {"name": "number of modes", "type": "Nat", "defined": {"from": ["modes"], "as": "fun ms => ms.length"},
             "places": [{"at": "doc.md::Modes", "read": {"find": "There are (\\d+) modes", "as": "nat"}}]}
    oldest = {"name": "oldest version", "type": "String", "defined": {"from": ["versions"], "as": 'fun vs => vs.headD ""'},
              "places": [{"at": "pyproject.toml", "read": {"find": 'requires-python = ">=([0-9.]+)"'}}]}
    def check(*facts):
        (tmp_path / "pw-facts.json").write_text(json.dumps(list(facts)))
        k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate())
        k.sync_facts(str(tmp_path / "pw-facts.json"))
        return {d["fact"]: d for d in k.recheck(cwd)["decisions"]}
    r = check(count, modes, versions, oldest)                                    # (declared before the facts it is defined from: no matter)
    assert [r[n]["state"] for n in ("modes", "number of modes", "versions", "oldest version")] == ["current"] * 4, r

    # a mode is added in the code: the list is still one place agreeing with itself, but the count in the document is now wrong
    (tmp_path / "app.py").write_text('MODES = ["fast", "safe", "turbo"]\nVERSIONS = ["3.10", "3.11"]\n')
    r = check(count, modes, versions, oldest)
    d = r["number of modes"]
    assert r["modes"]["state"] == "re-established" and d["state"] == "violated" and d["gives"] == "3", d
    assert d["places"][0]["differs from the definition"] and "against" not in d["places"][0]
    got = propagate(cwd, [count, modes, versions, oldest])                       # and written back, it reads 3
    assert got["files"]["doc.md"][1] == "## Modes\n\nThere are 3 modes.\n" and got["written"][0]["by"] == ["the definition from modes"]
    (tmp_path / "doc.md").write_text(got["files"]["doc.md"][1])
    assert check(count, modes, versions, oldest)["number of modes"]["state"] in ("current", "re-established")

    # the facts a definition is built on disagree: there is nothing to hold its places against
    (tmp_path / "pyproject.toml").write_text('requires-python = ">=3.10"\nversions = ["3.9", "3.10", "3.11"]\n')
    r = check(count, modes, versions, oldest)
    assert r["versions"]["state"] == "violated" and r["oldest version"]["state"] == "waits" and r["oldest version"]["waits for"] == ["versions is violated"]
    # a person settles it; the definition follows what was laid down, and names the place that now differs
    r = check(count, modes, {**versions, "instructions": [{"is": ["3.9", "3.10", "3.11"], "by": "alice"}]}, oldest)
    d = r["oldest version"]
    assert r["versions"]["state"] == "violated" and d["state"] == "violated" and d["gives"] == '"3.9"' and d["places"][0]["differs from the definition"], d
    # supposing a value for a fact shows what follows for the facts defined from it
    (tmp_path / "pyproject.toml").write_text('requires-python = ">=3.10"\nversions = ["3.10", "3.11"]\n')
    check(count, modes, versions, oldest)
    got = propagate(cwd, [count, modes, versions, oldest], {"versions": ["3.11", "3.12"]})
    assert ('pyproject.toml', '"3.11"') in [(w["at"], w["to"]) for w in got["written"]]
    assert 'requires-python = ">=3.11"' in got["files"]["pyproject.toml"][1]

    # a definition of a definition; and what is not a definition
    twice = {"name": "twice the modes", "type": "Nat", "defined": {"from": ["number of modes"], "as": "fun n => 2 * n"},
             "places": [{"at": "doc.md::Modes", "read": {"find": "There are (\\d+) modes", "as": "nat"}}]}
    r = check(count, modes, twice)
    assert r["twice the modes"]["state"] == "violated" and r["twice the modes"]["gives"] == "6"
    for bad in ({**count, "defined": {"from": ["nothing"], "as": "fun ms => ms.length"}},          # from a fact that is not declared
                {**count, "defined": {"from": ["modes"], "as": "fun ms => ms"}},                    # not a Nat
                {**count, "defined": {"from": ["number of modes"], "as": "fun n => n"}},            # from itself
                {**count, "instructions": [{"is": 2, "by": "alice"}]},                              # a definition takes no instruction
                {**count, "defined": {"from": ["twice the modes"], "as": "fun n => n"}}):           # in a circle
        with pytest.raises(KernelError):
            check(bad, modes, twice)


def test_an_agent_may_propose_the_new_text_of_a_place_and_it_is_read_back(tmp_path):
    """Where a pattern cannot write (a list, prose), an agent's proposed text is taken only if
    it is an edit, leaves every other declared place as it reads, and reads back as the value."""
    import json
    code = 'MODES = ["fast", "safe"]\nDEFAULT = "fast"\n'
    (tmp_path / "app.py").write_text(code)
    (tmp_path / "doc.md").write_text("## Modes\n\nThe modes are `fast` and `safe`. The default is `fast`.\n")
    cwd = str(tmp_path)
    facts = [{"name": "modes", "type": "List String", "gloss": "the modes, sorted", "instructions": [{"is": ["fast", "safe", "turbo"], "by": "alice"}],
              "places": [{"at": "app.py", "read": {"find_all": '"(\\w+)"[,\\]]', "sort": True}}, "doc.md::Modes"]},
             {"name": "default", "type": "String", "places": [{"at": "app.py", "read": {"find": 'DEFAULT = "(\\w+)"'}}]}]
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate())
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    h = next(h for h, f in k.state().facts.items() if f["name"] == "modes")
    k.read_place(h, "doc.md::Modes", '["fast", "safe"]', cwd=cwd, quote="The modes are `fast` and `safe`. The default is `fast`.")
    got = propagate(cwd, facts)
    assert [b["at"] for b in got["by hand"]] == ["app.py", "doc.md::Modes"] and got["files"] == {}       # without an agent: left by hand

    new_doc = "## Modes\n\nThe modes are `fast`, `safe` and `turbo`. The default is `fast`.\n"
    log = tmp_path.parent / "prompts.jsonl"
    def told(edit, read='["fast", "safe", "turbo"]'):
        log.write_text("")
        return {"edit": edit, "log": str(log),
                "read": {"doc.md::Modes": {"object": read, "quote": "The modes are `fast`, `safe` and `turbo`. The default is `fast`."}}}
    good = {"app.py": 'MODES = ["fast", "safe", "turbo"]\nDEFAULT = "fast"\n', "doc.md::Modes": new_doc}

    got = propagate(cwd, facts, told=told(good))
    assert [(w["at"], w["how"]) for w in got["written"]] == [("app.py", "changed by an agent; read back with its pattern"),
                                                             ("doc.md::Modes", "changed by an agent; read back by a blind reader")]
    assert got["files"]["app.py"][1] == good["app.py"] and got["files"]["doc.md"][1] == new_doc and not got["by hand"]
    assert len(got["readings"]) == 1 and (tmp_path / "app.py").read_text() == code                       # nothing written by looking
    sessions = [json.loads(l) for l in log.read_text().splitlines()]
    assert [s["env"].get("PW_TOOLS", "read") for s in sessions] == ["edit", "read"]
    assert "The modes are `fast` and `safe`." in sessions[0]["prompt"] and "alice" not in sessions[1]["prompt"]
    assert new_doc.split("\n")[2] in sessions[1]["prompt"] and "turbo" not in sessions[1]["prompt"].split("=== h:")[0]   # the reader is shown the proposed text, not what to expect

    # written, with the reader's reading taken over: the places now say what was laid down
    propagate(cwd, facts, told=told(good), apply=True)
    assert (tmp_path / "app.py").read_text() == good["app.py"] and (tmp_path / "doc.md").read_text() == new_doc
    r = next(d for d in k.recheck(cwd)["decisions"] if d["fact"] == "modes")
    assert r["state"] in ("current", "re-established") and all("against" not in p for p in r["places"]), r
    (tmp_path / "app.py").write_text(code)
    (tmp_path / "doc.md").write_text("## Modes\n\nThe modes are `fast` and `safe`. The default is `fast`.\n")

    def why(answers, read='["fast", "safe", "turbo"]'):
        got = propagate(cwd, facts, told=told(answers, read))
        return {b["at"]: b["why"] for b in got["by hand"]}, got
    # the edit does not give the value when read back
    assert "reads as" in why({**good, "app.py": 'MODES = ["fast", "turbo"]\nDEFAULT = "fast"\n'})[0]["app.py"]
    # the edit would change what another declared place reads as
    assert "would read as" in why({**good, "app.py": 'MODES = ["fast", "safe", "turbo"]\nDEFAULT = "turbo"\n'})[0]["app.py"]
    # a rewrite, not an edit
    assert "rewrote" in why({**good, "app.py": "# modes\n" * 60 + 'MODES = ["fast", "safe", "turbo"]\nDEFAULT = "fast"\n'})[0]["app.py"]
    # no answer; the passage returned as it was; and an agent that says it cannot
    assert "no answer" in why({"doc.md::Modes": new_doc})[0]["app.py"]
    assert "unchanged" in why({**good, "app.py": code})[0]["app.py"]
    assert "cannot be done: no room" in why({**good, "app.py": {"cannot": "no room"}})[0]["app.py"]
    # the blind reader does not read the value off the proposed prose: the prose is not taken
    left, got = why(good, '["fast", "safe"]')
    assert "a blind reader shown it reads" in left["doc.md::Modes"] and "doc.md" not in got["files"] and "app.py" in got["files"]


def test_checking_does_not_write_to_the_record(tmp_path, capsys):
    """pw check works on a copy of the record: trying something out leaves nothing in a committed file."""
    import json
    from pwt import check
    repo, record = str(tmp_path), str(tmp_path / "pw-log.jsonl")
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    (tmp_path / "pw-facts.json").write_text(json.dumps([{"name": "limit", "type": "Nat", "places": [
        {"at": "k.py", "read": {"find": r"= (\d+)", "as": "nat"}},
        {"at": "doc.md::Limits", "read": {"find": r"most (\d+)", "as": "nat"}}]}]))

    assert check.run(repo, record, unconfirmed="warn", lean="always") is False       # (no blind reader has seen the patterns: a warning here)
    assert "WARN current" in capsys.readouterr().out
    assert not os.path.exists(record)                                 # not even created

    (tmp_path / "k.py").write_text("LIMIT = 15\n")                    # changed on purpose, to see the check fail
    assert check.run(repo, record, unconfirmed="warn", lean="always") is True
    assert "FAIL violated" in capsys.readouterr().out and not os.path.exists(record)

    assert check.run(repo, record, unconfirmed="warn", keep=True, lean="always") is True          # asked to record: it does
    kept = open(record).read()
    assert {json.loads(l)["type"] for l in kept.splitlines()} == {"claim", "reading", "agree", "proof"}
    assert all(json.loads(l)["actor"] == "check" for l in kept.splitlines())

    (tmp_path / "k.py").write_text("LIMIT = 16\n")
    assert check.run(repo, record, verify=True, unconfirmed="warn", lean="always") is True
    out = capsys.readouterr().out
    assert open(record).read() == kept                                # an existing record is read, and left as it was
    assert "1 recorded proof(s) verified again, 0 refused" in out     # the record's proof, not the one this check just made

    # a proof written into the record by hand is still found out, by a check that records nothing
    f = next(json.loads(l)["f"] for l in kept.splitlines() if json.loads(l)["type"] == "agree")
    fake = {"ts": 0, "actor": "x", "type": "proof", "relation": "holds", "args": [f], "proof": "decide", "proof_sha": "x", "axioms": [], "gamma": "x"}
    open(record, "a").write(json.dumps(fake) + "\n")
    forged = open(record).read()
    assert check.run(repo, record, verify=True, unconfirmed="warn", lean="always") is True
    assert "1 recorded proof(s) verified again, 1 refused" in capsys.readouterr().out and open(record).read() == forged


def test_lean_is_not_run_where_the_tool_is_kept(tmp_path, monkeypatch):
    """The Lean project may be a shared checkout or a read-only install: the gate builds and checks elsewhere."""
    from pwt.core import LEAN_DIR
    project, work = tmp_path / "lean", tmp_path / "work"
    project.mkdir()
    names = [n for n in ("lean-toolchain", "Gamma.lean", "lakefile.toml", "lake-manifest.json") if os.path.exists(os.path.join(LEAN_DIR, n))]
    for n in names:
        shutil.copy(os.path.join(LEAN_DIR, n), project / n)
    monkeypatch.setenv("PW_LEAN_WORK", str(work))
    gate = LeanGate(str(project))
    assert gate.check("holds", P("(1 : Nat) = 1"), "rfl")["ok"]
    assert not gate.check("holds", P("(1 : Nat) = 2"), "rfl")["ok"]
    assert gate.typecheck([("Nat", "14")])["ok"] and gate.evaluate("Nat", "[1, 2, 3].length") == "3"
    assert sorted(os.listdir(project)) == sorted(names)               # nothing was written next to the project
    home, = os.listdir(work)
    assert sorted(os.listdir(work / home)) == sorted(names + [".lake"])            # built there; what each check wrote is gone

    (project / "Gamma.lean").write_text((project / "Gamma.lean").read_text() + "\ndef pwTestExtra : Nat := 7\n")
    assert gate.evaluate("Nat", "pwTestExtra") == "7"                 # other premises: another directory, not the old build
    assert len(os.listdir(work)) == 2

    os.remove(project / "lakefile.toml")
    v = gate.check("holds", P("(1 : Nat) = 1"), "rfl")
    assert not v["ok"] and "is not the Lean project" in v["reason"]


def test_a_reading_counts_by_the_reader_that_made_it(tmp_path, monkeypatch):
    """A reader is a model with its instructions. When the instructions change, what was read
    under the earlier ones still rests on the reader that read it, as measured then; only what
    is read from now on needs the new reader measured."""
    import pwt.kernel as K
    from pwt.kernel import pattern
    (tmp_path / "k.py").write_text("LIMIT = 14\nSIZE = 3\n")
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n\n## Size\n\nThree, that is 3, parts.\n")
    cwd = str(tmp_path)
    k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate(), actor="reader-1")
    limit = k.claim_fact("limit", "Nat", ["doc.md::Limits", {"at": "k.py", "reader": pattern(find=r"LIMIT = (\d+)", kind="nat")}])["h"]
    size = k.claim_fact("size", "Nat", ["doc.md::Size", {"at": "k.py", "reader": pattern(find=r"SIZE = (\d+)", kind="nat")}])["h"]
    stands = lambda h: next(p["stands"] for d in k.recheck(cwd)["decisions"] if d["h"] == h for p in d["places"] if p["by"] == "stated")

    monkeypatch.setattr(K, "INSTRUCTIONS", "first")
    k.read_place(limit, "doc.md::Limits", "14", cwd=cwd, quote="At most 14 atoms.", blind=True, model="opus")
    assert not stands(limit)                                           # nobody measured yet
    _measure(cwd, instructions="first", opus=27)
    assert stands(limit)

    monkeypatch.setattr(K, "INSTRUCTIONS", "second")                   # the instructions are reworded
    assert stands(limit)                                               # ...what was read before stays as it was
    Kernel(k.db_path, gate=LeanGate(), actor="reader-2").read_place(size, "doc.md::Size", "3", cwd=cwd, quote="Three, that is 3, parts.", blind=True, model="opus")
    assert not stands(size)                                            # ...what is read now is by a reader not yet measured
    r = next(p for d in k.recheck(cwd)["decisions"] if d["h"] == size for p in d["places"] if p["by"] == "stated")
    assert r["unmeasured readers"] == ["opus"]
    _measure(cwd, keep=True, instructions="second", opus=27)
    assert stands(size) and stands(limit)

    _measure(cwd, instructions="second", opus=27)                      # the earlier measurement is taken out of the file
    assert stands(size) and not stands(limit)                          # ...and the earlier reading has nothing to rest on


def test_a_way_of_reading_new_to_the_record_is_pointed_out(tmp_path, capsys):
    """A check does not write. A computed place whose way of reading is not in the record stands
    for the text as it is, and would stop standing at the next edit: the check says so, and
    recording once (no reader is called) keeps it."""
    import json
    from pwt import check
    repo, record = str(tmp_path), str(tmp_path / "pw-log.jsonl")
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    _measure(repo, opus=27)
    declare = lambda find: (tmp_path / "pw-facts.json").write_text(json.dumps([{"name": "limit", "type": "Nat", "places": [
        "doc.md::Limits", {"at": "k.py", "read": {"find": find, "as": "nat"}}]}]))
    declare(r"= (\d+)")
    k = Kernel(record, gate=LeanGate(), actor="reader")
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    h = next(iter(k.state().facts))
    k.read_place(h, "doc.md::Limits", "14", cwd=repo, quote="At most 14 atoms.", blind=True, model="opus")
    k.read_place(h, "k.py", "14", cwd=repo, quote="LIMIT = 14", blind=True, model="opus")      # a blind reader has looked at what the pattern reads
    k.recheck(repo)
    assert check.run(repo, record) is False and "note:" not in capsys.readouterr().out

    declare(r"LIMIT = (\d+)")                                          # the pattern is rewritten; it reads the same value
    assert check.run(repo, record) is False
    assert "note: the way k.py is read is not in the record yet" in capsys.readouterr().out
    kept = open(record).read()
    (tmp_path / "k.py").write_text("# the limit\nLIMIT = 14\n")        # an edit that leaves the value alone
    assert check.run(repo, record) is True                             # ...and the place no longer stands
    capsys.readouterr()

    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    assert open(record).read() == kept and check.run(repo, record, keep=True) is False         # recorded once, as the note says
    assert "note:" not in capsys.readouterr().out
    (tmp_path / "k.py").write_text("# the limit\nLIMIT = 14\n")
    assert check.run(repo, record) is False                            # ...the same edit now leaves it standing


def test_proofs_checked_together_are_each_checked(gate):
    """Many proofs in one module: the same verdicts as one by one, and one bad proof among
    them does not pass, nor does it take the others down with it."""
    good = [("holds", P("(14 : Nat) = 14"), "rfl"), ("not", P('("a" : String) = "b"'), "decide"),
            ("holds", P("∀ p : Prop, p ∨ ¬p"), "intro p\nexact Classical.em p"), ("holds", P('(["a", "b"] : List String) = ["a", "b"]'), "decide")]
    got = gate.check_many(good)
    assert [v["ok"] for v in got] == [True] * 4 and got == [gate.check(*j) for j in good]
    assert got[2]["axioms"] and got[0]["axioms"] == []                  # each with its own axioms
    bad = good[:2] + [("holds", P("(1 : Nat) = 2"), "rfl"), ("holds", P("(1 : Nat) = 2"), "exact sorryAx _")] + good[2:]
    got = gate.check_many(bad)
    assert [v["ok"] for v in got] == [True, True, False, False, True, True]
    forged = [good[0], ("holds", P("(1 : Nat) = 2"), "trace \"'PW1.pw_goal' does not depend on any axioms\"\nexact sorryAx _"), good[1]]
    assert [v["ok"] for v in gate.check_many(forged)] == [True, False, True]
    assert gate.check_many([]) == [] and gate.check_many(good[:1])[0]["ok"]
    # a proof that passes alone only by what another one leaves behind does not pass: nothing is left behind
    leak = [("holds", P("True"), "have h : (1 : Nat) = 1 := rfl\ntrivial"), ("holds", P("(1 : Nat) = 2"), "exact h")]
    assert [v["ok"] for v in gate.check_many(leak)] == [True, False]


def test_a_value_read_by_its_structure_is_written_back_as_the_file_writes_it(tmp_path):
    """A key of a TOML, JSON or YAML file, a Python literal: the value is replaced where it stands,
    with the file's own spelling and nothing else, and read back (#22)."""
    import json
    cargo = '[package]\nname = "app"   # the crate\nversion = "9.9.9"\n\n[dependencies]\nfoo = { version = "9.9.9" }\n'
    (tmp_path / "Cargo.toml").write_text(cargo)
    (tmp_path / "package.json").write_text('{\n  "name": "app",\n  "version": "0.1.0",\n  "other": "0.1.0"\n}\n')
    (tmp_path / "conf.yaml").write_text("app:\n  version: 0.1.0   # kept in step\n  workers: 4\n")
    (tmp_path / "app.py").write_text('VERSION = "0.1.0"\nWORKERS = 4\n')
    (tmp_path / "doc.md").write_text("## Version\n\nThis is version 0.1.0.\n")
    facts = [{"name": "version", "type": "String", "instructions": [{"is": "0.2.0", "by": "alice"}], "places": [
                 {"at": "Cargo.toml", "read": {"data": "package.version"}},
                 {"at": "package.json", "read": {"data": "version"}},
                 {"at": "conf.yaml", "read": {"data": "app.version"}},
                 {"at": "app.py::VERSION", "read": {"python": "value"}},
                 "doc.md::Version"]},
             {"name": "workers", "type": "Nat", "instructions": [{"is": 8, "by": "alice"}], "places": [
                 {"at": "conf.yaml", "read": {"data": "app.workers", "as": "nat"}}, {"at": "app.py::WORKERS", "read": {"python": "value", "as": "nat"}},
                 {"at": "app.py", "read": {"find": r"WORKERS = (\d+)", "as": "nat"}}]}]       # (two places of one fact in one file)
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    k = Kernel(str(tmp_path / "pw-log.jsonl"), gate=LeanGate())
    k.sync_facts(str(tmp_path / "pw-facts.json"))
    h = next(h for h, f in k.state().facts.items() if f["name"] == "version")
    k.read_place(h, "doc.md::Version", '"0.1.0"', cwd=str(tmp_path), quote="This is version 0.1.0.")
    got = propagate(str(tmp_path), facts)
    assert {(w["at"], w["how"]) for w in got["written"]} == {(a, "read back with its way of reading") for a in
                                                             ("Cargo.toml", "package.json", "conf.yaml", "app.py::VERSION", "app.py::WORKERS")} | {("app.py", "read back with its pattern")}
    files = {p: new for p, (_, new) in got["files"].items()}
    assert files["Cargo.toml"] == cargo.replace('version = "9.9.9"\n\n', 'version = "0.2.0"\n\n')       # the dependency's 9.9.9 is not the one read
    assert files["package.json"] == '{\n  "name": "app",\n  "version": "0.2.0",\n  "other": "0.1.0"\n}\n'
    assert files["conf.yaml"] == "app:\n  version: 0.2.0   # kept in step\n  workers: 8\n"
    assert files["app.py"] == 'VERSION = "0.2.0"\nWORKERS = 8\n'
    assert [b["at"] for b in got["by hand"]] == ["doc.md::Version"]
    shown = propagate(str(tmp_path), facts, json_out=False)
    assert "(or: pw propagate --agent" in shown                                                     # the next step is named (#22)

    # where replacing the value would change something else too, nothing is written
    (tmp_path / "package.json").write_text('{"version": "0.1.0", "list": ["0.1.0"]}\n')
    facts[0]["places"] = [{"at": "package.json", "read": {"data": "version"}}, "doc.md::Version"]
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    got = propagate(str(tmp_path), facts)
    assert json.loads(got["files"]["package.json"][1]) == {"version": "0.2.0", "list": ["0.1.0"]}
    (tmp_path / "list.py").write_text('L = ["0.1.0"]\n')
    facts[0]["places"] = [{"at": "package.json", "read": {"data": "list"}}, {"at": "list.py::L", "read": {"python": "value"}}]
    facts[0]["type"], facts[0]["instructions"] = "List String", [{"is": ["0.2.0"], "by": "alice"}]
    (tmp_path / "pw-facts.json").write_text(json.dumps(facts))
    got = propagate(str(tmp_path), facts)
    assert "package.json" not in got["files"] and "not a list" in next(b["why"] for b in got["by hand"] if b["at"] == "package.json")
