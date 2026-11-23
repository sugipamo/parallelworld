"""Runs the real Lean kernel. Skipped when Lean is not installed."""
import os
import shutil
import subprocess

import pytest

from pw.kernel import Kernel, KernelError, binding
from pw.lean_gate import LeanGate

LAKE = os.environ.get("PW_LAKE") or shutil.which("lake")
pytestmark = pytest.mark.skipif(not LAKE, reason="Lean not installed (set PW_LAKE)")

COMM = "∀ a b : Nat, a + b = b + a"
P = lambda *texts: [("Prop", t) for t in texts]


@pytest.fixture(scope="module")
def gate():
    return LeanGate()


def test_accepts_valid_proofs(gate):
    v = gate.check("holds", P(COMM), "intro a b\nexact Nat.add_comm a b")
    assert v["ok"] and v["axioms"] == [], v
    v = gate.check("iff", P(COMM, "∀ x y : Nat, y + x = x + y"),
                   "constructor\n· intro h x y\n  exact h y x\n· intro h a b\n  exact h b a")
    assert v["ok"], v
    assert gate.check("not", P("(1 : Nat) < 1"), "decide")["ok"]
    assert gate.check("implies", P("∀ n : Nat, n < 5", "(3 : Nat) < 5"), "intro h\nexact h 3")["ok"]
    assert gate.check("contradiction", P("(1 : Nat) = 2", "True"), "intro h\nexact absurd h.1 (by decide)")["ok"]


def test_classical_axioms_are_reported_and_allowed(gate):
    v = gate.check("holds", P("∀ p : Prop, p ∨ ¬p"), "intro p\nexact Classical.em p")
    assert v["ok"] and "Classical.choice" in v["axioms"], v


def test_rejects_wrong_and_incomplete_proofs(gate):
    assert not gate.check("holds", P("∀ a b : Nat, a + b = a"), "intro a b\nrfl")["ok"]
    assert not gate.check("holds", P(COMM), "intro a b")["ok"]            # unsolved goal
    assert not gate.check("iff", P("(1 : Nat) = 1", "(1 : Nat) = 2"), "decide")["ok"]
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


def test_kernel_end_to_end(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    h1, h2 = k.claim("add commutes")["h"], k.claim("order of addends is irrelevant")["h"]
    g1, g2 = k.ground(h1, COMM, prior=0.9), k.ground(h2, "∀ x y : Nat, y + x = x + y", prior=0.8)
    bad = k.prove("iff", [g1["f"], g2["f"]], "rfl")
    assert not bad["accepted"] and k.state().proofs == []
    good = k.prove("iff", [g1["f"], g2["f"]],
                   "constructor\n· intro h x y\n  exact h y x\n· intro h a b\n  exact h b a")
    assert good["accepted"], good
    b = k.infer(f"{h1} <-> {h2}")
    assert b["lo"] == pytest.approx(0.7, abs=1e-6)


FN = "Nat → Nat → Nat → Nat"
CLAMP = "fun x lo hi => min (max x lo) hi"
BOUND = "fun x lo hi => if x < lo then lo else if x > hi then hi else x"
SPEC1 = "fun f => ∀ x lo hi, lo ≤ hi → lo ≤ f x lo hi ∧ f x lo hi ≤ hi"
SPEC2 = "fun f => ∀ x lo hi, lo ≤ hi → f x lo hi ≥ lo ∧ hi ≥ f x lo hi"


def test_specification_and_object_identity_with_real_lean(tmp_path):
    """The case from the first two-worker run, now with a non-vacuous notion of sameness."""
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    h1, h2 = k.claim("clamp stays within [lo, hi]")["h"], k.claim("bound stays within [lo, hi]")["h"]
    a = k.ground_at(h1, "clamp", FN, SPEC1, CLAMP)
    b = k.ground_at(h2, "bound", FN, SPEC2, BOUND)
    assert k.prove("holds", [a["f"]], "intro x lo hi h\nomega")["accepted"]
    r = k.prove("holds", [b["f"]], "intro x lo hi h\nsplit\n· omega\n· split <;> omega")
    assert r["accepted"], r

    assert k.prove("pred_iff", [a["p"], b["p"]], "intro f\nexact Iff.rfl")["accepted"]
    alg = k.state().algebra
    assert alg.find(a["p"]) == alg.find(b["p"])          # same specification: verified
    assert alg.find(a["o"]) != alg.find(b["o"])          # same object: not claimed

    # clamp and bound differ when lo > hi, so Lean must refuse to identify them
    r = k.prove("obj_eq", [a["o"], b["o"]], "funext x lo hi\nomega")
    assert not r["accepted"]

    c = k.ground_at(k.claim("clamp2 stays within [lo, hi]")["h"], "clamp2", FN, SPEC1, "fun x lo hi => min hi (max lo x)")
    r = k.prove("obj_eq", [a["o"], c["o"]], "funext x lo hi\nomega")
    assert r["accepted"], r
    alg = k.state().algebra
    assert alg.find(a["f"]) == alg.find(c["f"])          # congruence closure identifies the propositions


def _clamp_repo(tmp_path, body="min(max(x, lo), hi)"):
    repo = tmp_path / "repo"                                  # the event log lives outside the code
    repo.mkdir()
    (repo / "clamp.py").write_text(f"def clamp(x, lo, hi):\n    return {body}\n")
    (repo / ".gitignore").write_text("__pycache__/\n")
    for cmd in ("git init -q", "git add -A", "git -c user.name=t -c user.email=t@t commit -qm init"):
        subprocess.run(cmd.split(), cwd=repo, check=True)
    return str(repo)


CALL = binding("clamp({0}, {1}, {2})", "from clamp import clamp", ["nat", "nat", "nat"])


def test_chosen_check_compares_lean_with_running_code(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    cwd = _clamp_repo(tmp_path)
    good = k.ground_at(k.claim("clamp is bounded")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP, binding=CALL, cwd=cwd)
    r = k.observe_model(good["m"], [7, 2, 5], cwd)
    assert r["outcome"] == "agree" and r["lean"] == "5" and not r["duplicate"], r
    assert k.observe_model(good["m"], [7, 2, 5], cwd)["duplicate"]
    assert k.infer(good["m"])["lo"] > 0.75

    # the if/else term is a wrong model of this code: they differ when lo > hi
    bad = k.ground_at(k.claim("clamp is bounded (alt)")["h"], "clamp.py::clamp", FN, SPEC1, BOUND, binding=CALL, cwd=cwd)
    assert bad["m"] != good["m"]
    r = k.observe_model(bad["m"], [0, 5, 3], cwd)
    assert r["outcome"] == "disagree" and (r["lean"], r["code"]) == ("5", "3"), r
    assert k.infer(bad["m"])["hi"] == 0.0
    for wrong in ([1, 2], [-1, 2, 3], ["1/2", 2, 3], [True, 2, 3]):       # not values of the stated domains
        with pytest.raises(KernelError):
            k.observe_model(good["m"], wrong, cwd)


def test_what_a_model_hypothesis_claims_is_recorded_and_checked_when_stated(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    cwd = _clamp_repo(tmp_path)
    h = k.claim("clamp is bounded")["h"]
    a = k.ground_at(h, "clamp.py::clamp", FN, SPEC1, CLAMP, binding=CALL, cwd=cwd)
    assert k.status()["models"][a["m"]]["binding"] == CALL
    # another way of calling, or other domains, is another hypothesis about the same code and term
    wider = binding("clamp({0}, {1}, {2})", "from clamp import clamp", ["int", "nat", "nat"])
    assert k.ground_at(k.claim("c2")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP, binding=wider, cwd=cwd)["m"] != a["m"]
    # a model stated without a binding cannot be checked at all
    bare = k.ground_at(k.claim("c3")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP)
    with pytest.raises(KernelError):
        k.sample_model(bare["m"], cwd)
    # a binding whose setup does not even load is refused when stated
    with pytest.raises(KernelError):
        k.ground_at(k.claim("c4")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP, cwd=cwd,
                    binding=binding("clamp({0}, {1}, {2})", "from nowhere import clamp", ["nat"] * 3))
    for bad in (dict(call="clamp(1, 2, 3)", domains=["nat"]), dict(call="clamp({0})", domains=["real"]), dict(call="", domains=["nat"])):
        with pytest.raises(KernelError):
            binding(**bad)


def test_kernel_drawn_checks_with_real_lean(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    cwd = _clamp_repo(tmp_path)
    good = k.ground_at(k.claim("clamp is bounded")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP, binding=CALL, cwd=cwd)
    r = k.sample_model(good["m"], cwd, n=12, seed=1)
    assert r["agree"] == r["drawn"] == r["new"] and not r["disagreements"], r
    assert k.infer(good["m"])["lo"] == pytest.approx(0.75 * (r["drawn"] + 1) / (0.75 * (r["drawn"] + 1) + 0.25))
    assert k.sample_model(good["m"], cwd, n=12, seed=1)["new"] == 0       # same draws: same evidence
    # ...also when a second author states the same hypothesis and draws the same inputs
    other = Kernel(str(tmp_path / "e.db"), gate=LeanGate(), actor="someone else")
    again = other.ground_at(other.claim("clamp never leaves the range")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP, binding=CALL, cwd=cwd)
    assert again["m"] == good["m"] and other.sample_model(again["m"], cwd, n=12, seed=1)["new"] == 0

    # the if/else term agrees with this code only when lo <= hi; random draws find that out
    bad = k.ground_at(k.claim("clamp is bounded (alt)")["h"], "clamp.py::clamp", FN, SPEC1, BOUND, binding=CALL, cwd=cwd)
    r = k.sample_model(bad["m"], cwd, n=12, seed=1)
    assert r["disagreements"], r
    assert k.infer(bad["m"])["hi"] == 0.0


def test_code_that_raises_on_an_input_from_the_domain_disagrees_with_a_total_model(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    cwd = _clamp_repo(tmp_path, body="min(max(x, lo), hi) if lo <= hi else 1 // 0")
    m = k.ground_at(k.claim("clamp is bounded")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP, binding=CALL, cwd=cwd)["m"]
    assert k.observe_model(m, [3, 1, 5], cwd)["outcome"] == "agree"
    r = k.observe_model(m, [3, 5, 1], cwd)
    assert r["outcome"] == "disagree" and r["code"] == "!raised ZeroDivisionError", r


MATHLIB = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "experiments", "selfcheck", "lean")


@pytest.mark.skipif(not os.path.isdir(os.path.join(MATHLIB, ".lake", "packages", "mathlib")),
                    reason="needs the mathlib-backed Gamma (experiments/selfcheck/lean)")
def test_rational_and_list_arguments_are_compared_exactly(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate(MATHLIB))
    cwd = _clamp_repo(tmp_path)
    (tmp_path / "repo" / "avg.py").write_text("def spread(p):\n    return (min(p), sum(p) / len(p), [x * x for x in p])\n")
    b = binding("spread({0})", "from avg import spread", ["units"])
    m = k.ground_at(k.claim("spread")["h"], "avg.py::spread", "List ℚ → ℚ × ℚ × List ℚ", "fun f => True",
                    "fun p => (p.foldr min 1, p.sum / p.length, p.map fun x => x * x)", binding=b, cwd=cwd)["m"]
    r = k.sample_model(m, cwd, n=8, seed=2)
    assert "error" not in r and not r["disagreements"] and r["distribution"] == "units within 15", r
    assert k.observe_model(m, [["1/2", 1, "1/3"]], cwd)["outcome"] == "agree"
    # a float that is not the exact value disagrees
    (tmp_path / "repo" / "avg.py").write_text("def spread(p):\n    return (min(p), float(sum(p)) / len(p), [x * x for x in p])\n")
    m2 = k.ground_at(k.claim("spread, float")["h"], "avg.py::spread@v2", "List ℚ → ℚ × ℚ × List ℚ", "fun f => True",
                     "fun p => (p.foldr min 1, p.sum / p.length, p.map fun x => x * x)", binding=b, cwd=cwd)["m"]
    assert k.observe_model(m2, [["1/3", "1/3", "1/2"]], cwd)["outcome"] == "disagree"


def test_formal_claim_using_a_definition_from_gamma(tmp_path):
    """A named specification lives in Gamma; claims refer to it instead of translating a sentence."""
    from pw.lean_gate import LEAN_DIR
    lean_dir = tmp_path / "lean"
    shutil.copytree(LEAN_DIR, lean_dir, ignore=shutil.ignore_patterns(".lake", "PWCheck"))
    with open(lean_dir / "Gamma.lean", "a") as fh:
        fh.write("\nnamespace Spec\n/-- stays within [lo, hi] whenever lo ≤ hi -/\n"
                 "def Bounded (f : Nat → Nat → Nat → Nat) : Prop :=\n"
                 "  ∀ x lo hi, lo ≤ hi → lo ≤ f x lo hi ∧ f x lo hi ≤ hi\nend Spec\n")
    gate = LeanGate(str(lean_dir))
    assert gate.gamma() != LeanGate().gamma()             # a different Gamma, and the proofs say so
    k = Kernel(str(tmp_path / "e.db"), gate=gate)
    c = k.claim_formal("clamp.py::clamp", FN, "Spec.Bounded", gloss="clamp stays within [lo, hi]")
    a = k.attach_model(c["h"], CLAMP)
    r = k.prove("holds", [a["f"]], "show ∀ x lo hi, lo ≤ hi → lo ≤ min (max x lo) hi ∧ min (max x lo) hi ≤ hi\n"
                                   "intro x lo hi h\nomega")
    assert r["accepted"] and r["gamma"] == gate.gamma(), r
    assert k.infer(c["h"])["lo"] == pytest.approx(0.875)

    r = k.reject_object(c["p"], "fun x lo hi => hi + 1", "intro h\nhave := (h 0 0 0 (Nat.le_refl 0)).2\nexact absurd this (by decide)")
    assert r["accepted"], r
    assert not k.reject_object(c["p"], CLAMP, "intro h\nexact absurd (h 0 0 0 (Nat.le_refl 0)).2 (by decide)")["accepted"]   # clamp does satisfy it
    assert not LeanGate().check("holds", [("Prop", "Spec.Bounded (fun x lo hi => lo)")], "trivial")["ok"]  # unknown in the default Gamma


VALID = "fun f => ∀ i n, 0 < n → f i n < n"
SENTINEL = "fun f => ∀ i n, n ≤ i → f i n = n"


def test_past_decisions_are_held_against_the_code_as_it_is_now(tmp_path):
    """Sessions later, with no model in the loop: does a change contradict what was decided?"""
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    repo = tmp_path / "repo"
    repo.mkdir()
    code = repo / "indexing.py"
    write = lambda body: code.write_text(f"def clamp_index(i, n):\n    return {body}\n")
    git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a], cwd=repo, check=True, capture_output=True)
    write("min(i, max(n - 1, 0))")
    (repo / ".gitignore").write_text("__pycache__/\n")
    (repo / "test_indexing.py").write_text("from indexing import clamp_index\n\ndef test_last():\n    assert clamp_index(9, 4) == 3\n")
    git("init", "-q"); git("add", "-A"); git("commit", "-qm", "v1")
    cwd = str(repo)

    # the decision, established once
    d = k.claim_formal("indexing.py::clamp_index", "Nat → Nat → Nat", VALID, gloss="always a valid index")
    from pw.kernel import subject_id
    a = k.attach_model(d["h"], "fun i n => min i (n - 1)", subject_version=subject_id("indexing.py::clamp_index", cwd), cwd=cwd,
                       binding=binding("clamp_index({0}, {1})", "from indexing import clamp_index", ["nat", "nat"]))
    assert k.prove("holds", [a["f"]], "intro i n h\nomega")["accepted"]
    assert not k.sample_model(a["m"], cwd, n=25, seed=1)["disagreements"]
    k.observe_command(d["h"], "test", "python3 -m pytest -q test_indexing.py", cwd)
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "current" and r["lo"] > 0.99, r

    # a refactoring that keeps the behaviour: the old proof still applies, found mechanically
    write("i if i < n else max(n - 1, 0)")
    git("commit", "-qam", "refactor")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "re-established" and r["lo"] > 0.99, r

    # a change that breaks the decision, although the test suite still passes
    write("min(i, n)")
    (repo / "test_indexing.py").write_text("from indexing import clamp_index\n\ndef test_in_range():\n    assert clamp_index(2, 4) == 2\n")
    git("commit", "-qam", "return n when out of range")
    r = k.recheck(cwd)["decisions"][0]
    # what was learnt about earlier versions must not be mixed in: taken together, the refuted
    # model of this version and the supported models of the old ones say almost nothing
    mixed = k.infer(d["h"])
    assert mixed["hi"] - mixed["lo"] > 0.2 and mixed["hi"] > 0.99
    assert k.infer(d["h"], current=k.versions(cwd))["hi"] <= 0.75
    assert r["state"] == "uncovered" and r["lo"] <= 0.75 and r["counterexample"]["lean"] != r["counterexample"]["code"], r

    # a new decision that cannot hold together with the old one
    e = k.claim_formal("indexing.py::clamp_index", "Nat → Nat → Nat", SENTINEL, gloss="returns n when out of range")
    assert k.recheck(cwd)["conflicts"] == []
    proof = "intro f h\nhave a := h.1 1 1 (by decide)\nhave b := h.2 1 1 (Nat.le_refl 1)\nomega"
    assert k.prove("pred_disjoint", [d["p"], e["p"]], proof)["accepted"]
    c = k.recheck(cwd)["conflicts"]
    assert [(x["a"], x["b"]) for x in c] == [(d["h"], e["h"])]
    assert k.infer(f"{d['h']} & {e['h']}")["hi"] == 0.0
    assert not any("error" in x for x in k.recheck(cwd)["decisions"])
    k.withdraw(d["h"], "superseded: callers now detect overflow by the sentinel")
    rep = k.recheck(cwd)
    assert rep["conflicts"] == [] and [x["h"] for x in rep["decisions"]] == [e["h"]]


def test_a_formalization_that_is_not_lean_is_refused_when_stated(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    h = k.claim("f is nice")["h"]
    with pytest.raises(KernelError):
        k.ground(h, "f is nice")
    with pytest.raises(KernelError):
        k.ground_at(h, "f.py::f", "Nat → Nat", "fun f => ∀ n, n ≤ f n", "fun n => n + true")
    with pytest.raises(KernelError):
        k.claim_formal("f.py::f", "Nat → Nat", "Spec.DoesNotExist")
    assert k.state().links == []


def test_natural_language_claims_are_held_by_rerunning_their_checks(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "api.py").write_text("def tool(text):\n    return text\n")
    git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a], cwd=repo, check=True, capture_output=True)
    git("init", "-q"); git("add", "-A"); git("commit", "-qm", "v1")
    h = k.claim("no tool takes a probability as an argument")["h"]
    k.observe_command(h, "test", "! grep -q probability api.py", str(repo))
    r = k.recheck(str(repo))["decisions"]
    assert [(x["state"], x["natural_language"]) for x in r] == [("checks pass", True)] and r[0]["lo"] < 0.9
    (repo / "api.py").write_text("def tool(text, probability):\n    return text\n")
    git("commit", "-qam", "v2")
    r = k.recheck(str(repo))["decisions"][0]
    assert r["state"] == "checks fail" and r["lo"] < 0.5
