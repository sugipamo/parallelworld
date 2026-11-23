"""Runs the real Lean kernel. Skipped when Lean is not installed."""
import os
import shutil
import subprocess

import pytest

from pw.kernel import Kernel
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


def test_model_check_compares_lean_with_running_code(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    repo = tmp_path / "repo"                                  # the event log lives outside the code
    repo.mkdir()
    (repo / "clamp.py").write_text("def clamp(x, lo, hi):\n    return min(max(x, lo), hi)\n")
    (repo / ".gitignore").write_text("__pycache__/\n")       # caches must not look like a changed tree
    for cmd in ("git init -q", "git add -A", "git -c user.name=t -c user.email=t@t commit -qm init"):
        subprocess.run(cmd.split(), cwd=repo, check=True)
    tmp_path = repo
    run = lambda *a: f'python3 -c "from clamp import clamp; print(clamp{a})"'
    good = k.ground_at(k.claim("clamp is bounded")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP)
    r = k.observe_model(good["m"], "7 2 5", run(7, 2, 5), str(tmp_path))
    assert r["outcome"] == "agree" and r["lean"] == "5" and not r["duplicate"], r
    assert k.observe_model(good["m"], "7 2 5", run(7, 2, 5), str(tmp_path))["duplicate"]
    assert k.infer(good["m"])["lo"] > 0.75

    # the if/else term is a wrong model of this code: they differ when lo > hi
    bad = k.ground_at(k.claim("clamp is bounded (alt)")["h"], "clamp.py::clamp", FN, SPEC1, BOUND)
    r = k.observe_model(bad["m"], "0 5 3", run(0, 5, 3), str(tmp_path))
    assert r["outcome"] == "disagree" and (r["lean"], r["code"]) == ("5", "3"), r
    assert k.infer(bad["m"])["hi"] < 0.75
    assert "error" in k.observe_model(good["m"], "true", run(1, 2, 3), str(tmp_path))   # ill-typed input
