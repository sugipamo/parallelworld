"""Runs the real Lean kernel. Skipped when Lean is not installed."""
import os
import shutil

import pytest

from pw.kernel import Kernel
from pw.lean_gate import LeanGate

LAKE = os.environ.get("PW_LAKE") or shutil.which("lake")
pytestmark = pytest.mark.skipif(not LAKE, reason="Lean not installed (set PW_LAKE)")

COMM = "∀ a b : Nat, a + b = b + a"


@pytest.fixture(scope="module")
def gate():
    return LeanGate()


def test_accepts_valid_proofs(gate):
    v = gate.check("holds", [COMM], "intro a b\nexact Nat.add_comm a b")
    assert v["ok"] and v["axioms"] == [], v
    v = gate.check("iff", [COMM, "∀ x y : Nat, y + x = x + y"],
                   "constructor\n· intro h x y\n  exact h y x\n· intro h a b\n  exact h b a")
    assert v["ok"], v
    assert gate.check("not", ["(1 : Nat) < 1"], "decide")["ok"]
    assert gate.check("implies", ["∀ n : Nat, n < 5", "(3 : Nat) < 5"], "intro h\nexact h 3")["ok"]
    assert gate.check("contradiction", ["(1 : Nat) = 2", "True"], "intro h\nexact absurd h.1 (by decide)")["ok"]


def test_classical_axioms_are_reported_and_allowed(gate):
    v = gate.check("holds", ["∀ p : Prop, p ∨ ¬p"], "intro p\nexact Classical.em p")
    assert v["ok"] and "Classical.choice" in v["axioms"], v


def test_rejects_wrong_and_incomplete_proofs(gate):
    assert not gate.check("holds", ["∀ a b : Nat, a + b = a"], "intro a b\nrfl")["ok"]
    assert not gate.check("holds", [COMM], "intro a b")["ok"]            # unsolved goal
    assert not gate.check("iff", ["(1 : Nat) = 1", "(1 : Nat) = 2"], "decide")["ok"]
    assert not gate.check("holds", ["this is not lean"], "trivial")["ok"]


@pytest.mark.parametrize("proof", [
    "exact sorryAx _",                                    # sorry without the keyword
    "exact sorryAx _ false",
    "exact (Lean.ofReduceBool true true rfl ▸ trivial)",  # native axiom
    "exact Lean.trustCompiler ▸ trivial",
])
def test_rejects_unapproved_axioms(gate, proof):
    assert not gate.check("holds", ["(1 : Nat) = 2"], proof)["ok"]


def test_forged_axiom_report_is_not_believed(gate):
    forged = "trace \"'pw_goal' does not depend on any axioms\"\nexact sorryAx _"
    v = gate.check("holds", ["(1 : Nat) = 2"], forged)
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
