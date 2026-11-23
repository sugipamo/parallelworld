"""Runs the real Lean kernel. Skipped when Lean is not installed."""
import os
import shutil
import subprocess

import pytest

from pw.kernel import Conflict, Kernel, KernelError
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


def test_kernel_drawn_checks_with_real_lean(tmp_path):
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "clamp.py").write_text("def clamp(x, lo, hi):\n    return min(max(x, lo), hi)\n")
    (repo / ".gitignore").write_text("__pycache__/\n")
    for cmd in ("git init -q", "git add -A", "git -c user.name=t -c user.email=t@t commit -qm init"):
        subprocess.run(cmd.split(), cwd=repo, check=True)
    template = 'python3 -c "from clamp import clamp; print(clamp({0}, {1}, {2}))"'

    good = k.ground_at(k.claim("clamp is bounded")["h"], "clamp.py::clamp", FN, SPEC1, CLAMP)
    r = k.sample_model(good["m"], template, str(repo), n=12, seed=1)
    assert r["agree"] == r["drawn"] == r["new"] and not r["disagreements"], r
    assert k.infer(good["m"])["lo"] == pytest.approx(0.75 * (r["drawn"] + 1) / (0.75 * (r["drawn"] + 1) + 0.25))
    assert k.sample_model(good["m"], template, str(repo), n=12, seed=1)["new"] == 0   # same draws: same evidence

    # the if/else term agrees with this code only when lo <= hi; random draws find that out
    bad = k.ground_at(k.claim("clamp is bounded (alt)")["h"], "clamp.py::clamp", FN, SPEC1, BOUND)
    r = k.sample_model(bad["m"], template, str(repo), n=12, seed=1)
    assert r["disagreements"], r
    assert k.infer(bad["m"])["hi"] == 0.0

    with pytest.raises(KernelError):
        other = k.ground_at(k.claim("p")["h"], "x", "Bool → Bool", "fun f => True", "fun b => b")
        k.sample_model(other["m"], "echo {0}", str(repo))
    assert "disagree" not in str(k.sample_model(good["m"], template, str(repo), n=5, seed=3, domains=["nat"] * 3)["disagreements"])


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
    a = k.attach_model(d["h"], "fun i n => min i (n - 1)", subject_version=subject_id("indexing.py::clamp_index", cwd))
    assert k.prove("holds", [a["f"]], "intro i n h\nomega")["accepted"]
    template = 'python3 -c "from indexing import clamp_index; print(clamp_index({0}, {1}))"'
    assert not k.sample_model(a["m"], template, cwd, n=25, seed=1)["disagreements"]
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
    assert r["state"] == "broken" and r["lo"] <= 0.75 and r["counterexample"]["lean"] != r["counterexample"]["code"], r

    # a new decision that cannot hold together with the old one
    e = k.claim_formal("indexing.py::clamp_index", "Nat → Nat → Nat", SENTINEL, gloss="returns n when out of range")
    assert k.recheck(cwd)["conflicts"] == []
    proof = "intro f h\nhave a := h.1 1 1 (by decide)\nhave b := h.2 1 1 (Nat.le_refl 1)\nomega"
    assert k.prove("pred_disjoint", [d["p"], e["p"]], proof)["accepted"]
    c = k.recheck(cwd)["conflicts"]
    assert [(x["a"], x["b"]) for x in c] == [(d["h"], e["h"])]
    with pytest.raises(Conflict):                 # one is established, so the other cannot even sit at its base rate
        k.infer(f"{d['h']} & {e['h']}")
    assert all("error" in x for x in k.recheck(cwd)["decisions"])
    k.withdraw(d["h"], "superseded: callers now detect overflow by the sentinel")
    rep = k.recheck(cwd)
    assert rep["conflicts"] == [] and [x["h"] for x in rep["decisions"]] == [e["h"]]
