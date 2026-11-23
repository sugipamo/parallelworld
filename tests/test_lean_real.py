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
    from pw.kernel import _tree
    assert k.infer(d["h"], current=k.versions(cwd))["hi"] < 0.95 < mixed["hi"]          # no longer "possibly established"
    assert k.infer(d["h"], current=k.versions(cwd), tree=_tree(cwd))["hi"] <= 0.75      # and with only this tree's test runs
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


TABLE = "List (String × List (String × Nat × Nat))"
SUMS = "fun c => ∀ k ∈ c, (k.2.map (fun o => o.2.1)).foldr (· + ·) 0 = 1000 ∧ (k.2.map (fun o => o.2.2)).foldr (· + ·) 0 = 1000"
READ = ('"[" + ", ".join("(" + lean_string(k) + ", [" + ", ".join("(" + lean_string(o) + ", " + str(permille(v[0])) + ", " '
        '+ str(permille(v[1])) + ")" for o, v in sorted(e["outcomes"].items())) + "])" for k, e in sorted(data["evidence"].items())) + "]"')


def _config_repo(tmp_path):
    import json
    repo = tmp_path / "repo"
    repo.mkdir()
    def write(test_pass, test_fail):
        (repo / "catalog.json").write_text(json.dumps({"evidence": {
            "test": {"outcomes": {"pass": test_pass, "fail": test_fail}},
            "review": {"outcomes": {"agree": [0.8, 0.35], "disagree": [0.2, 0.65]}}}}))
    write([0.95, 0.4], [0.05, 0.6])
    git = lambda *a: subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", *a], cwd=repo, check=True, capture_output=True)
    git("init", "-q"); git("add", "-A"); git("commit", "-qm", "v1")
    return str(repo), write, git


def test_a_file_that_is_not_code_read_by_a_reader_is_carried_over_or_found_violated(tmp_path):
    """Nobody is asked what the file says: the term is recomputed and the stored proof tried again."""
    from pw.kernel import reader
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    cwd, write, git = _config_repo(tmp_path)
    d = k.claim_formal("catalog.json::evidence", TABLE, SUMS, gloss="each column of likelihoods sums to 1")
    a = k.attach_derived(d["h"], reader(READ), cwd)
    assert k.state().algebra.objs[a["o"]]["text"].startswith('[("review", [("agree", 800, 350)')
    assert k.prove("holds", [a["f"]], "decide")["accepted"]
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "current" and r["lo"] == pytest.approx(0.99), r

    write([0.9, 0.3], [0.1, 0.7]); git("commit", "-qam", "retune, columns still sum to 1")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "re-established" and r["lo"] == pytest.approx(0.99), r

    write([0.9, 0.4], [0.05, 0.6]); git("commit", "-qam", "retune, first column now sums to 0.95")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "violated" and r["hi"] < 0.05, r

    write([0.9, 0.3], [0.1, 0.7]); git("commit", "-qam", "back")
    assert k.recheck(cwd)["decisions"][0]["state"] == "current"
    write([0.9005, 0.3], [0.0995, 0.7]); git("commit", "-qam", "a value the reader cannot represent")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "unsupported" and "thousandths" in r["error"], r


def test_a_file_read_by_an_agent_goes_stale_when_it_changes(tmp_path):
    from pw.kernel import subject_id
    k = Kernel(str(tmp_path / "e.db"), gate=LeanGate())
    cwd, write, git = _config_repo(tmp_path)
    d = k.claim_formal("catalog.json::evidence", TABLE, SUMS)
    said = '[("review", [("agree", 800, 350), ("disagree", 200, 650)]), ("test", [("fail", 50, 600), ("pass", 950, 400)])]'
    a = k.attach_model(d["h"], said, subject_version=subject_id("catalog.json::evidence", cwd))
    assert k.prove("holds", [a["f"]], "decide")["accepted"]
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "current" and r["lo"] == pytest.approx(0.875), r      # proved, but only an agent says what the file contains
    with pytest.raises(KernelError):
        k.sample_model(a["m"], cwd)                                             # nothing to run
    k.sign_off(a["m"], "reviewer")
    assert k.recheck(cwd)["decisions"][0]["lo"] > 0.98                          # a person compared the reading with the file

    write([0.9, 0.4], [0.05, 0.6]); git("commit", "-qam", "changed")
    r = k.recheck(cwd)["decisions"][0]
    assert r["state"] == "stale" and r["lo"] == pytest.approx(0.5), r           # the old reading, proof and sign-off say nothing now


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
    from pw.kernel import reader
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
              {"at": "k.py::K.__init__", "reader": reader('lean_string(re.search(r\'dependence="(\\w+)"\', part).group(1))', "text")}]
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
    from pw.kernel import reader
    log = tmp_path / "pw-log.jsonl"
    (tmp_path / "k.py").write_text('LIMIT = 14\n')
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    cwd = str(tmp_path)
    places = ["doc.md::Limits", {"at": "k.py::LIMIT", "reader": reader('re.search(r"= (\\d+)", part).group(1)', "text")}]
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
    f = next(f for gs, hh, f in st.links if hh == h)
    fake = {"ts": 0, "actor": "x", "type": "proof", "relation": "not", "args": [f], "proof": "decide", "proof_sha": "x", "axioms": [], "gamma": "x"}
    log.write_text("\n".join(lines + [json.dumps(fake)]) + "\n")
    refused = Kernel(str(log), gate=LeanGate()).verify()
    assert [r["relation"] for r in refused] == ["not"], refused

    log.write_text("\n".join(lines) + "\nnot json\n")
    with pytest.raises(KernelError):
        Kernel(str(log), gate=LeanGate()).state()


def test_a_fact_keeps_its_readings_when_its_declaration_changes(tmp_path):
    """How a place is read, or which places are listed, can change without the fact becoming another one."""
    from pw.kernel import pattern, reader
    k = Kernel(str(tmp_path / "e.jsonl"), gate=LeanGate())
    (tmp_path / "doc.md").write_text("## Limits\n\nAt most 14 atoms.\n")
    (tmp_path / "k.py").write_text("LIMIT = 14\n")
    (tmp_path / "c.txt").write_text("limit: 14\n")
    cwd = str(tmp_path)
    h = k.claim_fact("limit", "Nat", ["doc.md::Limits", {"at": "k.py::LIMIT", "reader": reader('re.search(r"= (\\d+)", part).group(1)', "text")}])["h"]
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
    """Write what pw.calibrate would: for each model, how many of 27 planted changes it read
    (and, of 27 decoys, how many it declined). With keep, the runs are added to those there."""
    import json
    from pw.kernel import INSTRUCTIONS
    path = os.path.join(cwd, "pw-calibration.json")
    runs = json.load(open(path)) if keep and os.path.exists(path) else []
    runs += [{"model": m, "instructions": instructions or INSTRUCTIONS, "planted": {"n": 27, "read": k, "stuck": 27 - k},
              "decoys": {"n": 27, "accepted": 27 - k}} for m, k in readers.items()]
    with open(path, "w") as fh:
        json.dump(runs, fh)


def test_a_reading_stands_by_the_rules_not_by_a_number(tmp_path):
    import json
    from pw.kernel import pattern
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
    from pw.kernel import pattern
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


def test_a_small_place_is_shown_with_what_surrounds_it(tmp_path):
    from pw.kernel import context
    (tmp_path / "rules.json").write_text('{"note": "readers", "bar": {"read at least": 0.85, "stuck at most": 0.15}, "rows": [["a"]]}')
    (tmp_path / "app.py").write_text("# how many atoms a component may have\nLIMIT = 14\n\ndef f():\n    return LIMIT\n")
    (tmp_path / "doc.md").write_text("# Doc\n\n## Limits\n\n" + "A long section. " * 30 + "\n")
    cwd = str(tmp_path)
    around = context("rules.json::bar.read at least", cwd)
    assert '"read at least": 0.85' in around and '"stuck at most": 0.15' in around and "note" not in around   # the enclosing object
    assert "how many atoms" in context("app.py::LIMIT", cwd) and "def f" in context("app.py::LIMIT", cwd)    # the lines around it
    assert context("doc.md::Limits", cwd) is None and context("app.py", cwd) is None                         # big enough, or whole
    assert context("missing.json::a", cwd) is None
