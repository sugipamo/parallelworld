"""Can a later change or a later decision be held against what was decided before?

    python -m experiments.decisions.run OUT_DIR

Session 1  A worker implements `clamp_index` and establishes the decision "always a valid index".
           Its branch is merged.
Later      Three edits are made to the merged code by hand, with no model in the loop, and
           `pw.check` is run after each:
             refactor   same behaviour, different code
             break      returns n when out of range, and the test suite is weakened so it passes
             (restore)
Session 2  Two workers get new decisions about the same function:
             sentinel   "returns n when the index is out of range"   (cannot hold with session 1's)
             identity   "returns the index unchanged when in range"  (can)
           `pw.check` is run again.
"""
import json
import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
T = "Nat → Nat → Nat"

GAMMA = '''
namespace Spec

/-- For a non-empty sequence the result is a valid index. -/
def ValidIndex (f : Nat → Nat → Nat) : Prop := ∀ i n, 0 < n → f i n < n

/-- An index past the end is reported by returning the length. -/
def OverflowSentinel (f : Nat → Nat → Nat) : Prop := ∀ i n, n ≤ i → f i n = n

/-- An index inside the sequence is returned unchanged. -/
def IdentityInRange (f : Nat → Nat → Nat) : Prop := ∀ i n, i < n → f i n = i

end Spec
'''

SESSION1 = [{"name": "s1-index", "requires": [
    {"subject": "indexing.py::clamp_index", "type": T, "predicate": "Spec.ValidIndex",
     "gloss": "for n > 0, clamp_index(i, n) is a valid index, i.e. < n"}],
    "prompt": "Create indexing.py with clamp_index(i, n) for natural numbers: limit i to a valid index of a "
              "sequence of length n (return 0 when n is 0). Add test_indexing.py runnable by "
              "`python3 -m pytest -q test_indexing.py`. Establish the required claim."}]

SESSION2 = [
    {"name": "s2-sentinel", "requires": [
        {"subject": "indexing.py::clamp_index", "type": T, "predicate": "Spec.OverflowSentinel",
         "gloss": "when i >= n, clamp_index(i, n) returns n so that callers can detect an out-of-range index"}],
     "prompt": "A caller wants to detect out-of-range indices. Change clamp_index in indexing.py so that it "
               "returns n whenever i >= n, update the tests, and establish the required claim."},
    {"name": "s2-identity", "requires": [
        {"subject": "indexing.py::clamp_index", "type": T, "predicate": "Spec.IdentityInRange",
         "gloss": "when i < n, clamp_index(i, n) returns i unchanged"}],
     "prompt": "Callers rely on clamp_index in indexing.py leaving in-range indices alone. Establish the "
               "required claim for the code as it is; change the code only if it does not already hold."},
]


def sh(*cmd, cwd, check=True):
    return subprocess.run(cmd, cwd=cwd, check=check, capture_output=True, text=True)


def orchestrate(repo, lean, tasks, tag):
    path = os.path.join(repo, ".pw", f"tasks-{tag}.json")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump(tasks, fh, ensure_ascii=False)
    r = subprocess.run([sys.executable, "-m", "pw.orchestrator", path, "--repo", repo, "--lean-dir", lean,
                        "--budget", "4", "--parallel", "2"], cwd=ROOT, capture_output=True, text=True)
    return r.stdout + r.stderr


def check(repo, lean):
    r = subprocess.run([sys.executable, "-m", "pw.check", "--repo", repo, "--lean-dir", lean],
                       cwd=ROOT, capture_output=True, text=True)
    return {"exit": r.returncode, "output": (r.stdout + r.stderr).strip()}


def reports(repo, tasks):
    out = {}
    for t in tasks:
        with open(os.path.join(repo, ".pw", f"worker-{t['name']}.json")) as fh:
            d = json.load(fh)
        out[t["name"]] = {"turns": d.get("num_turns"), "cost_usd": round(d.get("total_cost_usd", 0), 2),
                          "seconds": round(d.get("duration_ms", 0) / 1000), "report": d.get("result", "")}
    return out


def main():
    out = os.path.abspath(sys.argv[1])
    repo, lean = os.path.join(out, "repo"), os.path.join(out, "lean")
    shutil.rmtree(out, ignore_errors=True)
    os.makedirs(repo)
    shutil.copytree(os.path.join(ROOT, "lean"), lean, ignore=shutil.ignore_patterns(".lake", "PWCheck"))
    with open(os.path.join(lean, "Gamma.lean"), "a") as fh:
        fh.write(GAMMA)
    sh("git", "init", "-q", "-b", "main", cwd=repo)
    sh("git", "config", "user.name", "pw", cwd=repo)
    sh("git", "config", "user.email", "pw@localhost", cwd=repo)
    with open(os.path.join(repo, ".gitignore"), "w") as fh:
        fh.write(".pw/\n__pycache__/\n.pytest_cache/\n")
    sh("git", "add", "-A", cwd=repo)
    sh("git", "commit", "-qm", "init", cwd=repo)
    result = {}

    def step(name, value):
        result[name] = value
        with open(os.path.join(out, "result.json"), "w") as fh:
            json.dump(result, fh, ensure_ascii=False, indent=1)
        print("==", name, "\n" + (value["output"] if "output" in value else json.dumps(value, ensure_ascii=False)[:600]), flush=True)

    # session 1
    log = orchestrate(repo, lean, SESSION1, "s1")
    step("session1", {"output": log[log.find("MERGEABLE") if "MERGEABLE" in log else log.find("HOLD"):], "workers": reports(repo, SESSION1)})
    sh("git", "merge", "-q", "--no-edit", "pw/s1-index", cwd=repo)
    original = open(os.path.join(repo, "indexing.py")).read()
    tests = open(os.path.join(repo, "test_indexing.py")).read()
    step("check after merge", check(repo, lean))

    # later, by hand
    def edit(body, test=None):
        with open(os.path.join(repo, "indexing.py"), "w") as fh:
            fh.write(f'def clamp_index(i, n):\n    """Limit i to a valid index of a sequence of length n."""\n{body}')
        if test is not None:
            with open(os.path.join(repo, "test_indexing.py"), "w") as fh:
                fh.write(test)

    edit("    if n == 0:\n        return 0\n    return i if i < n else n - 1\n")
    step("check after refactor", check(repo, lean))
    edit("    return min(i, n)\n",
         "from indexing import clamp_index\n\n\ndef test_in_range():\n    assert clamp_index(0, 5) == 0\n    assert clamp_index(4, 5) == 4\n")
    step("check after breaking change", check(repo, lean))
    with open(os.path.join(repo, "indexing.py"), "w") as fh:
        fh.write(original)
    with open(os.path.join(repo, "test_indexing.py"), "w") as fh:
        fh.write(tests)
    step("check after restore", check(repo, lean))

    # session 2
    log = orchestrate(repo, lean, SESSION2, "s2")
    start = min([i for i in (log.find("MERGEABLE"), log.find("HOLD")) if i >= 0] or [0])
    step("session2", {"output": log[start:], "workers": reports(repo, SESSION2)})
    step("check after session 2", check(repo, lean))
    for b in ("pw/s2-sentinel", "pw/s2-identity"):
        step(f"diff {b}", {"output": sh("git", "diff", "--stat", f"main..{b}", cwd=repo, check=False).stdout})


if __name__ == "__main__":
    main()
