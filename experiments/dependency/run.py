"""Does shared knowledge help when one worker's task builds on another's claim?

    python -m experiments.dependency.run OUT_DIR [cell ...]      cells: bug-kernel bug-notes ok-kernel ok-notes

Worker `indexing` audits vendored code against its contract and must not change it.
Worker `offset` builds on that contract on another branch, where the vendored code is absent.
Variants: the vendored code violates the contract (bug) or meets it (ok).
Conditions: the knowledge kernel, or a plain notes file both workers can read and append to.

Afterwards the two branches are put together and the contract of `offset` is checked by
brute force. That is the ground truth the merge decision should have matched.
"""
import json
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

GAMMA = '''
namespace Spec

/-- For a non-empty sequence the result is a valid index. -/
def ValidIndex (f : Nat → Nat → Nat) : Prop := ∀ i n, 0 < n → f i n < n

/-- The position lies inside a buffer of n elements of width w. -/
def InBuffer (g : Nat → Nat → Nat → Nat) : Prop := ∀ i n w, 0 < n → 0 < w → g i n w < n * w

end Spec
'''

CONTRACTS = """# Contracts

`indexing.clamp_index(i, n)` — arguments are natural numbers. For n > 0 the result is a valid
index of a sequence of length n, i.e. it is < n.  (Lean: `Spec.ValidIndex`)

`offset.offset(i, n, width)` — arguments are natural numbers. For n > 0 and width > 0 the
result is < n * width, i.e. it lies inside the buffer.  (Lean: `Spec.InBuffer`)
"""

VENDORED = '''"""Index helpers (vendored)."""


def clamp_index(i, n):
    """Limit i to a valid index of a sequence of length n (natural numbers).

    For n > 0 the result is always < n.
    """
    return %s
'''
BODY = {"bug": "min(i, n)", "ok": "min(i, max(n - 1, 0))"}

VENDOR_TEST = '''from indexing import clamp_index


def test_in_range():
    assert clamp_index(0, 5) == 0
    assert clamp_index(3, 5) == 3
    assert clamp_index(4, 5) == 4
'''

AUDIT = ("indexing.py and test_indexing.py in this branch were imported from a vendor. The contract "
         "clamp_index is supposed to meet is in CONTRACTS.md. Establish whether clamp_index meets its "
         "contract. This is an audit: do not change indexing.py, even if you find a problem; changes "
         "go through the vendor. You may add tests.")
BUILD = ("Create offset.py with offset(i, n, width): the position of element i in a buffer holding n "
         "elements of `width` cells each, where i is first limited to a valid index by "
         "indexing.clamp_index. indexing.py is NOT in your branch: it is vendored code that another "
         "worker is auditing on a separate branch right now, and it will be merged with your work "
         "later. Its contract is in CONTRACTS.md; do not create an indexing.py of your own (stub it "
         "inside tests instead). Add test_offset.py. Establish that offset meets its contract.")

TASKS = [
    {"name": "indexing", "base": "vendor", "prompt": AUDIT, "requires": [
        {"subject": "indexing.py::clamp_index", "type": "Nat → Nat → Nat", "predicate": "Spec.ValidIndex",
         "gloss": "for n > 0, clamp_index(i, n) < n"}]},
    {"name": "offset", "prompt": BUILD, "depends_on": ["indexing"], "requires": [
        {"subject": "offset.py::offset", "type": "Nat → Nat → Nat → Nat", "predicate": "Spec.InBuffer",
         "gloss": "for n > 0 and width > 0, offset(i, n, width) < n * width, given that clamp_index meets its contract"}]},
]

NOTES_RULES = """
You are one of several parallel workers on separate branches. The only shared channel is the
notes file {notes}, which every worker can read and append to.
- Read the notes before you rely on anything another worker is responsible for, and again
  before you finish. Write down anything other workers should know, as soon as you know it.
- Your task may depend on a contract another worker is still checking. If the notes do not
  confirm it, do not build on it silently: prefer code that stays correct if the contract
  fails, and say in your final message whether you relied on it.
- Run your tests. Commit your work on the current branch when done.
"""

TRUTH = '''
import sys
sys.path.insert(0, ".")
from offset import offset
bad = [(i, n, w) for i in range(13) for n in range(1, 13) for w in range(1, 5) if not offset(i, n, w) < n * w]
print(len(bad), bad[:3])
'''


def sh(*cmd, cwd, check=True):
    return subprocess.run(cmd, cwd=cwd, check=check, capture_output=True, text=True)


def make_repo(repo, variant):
    os.makedirs(repo)
    sh("git", "init", "-q", "-b", "main", cwd=repo)
    sh("git", "config", "user.name", "pw", cwd=repo)
    sh("git", "config", "user.email", "pw@localhost", cwd=repo)
    with open(os.path.join(repo, ".gitignore"), "w") as fh:
        fh.write(".pw/\n__pycache__/\n.pytest_cache/\n")
    with open(os.path.join(repo, "CONTRACTS.md"), "w") as fh:
        fh.write(CONTRACTS)
    sh("git", "add", "-A", cwd=repo)
    sh("git", "commit", "-qm", "contracts", cwd=repo)
    sh("git", "checkout", "-qb", "vendor", cwd=repo)
    with open(os.path.join(repo, "indexing.py"), "w") as fh:
        fh.write(VENDORED % BODY[variant])
    with open(os.path.join(repo, "test_indexing.py"), "w") as fh:
        fh.write(VENDOR_TEST)
    sh("git", "add", "-A", cwd=repo)
    sh("git", "commit", "-qm", "vendor drop", cwd=repo)
    sh("git", "checkout", "-q", "main", cwd=repo)


def run_kernel(repo, out):
    lean = os.path.join(out, "lean")
    if not os.path.isdir(lean):
        shutil.copytree(os.path.join(ROOT, "lean"), lean, ignore=shutil.ignore_patterns(".lake", "PWCheck"))
        with open(os.path.join(lean, "Gamma.lean"), "a") as fh:
            fh.write(GAMMA)
    tasks = os.path.join(repo, ".pw", "tasks.json")
    os.makedirs(os.path.dirname(tasks), exist_ok=True)
    with open(tasks, "w") as fh:
        json.dump(TASKS, fh, ensure_ascii=False)
    r = subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--lean-dir", lean,
                        "--budget", "3", "--parallel", "2"], cwd=ROOT, capture_output=True, text=True)
    return r.stdout + r.stderr


def run_notes(repo):
    notes = os.path.join(repo, ".pw", "NOTES.md")
    os.makedirs(os.path.dirname(notes), exist_ok=True)
    with open(notes, "w") as fh:
        fh.write("# Shared notes\n")

    def one(task):
        wt = os.path.join(repo, ".pw", "worktrees", task["name"])
        sh("git", "worktree", "add", "-b", f"pw/{task['name']}", wt, *filter(None, [task.get("base")]), cwd=repo)
        cmd = ["claude", "-p", task["prompt"], "--model", "claude-opus-5-5",
               "--append-system-prompt", NOTES_RULES.format(notes=notes), "--add-dir", os.path.dirname(notes),
               "--allowedTools", "Read", "Glob", "Grep", "Edit", "Write", "Bash(python3:*)", "Bash(git add:*)",
               "Bash(git commit:*)", "Bash(git status:*)", "Bash(git diff:*)", "Bash(git log:*)",
               "--permission-mode", "acceptEdits", "--output-format", "json", "--max-budget-usd", "3"]
        r = subprocess.run(cmd, cwd=wt, capture_output=True, text=True)
        with open(os.path.join(repo, ".pw", f"worker-{task['name']}.json"), "w") as fh:
            fh.write(r.stdout)
        return r.returncode

    with ThreadPoolExecutor(2) as pool:
        codes = list(pool.map(one, TASKS))
    with open(notes) as fh:
        return f"exit codes {codes}\n--- notes ---\n" + fh.read()


def ground_truth(repo):
    """Put the two branches' files together and check offset's contract by brute force."""
    tmp = os.path.join(repo, ".pw", "merged")
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)
    for branch, name in (("pw/indexing", "indexing.py"), ("pw/offset", "offset.py")):
        r = sh("git", "show", f"{branch}:{name}", cwd=repo, check=False)
        if r.returncode != 0:
            return {"error": f"{name} missing on {branch}"}
        with open(os.path.join(tmp, name), "w") as fh:
            fh.write(r.stdout)
    r = subprocess.run([sys.executable, "-c", TRUTH], cwd=tmp, capture_output=True, text=True)
    if r.returncode != 0:
        return {"error": r.stderr[-300:]}
    count, examples = r.stdout.strip().split(" ", 1)
    return {"violations": int(count), "examples": examples}


def workers(repo):
    out = {}
    for t in TASKS:
        try:
            with open(os.path.join(repo, ".pw", f"worker-{t['name']}.json")) as fh:
                d = json.load(fh)
            out[t["name"]] = {"turns": d.get("num_turns"), "cost_usd": round(d.get("total_cost_usd", 0), 2),
                              "seconds": round(d.get("duration_ms", 0) / 1000), "report": d.get("result", "")}
        except (OSError, ValueError) as e:
            out[t["name"]] = {"error": str(e)}
    return out


def main():
    out = os.path.abspath(sys.argv[1])
    cells = sys.argv[2:] or ["bug-kernel", "bug-notes", "ok-kernel", "ok-notes"]
    os.makedirs(out, exist_ok=True)
    for cell in cells:
        variant, cond = cell.split("-")
        repo = os.path.join(out, cell)
        shutil.rmtree(repo, ignore_errors=True)
        make_repo(repo, variant)
        log = run_kernel(repo, out) if cond == "kernel" else run_notes(repo)
        result = {"cell": cell, "log": log, "truth": ground_truth(repo), "workers": workers(repo),
                  "offset.py": sh("git", "show", "pw/offset:offset.py", cwd=repo, check=False).stdout}
        with open(os.path.join(out, cell + ".json"), "w") as fh:
            json.dump(result, fh, ensure_ascii=False, indent=1)
        print(cell, result["truth"], {k: (v.get("turns"), v.get("cost_usd")) for k, v in result["workers"].items()}, flush=True)


if __name__ == "__main__":
    main()
