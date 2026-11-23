"""Decisions about a file that is not code: the kernel's own likelihood table, pw/catalog.json.

    python -m experiments.artifacts.run OUT_DIR

Decision: in every kind of evidence, the likelihoods given "true" sum to 1, and so do those given "false".

Path A  an agent reads the file and states it as a Lean term; when the file changes, `pw.maintain`
        has an agent read it again.
Path B  a recorded reader computes the term; when the file changes, `pw.check` recomputes it and
        tries the stored proof again. No agent at any point.

Both paths see the same two edits: one that keeps the decision true, one that breaks it.
"""
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
from pw.kernel import Kernel, reader  # noqa: E402
from pw.lean_gate import LeanGate  # noqa: E402

TABLE = "List (String × List (String × Nat × Nat))"
GAMMA = '''
namespace Spec

/-- A table of evidence kinds; each lists its outcomes with the likelihood of the outcome if the
target is true and if it is false, in thousandths. Both columns of every kind sum to 1. -/
def Likelihoods (c : List (String × List (String × Nat × Nat))) : Prop :=
  ∀ k ∈ c, (k.2.map (fun o => o.2.1)).foldr (· + ·) 0 = 1000 ∧ (k.2.map (fun o => o.2.2)).foldr (· + ·) 0 = 1000

end Spec
'''
DECISION = {"subject": "pw/catalog.json::evidence", "type": TABLE, "predicate": "Spec.Likelihoods",
            "gloss": "for every kind of evidence, the likelihoods given true sum to 1 and so do those given false"}
READ = ('"[" + ", ".join("(" + lean_string(k) + ", [" + ", ".join("(" + lean_string(o) + ", " + str(permille(v[0])) + ", " '
        '+ str(permille(v[1])) + ")" for o, v in sorted(e["outcomes"].items())) + "])" for k, e in sorted(data["evidence"].items())) + "]"')
TASK = [{"name": "read-catalog", "requires": [DECISION],
         "prompt": "pw/catalog.json holds the likelihood table of a knowledge kernel. Establish the required claim about "
                   "its `evidence` section. The file is data, not code you can call: state the table as a Lean term with "
                   "`model` (no setup, call or domains), writing each number as a whole number of thousandths "
                   "(0.95 becomes 950), and prove the claim. Do not change the file."}]
EDITS = [("retune test: columns still sum to 1", "test", {"pass": [0.90, 0.40], "fail": [0.10, 0.60]}),
         ("retune property_test: the false column now sums to 1.1", "property_test", {"pass": [0.90, 0.25], "fail": [0.10, 0.85]})]


def sh(*cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, check=True, capture_output=True, text=True)


def setup(out, name):
    repo = os.path.join(out, name)
    os.makedirs(os.path.join(repo, "pw"))
    shutil.copy(os.path.join(ROOT, "pw", "catalog.json"), os.path.join(repo, "pw", "catalog.json"))
    with open(os.path.join(repo, ".gitignore"), "w") as fh:
        fh.write(".pw/\n")
    sh("git", "init", "-q", "-b", "main", cwd=repo)
    sh("git", "config", "user.name", "pw", cwd=repo)
    sh("git", "config", "user.email", "pw@localhost", cwd=repo)
    sh("git", "add", "-A", cwd=repo)
    sh("git", "commit", "-qm", "catalog", cwd=repo)
    return repo


def edit(repo, message, kind, outcomes):
    path = os.path.join(repo, "pw", "catalog.json")
    with open(path) as fh:
        data = json.load(fh)
    data["evidence"][kind]["outcomes"] = outcomes
    with open(path, "w") as fh:
        json.dump(data, fh, indent=2, ensure_ascii=False)
    sh("git", "commit", "-qam", message, cwd=repo)


def run(module, repo, lean, *extra):
    r = subprocess.run([sys.executable, "-m", module, "--repo", repo, "--lean-dir", lean, *extra], cwd=ROOT, capture_output=True, text=True)
    return {"exit": r.returncode, "output": (r.stdout + r.stderr).strip()}


def workers(repo):
    out = {}
    for f in sorted(os.listdir(os.path.join(repo, ".pw"))):
        if f.startswith("worker-"):
            with open(os.path.join(repo, ".pw", f)) as fh:
                d = json.load(fh)
            out[f[7:-5]] = {"turns": d.get("num_turns"), "cost_usd": round(d.get("total_cost_usd", 0), 2),
                            "seconds": round(d.get("duration_ms", 0) / 1000), "report": d.get("result", "")}
    return out


def main():
    out = os.path.abspath(sys.argv[1])
    shutil.rmtree(out, ignore_errors=True)
    os.makedirs(out)
    lean = os.path.join(out, "lean")
    shutil.copytree(os.path.join(ROOT, "lean"), lean, ignore=shutil.ignore_patterns(".lake", "PWCheck"))
    with open(os.path.join(lean, "Gamma.lean"), "a") as fh:
        fh.write(GAMMA)
    result = {"A": {}, "B": {}}

    def step(path, name, value):
        result[path][name] = value
        with open(os.path.join(out, "result.json"), "w") as fh:
            json.dump(result, fh, ensure_ascii=False, indent=1)
        print(f"== {path}: {name} (exit {value.get('exit', '-')})\n{value.get('output', '')}\n", flush=True)

    # ---- path B: a reader, no agent
    repo = setup(out, "reader")
    k = Kernel(os.path.join(repo, ".pw", "events.db"), gate=LeanGate(lean), actor="setup")
    d = k.claim_formal(DECISION["subject"], TABLE, DECISION["predicate"], DECISION["gloss"])
    a = k.attach_derived(d["h"], reader(READ), repo)
    step("B", "proof", {"output": json.dumps(k.prove("holds", [a["f"]], "unfold Spec.Likelihoods\ndecide"))})
    step("B", "check", run("pw.check", repo, lean))
    for i, (message, kind, outcomes) in enumerate(EDITS, 1):
        edit(repo, message, kind, outcomes)
        step("B", f"check after edit {i}: {message}", run("pw.check", repo, lean))
    derived = k.state().algebra.objs[a["o"]]["text"]

    # ---- path A: an agent reads
    repo = setup(out, "agent")
    tasks = os.path.join(repo, ".pw", "tasks.json")
    os.makedirs(os.path.dirname(tasks))
    with open(tasks, "w") as fh:
        json.dump(TASK, fh, ensure_ascii=False)
    r = subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--lean-dir", lean, "--budget", "3"],
                       cwd=ROOT, capture_output=True, text=True)
    step("A", "agent reads the file", {"output": r.stdout[r.stdout.find("MERGEABLE") if "MERGEABLE" in r.stdout else r.stdout.find("HOLD"):].strip()})
    step("A", "check", run("pw.check", repo, lean))
    k = Kernel(os.path.join(repo, ".pw", "events.db"), gate=LeanGate(lean), actor="person")
    st = k.state()
    said = [st.algebra.objs[info["obj"]]["text"] for info in st.models.values()]
    rows = lambda t: sorted(re.findall(r'\("[a-z_]+", \d+, \d+\)', t))
    step("A", "the agent's reading against the reader's", {"output": json.dumps({
        "same rows": bool(said) and rows(said[-1]) == rows(derived), "rows": len(rows(derived)), "same text": bool(said) and said[-1] == derived})})
    for m in st.models:
        k.sign_off(m, "reviewer")
    step("A", "check after a person confirms the reading", run("pw.check", repo, lean))
    for i, (message, kind, outcomes) in enumerate(EDITS, 1):
        edit(repo, message, kind, outcomes)
        step("A", f"check after edit {i}: {message}", run("pw.check", repo, lean))
        step("A", f"maintain after edit {i}", run("pw.maintain", repo, lean))
    result["A"]["workers"] = workers(repo)
    with open(os.path.join(out, "result.json"), "w") as fh:
        json.dump(result, fh, ensure_ascii=False, indent=1)
    print({w: (v["turns"], v["cost_usd"], v["seconds"]) for w, v in result["A"]["workers"].items()})


if __name__ == "__main__":
    main()
