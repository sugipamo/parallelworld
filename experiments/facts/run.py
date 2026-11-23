"""Run the loop on this repository's own facts (pw-facts.json), on a clone.

    python -m experiments.facts.run OUT_DIR

  1. check      what can be settled mechanically
  2. maintain   an agent reads the prose places
  3. confirm    a person confirms the agent's readings
  4. edits      one place changes; then everything follows; then a code-only drift
"""
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

EDITS = [
    ("one section changes its mind about the default",
     [("docs/spec.md", "既定の `pqd` は正の依存で、独立と完全な重複の間。", "既定の `frechet` は依存について何も仮定しない。")]),
    ("the other places follow",
     [("docs/spec.md", "`independent` / `comonotone` / `pqd`（既定）/ `frechet`", "`independent` / `comonotone` / `pqd` / `frechet`（既定）"),
      ("docs/symbols.md", "| `pqd`（既定） |", "| `pqd` |"),
      ("docs/symbols.md", "| `frechet` | W ≤ C ≤ M |", "| `frechet`（既定） | W ≤ C ≤ M |"),
      ("pw/kernel.py", 'max_atoms=14, dependence="pqd"', 'max_atoms=14, dependence="frechet"')]),
    ("one command gets a different default threshold",
     [("pw/maintain.py", '"--threshold", type=float, default=0.9', '"--threshold", type=float, default=0.8')]),
]


def sh(*cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, check=True, capture_output=True, text=True)


def run(module, repo, *extra):
    r = subprocess.run([sys.executable, "-m", module, "--repo", repo, *extra], cwd=ROOT, capture_output=True, text=True)
    return {"exit": r.returncode, "output": (r.stdout + r.stderr).strip()}


def main():
    out = os.path.abspath(sys.argv[1])
    repo = os.path.join(out, "repo")
    shutil.rmtree(out, ignore_errors=True)
    os.makedirs(out)
    sh("git", "clone", "-q", ROOT, repo, cwd=ROOT)
    sh("git", "config", "user.name", "pw", cwd=repo)
    sh("git", "config", "user.email", "pw@localhost", cwd=repo)
    result = {}

    def step(name, value):
        result[name] = value
        with open(os.path.join(out, "result.json"), "w") as fh:
            json.dump(result, fh, ensure_ascii=False, indent=1)
        print(f"== {name} (exit {value['exit']})\n{value['output']}\n", flush=True)

    def settle(label):
        """One round as a project would run it: check; if places need reading, maintain; confirm; check."""
        step(f"{label}: check", run("pw.check", repo))
        if "pw.maintain" in result[f"{label}: check"]["output"]:
            step(f"{label}: maintain", run("pw.maintain", repo))
        listing = run("pw.confirm", repo)
        todo = re.findall(r"^(M:\w+)  ", listing["output"], re.M)
        if todo:
            step(f"{label}: readings a person has to confirm", listing)
            step(f"{label}: confirmed", run("pw.confirm", repo, "--who", "reviewer", *todo))
            step(f"{label}: check after confirming", run("pw.check", repo))

    settle("as it is")
    for label, edits in EDITS:
        for path, old, new in edits:
            with open(os.path.join(repo, path), encoding="utf-8") as fh:
                text = fh.read()
            assert text.count(old) == 1, (path, old)
            with open(os.path.join(repo, path), "w", encoding="utf-8") as fh:
                fh.write(text.replace(old, new))
        sh("git", "commit", "-qam", label, cwd=repo)
        settle(label)

    workers = {}
    for f in sorted(os.listdir(os.path.join(repo, ".pw"))):
        if f.startswith("worker-"):
            with open(os.path.join(repo, ".pw", f)) as fh:
                d = json.load(fh)
            workers[f[7:-5]] = {"turns": d.get("num_turns"), "cost_usd": round(d.get("total_cost_usd", 0), 2),
                                "seconds": round(d.get("duration_ms", 0) / 1000), "report": d.get("result", "")}
    result["workers"] = workers
    with open(os.path.join(out, "result.json"), "w") as fh:
        json.dump(result, fh, ensure_ascii=False, indent=1)
    print({w: (v["turns"], v["cost_usd"], v["seconds"]) for w, v in workers.items()})


if __name__ == "__main__":
    main()
