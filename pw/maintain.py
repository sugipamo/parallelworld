"""Keep the decisions true of the files as they change.

    python -m pw.maintain [--repo DIR] [--lean-dir DIR] [--threshold 0.9] [--model ...] [--budget 3]

One round of the loop that managing a project comes down to:

  1. hold every decision against the files as they are (what `pw.check` does, mechanically);
  2. where a file changed and only an agent's reading connected it to its decision, have an
     agent read it again and prove the decision again, or prove that it no longer holds;
  3. hold everything against the files once more and report.

What is left after that is for a person: decisions that are violated or contradict each other,
and readings nobody has confirmed. Exit status 1 if anything is left.
"""
import argparse
import json
import os
import subprocess
import sys

from .check import show
from .kernel import Kernel, _sha
from .lean_gate import LEAN_DIR, LeanGate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PROMPT = """Some files changed, and the decisions below were tied to them only by an agent's reading of the
earlier version. Read each file as it is now and state it again. Do not change any file.

For each decision:
1. Read the file. Write its content, as far as the decision is concerned, as a Lean term of the
   given type, and state it with `model(h, object)`. Leave out setup, call and domains unless the
   file is code you can call. Be faithful to the file, not to the decision: write what is there.
2. Prove `holds [F]` for the proposition F that `model` returns. If the file as it is now does not
   satisfy the specification, prove `not [F]` instead.
3. In your final message say, for each decision, whether it still holds.

Decisions:
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--threshold", type=float, default=0.9)
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--budget", type=float, default=3.0)
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(os.path.join(repo, ".pw", "events.db"), gate=LeanGate(args.lean_dir), actor="maintain")

    report = kernel.recheck(repo)
    todo = [d for d in report["decisions"] if d["state"] in ("stale", "unsupported") and not d.get("natural_language")]
    if todo:
        dirty = subprocess.run(["git", "status", "--porcelain"], cwd=repo, capture_output=True, text=True).stdout.strip()
        if dirty:
            show(report, args.threshold)
            sys.exit("\nCommit the changes first: an agent reads the files as they are committed.")
        st = kernel.state()
        lines = []
        for d in todo:
            pred = st.algebra.preds[st.formal[d["h"]]["pred"]]
            old = [st.algebra.objs[st.models[x]["obj"]]["text"] for gs, hh, _ in st.links if hh == d["h"] for x in gs if x[0] == "M"]
            lines.append(f'- {d["h"]}: {d["subject"].split("@")[0]} must satisfy `{pred["text"]}` — {d["text"]}\n'
                         f'  type of the term: {pred["type"]}\n'
                         + (f'  the earlier version was read as: {old[-1]}\n' if old else ""))
        name = "maintain-" + _sha(report["tree"], *[d["h"] for d in todo])[:6]
        tasks = os.path.join(repo, ".pw", f"tasks-{name}.json")
        with open(tasks, "w") as fh:
            json.dump([{"name": name, "prompt": PROMPT + "\n".join(lines), "requires": []}], fh, ensure_ascii=False)
        print(f"{len(todo)} decision(s) need a file read again; asking an agent ({name})", flush=True)
        subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--lean-dir", args.lean_dir,
                        "--model", args.model, "--budget", str(args.budget), "--parallel", "1"],
                       cwd=ROOT, capture_output=True, text=True)
        report = kernel.recheck(repo)
    sys.exit(1 if show(report, args.threshold) else 0)


if __name__ == "__main__":
    main()
