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

from .check import FACTS, show
from .kernel import LOG, Kernel, _sha
from .lean_gate import LEAN_DIR, LeanGate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PROMPT = """Some content changed or was never read, and what it says has to be stated (again). Do not change any file.

For each item below, read the place named and write what it says as a Lean term of the given type.
Write what that place itself says. Do not consult other files, other sections or the code to fill it
in or to correct it: if the place does not say it, or says something unexpected, write that.
"""

DECISIONS = """
Decisions (a file must satisfy a specification). State the content with `model(h, object)`, leaving out
setup, call and domains unless the file is code you can call. Then prove `holds [F]` for the proposition
`model` returns, or `not [F]` if the file as it is now does not satisfy the specification.
"""

PLACES = """
Facts (one thing stated in several places). State what the place says with
`read_place(h, place, object, quote)`, where `quote` is the sentence or table row of the place that
says it, copied word for word. Nothing has to be proved: the kernel compares the places itself.
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
    kernel = Kernel(os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor="maintain")

    if os.path.exists(os.path.join(repo, FACTS)):
        kernel.sync_facts(os.path.join(repo, FACTS))
    report = kernel.recheck(repo)
    decisions = [d for d in report["decisions"] if d["state"] in ("stale", "unsupported") and "subject" in d]
    places = [(d, u["at"]) for d in report["decisions"] if "fact" in d
              for u in d.get("unread", []) if "has no reader" in u["why"] or "read" in u["why"]]
    st = kernel.state()
    places = [(d, at) for d, at in places if not next(p for p in st.facts[d["h"]]["places"] if p["at"] == at)["reader"]]
    if decisions or places:
        dirty = subprocess.run(["git", "status", "--porcelain", "--", ".", f":(exclude){LOG}"], cwd=repo, capture_output=True, text=True).stdout.strip()
        if dirty:
            show(report, args.threshold)
            sys.exit("\nCommit the changes first: an agent reads the files as they are committed.")
        prompt = PROMPT
        if decisions:
            prompt += DECISIONS
            for d in decisions:
                pred = st.algebra.preds[st.formal[d["h"]]["pred"]]
                prompt += (f'- {d["h"]}: {d["subject"].split("@")[0]} must satisfy `{pred["text"]}` — {d["text"]}\n'
                           f'  type of the term: {pred["type"]}\n')
        if places:
            prompt += PLACES
            for d, at in places:
                prompt += f'- {d["h"]}, place `{at}`: {d["text"]} — a term of type {st.facts[d["h"]]["type"]}\n'
        name = "maintain-" + _sha(report["tree"], *[d["h"] for d in decisions], *[at for _, at in places])[:6]
        tasks = os.path.join(repo, ".pw", f"tasks-{name}.json")
        os.makedirs(os.path.dirname(tasks), exist_ok=True)
        with open(tasks, "w") as fh:
            json.dump([{"name": name, "prompt": prompt, "requires": []}], fh, ensure_ascii=False)
        print(f"{len(decisions)} decision(s) and {len(places)} place(s) need reading; asking an agent ({name})", flush=True)
        subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--lean-dir", args.lean_dir,
                        "--model", args.model, "--budget", str(args.budget), "--parallel", "1"],
                       cwd=ROOT, capture_output=True, text=True)
        report = kernel.recheck(repo)
    sys.exit(1 if show(report, args.threshold) else 0)


if __name__ == "__main__":
    main()
