"""How far do decisions written in natural language fit into the kernel?

    python -m experiments.nl.run OUT_DIR formalize     three workers, kept apart, formalize the same decisions
    python -m experiments.nl.run OUT_DIR judge         one worker relates their formalizations with Lean
    python -m experiments.nl.run OUT_DIR summary       tabulate

The decisions are real ones from this project (docs/spec.md, docs/symbols.md), plus one that is
false of the code (N9) and two that pull against each other (N7, N8).
Needs experiments/selfcheck/lean built (Gamma with mathlib).
"""
import json
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN = os.path.join(ROOT, "experiments", "selfcheck", "lean")
AUTHORS = ["f1", "f2", "f3"]

DECISIONS = {
    "N1": "The lower Fréchet bound never exceeds the product of the probabilities, and the product never exceeds their minimum.",
    "N2": "Random checks that agree never make a model hypothesis less credible, however many of them there are.",
    "N3": "A single disagreement between a model and the code refutes the model hypothesis.",
    "N4": "The same evidence counts once, no matter how many agents report it.",
    "N5": "Agents never state probabilities; all numbers come from the catalog.",
    "N6": "A failed proof attempt is not evidence of anything.",
    "N7": "Independence between pieces of evidence is never assumed.",
    "N8": "Evidence that has been declared independent is combined by multiplying likelihoods.",
    "N9": "The kernel never executes commands supplied by an agent.",
    "N10": "The merge threshold should be strict enough to be safe without blocking useful work.",
    "N11": "Keep the trusted part of the system small enough for one person to read.",
    "N12": "Checking past decisions must be fast enough to run on every commit.",
}

FORMALIZE = """This repository is a knowledge kernel (see README.md, docs/spec.md, pw/). Below are decisions
recorded for this project in natural language. Your job is to find out how far each one can be put
into the kernel, and to be exact about what gets lost on the way. Work alone.

For each decision, choose the strongest of these that is honestly possible:
- "lean": it can be stated as a Lean proposition (Mathlib is available) about a mathematical model of
  the code or of the concept. Register it with `claim` (the exact sentence) and connect it with
  `ground` (a closed proposition) or `ground_at` (subject, type, predicate, object). The kernel refuses
  text Lean does not accept. Proving is optional: try `prove` once if the proof looks short.
- "check": it cannot sensibly be stated in Lean, but a command can hold it against the code. Register
  it with `claim` and record the command with `observe_command` (kind "test"); the command must fail
  when the decision is violated. Use only standard tools (python3, grep, ...), run from the repository root.
- "none": neither is possible without inventing content the sentence does not have.

Then write the file formalizations.json in the repository root:
{"decisions": [{"id": "N1", "kind": "lean" | "check" | "none",
                "lean": {"form": "closed", "prop": "..."} or
                        {"form": "at", "subject": "...", "type": "...", "predicate": "...", "object": "..."} or null,
                "command": "..." or null,
                "left_out": "what the sentence says or implies that your formalization does not capture",
                "added": "what your formalization fixes that the sentence leaves open",
                "holds": true | false | null   (does the decision hold of the code as it is, as far as you can tell)}],
 "contradictions": [{"ids": ["N?", "N?"], "why": "...", "shown_in_kernel": true | false}]}
List under "contradictions" any decisions that cannot all hold, or that the code contradicts. Commit the file.

Decisions:
"""

JUDGE = """Three authors, kept apart, each formalized the same natural-language decisions in Lean (Mathlib is
available). Your job is to establish, with the Lean kernel as the judge, how their formalizations of
each decision relate. Do not judge which one is right.

For each decision below and each pair of authors who gave a Lean formalization:
1. Register both: `claim` with the decision's sentence, then `ground` (form "closed") or `ground_at`
   (form "at"). For form "at" the proposition is the predicate applied to the object.
2. Relate the two PROPOSITIONS with `prove`: try `iff`; failing that `implies` in each direction.
   If both are form "at" with the same type, also try `pred_iff` on the predicates.
3. Record one of: "equivalent", "a_implies_b", "b_implies_a" (only one direction proved),
   "different_shape" (they are not about the same kind of thing, so no relation can even be stated
   usefully), "unrelated_proved" (both proved true or false independently, so `iff` would say nothing
   about sameness: say so), "undecided".
Spend effort in proportion: a few `prove` attempts per pair, then move on.

Write comparisons.json in the repository root and commit it:
{"comparisons": [{"id": "N1", "a": "f1", "b": "f2", "relation": "...", "accepted_by_lean": true | false,
                  "note": "what differs between the two, in one sentence"}]}

Formalizations:
"""


def clone(dest):
    shutil.rmtree(dest, ignore_errors=True)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    subprocess.run(["git", "clone", "-q", ROOT, dest], check=True)
    for k, v in (("user.name", "pw"), ("user.email", "pw@localhost")):
        subprocess.run(["git", "config", k, v], cwd=dest, check=True)


def orchestrate(repo, name, prompt, budget):
    tasks = os.path.join(repo, ".pw", "tasks.json")
    os.makedirs(os.path.dirname(tasks), exist_ok=True)
    with open(tasks, "w") as fh:
        json.dump([{"name": name, "prompt": prompt, "requires": []}], fh, ensure_ascii=False)
    r = subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--lean-dir", LEAN,
                        "--budget", str(budget), "--parallel", "1"], cwd=ROOT, capture_output=True, text=True)
    return r.stdout + r.stderr


def load(repo, name, filename):
    path = os.path.join(repo, ".pw", "worktrees", name, filename)
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError) as e:
        return {"error": str(e)}


def worker(repo, name):
    try:
        with open(os.path.join(repo, ".pw", f"worker-{name}.json")) as fh:
            d = json.load(fh)
        return {"turns": d.get("num_turns"), "cost_usd": round(d.get("total_cost_usd", 0), 2),
                "seconds": round(d.get("duration_ms", 0) / 1000), "report": d.get("result", "")}
    except (OSError, ValueError) as e:
        return {"error": str(e)}


def formalize(out):
    prompt = FORMALIZE + "\n".join(f"- {k}: {v}" for k, v in DECISIONS.items())

    def one(author):
        repo = os.path.join(out, author, "repo")
        clone(repo)
        orchestrate(repo, "formalize", prompt, 8)
        return author, {"formalizations": load(repo, "formalize", "formalizations.json"), "worker": worker(repo, "formalize")}

    with ThreadPoolExecutor(3) as pool:
        result = dict(pool.map(one, AUTHORS))
    with open(os.path.join(out, "formalizations.json"), "w") as fh:
        json.dump(result, fh, ensure_ascii=False, indent=1)
    for a, r in result.items():
        ds = r["formalizations"].get("decisions", [])
        print(a, r["worker"].get("turns"), r["worker"].get("cost_usd"), {d["id"]: d["kind"] for d in ds})


def judge(out):
    with open(os.path.join(out, "formalizations.json")) as fh:
        result = json.load(fh)
    lines = []
    for nid, text in DECISIONS.items():
        forms = []
        for a in AUTHORS:
            for d in result[a]["formalizations"].get("decisions", []):
                if d["id"] == nid and d.get("kind") == "lean" and d.get("lean"):
                    forms.append(f"  {a}: {json.dumps(d['lean'], ensure_ascii=False)}")
        if len(forms) >= 2:
            lines.append(f"{nid}: {text}\n" + "\n".join(forms))
    repo = os.path.join(out, "judge", "repo")
    clone(repo)
    orchestrate(repo, "judge", JUDGE + "\n\n".join(lines), 10)
    res = {"comparisons": load(repo, "judge", "comparisons.json"), "worker": worker(repo, "judge")}
    sys.path.insert(0, ROOT)
    from pw.kernel import LOG, Kernel
    res["proofs"] = [{"relation": e["relation"], "args": e["args"]} for e in Kernel(os.path.join(repo, LOG)).events() if e["type"] == "proof"]
    with open(os.path.join(out, "comparisons.json"), "w") as fh:
        json.dump(res, fh, ensure_ascii=False, indent=1)
    print(res["worker"].get("turns"), res["worker"].get("cost_usd"), len(res["proofs"]), "proofs accepted")
    for c in res["comparisons"].get("comparisons", []):
        print(c["id"], c["a"], c["b"], c["relation"], c.get("accepted_by_lean"))


def summary(out):
    with open(os.path.join(out, "formalizations.json")) as fh:
        result = json.load(fh)
    for nid, text in DECISIONS.items():
        print(f"\n{nid}: {text}")
        for a in AUTHORS:
            for d in result[a]["formalizations"].get("decisions", []):
                if d["id"] == nid:
                    body = d.get("lean") or d.get("command")
                    print(f"  {a} [{d['kind']}] holds={d.get('holds')} :: {json.dumps(body, ensure_ascii=False)[:300]}")
                    print(f"      left out: {str(d.get('left_out'))[:260]}")
                    print(f"      added:    {str(d.get('added'))[:260]}")
    for a in AUTHORS:
        print(a, "contradictions:", json.dumps(result[a]["formalizations"].get("contradictions"), ensure_ascii=False)[:900])


if __name__ == "__main__":
    {"formalize": formalize, "judge": judge, "summary": summary}[sys.argv[2]](os.path.abspath(sys.argv[1]))
