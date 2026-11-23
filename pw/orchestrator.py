"""Run Claude Code workers in parallel, one git worktree each, sharing one kernel.

    python -m pw.orchestrator tasks.json [--dry-run] [--model claude-opus-5-5]

tasks.json: [{"name": "parser", "prompt": "...", "requires": [<claim>, ...]}, ...]
A required claim is best given formally, so that nothing has to be translated:
    {"subject": "clamp.py::clamp", "type": "Nat → Nat → Nat → Nat", "predicate": "Spec.Bounded",
     "gloss": "clamp stays within [lo, hi]"}
where the predicate may use definitions from Gamma (--lean-dir). A plain string is also accepted
and is treated as a natural-language claim the worker must formalize.
Optional per task: "base" (branch to start the worktree from) and "depends_on" (names of tasks
whose required claims this task builds on).
A task's branch is reported mergeable only if every required claim has lo >= --threshold and,
when it depends on other tasks, the conjunction with their claims does too (assume-guarantee).
"""
import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

from .kernel import Kernel, KernelError
from .lean_gate import LEAN_DIR, LeanGate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

WORKER_RULES = """
You are one of several parallel workers. Shared knowledge lives in the `pw` MCP server.
- Before relying on anything another worker may have established, call `status` / `infer`.
- Gather evidence for every required claim with `observe_command` (the kernel runs the check;
  you do not report results yourself).
- A required claim given with an id (H:...) is FORMAL: its predicate is fixed. Write the code,
  give a Lean term modelling it with `model`, prove `holds`, support the model with
  `sample_model`, and try to break it with `check_model` on edge cases.
- A required claim given only as a sentence, and any claim of your own: register it with
  `claim`, connect it with `ground_at` (subject, object, predicate), prove it, check the model
  the same way, and show the predicate is not vacuous with `reject_object`.
- A failed proof proves nothing; do not treat it as evidence. If a claim is false, show it:
  prove `not [F]` for a faithful model, or find the input where model and code part ways.
- Claims listed under "Depends on" belong to other workers. Check them with `infer` before you
  rely on them and again before you finish. If the lower bound is low, do not build on the
  claim silently: prefer code that stays correct if the claim fails, and say in your final
  message whether you relied on it.
- Claims listed under "Past decisions" were settled earlier about the same code and still
  stand. Before you change anything, decide for each whether your required claim can hold
  together with it. If it cannot, prove that with `pred_disjoint [P_past, P_yours]` and STOP:
  do not change the code, and say in your final message that the decisions contradict each
  other; a person has to choose. If your claim follows from a past decision, or implies it,
  you may record that with `pred_implies`.
- If `status` shows another worker's specification or object that you believe is the same as
  yours, try `pred_iff` / `obj_eq`. Only prove what is true: different code is usually a
  different object even when it meets the same specification.
- Never state probabilities. Commit your work on the current branch when done.
"""


def required(kernel, task):
    """[(H id, description)] for a task, registering formal claims on the way."""
    out = []
    for c in task.get("requires", []):
        if isinstance(c, str):
            out.append((kernel.claim(c)["h"], c))
        else:
            h = kernel.claim_formal(c["subject"], c["type"], c["predicate"], c.get("gloss", ""))["h"]
            p = kernel.state().formal[h]["pred"]
            out.append((h, f'{h} (formal, specification {p}): {c["subject"]} satisfies `{c["predicate"]}` : ({c["type"]}) → Prop'
                           + (f' — {c["gloss"]}' if c.get("gloss") else "")))
    return out


def run_task(task, args, repo):
    name = task["name"]
    wt = os.path.join(repo, ".pw", "worktrees", name)
    cfg_path = os.path.join(repo, ".pw", f"mcp-{name}.json")
    cfg = {"mcpServers": {"pw": {
        "command": sys.executable, "args": ["-m", "pw.mcp_server"],
        "env": {"PW_DB": args.db, "PW_AGENT": name, "PW_WORKDIR": wt, "PYTHONPATH": ROOT,
                "PW_LEAN_DIR": args.lean_dir},
    }}}
    prompt = task["prompt"] + "\n\nRequired claims:\n" + "\n".join(f"- {d}" for _, d in task["_required"])
    if task["_past"]:
        prompt += "\n\nPast decisions (settled earlier, about the same code):\n" + "\n".join(f"- {d}" for d in task["_past"])
    if task["_depends"]:
        prompt += "\n\nDepends on (claims owned by other workers):\n" + "\n".join(f"- {d}" for _, d in task["_depends"])
    cmd = [
        "claude", "-p", prompt, "--model", args.model,
        "--append-system-prompt", WORKER_RULES,
        "--mcp-config", cfg_path, "--strict-mcp-config",
        "--allowedTools", *args.allow, "--permission-mode", "acceptEdits",
        "--output-format", "json", "--max-budget-usd", str(args.budget),
    ]
    if args.dry_run:
        return name, 0, " ".join(cmd[:1] + ["-p", "<prompt>"] + cmd[3:])
    os.makedirs(os.path.dirname(cfg_path), exist_ok=True)
    with open(cfg_path, "w") as fh:
        json.dump(cfg, fh)
    if not os.path.isdir(wt):
        subprocess.run(["git", "worktree", "add", "-b", f"pw/{name}", wt, *filter(None, [task.get("base")])],
                       cwd=repo, check=True)
    r = subprocess.run(cmd, cwd=wt, capture_output=True, text=True)
    with open(os.path.join(repo, ".pw", f"worker-{name}.json"), "w") as fh:
        fh.write(r.stdout)
    try:
        out = json.loads(r.stdout)
        summary = f"turns={out.get('num_turns')} cost=${out.get('total_cost_usd', 0):.2f}\n{out.get('result', '')}"
    except ValueError:
        summary = (r.stdout + r.stderr)[-2000:]
    return name, r.returncode, summary


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tasks")
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--model", default="claude-opus-5-5")
    ap.add_argument("--threshold", type=float, default=0.9)
    ap.add_argument("--budget", type=float, default=5.0, help="USD cap per worker")
    ap.add_argument("--parallel", type=int, default=4)
    ap.add_argument("--allow", nargs="+", default=[
        "mcp__pw", "Read", "Glob", "Grep", "Edit", "Write",
        "Bash(git add:*)", "Bash(git commit:*)", "Bash(git status:*)", "Bash(git diff:*)", "Bash(git log:*)",
    ], help="tools workers may use without prompting; checks run through the kernel, not Bash")
    ap.add_argument("--lean-dir", default=LEAN_DIR, help="Lean project whose Gamma.lean holds the shared definitions")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    args.lean_dir = os.path.abspath(args.lean_dir)
    args.db = os.path.join(os.path.abspath(args.repo), ".pw", "events.db")
    with open(args.tasks) as fh:
        tasks = json.load(fh)

    kernel = Kernel(args.db, gate=LeanGate(args.lean_dir), actor="orchestrator")
    before = set(kernel.state().formal)      # decisions that stood before this run
    for task in tasks:
        task["_required"] = required(kernel, task)
    st = kernel.state()
    for task in tasks:
        mine = {h for h, _ in task["_required"]}
        subjects = {st.formal[h]["subject"] for h in mine if h in st.formal}
        task["_past"] = [f'{h}: {st.formal[h]["subject"]} satisfies `{st.algebra.preds[st.formal[h]["pred"]]["text"]}` '
                         f'(specification {st.formal[h]["pred"]}) — {st.atoms[h]["text"]}'
                         for h in st.formal if h in before and h not in mine and h not in st.withdrawn
                         and st.formal[h]["subject"] in subjects]
    by_name = {t["name"]: t for t in tasks}
    for task in tasks:
        task["_depends"] = [c for d in task.get("depends_on", []) for c in by_name[d]["_required"]]

    with ThreadPoolExecutor(args.parallel) as pool:
        for name, rc, out in pool.map(lambda t: run_task(t, args, os.path.abspath(args.repo)), tasks):
            print(f"== {name}: exit {rc}\n{out}\n")
    if args.dry_run:
        return

    for task in tasks:
        verdicts = []
        current = kernel.versions(os.path.join(os.path.abspath(args.repo), ".pw", "worktrees", task["name"]))

        def judge(query, text):
            try:
                b = kernel.infer(query, current=current)     # the code as it is on this task's branch
                verdicts.append((b["lo"] >= args.threshold, b["lo"], b["hi"], text))
            except KernelError as e:      # e.g. it contradicts a decision that is established
                verdicts.append((False, 0.0, 1.0, f"{text}\n       cannot be evaluated: {e}"))

        for h, text in task["_required"]:
            judge(h, text)
        if task["_depends"]:
            judge(" & ".join(h for h, _ in task["_required"] + task["_depends"]),
                  "together with what it depends on: " + ", ".join(h for h, _ in task["_depends"]))
        ok = all(v[0] for v in verdicts)
        print(f"{'MERGEABLE' if ok else 'HOLD     '} pw/{task['name']}")
        for good, lo, hi, text in verdicts:
            print(f"   {'ok ' if good else 'low'} [{lo:.3f}, {hi:.3f}] {text}")


if __name__ == "__main__":
    main()
