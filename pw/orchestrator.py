"""Run Claude Code workers in parallel, one git worktree each, sharing one kernel.

    python -m pw.orchestrator tasks.json [--dry-run] [--model claude-opus-5-5]

tasks.json: [{"name": "parser", "prompt": "...", "requires": ["<claim text>", ...]}, ...]
A task's branch is reported mergeable only if every required claim has lo >= --threshold.
"""
import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

from .kernel import Kernel
from .lean_gate import LeanGate

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

WORKER_RULES = """
You are one of several parallel workers. Shared knowledge lives in the `pw` MCP server.
- Before relying on anything another worker may have established, call `status` / `infer`.
- For each claim listed under "Required claims", call `claim` with the EXACT text, then gather
  evidence with `observe_command` (the kernel runs the check; you do not report results yourself).
- Where a claim has precise mathematical content, connect it to Lean with `ground_at` (object +
  predicate) and try `prove`. A failed proof proves nothing; do not treat it as evidence.
- If `status` shows another worker's specification or object that you believe is the same as
  yours, try `pred_iff` / `obj_eq`. Only prove what is true: different code is usually a
  different object even when it meets the same specification.
- Never state probabilities. Commit your work on the current branch when done.
"""


def run_task(task, args, repo):
    name = task["name"]
    wt = os.path.join(repo, ".pw", "worktrees", name)
    cfg_path = os.path.join(repo, ".pw", f"mcp-{name}.json")
    cfg = {"mcpServers": {"pw": {
        "command": sys.executable, "args": ["-m", "pw.mcp_server"],
        "env": {"PW_DB": args.db, "PW_AGENT": name, "PW_WORKDIR": wt, "PYTHONPATH": ROOT},
    }}}
    prompt = task["prompt"] + "\n\nRequired claims:\n" + "\n".join(f"- {c}" for c in task.get("requires", []))
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
        subprocess.run(["git", "worktree", "add", "-b", f"pw/{name}", wt], cwd=repo, check=True)
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
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()
    args.db = os.path.join(os.path.abspath(args.repo), ".pw", "events.db")
    with open(args.tasks) as fh:
        tasks = json.load(fh)

    with ThreadPoolExecutor(args.parallel) as pool:
        for name, rc, out in pool.map(lambda t: run_task(t, args, os.path.abspath(args.repo)), tasks):
            print(f"== {name}: exit {rc}\n{out}\n")
    if args.dry_run:
        return

    kernel = Kernel(args.db, gate=LeanGate())
    for task in tasks:
        verdicts = []
        for text in task.get("requires", []):
            b = kernel.infer(kernel.claim(text)["h"])
            verdicts.append((b["lo"] >= args.threshold, b["lo"], b["hi"], text))
        ok = all(v[0] for v in verdicts)
        print(f"{'MERGEABLE' if ok else 'HOLD     '} pw/{task['name']}")
        for good, lo, hi, text in verdicts:
            print(f"   {'ok ' if good else 'low'} [{lo:.3f}, {hi:.3f}] {text}")


if __name__ == "__main__":
    main()
