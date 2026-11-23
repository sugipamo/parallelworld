#!/bin/bash
# Apply the kernel to claims about its own mathematics.  usage: run.sh OUT_DIR
# Works on a clone, so the worktrees and branches the workers create stay out of this checkout.
# Needs experiments/selfcheck/lean built first:  (cd experiments/selfcheck/lean && lake update && lake exe cache get && lake build)
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
OUT=$(mkdir -p "$1" && cd "$1" && pwd)
rm -rf "$OUT/repo"
git clone -q "$ROOT" "$OUT/repo"
git -C "$OUT/repo" config user.name pw
git -C "$OUT/repo" config user.email pw@localhost
cd "$ROOT"
python3 -m pw.orchestrator experiments/selfcheck/tasks.json --repo "$OUT/repo" \
  --lean-dir experiments/selfcheck/lean --budget 6 --parallel 3
