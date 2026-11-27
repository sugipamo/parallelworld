"""Hold every declared fact against the files as they are now: the Rust build's `pw check`.

    python -m pw.check [--repo DIR] [--facts PATH] [--db PATH] [--lean-dir DIR] [--verify]
                       [--unconfirmed warn] [--lean always] [--json] [--needs-lean] [--record]

The facts are those declared in the repository's pw-facts.json; the record is its pw-log.jsonl.
No model is consulted: places read by a pattern are computed again, the values are compared (Lean
settles what has to be worked out), and the project's rules (pw-rules.json) say whether each
reading stands. Exit status 1 if anything needs attention, 2 if the check could not be made.

Checking only looks: what it works out is not written to the record, unless --record asks for it.
This module only runs the Rust build (rust/target/release/pw, or PW_BIN); see pw/core.py.
"""
import os
import subprocess
import sys

from .core import FACTS, LEAN_DIR, missing, pw_binary  # noqa: F401  (FACTS: the name of a project's declaration)
from .kernel import KernelError


def run(repo, record, lean_dir=LEAN_DIR, verify=False, unconfirmed="fail", keep=False, lean="needed", as_json=False):
    """Hold the facts of `repo` against its files and print where they stand. True if anything needs attention."""
    args = ["check", "--repo", repo, "--db", record, "--lean-dir", lean_dir, "--unconfirmed", unconfirmed, "--lean", lean]
    args += ["--verify"] * verify + ["--record"] * keep + ["--json"] * as_json
    r = subprocess.run([pw_binary(), *args], capture_output=True, text=True)
    print(r.stdout, end="", flush=True)
    if r.returncode == 2:
        raise KernelError(r.stderr.strip().removeprefix("pw: "))
    return r.returncode == 1


def main():
    try:
        os.execv(pw_binary(), [pw_binary(), "check", *sys.argv[1:]])
    except FileNotFoundError:
        sys.exit(f"pw: {missing()}")


if __name__ == "__main__":
    main()
