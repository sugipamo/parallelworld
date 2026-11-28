"""`pw check` run on a repository, for tests: what it prints is printed, and it says whether anything needs attention."""
import subprocess

from .core import LEAN_DIR, pw_binary
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
