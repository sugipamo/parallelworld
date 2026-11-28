"""How long does a check take as the number of facts grows?

    python experiments/scale/run.py [--sizes 5 20 50] [--lean always|needed] [--out FILE]

A repository is made up with N facts, each stated in a code file (read by a pattern) and in
a table of a document (read by a pattern). Timed, each in a fresh process, as `python -m
pw.check` would run:

  cold     no record yet: every equation is put to Lean
  warm     the record holds the proofs (after `pw.check --record`): nothing is put to Lean
  verify   warm, with --verify: every recorded proof is run through Lean again (what CI does)
  one      warm, after one value was changed in one place: one new equation

With --lean always (as these were first measured) every comparison is put to Lean; with
--lean needed (the default since 0.10) written-out values are compared as they stand, and
nothing here is put to Lean at all.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def make(n):
    repo = tempfile.mkdtemp(prefix="pw-scale-")
    with open(os.path.join(repo, "k.py"), "w") as fh:
        fh.write("".join(f"LIMIT_{i} = {100 + i}\n" for i in range(n)))
    with open(os.path.join(repo, "doc.md"), "w") as fh:
        fh.write("## Limits\n\n| name | value |\n|---|---|\n" + "".join(f"| limit {i} | {100 + i} |\n" for i in range(n)))
    facts = [{"name": f"limit {i}", "type": "Nat", "places": [
        {"at": "k.py", "read": {"find": f"^LIMIT_{i} = (\\d+)", "as": "nat"}},
        {"at": "doc.md::Limits", "read": {"find": f"\\| limit {i} \\| (\\d+) \\|", "as": "nat"}}]} for i in range(n)]
    with open(os.path.join(repo, "pw-facts.json"), "w") as fh:
        json.dump(facts, fh)
    return repo


LEAN = "always"


def check(repo, *args):
    t = time.time()
    r = subprocess.run([sys.executable, "-m", "pw.check", "--repo", repo, "--unconfirmed", "warn", "--lean", LEAN, *args],
                       capture_output=True, text=True, env={**os.environ, "PYTHONPATH": ROOT})
    return round(time.time() - t, 1), r.returncode, r.stdout


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", type=int, nargs="+", default=[5, 20, 50])
    ap.add_argument("--lean", choices=("always", "needed"), default="always")
    ap.add_argument("--out")
    args = ap.parse_args()
    global LEAN
    LEAN = args.lean
    rows = []
    print(f"{'facts':>6}{'cold':>9}{'warm':>9}{'verify':>9}{'one':>9}   seconds")
    for n in args.sizes:
        repo = make(n)
        try:
            cold, code, out = check(repo)
            assert code == 0 and out.count("WARN current") == n, out[-400:]
            check(repo, "--record")
            warm, code, _ = check(repo)
            verify, code2, out = check(repo, "--verify")
            proofs = n if LEAN == "always" else 0
            assert code == 0 and code2 == 0 and f"{proofs} recorded proof(s) verified again, 0 refused" in out, out[-300:]
            with open(os.path.join(repo, "k.py")) as fh:
                text = fh.read()
            with open(os.path.join(repo, "k.py"), "w") as fh:
                fh.write(text.replace("LIMIT_0 = 100", "LIMIT_0 = 99"))
            one, code, out = check(repo)
            assert code == 1 and out.count("FAIL violated") == 1, out[-300:]
            rows.append({"facts": n, "lean": LEAN, "cold": cold, "warm": warm, "verify": verify, "one": one})
            print(f"{n:>6}{cold:>9}{warm:>9}{verify:>9}{one:>9}", flush=True)
        finally:
            shutil.rmtree(repo, ignore_errors=True)
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(rows, fh, indent=1)


if __name__ == "__main__":
    main()
