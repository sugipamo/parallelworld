"""Let a person confirm what an agent said a place says.

    python -m pw.confirm [--repo DIR]                          list unconfirmed readings, each beside its passage
    python -m pw.confirm [--repo DIR] --who NAME M:... M:...   confirm these readings
    python -m pw.confirm [--repo DIR] --who NAME --reject M:...

A reading stated by an agent is only as good as the agent. Confirming it means: I looked at the
passage and it does say this. The confirmation holds for that exact content; if the passage
changes, the new reading has to be confirmed again.
"""
import argparse
import os
import shutil
import tempfile

from .kernel import LOG, Kernel, KernelError, locate
from .lean_gate import LEAN_DIR, LeanGate


def unconfirmed(kernel, repo):
    """The readings stated by an agent that hold for the files as they are and that no person has confirmed or rejected.
    The facts are those declared now; the kernel is one on a copy of the record (listing writes nothing)."""
    kernel.sync_facts(os.path.join(repo, "pw-facts.json"))
    decisions = kernel.recheck(repo)["decisions"]
    st = kernel.state()                     # (with what the check has just computed)
    signed = {e["target"] for e in st.confirmations.values()}
    for d in decisions:
        for p in d["places"]:
            info = st.models[p["m"]]
            if p["by"] == "stated" and p["m"] not in signed:
                yield p["m"], p["at"], p["reads as"], info.get("quote"), info.get("anchor")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--who")
    ap.add_argument("--reject", action="store_true")
    ap.add_argument("readings", nargs="*")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(os.path.join(repo, LOG), gate=LeanGate(args.lean_dir), actor=args.who or "person")
    if args.readings:
        if not args.who:
            ap.error("say who is confirming: --who NAME")
        for m in args.readings:
            kernel.sign_off(m, args.who, confirmed=not args.reject)
            print(("rejected " if args.reject else "confirmed ") + m)
        return
    work = tempfile.mkdtemp(prefix="pw-confirm-")
    try:
        if os.path.exists(kernel.db_path):
            shutil.copy(kernel.db_path, os.path.join(work, LOG))
        todo = list(unconfirmed(Kernel(os.path.join(work, LOG), gate=kernel.gate, actor="confirm"), repo))
    except KernelError as e:              # name the project's record, not the copy
        raise KernelError(str(e).replace(os.path.join(work, LOG), kernel.db_path)) from None
    finally:
        shutil.rmtree(work, ignore_errors=True)
    for m, place, term, quote, anchor in todo:
        if quote and anchor:      # the kernel has checked that these words are in the place
            shown = "because it says: " + " ".join(quote.split())
        elif quote:
            shown = "for example it says: " + " ".join(quote.split()) + "\n   (a list is read off the whole place: compare it with " + place + ")"
        else:
            passage = (locate(place, repo) or b"").decode("utf-8", "replace").strip()
            shown = "passage:  " + passage[:600].replace("\n", "\n             ") + ("\n             …" if len(passage) > 600 else "")
        print(f"{m}  {place}\n   reads as: {term}\n   {shown}\n")
    print(f"{len(todo)} reading(s) nobody has confirmed" + ("" if not todo else "; confirm with: python -m pw.confirm --who NAME " + " ".join(t[0] for t in todo)))


if __name__ == "__main__":
    from .kernel import cli
    cli(main)
