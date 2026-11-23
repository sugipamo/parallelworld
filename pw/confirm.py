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

from .kernel import Kernel, locate
from .lean_gate import LEAN_DIR, LeanGate


def unconfirmed(kernel, repo):
    st = kernel.state()
    now = kernel.versions(repo)
    signed = {e["target"] for e in st.evidence.values() if e["kind"] == "sign_off"}
    for m, info in st.models.items():
        base = info["subject"].split("@")[0]
        if not info["binding"] and now.get(base) == info["subject"] and m not in signed:
            yield m, base, st.algebra.objs[info["obj"]]["text"], info.get("quote")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--who")
    ap.add_argument("--reject", action="store_true")
    ap.add_argument("readings", nargs="*")
    args = ap.parse_args()
    repo = os.path.abspath(args.repo)
    kernel = Kernel(os.path.join(repo, ".pw", "events.db"), gate=LeanGate(args.lean_dir), actor=args.who or "person")
    if args.readings:
        if not args.who:
            ap.error("say who is confirming: --who NAME")
        for m in args.readings:
            kernel.sign_off(m, args.who, confirmed=not args.reject)
            print(("rejected " if args.reject else "confirmed ") + m)
        return
    todo = list(unconfirmed(kernel, repo))
    for m, place, term, quote in todo:
        if quote:      # the kernel has checked that these words are in the place
            shown = "because it says: " + " ".join(quote.split())
        else:
            passage = (locate(place, repo) or b"").decode("utf-8", "replace").strip()
            shown = "passage:  " + passage[:600].replace("\n", "\n             ") + ("\n             …" if len(passage) > 600 else "")
        print(f"{m}  {place}\n   reads as: {term}\n   {shown}\n")
    print(f"{len(todo)} reading(s) nobody has confirmed" + ("" if not todo else "; confirm with: python -m pw.confirm --who NAME " + " ".join(t[0] for t in todo)))


if __name__ == "__main__":
    main()
