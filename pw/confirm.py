"""Let a person confirm what an agent said a place says: the Rust build's `pw confirm`.

    python -m pw.confirm [--repo DIR]                          list unconfirmed readings, each beside its passage
    python -m pw.confirm [--repo DIR] --who NAME M:... M:...   confirm these readings
    python -m pw.confirm [--repo DIR] --who NAME --reject M:...

A reading stated by an agent is only as good as the agent. Confirming it means: I looked at the
passage and it does say this. The confirmation holds for that exact content; if the passage
changes, the new reading has to be confirmed again.
"""
import os
import sys

from .core import missing, pw_binary


def main():
    try:
        os.execv(pw_binary(), [pw_binary(), "confirm", *sys.argv[1:]])
    except FileNotFoundError:
        sys.exit(f"pw: {missing()}")


if __name__ == "__main__":
    main()
