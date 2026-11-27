"""The kernel as the agent tools use it: the Rust build of this tool (rust/), called as a program.

The agents' side (pw.maintain, pw.calibrate, pw.discover, pw.propagate) decides what to show a
reader and what to propose; it never judges and never writes the record itself. Every verdict
and every line of the record comes from the Rust build:

    pw state  --db PATH                  the record as replayed (read here as `State`)
    pw sync   --db PATH --facts PATH      claim and withdraw facts as declared
    pw check  --record --json ...         hold the facts against the files, appending what was computed
    pw adopt  --db PATH                   take over readings made against a copy of the record
    pw mcp                                the readers' tools (pw.maintain starts it)
"""
import hashlib
import json
import os
import subprocess

from .kernel import KernelError

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def pw_binary():
    """The Rust build of this tool: PW_BIN, else rust/target/release/pw in this checkout."""
    return os.environ.get("PW_BIN") or os.path.join(ROOT, "rust", "target", "release", "pw")


def fact_id(name, typ):
    """The id the kernel gives a fact: the same fact, however its places come to be listed or read."""
    return "H:" + hashlib.sha256("\x00".join(("fact", name, " ".join(typ.split()))).encode()).hexdigest()[:10]


class State:
    """What the record says, as `pw state` replays it, in the shape the agent tools read:
    who read a reading as sets, readings as (place, M) pairs."""

    def __init__(self, dump):
        def who(w):
            return {**w, "by": set(w["by"]), "blind": set(w["blind"]), "models": set(w["models"]),
                    "under": {m: set(u) for m, u in w["under"].items()}}
        self.facts = {h: {**f, "readings": [tuple(r) for r in f["readings"]], "agreed": [(tuple(g), x) for g, x in f["agreed"]]}
                      for h, f in dump["facts"].items()}
        self.models = {m: {**who(x), "asked": {q: who(w) for q, w in x["asked"].items()}} for m, x in dump["models"].items()}
        self.objs = dump["objs"]
        self.props = dump["props"]
        self.verdict = {f: set(r) for f, r in dump["verdict"].items()}
        self.proofs = dump["proofs"]
        self.confirmations = dump["confirmations"]
        self.withdrawn = dump["withdrawn"]


class Kernel:
    """A record, acted on through the Rust build. `actor` is who the lines this adds are by."""

    def __init__(self, db_path, actor=None, lean_dir=None):
        self.db_path = db_path
        self.actor = actor or os.environ.get("PW_AGENT", "anon")
        self.lean_dir = lean_dir
        self.facts_path = None
        os.makedirs(os.path.dirname(os.path.abspath(db_path)), exist_ok=True)

    def _run(self, *args, stdin=None, ok=(0,)):
        lean = ("--lean-dir", self.lean_dir) if self.lean_dir else ()
        try:
            r = subprocess.run([pw_binary(), *args, *lean], input=stdin, capture_output=True, text=True)
        except FileNotFoundError:
            raise KernelError(f"the Rust build of this tool is not there ({pw_binary()}): "
                              "cargo build --release --manifest-path rust/Cargo.toml (or point PW_BIN at it)")
        if r.returncode not in ok:
            raise KernelError(r.stderr.strip().removeprefix("pw: ") or f"pw {args[0]} failed ({r.returncode})")
        return r

    def sync_facts(self, path):
        """Make the standing facts those declared in `path`; facts no longer declared are withdrawn."""
        self.facts_path = os.path.abspath(path)
        return set(json.loads(self._run("sync", "--db", self.db_path, "--facts", self.facts_path, "--actor", self.actor).stdout))

    def _declared(self, cwd):
        return self.facts_path or os.path.join(cwd, "pw-facts.json")

    def recheck(self, cwd):
        """Hold the declared facts against the files in `cwd`, appending what was computed to the record."""
        r = self._run("check", "--repo", cwd, "--facts", self._declared(cwd), "--db", self.db_path, "--record",
                      "--actor", self.actor, "--json", ok=(0, 1))
        return json.loads(r.stdout)

    def show(self, cwd, unconfirmed="fail"):
        """Hold the facts against the files and print where they stand, as `pw check` does. True if anything needs attention."""
        r = self._run("check", "--repo", cwd, "--facts", self._declared(cwd), "--db", self.db_path, "--record",
                      "--actor", self.actor, "--unconfirmed", unconfirmed, ok=(0, 1))
        print(r.stdout, end="", flush=True)
        return r.returncode == 1

    def needs_lean(self, cwd="."):
        return self._run("check", "--repo", cwd, "--facts", self._declared(cwd), "--needs-lean").stdout.strip() == "yes"

    def state(self):
        return State(json.loads(self._run("state", "--db", self.db_path).stdout))

    def events(self):
        if not os.path.exists(self.db_path):
            return []
        with open(self.db_path, encoding="utf-8") as fh:
            return [{"id": n, **json.loads(line)} for n, line in enumerate(fh, 1) if line.strip()]

    def adopt(self, events):
        """Take over readings that were made against a copy of this record, of text since written into the files."""
        self._run("adopt", "--db", self.db_path, "--actor", self.actor, stdin="".join(json.dumps(e, ensure_ascii=False) + "\n" for e in events))

    def claim_fact(self, name, typ, places, gloss=""):
        """Declare one more fact in a record of this kernel's own (pw.calibrate's trials): it is
        added to a declaration kept next to the record, and that is synced."""
        path = os.path.join(os.path.dirname(os.path.abspath(self.db_path)), "pw-claimed.json")
        claimed = []
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                claimed = json.load(fh)
        claimed = [d for d in claimed if d["name"] != name] + [{"name": name, "type": typ, "places": places, "gloss": gloss}]
        with open(path, "w") as fh:
            json.dump(claimed, fh, ensure_ascii=False)
        self.sync_facts(path)
        return {"h": fact_id(name, typ)}
