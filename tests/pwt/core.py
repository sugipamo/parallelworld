"""The kernel and the Lean gate, as the tests (and some experiments) use them: the pw executable, called as a program.

Nothing in Python judges or writes the record. Every verdict and every line of the record comes
from the Rust build; this module only asks it and reads its answers:

    pw kernel   one operation on a record: claim, sync, read, decline, sign_off, prove, verify,
                withdraw, recheck, needs_lean, adopt, state (a JSON request on stdin, a JSON reply)
    pw lean     one operation of the Lean gate: check, check_many, typecheck, evaluate, screen, ...
    pw check    hold the declared facts against the files
    pw mcp      the readers' tools (pw maintain starts it)

`Kernel` and `LeanGate` keep the methods the Python implementation had, so that the tests read as
they did. This is not part of the tool: the tool is the one executable.
"""
import functools
import hashlib
import json
import os
import shutil
import subprocess
from subprocess import run as _call      # (bound here: a test standing in for an agent session replaces subprocess.run)

from .kernel import KernelError

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN_DIR = os.path.join(ROOT, "lean")
FACTS = "pw-facts.json"      # a project's list of facts and the places that state them
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


class GateError(Exception):
    pass


def pw_binary():
    """The Rust build of this tool: PW_BIN; else the build in this checkout (rust/target/release/pw);
    else a `pw` on PATH that says it is this tool (`cargo install --path rust` puts one there)."""
    if os.environ.get("PW_BIN"):
        return os.environ["PW_BIN"]
    built = os.path.join(ROOT, "rust", "target", "release", "pw")
    if os.access(built, os.X_OK):
        return built
    return _on_path() or built


@functools.lru_cache(maxsize=None)
def _on_path():
    found = shutil.which("pw")
    if not found:
        return None
    try:                              # (another program may be called pw)
        said = _call([found, "version"], capture_output=True, text=True, timeout=10).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    return found if said.startswith("parallelworld ") else None


def missing():
    return (f"the pw executable is not there ({pw_binary()}): "
            "cargo build --release --manifest-path rust/Cargo.toml (or point PW_BIN at it)")


def fact_id(name, typ):
    """The id the kernel gives a fact: the same fact, however its places come to be listed or read."""
    return "H:" + hashlib.sha256("\x00".join(("fact", name, " ".join(typ.split()))).encode()).hexdigest()[:10]


def _ask(command, request, stdin_ok=(0,)):
    """One request to the Rust build; its answer, or the error it names."""
    try:
        r = _call([pw_binary(), command], input=json.dumps(request, ensure_ascii=False), capture_output=True, text=True)
    except FileNotFoundError:
        raise KernelError(missing())
    if r.returncode != 0 or not r.stdout.strip():
        raise KernelError(r.stderr.strip().removeprefix("pw: ") or f"pw {command} failed ({r.returncode})")
    out = json.loads(r.stdout)
    if "error" in out:
        raise {"GateError": GateError, "ValueError": ValueError}.get(out.get("kind"), KernelError)(out["error"])
    return out["ok"]


class LeanGate:
    """The Lean gate (rust/src/lean.rs): the only way it is settled that a proposition holds, or does not."""

    def __init__(self, lean_dir=LEAN_DIR, timeout=300):
        self.lean_dir = os.path.abspath(lean_dir)
        self.timeout = timeout

    def _ask(self, op, **args):
        return _ask("lean", {"lean_dir": self.lean_dir, "op": op, **args})

    def check(self, relation, items, proof):
        return self._ask("check", relation=relation, items=[list(i) for i in items], proof=proof)

    def check_many(self, jobs, batch=50):
        return self._ask("check_many", jobs=[[r, [list(i) for i in items], p] for r, items, p in jobs], batch=batch)

    def typecheck(self, items):
        return self._ask("typecheck", items=[list(i) for i in items])

    def evaluate(self, typ, term):
        return self._ask("evaluate", typ=typ, term=term)

    def screen(self, text):
        self._ask("screen", text=text)

    def render(self, relation, items, proof):
        return self._ask("render", relation=relation, items=[list(i) for i in items], proof=proof)

    def gamma(self):
        return self._ask("gamma")

    def available(self):
        return self._ask("available")

    def usable(self):
        self._ask("usable")

    @staticmethod
    def judge(returncode, output, gamma):
        return _ask("lean", {"op": "judge", "returncode": returncode, "output": output, "gamma": gamma})


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
    """A record, acted on through the Rust build. `actor` is who the lines this adds are by.

    `compare`: when Lean is asked. "needed" (only where a value has to be worked out) or
    "always" (every comparison, recorded with its proof)."""
    compare = "needed"

    def __init__(self, db_path, gate=None, actor=None, lean_dir=None):
        self.db_path = db_path
        self.gate = gate
        self.actor = actor or os.environ.get("PW_AGENT", "anon")
        self.lean_dir = lean_dir or getattr(gate, "lean_dir", None)
        self.facts_path = None
        os.makedirs(os.path.dirname(os.path.abspath(db_path)), exist_ok=True)

    def _op(self, op, **args):
        return _ask("kernel", {"db": self.db_path, "actor": self.actor, "always": self.compare == "always",
                               **({"lean_dir": self.lean_dir} if self.lean_dir else {}), "op": op, **args})

    def _run(self, *args, ok=(0,)):
        lean = ("--lean-dir", self.lean_dir) if self.lean_dir else ()
        try:
            r = _call([pw_binary(), *args, *lean], capture_output=True, text=True)
        except FileNotFoundError:
            raise KernelError(missing())
        if r.returncode not in ok:
            raise KernelError(r.stderr.strip().removeprefix("pw: ") or f"pw {args[0]} failed ({r.returncode})")
        return r

    # ---- the record ------------------------------------------------------------------------
    def state(self):
        return State(self._op("state"))

    def events(self):
        if not os.path.exists(self.db_path):
            return []
        with open(self.db_path, encoding="utf-8") as fh:
            return [{"id": n, **json.loads(line)} for n, line in enumerate(fh, 1) if line.strip()]

    def adopt(self, events):
        """Take over readings that were made against a copy of this record, of text since written into the files."""
        self._op("adopt", events=[{k: v for k, v in e.items() if k != "id"} for e in events])

    # ---- facts -------------------------------------------------------------------------------
    def claim_fact(self, name, typ, places, gloss="", instructions=(), defined=None):
        """Declare that the listed places all state the same fact; places are "path" or
        {"at", "reader"?, "some"?}, a reader in the form the record keeps (see kernel.pattern)."""
        return self._op("claim", name=name, type=typ, places=list(places), gloss=gloss, instructions=list(instructions), defined=defined)

    def sync_facts(self, path):
        """Make the standing facts those declared in `path`; facts no longer declared are withdrawn."""
        self.facts_path = os.path.abspath(path)
        return set(self._op("sync", path=self.facts_path))

    def withdraw(self, h, justification):
        return self._op("withdraw", h=h, justification=justification)

    def needs_lean(self):
        return self._op("needs_lean")

    # ---- what places say -------------------------------------------------------------------
    def read_place(self, h, place, obj=None, cwd=None, quote=None, blind=False, model=None):
        """How one place of a fact reads, for its content as it is now. Without `obj` the place's reader computes it."""
        if cwd is None:
            raise KernelError(f"{place} is not there")
        from . import kernel                       # (the instructions readers are given now: pw/reader.txt as this package has it)
        return self._op("read", h=h, place=place, obj=obj, cwd=cwd, quote=quote, blind=bool(blind), model=model, instructions=kernel.INSTRUCTIONS)

    def decline(self, h, place, why, cwd, blind=False, model=None):
        return self._op("decline", h=h, place=place, why=why, cwd=cwd, blind=bool(blind), model=model)

    def sign_off(self, m, who, confirmed=True):
        return self._op("sign_off", m=m, who=who, confirmed=confirmed)

    # ---- judging -----------------------------------------------------------------------------
    def recheck(self, cwd):
        """Hold every fact the record declares against the files in `cwd`, appending what was computed."""
        return self._op("recheck", cwd=cwd)

    def prove(self, relation, f, proof):
        return self._op("prove", relation=relation, f=f, proof=proof)

    def verify(self, proofs=None):
        return self._op("verify", proofs=proofs)

    def show(self, cwd, unconfirmed="fail"):
        """Hold the declared facts against the files and print where they stand, as `pw check` does
        (recording what it computed). True if anything needs attention."""
        r = self._run("check", "--repo", cwd, "--facts", self.facts_path or os.path.join(cwd, FACTS), "--db", self.db_path,
                      "--record", "--actor", self.actor, "--unconfirmed", unconfirmed, ok=(0, 1))
        print(r.stdout, end="", flush=True)
        return r.returncode == 1
