"""Lean gate: the only way it enters the record that a proposition holds, or does not.

The propositions are equations between the values read off a fact's places. The gate writes
the theorem statement itself from the registered text; the caller supplies only tactic text. Checking takes two Lean runs:

  1. compile the module holding the statement and the caller's tactics;
  2. in a second file containing no caller text, import it and `#print axioms`.

The proof is accepted iff run 1 succeeds and run 2 prints exactly one axiom
report listing only allowed axioms. Splitting the runs matters: tactics can
emit arbitrary messages, so a report read from run 1 could be forged.

Gamma (the fixed formal premises) = toolchain + lean/Gamma.lean + axiom allowlist.

Lean is not run where the project is kept. The project's files are copied to a directory of
the user's own (PW_LEAN_WORK, else the cache directory), Gamma is built there, and each check
writes its files to a directory under it that is removed afterwards. The directory this tool
is installed in is only read: it can be a checkout another job shares, or a read-only mount.
"""
import hashlib
import os
import re
import shutil
import subprocess
import tempfile

_HERE = os.path.dirname(os.path.abspath(__file__))
# The Lean project: next to the package in a checkout, inside it when installed (pyproject.toml).
LEAN_DIR = next((d for d in (os.path.join(_HERE, "lean"), os.path.join(os.path.dirname(_HERE), "lean"))
                 if os.path.exists(os.path.join(d, "lean-toolchain"))), os.path.join(os.path.dirname(_HERE), "lean"))
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Text from agents is spliced into a Lean file, so anything that could start a
# new command or alter the environment is refused. This is a denylist, i.e. a
# known weak point: see docs/spec.md "未解決".
_FORBIDDEN = re.compile(
    r"#|@\[|declare_|register_|builtin_|\b(sorry|admit|axiom|macro|macro_rules|syntax|notation|infix[lr]?|prefix|postfix|elab|"
    r"elab_rules|import|open|export|set_option|attribute|instance|unsafe|implemented_by|extern|"
    r"native_decide|initialize|local|scoped|private|protected|run_cmd|run_tac|namespace|section|end|theorem|lemma|def|abbrev|"
    r"example|structure|inductive|class|universe|variable|deriving|opaque|mutual)\b"
)

_GOALS = {
    "holds": "S0",
    "not": "_root_.Not S0",
}


class GateError(Exception):
    pass


_PROJECT = ("lean-toolchain", "Gamma.lean", "lakefile.toml")    # what Gamma is made of
_COPIED = _PROJECT + ("lake-manifest.json",)


class LeanGate:
    def __init__(self, lean_dir=LEAN_DIR, timeout=300):
        self.lean_dir = os.path.abspath(lean_dir)
        self.timeout = timeout

    def _home(self):
        """The directory Lean is run in: a copy of the project, kept outside the tool's own files.

        Named after the project's content, so that another Gamma gets another directory and a
        build is never reused for premises it was not made from.
        """
        h, files = hashlib.sha256(), {}
        for name in _COPIED:
            try:
                with open(os.path.join(self.lean_dir, name), "rb") as fh:
                    files[name] = fh.read()
            except FileNotFoundError:
                if name in _PROJECT:
                    raise GateError(f"{self.lean_dir} is not the Lean project: it has no {name}")
                continue
            h.update(name.encode() + b"\0" + files[name] + b"\0")
        base = os.environ.get("PW_LEAN_WORK") or os.path.join(
            os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache"), "parallelworld")
        home = os.path.join(base, "lean-" + h.hexdigest()[:16])
        try:
            os.makedirs(home, exist_ok=True)
            for name, content in files.items():
                path = os.path.join(home, name)
                if not os.path.exists(path):
                    fd, tmp = tempfile.mkstemp(dir=home)       # (another process may be doing the same)
                    with os.fdopen(fd, "wb") as fh:
                        fh.write(content)
                    os.replace(tmp, path)
        except OSError as e:
            raise GateError(f"Lean needs a directory it can write to, and {home} is not one ({e.strerror}); set PW_LEAN_WORK")
        return home

    def screen(self, text):
        # What is inside a plain string literal is data, not Lean: "declare_independent" names
        # a tool. Strings are set aside only in text with no backslash at all (escapes and raw
        # strings make it unclear where a string ends), and a quote written as a character
        # literal is refused, so that nothing can pose as a string and hide code.
        if "'\"'" in text:
            raise GateError("a double quote as a character literal is not accepted")
        m = _FORBIDDEN.search(text if "\\" in text else re.sub(r'"[^"\n]*"', '""', text))
        if m:
            raise GateError(f"forbidden token {m.group(0)!r} in Lean text")

    def gamma(self):
        h = hashlib.sha256()
        for name in _PROJECT:
            with open(os.path.join(self.lean_dir, name), "rb") as fh:
                h.update(fh.read())
        h.update(",".join(sorted(ALLOWED_AXIOMS)).encode())
        return h.hexdigest()[:12]

    def render(self, relation, items, proof):
        """items: [(Lean type, Lean term)] in the order the goal refers to them as S0, S1."""
        for typ, body in items:
            self.screen(typ)
            self.screen(body)
        self.screen(proof)
        defs = "\n".join(f"def S{i} : ({t}) := ({b})" for i, (t, b) in enumerate(items))
        names = " ".join(f"PWStmt.S{i}" for i in range(len(items)))
        goal = re.sub(r"\bS(\d)\b", r"PWStmt.S\1", _GOALS[relation])
        body = "\n".join("    " + line for line in proof.strip().splitlines())
        # Unfolding and simplifying the statement can already settle it (an equation between
        # two equal literals, say). Then there is nothing left for the caller's tactics to do.
        return (
            "import Gamma\n\nnamespace PWStmt\n" + defs + "\nend PWStmt\n\n"
            f"theorem pw_goal : {goal} := by\n  unfold {names}\n  try dsimp only\n"
            f"  first\n  | done\n  | (\n{body}\n    )\n"
        )

    def _lake(self):
        """Locate lake, insist its Lean version is the one Gamma pins, and make sure Gamma is built.
        Returns lake and the directory to run it in."""
        lake = os.environ.get("PW_LAKE") or shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
        if not os.path.exists(lake):
            raise GateError("Lean (lake) is not installed; no proof can be accepted")
        home = self._home()
        with open(os.path.join(home, "lean-toolchain")) as fh:
            want = fh.read().strip().rsplit(":v", 1)[-1]
        r = subprocess.run([lake, "--version"], cwd=home, capture_output=True, text=True)
        if f"Lean version {want})" not in r.stdout:
            raise GateError(f"Gamma pins Lean {want} ({os.path.join(self.lean_dir, 'lean-toolchain')}) but lake reports: "
                            f"{r.stdout.strip() or r.stderr.strip()[:200]}. Install Lean {want}, or point PW_LAKE at its lake")
        try:
            b = subprocess.run([lake, "build"], cwd=home, capture_output=True, text=True, timeout=self.timeout)
        except subprocess.TimeoutExpired:
            raise GateError("Gamma did not build in time")
        if b.returncode != 0:
            raise GateError("Gamma failed to build: " + (b.stdout + b.stderr)[-500:])
        return lake, home

    def check(self, relation, items, proof):
        try:
            src = self.render(relation, items, proof)
            lake, home = self._lake()
        except GateError as e:
            return {"ok": False, "reason": str(e)}
        with tempfile.TemporaryDirectory(prefix="run-", dir=home) as work:      # (Lean wants its input under the project)
            mod = "PWProof_" + hashlib.sha256(src.encode()).hexdigest()[:16]
            proof_file = os.path.join(work, mod + ".lean")
            audit_file = os.path.join(work, mod + "_audit.lean")
            with open(proof_file, "w") as fh:
                fh.write(src)
            with open(audit_file, "w") as fh:
                fh.write(f"import {mod}\n#print axioms pw_goal\n")

            def run(*cmd, **kw):
                return subprocess.run(cmd, cwd=home, capture_output=True, text=True, timeout=self.timeout, **kw)
            try:
                lean = os.path.join(os.path.dirname(lake), "lean")
                path = run(lake, "env", "printenv", "LEAN_PATH").stdout.strip()
                env = dict(os.environ, LEAN_PATH=f"{path}:{work}")
                r = run(lean, "-o", os.path.join(work, mod + ".olean"), proof_file, env=env)
                if r.returncode != 0:
                    return {"ok": False, "reason": (r.stdout + r.stderr)[-1500:]}
                r = run(lean, audit_file, env=env)
            except subprocess.TimeoutExpired:
                return {"ok": False, "reason": "timeout"}
        return self.judge(r.returncode, r.stdout + r.stderr, self.gamma())

    def _run_file(self, src, lake, home):
        """Run Lean on a file of ours that nothing imports. None if it does not finish in time."""
        with tempfile.TemporaryDirectory(prefix="run-", dir=home) as work:      # (Lean wants its input under the project)
            path = os.path.join(work, "PW_" + hashlib.sha256(src.encode()).hexdigest()[:16] + ".lean")
            with open(path, "w") as fh:
                fh.write(src)
            try:
                return subprocess.run([lake, "env", "lean", path], cwd=home, capture_output=True, text=True, timeout=self.timeout)
            except subprocess.TimeoutExpired:
                return None

    def typecheck(self, items):
        """Does Lean accept each (type, term) under Gamma? Catches a formalization that is not Lean at all."""
        try:
            for typ, body in items:
                self.screen(typ)
                self.screen(body)
            lake, home = self._lake()
        except GateError as e:
            return {"ok": False, "reason": str(e)}
        r = self._run_file("import Gamma\n\n" + "".join(f"example : ({t}) := ({b})\n" for t, b in items), lake, home)
        if r is None:
            return {"ok": False, "reason": "timeout"}
        return {"ok": r.returncode == 0, "reason": (r.stdout + r.stderr)[-800:]}

    def evaluate(self, typ, term):
        """The value of a term, as Lean prints it: the same spelling the places are read as
        ("3.10" with its quotes, 14, ["a", "b"]). None if Lean does not evaluate it. This is
        for showing a value and for writing it into a file; whether a place equals the term is
        still settled by a proof."""
        try:
            self.screen(typ)
            self.screen(term)
            lake, home = self._lake()
        except GateError:
            return None
        r = self._run_file(f"import Gamma\n\ndef pw_value : ({typ}) := ({term})\n\n#eval IO.println (repr pw_value)\n", lake, home)
        return r.stdout.strip() if r is not None and r.returncode == 0 and r.stdout.strip() else None

    @staticmethod
    def judge(returncode, output, gamma):
        """Read the audit run. Its whole output must be one axiom report, nothing else."""
        out = " ".join(output.split())
        if returncode != 0:
            return {"ok": False, "reason": output[-1500:]}
        if out == "'pw_goal' does not depend on any axioms":
            axioms = []
        else:
            m = re.fullmatch(r"'pw_goal' depends on axioms: \[([^\]]*)\]", out)
            if not m:
                return {"ok": False, "reason": "unexpected audit output: " + output[-500:]}
            axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        bad = sorted(set(axioms) - ALLOWED_AXIOMS)
        if bad:
            return {"ok": False, "reason": f"depends on unapproved axioms: {bad}"}
        return {"ok": True, "axioms": sorted(axioms), "gamma": gamma}
