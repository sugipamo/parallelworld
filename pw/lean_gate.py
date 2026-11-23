"""Lean gate: the only way a deterministic relation enters the kernel.

The gate writes the theorem statement itself from registered proposition
texts; the caller supplies only tactic text. A proof is accepted iff Lean
elaborates the file without error and `#print axioms` lists only allowed axioms.

Gamma (the fixed formal premises) = toolchain + lean/Gamma.lean + axiom allowlist.
"""
import hashlib
import os
import re
import shutil
import subprocess

LEAN_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "lean")
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Text from agents is spliced into a Lean file, so anything that could start a
# new command or alter the environment is refused. This is a denylist, i.e. a
# known weak point: see docs/spec.md "未解決".
_FORBIDDEN = re.compile(
    r"#|\b(sorry|admit|axiom|macro|macro_rules|syntax|notation|infix[lr]?|prefix|postfix|elab|"
    r"elab_rules|import|open|export|set_option|attribute|instance|unsafe|implemented_by|extern|"
    r"native_decide|initialize|run_cmd|run_tac|namespace|section|end|theorem|lemma|def|abbrev|"
    r"example|structure|inductive|class|universe|variable|deriving|opaque|mutual)\b"
)

_GOALS = {
    "holds": "PWStmt.S0",
    "not": "_root_.Not PWStmt.S0",
    "iff": "_root_.Iff PWStmt.S0 PWStmt.S1",
    "implies": "PWStmt.S0 → PWStmt.S1",
    "contradiction": "_root_.Not (_root_.And PWStmt.S0 PWStmt.S1)",
}


class GateError(Exception):
    pass


class LeanGate:
    def __init__(self, lean_dir=LEAN_DIR, timeout=300):
        self.lean_dir = lean_dir
        self.timeout = timeout

    def screen(self, text):
        m = _FORBIDDEN.search(text)
        if m:
            raise GateError(f"forbidden token {m.group(0)!r} in Lean text")

    def gamma(self):
        h = hashlib.sha256()
        for name in ("lean-toolchain", "Gamma.lean", "lakefile.toml"):
            with open(os.path.join(self.lean_dir, name), "rb") as fh:
                h.update(fh.read())
        h.update(",".join(sorted(ALLOWED_AXIOMS)).encode())
        return h.hexdigest()[:12]

    def render(self, relation, props, proof):
        for t in (*props, proof):
            self.screen(t)
        defs = "\n".join(f"def S{i} : Prop := ({p})" for i, p in enumerate(props))
        names = " ".join(f"PWStmt.S{i}" for i in range(len(props)))
        body = "\n".join("  " + line for line in proof.strip().splitlines())
        return (
            "import Gamma\n\nnamespace PWStmt\n" + defs + "\nend PWStmt\n\n"
            f"theorem pw_goal : {_GOALS[relation]} := by\n  unfold {names}\n{body}\n\n"
            "#print axioms pw_goal\n"
        )

    def _lake(self):
        lake = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
        if not os.path.exists(lake):
            raise GateError("Lean (lake) is not installed; no proof can be accepted")
        return lake

    def check(self, relation, props, proof):
        try:
            src = self.render(relation, props, proof)
            lake = self._lake()
        except GateError as e:
            return {"ok": False, "reason": str(e)}
        work = os.path.join(self.lean_dir, "PWCheck")
        os.makedirs(work, exist_ok=True)
        path = os.path.join(work, hashlib.sha256(src.encode()).hexdigest()[:16] + ".lean")
        with open(path, "w") as fh:
            fh.write(src)
        try:
            b = subprocess.run([lake, "build"], cwd=self.lean_dir, capture_output=True, text=True, timeout=self.timeout)
            if b.returncode != 0:
                return {"ok": False, "reason": "Gamma failed to build: " + (b.stdout + b.stderr)[-500:]}
            r = subprocess.run([lake, "env", "lean", path], cwd=self.lean_dir, capture_output=True,
                               text=True, timeout=self.timeout)
        except subprocess.TimeoutExpired:
            return {"ok": False, "reason": "timeout"}
        return self.judge(r.returncode, r.stdout + r.stderr, self.gamma())

    @staticmethod
    def judge(returncode, output, gamma):
        if returncode != 0 or "error" in output:
            return {"ok": False, "reason": output[-1500:]}
        if "'pw_goal' does not depend on any axioms" in output:
            axioms = []
        else:
            m = re.search(r"'pw_goal' depends on axioms: \[([^\]]*)\]", output)
            if not m:
                return {"ok": False, "reason": "could not read axiom report: " + output[-500:]}
            axioms = [a.strip() for a in m.group(1).split(",") if a.strip()]
        bad = sorted(set(axioms) - ALLOWED_AXIOMS)
        if bad:
            return {"ok": False, "reason": f"depends on unapproved axioms: {bad}"}
        return {"ok": True, "axioms": sorted(axioms), "gamma": gamma}
