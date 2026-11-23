"""MCP server exposing the kernel to Claude Code workers (stdio).

Env: PW_DB (event log path), PW_AGENT (actor name), PW_WORKDIR (where checks run).
Workers never supply probabilities: priors and likelihoods come from the catalog.
"""
import os

try:  # mcp 2.x
    from mcp.server.mcpserver import MCPServer as FastMCP
except ImportError:  # mcp 1.x
    from mcp.server.fastmcp import FastMCP

from .kernel import Kernel, KernelError
from .lean_gate import GateError, LeanGate

mcp = FastMCP("pw")
_kernel = Kernel(os.environ.get("PW_DB", ".pw/events.db"), gate=LeanGate())


def _safe(fn, *a, **kw):
    try:
        return fn(*a, **kw)
    except (KernelError, GateError, ValueError) as e:
        return {"error": f"{type(e).__name__}: {e}"}


@mcp.tool()
def claim(text: str) -> dict:
    """Register a knowledge proposition H about the code or spec. One precise, falsifiable
    sentence. Identical text from any agent maps to the same H. Returns its id."""
    return _safe(_kernel.claim, text)


@mcp.tool()
def ground(h: str, lean: str) -> dict:
    """State that claim `h` means the Lean proposition `lean` (a term of type Prop, using only
    Lean core and Gamma). This introduces a connection hypothesis G whose correctness stays
    uncertain. Returns ids of G and F."""
    return _safe(_kernel.ground, h, lean)


@mcp.tool()
def observe_command(target: str, kind: str, command: str) -> dict:
    """Have the kernel run a shell check (kind: test | property_test | typecheck) in the worktree
    and record pass/fail as evidence for claim `target`. Re-running the same command on the same
    tree is the same evidence and changes nothing."""
    return _safe(_kernel.observe_command, target, kind, command, os.environ.get("PW_WORKDIR", os.getcwd()))


@mcp.tool()
def observe(target: str, kind: str, outcome: str, source: str) -> dict:
    """Record evidence that cannot be produced by a command (kind: review | instance_check |
    back_translation). `source` must identify the physical origin (e.g. artifact hash)."""
    if kind in ("test", "property_test", "typecheck"):
        return {"error": "use observe_command for this kind"}
    return _safe(_kernel.observe, target, kind, outcome, source)


@mcp.tool()
def declare_independent(eid: str, justification: str) -> dict:
    """Assert that evidence `eid` shares no cause with other evidence on the same target.
    Without this, evidence on one target is treated as possibly redundant."""
    return _safe(_kernel.declare_independent, eid, justification)


@mcp.tool()
def prove(relation: str, fs: list[str], proof: str) -> dict:
    """Submit Lean tactic text proving a relation between formal propositions:
    holds [F] | not [F] | iff [F1,F2] | implies [F1,F2] | contradiction [F1,F2].
    Accepted only if the Lean kernel checks it with approved axioms and no sorry."""
    return _safe(_kernel.prove, relation, fs, proof)


@mcp.tool()
def infer(query: str) -> dict:
    """Bounds [lo, hi] on the probability of a formula over atom ids, e.g. "H:ab12" or
    "H:ab12 <-> H:cd34". Operators: ! & | -> <->. Rely on a claim only if `lo` is high enough."""
    return _safe(_kernel.infer, query)


@mcp.tool()
def status() -> dict:
    """All claims with current bounds, formal equivalence classes, and accepted proofs."""
    return _safe(_kernel.status)


if __name__ == "__main__":
    mcp.run()
