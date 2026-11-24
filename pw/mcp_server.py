"""MCP server through which a reader says what a place states (stdio).

Env: PW_DB (path of the record, pw-log.jsonl), PW_AGENT (the reader's name), PW_WORKDIR (the
repository), PW_LEAN_DIR (the Lean project; defaults to this repository's lean/), PW_BLIND ("1" if
the reader is shown the place and nothing else), PW_MODEL (which model the reader is).
A reader has two things to say about a place, and no other way to act.
"""
import os

try:  # mcp 2.x
    from mcp.server.mcpserver import MCPServer as FastMCP
except ImportError:  # mcp 1.x
    from mcp.server.fastmcp import FastMCP

from .kernel import Kernel, KernelError
from .lean_gate import LEAN_DIR, GateError, LeanGate

mcp = FastMCP("pw")
_kernel = Kernel(os.environ.get("PW_DB", "pw-log.jsonl"), gate=LeanGate(os.environ.get("PW_LEAN_DIR", LEAN_DIR)))


def _safe(fn, *a, **kw):
    try:
        return fn(*a, **kw)
    except (KernelError, GateError, ValueError) as e:
        return {"error": f"{type(e).__name__}: {e}"}


def _workdir():
    return os.environ.get("PW_WORKDIR", os.getcwd())


def _reader():
    return {"blind": os.environ.get("PW_BLIND") == "1", "model": os.environ.get("PW_MODEL")}


@mcp.tool()
def read_place(h: str, place: str, object: str, quote: str) -> dict:
    """For a FACT (one thing stated in several places): state what one of its places says, as a
    Lean term of the fact's type, e.g. object "\"pqd\"" or "[\"a\", \"b\"]" or "14". `place` is exactly
    as listed for the fact, e.g. "docs/spec.md::3. Model". `quote` is the sentence or table row of
    that place which says it, copied word for word (for a list spread over a table, the row of
    one entry); the kernel checks the quote is there and shows it to the person who confirms your
    reading. Write what the place itself says. The kernel compares the places; you prove nothing."""
    return _safe(lambda: _kernel.read_place(h, place, object, cwd=_workdir(), quote=quote, **_reader()))


@mcp.tool()
def not_stated(h: str, place: str, why: str) -> dict:
    """For a FACT: say that a place you were shown does not state it. Use this instead of
    `read_place` when the place is about something else, or mentions the thing without saying
    what its value is. `why` says in a sentence what the place is about instead. Declining is
    an answer: a place that is read as something it does not say hides a disagreement."""
    return _safe(lambda: _kernel.decline(h, place, why, _workdir(), **_reader()))


if __name__ == "__main__":
    mcp.run()
