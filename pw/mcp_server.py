"""MCP server exposing the kernel to Claude Code workers (stdio).

Env: PW_DB (event log path), PW_AGENT (actor name), PW_WORKDIR (where checks run),
PW_LEAN_DIR (the Lean project holding Gamma; defaults to this repository's lean/).
Workers never supply probabilities: priors and likelihoods come from the catalog.
"""
import os

try:  # mcp 2.x
    from mcp.server.mcpserver import MCPServer as FastMCP
except ImportError:  # mcp 1.x
    from mcp.server.fastmcp import FastMCP

from .kernel import Kernel, KernelError, binding, subject_id
from .lean_gate import LEAN_DIR, GateError, LeanGate

mcp = FastMCP("pw")
_kernel = Kernel(os.environ.get("PW_DB", ".pw/events.db"), gate=LeanGate(os.environ.get("PW_LEAN_DIR", LEAN_DIR)))


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


def _workdir():
    return os.environ.get("PW_WORKDIR", os.getcwd())


def _binding(setup, call, domains):
    return binding(call, setup, domains or []) if call else None


@mcp.tool()
def model(h: str, object: str, setup: str = "", call: str = "", domains: list[str] | None = None) -> dict:
    """For a FORMAL claim (one given to you as a predicate; `status` marks it formal): state
    that the Lean term `object` models the claim's code. The claim's predicate and type are
    already fixed. Also say how the code is called:
      setup      Python statements run before the call, e.g. "from clamp import clamp"
      call       a Python expression calling the code on arguments {0}, {1}, ..., e.g. "clamp({0}, {1}, {2})"
      domains    how each argument is drawn: "nat", "int", "unit" (rational in [0, 1], passed as a
                 Fraction), "pos" (positive rational), "units" (non-empty list of rationals in [0, 1])
    `setup`, `call` and `domains` are part of what the model hypothesis claims: "on every input from
    these domains, calling the code this way gives what the Lean term gives". The kernel builds and
    runs the checks from them; you do not write check commands.
    For a file that is not code you can call (a configuration, a schema, a document), leave out
    setup, call and domains: you are then stating how you read the file, and the reading holds
    for this exact content only. Write what the file says, not what the claim would like it to say.
    Returns ids of the model hypothesis M and the proposition F = predicate(object);
    then prove `holds [F]` (or `not [F]` if the file does not satisfy the predicate), and for
    callable code support M with sample_model."""
    st = _kernel.state()
    if h not in st.formal:
        return {"error": f"{h} is not a formal claim; use ground_at"}
    return _safe(lambda: _kernel.attach_model(h, object, subject_id(st.formal[h]["subject"], _workdir()),
                                               binding=_binding(setup, call, domains), cwd=_workdir()))


@mcp.tool()
def read_place(h: str, place: str, object: str, quote: str) -> dict:
    """For a FACT (one thing stated in several places): state what one of its places says, as a
    Lean term of the fact's type, e.g. object "\"pqd\"" or "[\"a\", \"b\"]" or "14". `place` is exactly
    as listed for the fact, e.g. "docs/spec.md::3. Model". `quote` is the sentence or table row of
    that place which says it, copied word for word (for a list spread over a table, the row of
    one entry); the kernel checks the quote is there and shows it to the person who confirms your
    reading. Write what the place itself says. The kernel compares the places; you prove nothing."""
    return _safe(lambda: _kernel.read_place(h, place, object, cwd=_workdir(), quote=quote))


@mcp.tool()
def reject_object(p: str, object: str, proof: str) -> dict:
    """Show that specification `p` is not vacuous: give a Lean term `object` (of p's type) that
    should NOT satisfy it, and tactics proving `¬ p object`. Use this for specifications you
    wrote yourself with ground_at; a specification that excludes nothing says nothing."""
    return _safe(_kernel.reject_object, p, object, proof)


@mcp.tool()
def ground_at(h: str, subject: str, type: str, predicate: str, object: str,
              setup: str = "", call: str = "", domains: list[str] | None = None,
              left_out: str = "", added: str = "") -> dict:
    """For a claim in natural language: state that claim `h` says the code `subject` has a property. Give
      subject    what the claim is about, as "path::name", e.g. "clamp.py::clamp"
      object     a Lean term of type `type` modelling that code's behaviour
      predicate  a Lean term of type `type -> Prop` stating the property
      setup      Python statements run before the call, e.g. "from clamp import clamp"
      call       a Python expression calling the code on arguments {0}, {1}, ..., e.g. "clamp({0}, {1}, {2})"
      domains    how each argument is drawn: "nat", "int", "unit" (rational in [0, 1], passed as a
                 Fraction), "pos" (positive rational), "units" (non-empty list of rationals in [0, 1])
    `setup`, `call` and `domains` are part of what the model hypothesis claims: "on every input from
    these domains, calling the code this way gives what the Lean term gives". The kernel builds and
    runs the checks from them; you do not write check commands.
      left_out   what the sentence says or implies that your formalization does not capture
      added      what your formalization fixes that the sentence leaves open
    using only Lean core and Gamma, e.g. type "Nat → Nat", predicate "fun f => ∀ n, n ≤ f n",
    object "fun n => n + 1". This introduces two separate uncertain hypotheses: G (the predicate
    expresses the claim's property) and M (the object models the code). M is shared by every
    claim that states the same code, object and way of calling, and is tied to the file's content.
    Be exact in `left_out` and `added`: a person reads them to judge the connection.
    Returns ids of G, M, proposition F, specification P and object O."""
    return _safe(lambda: _kernel.ground_at(h, subject_id(subject, _workdir()), type, predicate, object,
                                           left_out=left_out, added=added,
                                           binding=_binding(setup, call, domains), cwd=_workdir()))


@mcp.tool()
def sample_model(m: str, n: int = 10) -> dict:
    """Support a model hypothesis M with random checks. The kernel draws `n` inputs from M's
    recorded domains, calls the code the recorded way, and compares the result with the Lean
    object, as exact values. Every agreement raises confidence in M; a single disagreement
    (including the code raising an exception on an input from the domain) refutes it."""
    return _safe(_kernel.sample_model, m, _workdir(), n)


@mcp.tool()
def check_model(m: str, values: list) -> dict:
    """Try to refute a model hypothesis M on an input you choose: one value per argument, each
    an integer, a string like "3/4", or a list of these, lying in that argument's domain
    (e.g. [7, 2, 5] or [["1/2", "1"]]). A disagreement refutes M. Agreements on hand-picked
    inputs add little support however many there are; use sample_model for support and this
    for edge cases, especially ones outside what the claim covers."""
    return _safe(_kernel.observe_model, m, values, _workdir())


@mcp.tool()
def ground(h: str, lean: str, left_out: str = "", added: str = "") -> dict:
    """State that claim `h` means the closed Lean proposition `lean`. Use only when the claim is
    not about a piece of code; a claim about code stated as a closed proposition becomes a fact
    about the concept and says nothing about the code, so use ground_at for those.
    `left_out`: what the sentence says that the proposition does not. `added`: what the
    proposition fixes that the sentence leaves open."""
    return _safe(_kernel.ground, h, lean, left_out=left_out, added=added)


@mcp.tool()
def observe_command(target: str, kind: str, command: str) -> dict:
    """Have the kernel run a shell check (kind: test | property_test | typecheck) in the worktree
    and record pass/fail as evidence for claim `target`. Re-running the same command on the same
    tree is the same evidence and changes nothing."""
    return _safe(_kernel.observe_command, target, kind, command, _workdir())


@mcp.tool()
def observe(target: str, kind: str, outcome: str, source: str) -> dict:
    """Record evidence that cannot be produced by a command (kind: review for claims,
    back_translation for G). `source` must identify the physical origin (e.g. artifact hash)."""
    if kind in ("test", "property_test", "typecheck"):
        return {"error": "use observe_command for this kind"}
    return _safe(_kernel.observe, target, kind, outcome, source)


@mcp.tool()
def declare_independent(eid: str, justification: str) -> dict:
    """Assert that evidence `eid` shares no cause with other evidence on the same target.
    Without this, evidence on one target is treated as possibly redundant."""
    return _safe(_kernel.declare_independent, eid, justification)


@mcp.tool()
def prove(relation: str, args: list[str], proof: str) -> dict:
    """Submit Lean tactic text proving a relation. The goal is stated for you; write tactics only.
      holds [F] | not [F] | iff [F1,F2] | implies [F1,F2] | contradiction [F1,F2]
      pred_iff [P1,P2]      ∀ x, P1 x ↔ P2 x   the two specifications are the same
      pred_implies [P1,P2]  ∀ x, P1 x → P2 x   P1 refines P2
      obj_eq [O1,O2]        O1 = O2            the two objects are the same
      pred_disjoint [P1,P2] ∀ x, ¬(P1 x ∧ P2 x)  nothing can meet both specifications
    Accepted only if the Lean kernel checks it with approved axioms and no sorry. Note that
    `iff` between two propositions that are each already proved says nothing; to say two claims
    are about the same thing, use pred_iff and obj_eq."""
    return _safe(_kernel.prove, relation, args, proof)


@mcp.tool()
def distance(a: str, b: str) -> dict:
    """Bounds on the probability that two claims or propositions disagree (0 = identical)."""
    return _safe(lambda: _kernel.distance(a, b, current=_kernel.versions(_workdir())))


@mcp.tool()
def infer(query: str) -> dict:
    """Bounds [lo, hi] on the probability of a formula over atom ids, for the code as it is in
    your worktree (what was learnt about other versions of a file is set aside), e.g. "H:ab12" or
    "H:ab12 <-> H:cd34". Operators: ! & | -> <->. Rely on a claim only if `lo` is high enough."""
    return _safe(lambda: _kernel.infer(query, current=_kernel.versions(_workdir())))


@mcp.tool()
def status() -> dict:
    """All claims with current bounds and what they are connected to; model hypotheses; the classes of
    propositions, specifications and objects Lean has identified; accepted proofs."""
    return _safe(lambda: _kernel.status(current=_kernel.versions(_workdir())))


if __name__ == "__main__":
    mcp.run()
