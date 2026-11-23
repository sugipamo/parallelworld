"""Decisions about prose: passages of docs/spec.md (Japanese text and tables).

    python -m experiments.prose.run OUT_DIR read       three agents, kept apart, read the same passages
    python -m experiments.prose.run OUT_DIR maintain   edits to the document and the code, held against the decisions

Each decision fixes a fact (which axioms are allowed, the largest component, the tool names, the
states a check reports, the default dependence class). The document must say it, and where the
code states the same fact, the code must too: the document is read by an agent, the code by a
recorded reader.
"""
import json
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, ROOT)
from pw.kernel import LOG, Kernel, KernelError, reader  # noqa: E402
from pw.lean_gate import LEAN_DIR, LeanGate  # noqa: E402

AUTHORS = ["r1", "r2", "r3"]
TOOLS = ["check_model", "claim", "declare_independent", "distance", "ground", "ground_at", "infer", "model",
         "observe", "observe_command", "prove", "reject_object", "sample_model", "status"]
lean_list = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"

# fact: (type, predicate, where the document says it, what to read there, where the code says it, reader)
FACTS = {
    "axioms": ("List String", f'fun l => l = {lean_list(["Classical.choice", "Quot.sound", "propext"])}',
               "docs/spec.md::5. Lean Gate", "the axioms an accepted proof may depend on, sorted alphabetically",
               "pw/lean_gate.py::ALLOWED_AXIOMS",
               '"[" + ", ".join(lean_string(x) for x in sorted(re.findall(r\'"([^"]+)"\', part))) + "]"'),
    "largest component": ("Nat", "fun n => n = 14",
                          "docs/spec.md::7. 未解決", "the largest number of atoms in a connected component that inference still solves",
                          "pw/kernel.py::Kernel.__init__", 're.search(r"max_atoms=(\\d+)", part).group(1)'),
    "tools": ("List String", f"fun l => l = {lean_list(TOOLS)}",
              "docs/spec.md::4. 操作（MCPツール）", "the names of the MCP tools, sorted alphabetically",
              "pw/mcp_server.py",
              '"[" + ", ".join(lean_string(x) for x in sorted(re.findall(r"@mcp\\.tool\\(\\)\\ndef (\\w+)\\(", data))) + "]"'),
    "states": ("List String", f'fun l => l = {lean_list(["current", "re-established", "stale", "uncovered", "unsupported", "violated"])}',
               "docs/spec.md::9. 時間をまたぐ決定",
               "the states the recheck (pw.check) can report for a formal decision, each translated to one of the English "
               "words current, re-established, violated, uncovered, stale, unsupported, sorted alphabetically",
               None, None),
    "default dependence": ("String", 'fun s => s = "pqd"',
                           "docs/spec.md::3. モデル", "the name of the copula class used by default for evidence on one target",
                           "pw/kernel.py::Kernel.__init__", 'lean_string(re.search(r\'dependence="(\\w+)"\', part).group(1))'),
}

READ = ("Each required claim is about one passage of docs/spec.md, which is written in Japanese. The passage is the "
        "section under the heading named in the claim. For each claim: read the passage and state what it says as a Lean "
        "term of the claim's type with `model(h, object)` (no setup, call or domains: a document cannot be called). Write "
        "what the passage itself says. Do not look at the code or at other sections to fill in or correct it; if the "
        "passage does not say it, or says something else, write that. Then prove `holds [F]`, or `not [F]` if what the "
        "passage says does not satisfy the claim. Do not change any file.")

EDITS = {
    "elsewhere": [("docs/spec.md", "## 1. 構成\n", "## 1. 構成\n\nこの節は全体の構成をまとめたものである。\n")],
    "reworded": [("docs/spec.md", "許可リスト（`propext`、`Classical.choice`、`Quot.sound`）に収まる",
                  "そこに挙がる公理が `Quot.sound`・`propext`・`Classical.choice` の三つの範囲内である")],
    "meaning changed": [("docs/spec.md", "連結成分が14原子を超えると解けない", "連結成分が16原子を超えると解けない"),
                        ("docs/spec.md", "既定の `pqd` は正の依存で、独立と完全な重複の間。", "既定の `frechet` は依存について何も仮定しない。")],
    "code changed": [("pw/lean_gate.py", 'frozenset({"propext", "Classical.choice", "Quot.sound"})',
                      'frozenset({"propext", "Classical.choice", "Quot.sound", "Lean.ofReduceBool"})')],
}


def sh(*cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, check=True, capture_output=True, text=True)


def clone(dest):
    shutil.rmtree(dest, ignore_errors=True)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    sh("git", "clone", "-q", ROOT, dest, cwd=ROOT)
    sh("git", "config", "user.name", "pw", cwd=dest)
    sh("git", "config", "user.email", "pw@localhost", cwd=dest)


def doc_claims():
    return [{"subject": doc, "type": typ, "predicate": pred, "gloss": what} for typ, pred, doc, what, _, _ in FACTS.values()]


def readings(repo):
    """What each document decision was read as, and what was then proved."""
    k = Kernel(os.path.join(repo, LOG))
    st = k.state()
    out = {}
    for name, (typ, pred, doc, *_rest) in FACTS.items():
        hs = [h for h, f in st.formal.items() if f["subject"] == doc and st.algebra.preds[f["pred"]]["text"] == " ".join(pred.split())]
        said = [(st.algebra.objs[st.models[x]["obj"]]["text"], f) for gs, hh, f in st.links if hs and hh == hs[0] for x in gs if x[0] == "M"]
        verdict = [p["relation"] for p in st.proofs if said and p["relation"] in ("holds", "not") and p["args"] == [said[-1][1]]]
        out[name] = {"read as": said[-1][0] if said else None, "proved": verdict[-1] if verdict else None}
    return out


def worker(repo, name):
    with open(os.path.join(repo, ".pw", f"worker-{name}.json")) as fh:
        d = json.load(fh)
    return {"turns": d.get("num_turns"), "cost_usd": round(d.get("total_cost_usd", 0), 2),
            "seconds": round(d.get("duration_ms", 0) / 1000), "report": d.get("result", "")}


def read(out):
    def one(author):
        repo = os.path.join(out, author)
        clone(repo)
        tasks = os.path.join(repo, ".pw", "tasks.json")
        os.makedirs(os.path.dirname(tasks))
        with open(tasks, "w") as fh:
            json.dump([{"name": "read", "prompt": READ, "requires": doc_claims()}], fh, ensure_ascii=False)
        subprocess.run([sys.executable, "-m", "pw.orchestrator", tasks, "--repo", repo, "--budget", "4"], cwd=ROOT, capture_output=True, text=True)
        return author, {"readings": readings(repo), "worker": worker(repo, "read")}

    with ThreadPoolExecutor(3) as pool:
        result = dict(pool.map(one, AUTHORS))
    with open(os.path.join(out, "read.json"), "w") as fh:
        json.dump(result, fh, ensure_ascii=False, indent=1)
    for name in FACTS:
        print(name)
        for a in AUTHORS:
            r = result[a]["readings"][name]
            print(f"   {a} [{r['proved']}] {r['read as']}")
    print({a: (r["worker"]["turns"], r["worker"]["cost_usd"], r["worker"]["seconds"]) for a, r in result.items()})


def check(repo, module="pw.check"):
    r = subprocess.run([sys.executable, "-m", module, "--repo", repo], cwd=ROOT, capture_output=True, text=True)
    return {"exit": r.returncode, "output": (r.stdout + r.stderr).strip()}


def maintain(out):
    repo = os.path.join(out, AUTHORS[0])
    k = Kernel(os.path.join(repo, LOG), gate=LeanGate(LEAN_DIR), actor="person")
    result = {}

    def step(name, value):
        result[name] = value
        with open(os.path.join(out, "maintain.json"), "w") as fh:
            json.dump(result, fh, ensure_ascii=False, indent=1)
        print(f"== {name} (exit {value.get('exit', '-')})\n{value['output']}\n", flush=True)

    # the code side of each fact: computed by a reader, proved once
    for name, (typ, pred, _doc, _what, code, expr) in FACTS.items():
        if code:
            h = k.claim_formal(code, typ, pred, f"the code states the same fact: {name}")["h"]
            a = k.attach_derived(h, reader(expr, "text"), repo)
            ok = next((t for t in ("rfl", "decide", "simp") if k.prove("holds", [a["f"]], t)["accepted"]), None)
            print(f"code side of {name}: read as {k.state().algebra.objs[a['o']]['text'][:70]} proved by {ok}", flush=True)
    step("as read by the first agent", check(repo))
    for m in k.state().models:
        try:
            if not k.state().models[m]["binding"]:
                k.sign_off(m, "reviewer")
        except KernelError:
            pass
    step("after a person confirms the agent's readings", check(repo))

    for label, edits in EDITS.items():
        for path, old, new in edits:
            with open(os.path.join(repo, path), encoding="utf-8") as fh:
                text = fh.read()
            assert text.count(old) == 1, (path, old)
            with open(os.path.join(repo, path), "w", encoding="utf-8") as fh:
                fh.write(text.replace(old, new))
        sh("git", "commit", "-qam", label, cwd=repo)
        step(f"{label}: check", check(repo))
        if result[f"{label}: check"]["exit"] and "stale" in result[f"{label}: check"]["output"]:
            step(f"{label}: maintain", check(repo, "pw.maintain"))
    result["workers"] = {f[7:-5]: worker(repo, f[7:-5]) for f in sorted(os.listdir(os.path.join(repo, ".pw"))) if f.startswith("worker-maintain")}
    result["readings at the end"] = readings(repo)
    with open(os.path.join(out, "maintain.json"), "w") as fh:
        json.dump(result, fh, ensure_ascii=False, indent=1)
    print({w: (v["turns"], v["cost_usd"], v["seconds"]) for w, v in result["workers"].items()})


if __name__ == "__main__":
    {"read": read, "maintain": maintain}[sys.argv[2]](os.path.abspath(sys.argv[1]))
