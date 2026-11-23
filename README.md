# parallelworld

並列コーディングエージェントが共有する知識を、ベイズ推定とLeanの証明だけで扱うバックエンドの叩き台。

- 設計: [docs/spec.md](docs/spec.md)
- `pw/kernel.py` — イベントログと区間推論
- `pw/lean_gate.py` — Lean による証明の検証
- `pw/mcp_server.py` — Claude Code ワーカー向け MCP サーバー
- `pw/orchestrator.py` — worktree ごとにワーカーを並列起動し、主張の下界でマージ可否を判定

## 動かす

```
pip install scipy numpy mcp pytest
python -m pytest tests
python -m pw.orchestrator tasks.json --dry-run     # 起動コマンドの確認のみ
python -m pw.orchestrator tasks.json               # claude-opus-5-5 のワーカーを起動（課金あり）
```

`prove` には `lean/lean-toolchain` と同じ版の Lean 4 が必要。`lake` が PATH にないときは `PW_LAKE` でパスを渡す。
Lean がない、または版が違うときは、証明はすべて不受理になる（`tests/test_lean_real.py` はスキップされる）。
