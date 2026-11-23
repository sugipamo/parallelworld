# parallelworld

並列コーディングエージェントが共有する知識を、ベイズ推定とLeanの証明だけで扱うバックエンドの叩き台。

- 設計: [docs/spec.md](docs/spec.md)、記号と既存概念への対応: [docs/symbols.md](docs/symbols.md)
- 自然言語の決定がどこまで乗るかの知見: [docs/natural-language.md](docs/natural-language.md)
- `pw/lindenbaum.py` — 形式層（検証済みの関係で表示されたブール代数、仕様と対象、合同閉包）
- `pw/credal.py` — 確率層（クレーダル集合、一般化ベイズ則、コピュラ）
- `pw/kernel.py` — イベントログと、主張を命題に結ぶ信頼性モデル
- `pw/lean_gate.py` — Lean による証明の検証
- `pw/mcp_server.py` — Claude Code ワーカー向け MCP サーバー
- `pw/orchestrator.py` — worktree ごとにワーカーを並列起動し、主張の下界でマージ可否を判定

- `pw/check.py` — 立っている決定を、いまのファイルに当て直す（言語モデルなし）
- `pw/maintain.py` — 当て直しで残った失効を、エージェントに読み直させる
- `pw/confirm.py` — エージェントの読みを、根拠の一文と並べて人が確認する
- `pw-facts.json` — このプロジェクトの事実と、それを述べている箇所の一覧
- `pw-log.jsonl` — 記録（読み、証明、人の確認）。追記式のテキストで、リポジトリに含める

実験の記録: [依存のある並列タスク](experiments/dependency/RESULTS.md)、[自己適用](experiments/selfcheck/RESULTS.md)、[過去の決定との矛盾](experiments/decisions/RESULTS.md)、[自然言語の決定の形式化](experiments/nl/RESULTS.md)、[コードでないファイル](experiments/artifacts/RESULTS.md)、[散文](experiments/prose/RESULTS.md)、[事実と箇所](experiments/facts/RESULTS.md)

## 動かす

```
pip install scipy numpy mcp pytest
python -m pytest tests
python -m pw.orchestrator tasks.json --dry-run     # 起動コマンドの確認のみ
python -m pw.orchestrator tasks.json               # claude-opus-5-5 のワーカーを起動（課金あり）
python -m pw.check --repo .                        # 決定をいまのファイルで確かめ直す。機械的に通らないものがあれば終了コード 1
python -m pw.check --repo . --verify               # 加えて、記録にある証明を Lean に通し直す（CI ではこちら）
python -m pw.maintain --repo .                     # 上に加えて、変わったファイルをエージェントに読み直させる（課金あり）
python -m pw.confirm --repo .                      # エージェントの読みのうち、誰も確認していないものを一覧する
```

`prove` には `lean/lean-toolchain` と同じ版の Lean 4 が必要。`lake` が PATH にないときは `PW_LAKE` でパスを渡す。
Lean がない、または版が違うときは、証明はすべて不受理になる（`tests/test_lean_real.py` はスキップされる）。
