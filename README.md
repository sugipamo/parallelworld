# parallelworld

プロジェクトが何箇所にも書いている同じ事柄（既定値、版、名前の一覧など）を宣言しておき、全部の箇所が同じ値のままであることを確かめ続ける仕組み。

- 箇所の読みは、宣言したパターンで計算するか、その箇所だけを見せたエージェント（目隠しの読み手）に読ませる。
- 箇所どうしが一致するかは、読んだ値の等式として Lean が判定する。
- 読みを当てにしてよいかは、プロジェクトが書く規則の表（`pw-rules.json`）で決める。

設計は [docs/spec.md](docs/spec.md)。もとは、並列コーディングエージェントが共有する知識をベイズ推定と Lean の証明で扱うバックエンドの叩き台だった。その層は使われなかったので削除した（経緯は仕様書の §7、当時の仕様は [docs/archive/](docs/archive/)、知見は [docs/natural-language.md](docs/natural-language.md)）。

- `pw/kernel.py` — 記録と、事実・読み・一致の判定・規則の適用
- `pw/lean_gate.py` — Lean による等式の判定
- `pw/check.py` — 宣言された事実を、いまのファイルに当て直す（言語モデルなし）
- `pw/maintain.py` — 変わった箇所・未読の箇所を、目隠しの読み手に読ませる
- `pw/mcp_server.py` — 読み手が答えるための道具
- `pw/calibrate.py` — 読み手を測る
- `pw/discover.py` — 宣言に漏れている箇所と、まだ宣言されていない事実をエージェントに探させる
- `pw/confirm.py` — エージェントの読みを、根拠の一文と並べて人が確認する
- `pw-facts.json` — このプロジェクトの事実と、それを述べている箇所の一覧
- `pw-log.jsonl` — 記録（読み、証明、人の確認）。追記式のテキストで、リポジトリに含める
- `pw-rules.json` — 読みが成り立つ条件の表と、読み手に求める測定の基準
- `pw/reader.txt` — 目隠しの読み手に渡す指示文。変えると読み手の測り直しになる
- `pw-calibration.json` — 読み手の測定結果

実験の記録: [依存のある並列タスク](experiments/dependency/RESULTS.md)、[自己適用](experiments/selfcheck/RESULTS.md)、[過去の決定との矛盾](experiments/decisions/RESULTS.md)、[自然言語の決定の形式化](experiments/nl/RESULTS.md)、[コードでないファイル](experiments/artifacts/RESULTS.md)、[散文](experiments/prose/RESULTS.md)、[事実と箇所](experiments/facts/RESULTS.md)、[読み手の測定](experiments/calibration/RESULTS.md)、[箇所の探索](experiments/discovery/RESULTS.md)、[別のリポジトリで使う](experiments/external/RESULTS.md)（最初の 7 つは削除した層の上で行ったもの。[experiments/README.md](experiments/README.md)）

## 動かす

```
pip install scipy numpy mcp pytest          # CI は requirements-ci.txt の版とハッシュで固定している
python -m pytest tests
python -m pw.check --repo .                        # 事実をいまのファイルで確かめ直す。通らないものがあれば終了コード 1
python -m pw.check --repo . --verify               # 加えて、記録にある証明を Lean に通し直す（CI はこれを回す：.github/workflows/decisions.yml）
python -m pw.maintain --repo .                     # 上に加えて、変わった箇所を目隠しの読み手に読み直させる（課金あり）
python -m pw.confirm --repo .                      # エージェントの読みのうち、誰も確認していないものを一覧する
python -m pw.calibrate --repo .                    # 値をわざと書き換えた本文とおとりを読ませ、読み手を測る（課金あり）
python -m pw.discover --repo . --apply            # 宣言に漏れている箇所と新しい事実を探させ、pw-facts.json に書き込む（課金あり）
```

一致の判定には `lean/lean-toolchain` と同じ版の Lean 4 が必要。`lake` が PATH にないときは `PW_LAKE` でパスを渡す。
Lean がない、または版が違うときは、判定はすべて不受理になる（`tests/test_lean_real.py` はスキップされる）。
