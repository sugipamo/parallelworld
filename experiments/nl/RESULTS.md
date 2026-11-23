# 自然言語の決定の形式化 ― 実行の記録

実行:

```
python -m experiments.nl.run OUT_DIR formalize    # 互いに見えない 3 体が同じ 12 決定を形式化する
python -m experiments.nl.run OUT_DIR judge        # 4 体目が形式化どうしの関係を Lean で判定する
python -m experiments.nl.run OUT_DIR summary
```

- `results/formalizations.json` — 3 体それぞれの分類、Lean の命題または検査コマンド、落としたもの・足したもの、指摘した矛盾、ワーカーの報告。
- `results/comparisons.json` — 9 組の比較と、判定側の Kernel が受理した証明の一覧。

結果の読み取りと知見は [docs/natural-language.md](../../docs/natural-language.md) にまとめた。
