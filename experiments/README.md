# 実験の記録

| フォルダ | 何を試したか | 動かすには |
|----------|--------------|-----------|
| `dependency/` | 依存のある並列タスクで、共有の知識が役に立つか | 削除した層。コミット `e11f8fe` |
| `selfcheck/` | この仕組み自身の数学を、この仕組みで確かめる | 同上 |
| `decisions/` | 過去の決定との矛盾を検出できるか | 同上 |
| `nl/` | 自然言語の決定を形式化させると何が起きるか | 同上 |
| `artifacts/` | コードでないファイルを対象にできるか | 同上 |
| `prose/` | 散文の箇所を読ませて安定するか | 同上 |
| `facts/` | 事実と箇所の運用 | 同上（記録の形式はいまと同じ） |
| `calibration/` | 読み手の測定 | いまのコード：`python -m pw.calibrate` |
| `discovery/` | 宣言に漏れた箇所を探させる | コミット `5130a42`（Python 版のカーネルがあった最後のコミット）：`python experiments/discovery/run.py`。探す対象は `e11f8fe` 時点のリポジトリ（正解の箇所の多くが、削除したコードの中にあるため） |
| `external/` | 別のリポジトリで一連の流れを回す | いまのコード |
| `survey/` | さらに 2 つのリポジトリで、複数箇所に書かれている事柄の種類と、宣言できないものを数える | いまのコード |
| `history/` | 2 つのリポジトリの履歴を 1 コミットずつ再生し、使い続けると何が起きるかを数える | コミット `5130a42`：`python experiments/history/run.py`（miclow のクローンが要る。`--read` は課金あり）。`rust.py` は Python 版と Rust 版の突き合わせ |
| `patterns/` | 宣言済みのパターンに、値を変えない書き換えと値を変える編集を当て、読めなくなる・別の値を読む・見逃す頻度を測る | コミット `5130a42`：`python experiments/patterns/run.py <リポジトリ>...` |
| `merge/` | 2 つのブランチが記録を足してからマージしたとき、判定が向きによらず同じで正しいか | コミット `5130a42`：`python experiments/merge/run.py` |
| `scale/` | 事実の数と `pw.check` の所要時間 | コミット `5130a42`：`python experiments/scale/run.py` |
| `gate/` | 読み手の値として Lean に渡る文字列で、偽の一致を作れるか、チェックを止められるか | コミット `5130a42`：`python experiments/gate/run.py` |
| `hard/` | 手で書いた読み違えやすい文面で、目隠しの読み手を測る | コミット `5130a42`：`python experiments/hard/run.py`（課金あり） |

`5130a42` と書いた実験は、Python 版のカーネル（`pw/kernel.py` の `Kernel`、`pw/lean_gate.py`、Python 版の `pw.check`）を直接使う。判定と記録は Rust 版に移してそれらは消したので、動かすにはそのコミットを取り出す（`git worktree add ../pw-5130a42 5130a42`）。結果（`RESULTS.md`）はそのとき測ったもの。

上の 7 つは、主張・接続・確率の区間・並列ワーカーの層の上で行った。その層は削除した（`docs/spec.md` §7）。`RESULTS.md` と `results/` は当時のまま残してあり、`run.py` を動かすには削除前の最後のコミット `e11f8fe` のコードが要る。

`selfcheck/lean/` は mathlib を使う別の Lean プロジェクトで、その `lean-toolchain` は「Lean の版」という事実の箇所として宣言してある。
