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
| `discovery/` | 宣言に漏れた箇所を探させる | いまのコード：`python experiments/discovery/run.py`（課金あり）。探す対象は `e11f8fe` 時点のリポジトリ（正解の箇所の多くが、削除したコードの中にあるため） |
| `external/` | 別のリポジトリで一連の流れを回す | いまのコード |
| `survey/` | さらに 2 つのリポジトリで、複数箇所に書かれている事柄の種類と、宣言できないものを数える | いまのコード |
| `history/` | 2 つのリポジトリの履歴を 1 コミットずつ再生し、使い続けると何が起きるかを数える | いまのコード：`python experiments/history/run.py`（miclow のクローンが要る。`--read` は課金あり） |
| `patterns/` | 宣言済みのパターンに、値を変えない書き換えと値を変える編集を当て、読めなくなる・別の値を読む・見逃す頻度を測る | いまのコード：`python experiments/{d}/run.py <リポジトリ>...` |
| `merge/` | 2 つのブランチが記録を足してからマージしたとき、判定が向きによらず同じで正しいか | いまのコード：`python experiments/{d}/run.py` |
| `scale/` | 事実の数と `pw.check` の所要時間 | いまのコード：`python experiments/{d}/run.py` |
| `gate/` | 読み手の値として Lean に渡る文字列で、偽の一致を作れるか、チェックを止められるか | いまのコード：`python experiments/{d}/run.py` |
| `hard/` | 手で書いた読み違えやすい文面で、目隠しの読み手を測る | いまのコード：`python experiments/{d}/run.py`（課金あり） |

`discovery`・`history`・`patterns`・`merge`・`scale`・`gate`・`hard` は、Python 版のカーネルを消したあと、いまのコード（`pw/core.py` 経由で Rust 版）で動くように直した。`history`（言語モデルなし）・`patterns`・`merge`・`scale`・`gate` は回し直して確かめた（各 `RESULTS.md` の最後の節）。`discovery` と `hard` は読み手を呼ぶ（課金あり）ので、読み込めることだけ確かめて、回し直してはいない。

上の 7 つは、主張・接続・確率の区間・並列ワーカーの層の上で行った。その層は削除した（`docs/spec.md` §7）。`RESULTS.md` と `results/` は当時のまま残してあり、`run.py` を動かすには削除前の最後のコミット `e11f8fe` のコードが要る。

`selfcheck/lean/` は mathlib を使う別の Lean プロジェクトで、その `lean-toolchain` は「Lean の版」という事実の箇所として宣言してある。
