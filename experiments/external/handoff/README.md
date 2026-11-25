# 引き継ぎ：miclow に事実の宣言と修正を入れる

前のセッションで、miclow の食い違い 3 件をこの仕組みで直した（`experiments/external/RESULTS.md` の「その後：実際に直した」）。作業は `yuunamaniaiiidx/miclow` のクローンでコミットまで済んだが、そのリポジトリには書き込めなかった。所有者は **`sugipamo/miclow`** を使うことにしたので、そちらに入れる。

## 渡すもの

- `miclow-pw.patch` — 3 コミット分（`git am` で当たる）。土台は `yuunamaniaiiidx/miclow` の main、`79e0afa`（「Merge pull request #10 from yuunamaniaiiidx/develop」）。

| コミット | 中身 |
|----------|------|
| Declare where miclow states the same thing twice, and what is right | `pw-facts.json`（7 つの事実）、`pw-log.jsonl`（読みの記録）、`pw-calibration.json`（読み手の測定）、`.gitattributes`（記録は `merge=union`）。食い違う 3 件に指示を書いた |
| Record the reading of the configuration section as an excerpt | README「設定ファイル形式」を一部を挙げる箇所として読み直した記録 |
| Make the places say what was laid down | `Cargo.toml` のライセンスを MIT に、README の設定のキーをコードに合わせ、`python/README.md` のメソッド一覧をクライアントの実際のメソッドに |

指示の `by` は「Claude, on the owner's leave to decide for miclow」。所有者が判断を任せたので、判断した者としてそう書いてある。所有者の名前で書き換えないこと。

## 手順

1. **土台を確かめる。** `sugipamo/miclow` の既定のブランチが `79e0afa` と同じ中身か見る（`git log`、または `Cargo.toml`・`README.md`・`python/README.md`・`src/config.rs` を比べる）。違えば、パッチを当てる前に所有者に聞く。
2. **作業用のブランチを切ってパッチを当てる。** `git checkout -b claude/<このセッションのブランチ名>`、`git am <パッチ>`。コミットの作者・メッセージはそのまま残す。
3. **この仕組みを用意する。** `sugipamo/parallelworld` を読み取りで追加し、ブランチ `claude/focused-rubin-7dvtcg` の、このファイルがあるコミットを使う（`git -C … log -1` で記録しておく）。
   - Python: `pip install --require-hashes -r requirements-ci.txt`（parallelworld 側）。
   - Lean 4.14.0: parallelworld の `.github/workflows/decisions.yml` の「Lean, by checksum」と同じ手順（アーカイブを取り、SHA-256 を確かめて展開し、`bin` を PATH に）。`lake` がないと、箇所どうしの一致がすべて判定できない。
4. **確かめる。** miclow のクローンで
   ```
   PYTHONPATH=<parallelworld> python -m pw.check --repo . --lean-dir <parallelworld>/lean --verify
   ```
   7 つの事実がすべて `ok` になるはず（前のセッションではそうなった）。ならなければ、出力をそのまま所有者に見せる。読み直しが要ると言われたら `python -m pw.maintain --repo .`（エージェントを使う。課金あり）。
5. **プッシュする。** 作業用のブランチへ。main へのマージとプルリクエストは、所有者が頼んだときだけ。

## 決まっていないこと

- **miclow の CI。** `sugipamo/parallelworld` は非公開なので、miclow の CI からこの仕組みのコードを取ってこられない。選択肢は、parallelworld を公開する／読み取り専用のトークンを miclow のシークレットに置く／仕組みのコードを miclow に写す、のどれか。前のセッションでは「公開してよければ 1 つ目」を勧めたが、所有者の答えはまだない。勝手に決めない。
- **範囲の外として触れていないもの。** `python/README.md` の Convenience Functions に、存在しない `miclow.stdout`・`miclow.stderr` が載っている（宣言していない事実）。README のワーカー例の書式がパーサ（`src/buffer.rs`）と合わない（書式は範囲の外）。どちらも直していない。直すなら所有者に聞く。

## 所有者について分かっていること

- 返事は日本語で。
- コミットの末尾には、セッションの案内どおりの帰属の行を付ける。モデルの識別子は、コミットにもリポジトリのファイルにも書かない。
- プルリクエストは頼まれたときだけ。
- 所有者が言っていないことを、所有者の名前で記録に書かない。
- この仕組みの立場：宣言したものの見落としは指摘する。宣言していないものには関与しない。探索役（`pw.discover`）の既定の仕事は、宣言済みの事実の面倒を見ること。
