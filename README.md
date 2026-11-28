# parallelworld

プロジェクトが何箇所にも書いている同じ事柄（既定値、版、名前の一覧など）を宣言しておき、全部の箇所が同じ値のままであることを確かめ続ける仕組み。面倒を見るのは宣言したものだけで、宣言していないものには関与しない。

- 箇所の読みは、宣言した読み方（文字の並びのパターン、または Python の構文・TOML や JSON の構造）で計算するか、その箇所だけを見せたエージェント（目隠しの読み手）に読ませる。
- 箇所どうしが一致するかは、読んだ値（書き下した数・文字列・その一覧）をそのまま比べて決める。値を計算しないと決まらないとき（ほかの事実から式で導く定義）は、等式として Lean が判定する。
- 読みを当てにしてよいかは、プロジェクトが書く規則の表（`pw-rules.json`）で決める。
- 人が「この値はこうである」と決めた指示は公理として書いておける。箇所はそれに照らし、指示どうしが食い違えば、どちらも使わずに人に戻す。
- ほかの事実から式で導く事実（個数、最小値など）は、定義として宣言できる。

設計は [docs/spec.md](docs/spec.md)。もとは、並列コーディングエージェントが共有する知識をベイズ推定と Lean の証明で扱うバックエンドの叩き台だった。その層は使われなかったので削除した（経緯は仕様書の §7、当時の仕様は [docs/archive/](docs/archive/)、知見は [docs/natural-language.md](docs/natural-language.md)）。

- `rust/` — この仕組みの全部。実行ファイル `pw` 1 つ。記録、事実・読み・一致の判定、規則の適用、Lean による判定（`pw check`、`pw confirm`）と、エージェントを使う側（`pw maintain`、`pw calibrate`、`pw discover`、`pw propagate`、`pw start`）。読み手が答えるための道具（MCP）も `pw mcp` として同じ実行ファイルが出す
- `tests/` — 外から実行ファイルを動かすテスト（pytest）。`tests/pwt/` はテストが実行ファイルに 1 操作ずつ頼むための補助で、仕組みの一部ではない。`tests/fake_claude.py` は `claude` の代わりに MCP の道具を呼ぶ、テスト用の読み手と書き手
- `pw-facts.json` — このプロジェクトの事実と、それを述べている箇所の一覧
- `pw-log.jsonl` — 記録（読み、証明、人の確認）。追記式のテキストで、リポジトリに含める
- `pw-rules.json` — 読みが成り立つ条件の表と、読み手に求める測定の基準
- `pw/reader.txt` — 目隠しの読み手に渡す指示文（実行ファイルに埋め込む）。変えると読み手の測り直しになる
- `pw/rules.json` — 規則の表の既定（実行ファイルに埋め込む）。対象のリポジトリに `pw-rules.json` がなければこれを使う
- `rust/calibration/passages.json` — 読み手を測るための、答えの分かっている文面（実行ファイルに埋め込む）。対象のリポジトリの文面だけでは測りきれないときに足す
- `pw-calibration.json` — 読み手の測定結果
- `action.yml`、`ci/lean.sh` — ほかのリポジトリの CI から使うための入口と、Lean を取ってくる手順（下の「他のリポジトリから使う」）

実験の記録: [依存のある並列タスク](experiments/dependency/RESULTS.md)、[自己適用](experiments/selfcheck/RESULTS.md)、[過去の決定との矛盾](experiments/decisions/RESULTS.md)、[自然言語の決定の形式化](experiments/nl/RESULTS.md)、[コードでないファイル](experiments/artifacts/RESULTS.md)、[散文](experiments/prose/RESULTS.md)、[事実と箇所](experiments/facts/RESULTS.md)、[読み手の測定](experiments/calibration/RESULTS.md)、[箇所の探索](experiments/discovery/RESULTS.md)、[別のリポジトリで使う](experiments/external/RESULTS.md)、[何が乗らないかの調査](experiments/survey/RESULTS.md)、[履歴の再生](experiments/history/RESULTS.md)、[パターンの壊れ方](experiments/patterns/RESULTS.md)、[記録のマージ](experiments/merge/RESULTS.md)、[規模と所要時間](experiments/scale/RESULTS.md)、[Gate のふるいへの攻撃](experiments/gate/RESULTS.md)、[読み違えやすい文面での測定](experiments/hard/RESULTS.md)（最初の 7 つは削除した層の上で行ったもの。[experiments/README.md](experiments/README.md)）

## 動かす

```
cargo build --release --manifest-path rust/Cargo.toml   # 実行ファイル rust/target/release/pw。以下の pw はこれ（cargo install --path rust で PATH に置ける）
pw start --repo .                       # 初めて使うリポジトリで：準備、事実の提案、読み手の測定、読み、確認を順に。費用のかかる手順の前で止まって、何にいくらまで使うかを言う
pw check --repo .                       # 事実をいまのファイルで確かめ直す。通らないものがあれば終了コード 1。記録（pw-log.jsonl）には書かない
pw check --repo . --verify              # 加えて、記録にある証明を Lean に通し直す（CI はこれを回す：.github/workflows/decisions.yml）
pw check --repo . --record              # 確かめた結果（計算した読み、Lean の証明）を記録に書き足す。ふつうは要らない
pw maintain --repo .                    # 変わった箇所・未読の箇所を目隠しの読み手に読ませる（課金あり）。読みは記録に書き足されるので、コミットに含める
pw confirm --repo .                     # エージェントの読みのうち、誰も確認していないものを一覧する
pw calibrate --repo .                   # 値をわざと書き換えた本文とおとりを読ませ、読み手を測る（課金あり）
pw discover --repo . --apply            # 宣言した事実について、読めなくなった箇所を付け替え、漏れている箇所を探す（課金あり）
pw discover --repo . --new --apply      # 加えて、まだ宣言されていない事柄を提案させる
pw propagate --repo .                   # 人が定めた値と違う箇所への書き戻しを、差分で示す（--apply で適用）
pw propagate --repo . --suppose 'Lean version=4.15.0'   # 仮にこの値にしたら、どこを書き換えることになるか
pw propagate --repo . --agent           # 一覧や散文は、エージェントに新しい本文を出させて読み戻す（課金あり）
pw help COMMAND                         # 各コマンドの説明
python -m pytest tests                  # テスト（pytest だけが要る。CI は requirements-test.txt の版とハッシュで固定している）
```

動かすのは Linux と macOS。Windows には対応しない。

宣言に定義（`defined`）があるとき、または `--lean always` で全部の比較を Lean に通すときは、`lean/lean-toolchain` と同じ版の Lean 4 が必要（このリポジトリ自身は定義を 1 つ宣言しているので要る）。定義がなければ Lean は要らない。`pw check --needs-lean` が yes か no で答える。`lake` が PATH にないときは `PW_LAKE` でパスを渡す。
Lean が要るのに無い、または版が違うときは、`pw check` は何も確かめずに、理由を 1 行で言って終了コード 2 で止まる（`tests/test_lean_real.py` はスキップされる）。終了コードは、確かめて通らなければ 1、確かめられなければ 2（Lean が使えない、`pw-facts.json` が無い・書き方が違う）。
その版の Lean が手元になければ `ci/lean.sh` が取ってくる（`export PATH="$(ci/lean.sh):$PATH"`。Linux x86_64 のみ。`curl` と `zstd` が要る）。

Lean は `lean/` の中では動かさない。`lean/` の中身を `~/.cache/parallelworld/`（`PW_LEAN_WORK` で変えられる）に写し、そこでビルドと判定をする。仕組みを置いた場所は読むだけなので、読み取り専用でも、ほかのジョブと共有していてもよい。

## 実行ファイル 1 つ

この仕組みは Rust で書いた実行ファイル 1 つ（`rust/`）で、Python は使わない（テストを除く）。

- Lean は、定義のある事実か `--lean always` のときだけ要る。エージェントを使うコマンドには `claude` の CLI が要る（足りなければ、読み手を呼ぶ前に止まり、課金は起きない）。
- このリポジトリの確認は 0.5 秒、`--verify` つきで 1.3 秒（以前の Python 版は 1.8 秒と 2.6 秒）。
- 以前は同じカーネルが Python にもあった。2 つのリポジトリの全履歴（判定 3,670 件）で両方の判定が 1 件も違わないこと、記録に書く行が 1 行ずつ同じことを確かめてから、Python 版を消した（`experiments/history/RESULTS.md`）。エージェント側（maintain・calibrate・discover・propagate）も、同じ出力と同じ記録の行になるように Rust に移し、Python のパッケージは消した（0.17.0）。
- 同じことを 2 か所で実装しているところは、もうない。

## 他のリポジトリから使う

対象のリポジトリに置くのは、宣言（`pw-facts.json`）と、読み手が書く記録（`pw-log.jsonl`、`pw-calibration.json`）、変えたければ規則の表（`pw-rules.json`）。この仕組みのコードは写さない。記録をブランチどうしで両方残してマージするには、対象のリポジトリの `.gitattributes` に `pw-log.jsonl merge=union` と書く。

最初の一歩は `pw init --repo 対象のリポジトリ`。空の宣言、`.gitattributes` のその 1 行、このアクションを使う CI のジョブ（`.github/workflows/facts.yml`。いま使っているこの仕組みのクローンのコミットに固定する。別のコミットにするなら `--pin`）を置く。すでにあるファイルは書き換えない。あとは事実を宣言するか、`pw discover --repo . --new --apply` でエージェントに提案させ、`pw maintain --repo .` で読ませてコミットする。`pw start` は、この順を 1 つずつ（済んだものは飛ばして）進める。

### 手元で

```
export PATH="$(/path/to/parallelworld/ci/pw.sh | xargs dirname):$PATH"   # 公開済みの実行ファイルを取ってくる（なければビルドする）。cargo install --path rust でもよい
export PATH="$(/path/to/parallelworld/ci/lean.sh):$PATH"              # 同じ版の Lean が PATH になく、定義を宣言しているとき
cd 対象のリポジトリ
pw start
```

- `--lean-dir` は付けなくてよい（Lean のプロジェクトは実行ファイルに入っている）。
- エージェントを使うもの（`pw maintain`、`pw calibrate`、`pw discover`、`pw propagate --agent`、`pw start`）には、`claude` の CLI が要る。それ以外は要らない。
- `pw maintain` は作業ツリーの内容をそのまま読む。文面の変更と、増えた `pw-log.jsonl` を、同じコミットに入れてよい。
- `pw check` は何もファイルを書き換えない。対象のリポジトリの記録が増えるのは、`pw maintain`・`pw confirm`・`pw discover --apply`・`pw propagate --apply` と、`pw check --record` を回したとき。増えた行はコミットに含める。
- 読み方（パターンなど）を替えたら、`pw maintain` か `pw check --record` を回して、増えた行をコミットする。読み手は呼ばれない。替えたまま記録に残さないと、その箇所を次に編集したときに読み直しになる（`pw check` が note として挙げる）。

### CI で

このリポジトリは、そのままアクションとして使える。対象のリポジトリのワークフローに 1 ステップ足す。

```yaml
permissions:
  contents: read

jobs:
  facts:
    runs-on: ubuntu-24.04
    steps:
      - uses: actions/checkout@<コミット>
        with:
          persist-credentials: false
      - uses: sugipamo/parallelworld@<このリポジトリのコミット>
```

- することは、Rust 版の `check` を用意すること（`ci/pw.sh`。`rust/release.txt` が、このコミットのソースからビルドして公開した実行ファイルを SHA-256 つきで名指ししていれば、それを取ってきてチェックサムを照らす。1 秒ほど。名指しがない、またはソースが違うときは、ランナーの `cargo` でソースからビルドする。クレートは `rust/Cargo.lock` のチェックサムで固定、4 コアで 1 分半ほど）、宣言に定義があるときだけ Lean の取得（`lean/lean-toolchain` の版、`ci/lean.sh` のチェックサムで固定）、`pw check --repo . --verify`。エージェントは使わない。何もキャッシュしない。
- **使う側が固定するのは、このリポジトリのコミット 1 つ。** Lean の版もチェックサムもクレートのチェックサムも、そのコミットの中で決まる。使う側に写す値はない。
- 入力は 2 つ。`repo`（確かめるディレクトリ。既定は `.`）と `args`（`pw check` に渡す引数。既定は `--verify`。規則を満たさない読みを警告にとどめるなら `--verify --unconfirmed warn`）。
- CI は記録を読むだけなので、手元で確かめたときと記録の中身がずれない。

### 参照先を上げるとき

1. 固定しているコミットを上げ、`pw check --repo . --verify` を回す。使う側で何かが要る変更は [CHANGES.md](CHANGES.md) に書いてある。
2. 通れば終わり。読み手の指示文（`pw/reader.txt`）が変わった更新でも、すでにある読みは落ちない。読みは、それを読んだときの読み手のものとして数える。
3. そのあと新しく読ませる（`pw maintain`）前に、新しい指示文の読み手を測る：`pw calibrate --repo .`（モデルごと。基準に届かなければ `--seed` を変えて足す。1 回 $1〜2 ほど）。測る前に読ませた読みは、測るまで数えられない。
