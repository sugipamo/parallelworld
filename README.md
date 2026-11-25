# parallelworld

プロジェクトが何箇所にも書いている同じ事柄（既定値、版、名前の一覧など）を宣言しておき、全部の箇所が同じ値のままであることを確かめ続ける仕組み。面倒を見るのは宣言したものだけで、宣言していないものには関与しない。

- 箇所の読みは、宣言したパターンで計算するか、その箇所だけを見せたエージェント（目隠しの読み手）に読ませる。
- 箇所どうしが一致するかは、読んだ値の等式として Lean が判定する。
- 読みを当てにしてよいかは、プロジェクトが書く規則の表（`pw-rules.json`）で決める。
- 人が「この値はこうである」と決めた指示は公理として書いておける。箇所はそれに照らし、指示どうしが食い違えば、どちらも使わずに人に戻す。
- ほかの事実から式で導く事実（個数、最小値など）は、定義として宣言できる。

設計は [docs/spec.md](docs/spec.md)。もとは、並列コーディングエージェントが共有する知識をベイズ推定と Lean の証明で扱うバックエンドの叩き台だった。その層は使われなかったので削除した（経緯は仕様書の §7、当時の仕様は [docs/archive/](docs/archive/)、知見は [docs/natural-language.md](docs/natural-language.md)）。

- `pw/kernel.py` — 記録と、事実・読み・一致の判定・規則の適用
- `pw/lean_gate.py` — Lean による等式の判定
- `pw/check.py` — 宣言された事実を、いまのファイルに当て直す（言語モデルなし。記録は読むだけで、書き足さない）
- `pw/maintain.py` — 変わった箇所・未読の箇所を、目隠しの読み手に読ませる
- `pw/mcp_server.py` — 読み手が答えるための道具
- `pw/calibrate.py` — 読み手を測る
- `pw/discover.py` — 宣言した事実の面倒を探索役に見させる（読めなくなった箇所の付け替え、漏れている箇所の探索。頼めば新しい事実の提案も）
- `pw/confirm.py` — エージェントの読みを、根拠の一文と並べて人が確認する
- `pw/propagate.py` — 人が定めた値（または仮に置いた値）を、それと違う箇所に書き戻す
- `pw-facts.json` — このプロジェクトの事実と、それを述べている箇所の一覧
- `pw-log.jsonl` — 記録（読み、証明、人の確認）。追記式のテキストで、リポジトリに含める
- `pw-rules.json` — 読みが成り立つ条件の表と、読み手に求める測定の基準
- `pw/reader.txt` — 目隠しの読み手に渡す指示文。変えると読み手の測り直しになる
- `pw-calibration.json` — 読み手の測定結果
- `action.yml`、`ci/lean.sh` — ほかのリポジトリの CI から使うための入口と、Lean を取ってくる手順（下の「他のリポジトリから使う」）

実験の記録: [依存のある並列タスク](experiments/dependency/RESULTS.md)、[自己適用](experiments/selfcheck/RESULTS.md)、[過去の決定との矛盾](experiments/decisions/RESULTS.md)、[自然言語の決定の形式化](experiments/nl/RESULTS.md)、[コードでないファイル](experiments/artifacts/RESULTS.md)、[散文](experiments/prose/RESULTS.md)、[事実と箇所](experiments/facts/RESULTS.md)、[読み手の測定](experiments/calibration/RESULTS.md)、[箇所の探索](experiments/discovery/RESULTS.md)、[別のリポジトリで使う](experiments/external/RESULTS.md)、[何が乗らないかの調査](experiments/survey/RESULTS.md)（最初の 7 つは削除した層の上で行ったもの。[experiments/README.md](experiments/README.md)）

## 動かす

```
pip install -e '.[agents,test]'             # scipy と、エージェントを使うものに要る mcp、テスト用の pytest。CI は requirements-ci.txt（動かすのに要るもの）と requirements-test.txt（テスト用）の版とハッシュで固定している
python -m pytest tests
python -m pw.check --repo .                        # 事実をいまのファイルで確かめ直す。通らないものがあれば終了コード 1。記録（pw-log.jsonl）には書かない
python -m pw.check --repo . --verify               # 加えて、記録にある証明を Lean に通し直す（CI はこれを回す：.github/workflows/decisions.yml）
python -m pw.check --repo . --record               # 確かめた結果（計算した読み、Lean の証明）を記録に書き足す。ふつうは要らない
python -m pw.maintain --repo .                     # 上に加えて、変わった箇所を目隠しの読み手に読み直させる（課金あり）。読みは記録に書き足されるので、コミットに含める
python -m pw.confirm --repo .                      # エージェントの読みのうち、誰も確認していないものを一覧する
python -m pw.calibrate --repo .                    # 値をわざと書き換えた本文とおとりを読ませ、読み手を測る（課金あり）
python -m pw.discover --repo . --apply            # 宣言した事実について、読めなくなった箇所を付け替え、漏れている箇所を探す（課金あり）
python -m pw.discover --repo . --new --apply      # 加えて、まだ宣言されていない事柄を提案させる
python -m pw.propagate --repo .                    # 人が定めた値と違う箇所への書き戻しを、差分で示す（--apply で適用）
python -m pw.propagate --repo . --suppose 'Lean version=4.15.0'   # 仮にこの値にしたら、どこを書き換えることになるか
python -m pw.propagate --repo . --agent            # 一覧や散文は、エージェントに新しい本文を出させて読み戻す（課金あり）
```

一致の判定には `lean/lean-toolchain` と同じ版の Lean 4 が必要。`lake` が PATH にないときは `PW_LAKE` でパスを渡す。
Lean がない、または版が違うときは、判定はすべて不受理になる（`tests/test_lean_real.py` はスキップされる）。
その版の Lean が手元になければ `ci/lean.sh` が取ってくる（`export PATH="$(ci/lean.sh):$PATH"`。Linux x86_64 のみ。`curl` と `zstd` が要る）。

Lean は `lean/` の中では動かさない。`lean/` の中身を `~/.cache/parallelworld/`（`PW_LEAN_WORK` で変えられる）に写し、そこでビルドと判定をする。仕組みを置いた場所は読むだけなので、読み取り専用でも、ほかのジョブと共有していてもよい。

## 他のリポジトリから使う

対象のリポジトリに置くのは、宣言（`pw-facts.json`）と、読み手が書く記録（`pw-log.jsonl`、`pw-calibration.json`）、変えたければ規則の表（`pw-rules.json`）。この仕組みのコードは写さない。記録をブランチどうしで両方残してマージするには、対象のリポジトリの `.gitattributes` に `pw-log.jsonl merge=union` と書く。

### 手元で

```
pip install /path/to/parallelworld                           # または、入れずに PYTHONPATH=/path/to/parallelworld を付けて動かす
export PATH="$(/path/to/parallelworld/ci/lean.sh):$PATH"     # 同じ版の Lean が PATH になければ
cd 対象のリポジトリ
python -m pw.check --repo . --verify
```

- `--lean-dir` は付けなくてよい（この仕組みに付いている Lean のプロジェクトを使う）。
- エージェントを使うもの（`pw.maintain`、`pw.calibrate`、`pw.discover`、`pw.propagate --agent`）には、加えて `mcp` パッケージと `claude` の CLI が要る（`pip install '/path/to/parallelworld[agents]'`）。
- `pw.check` は何もファイルを書き換えない。対象のリポジトリの記録が増えるのは、`pw.maintain`・`pw.confirm`・`pw.discover --apply`・`pw.propagate --apply` と、`pw.check --record` を回したとき。増えた行はコミットに含める。

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

- することは、Python 3.13 の用意、パッケージの導入（`requirements-ci.txt`、ハッシュで固定）、Lean の取得（`lean/lean-toolchain` の版、`ci/lean.sh` のチェックサムで固定）、`python -m pw.check --repo . --verify`。エージェントは使わない。
- **使う側が固定するのは、このリポジトリのコミット 1 つ。** Lean の版もチェックサムもパッケージのハッシュも、そのコミットの中で決まる。使う側に写す値はない。
- 入力は 2 つ。`repo`（確かめるディレクトリ。既定は `.`）と `args`（`pw.check` に渡す引数。既定は `--verify`。規則を満たさない読みを警告にとどめるなら `--verify --unconfirmed warn`）。
- CI は記録を読むだけなので、手元で確かめたときと記録の中身がずれない。
