# オラクル用テストケース

Lean オラクル(`lake exe oracle`)の出力を正解とする差分テストのケース。Go 実装は、同じ入力に対して同じ出力を返さなければならない(Phase 5)。

| ディレクトリ | 内容 | 入力の作り方 |
|---|---|---|
| `rules/` | 規則ごとのケース。仕様書 §4 の全 54 規則が、少なくとも1つのケースで出る | `tools/oracle/cases.py`(手書き) |
| `edge/` | 境界条件・意味論のケース(移動の mode、知覚、導出制約、集計、R による打ち切りなど) | 同上 |
| `regress/` | 証明の途中で見つかった反例の回帰テスト(`docs/PROOFS.md`)。`_a` / `_b` などの組は出力が同じになる | 同上 |
| `schema/` | 入力エラー(§6.4)。期待出力は `{"input_error": true}` | 同上 |
| `spec/` | 仕様書 §9 の例。`example.spec_expected.json` は仕様書に書かれた期待出力で、オラクルの出力と一致することを点検する | 仕様書から抜き出す |
| `gen/` | ランダムに生成したケース(乱数の種は固定) | `tools/oracle/gen.py` |

`examples/*/scenario.json` も同じ手順で `expected.json` を作る。

## ファイル

- `NAME.input.json`: 入力。`"_case": {"doc": 説明, "expect": [必ず出るコード]}` はケースの説明で、オラクルも Go も読まない(入力が JSON として不正なケースは `NAME.case.json` に書く)
- `NAME.expected.json`: Lean オラクルの出力。手で編集しない

## 手順

```sh
make cases    # 入力を作り直す
make oracle   # Lean をビルドし、期待出力を作り直して点検する(tools/oracle/check.py)
make diff-check  # 上の2つを実行して、コミット済みのものと差分がないことを確かめる(CI)
```

点検の内容: どの入力にも期待出力がある / 各ケースの `expect` のコードが出力に含まれる(`expect` が空なら検出結果 0 件)/ 全規則が `rules/` で出る / 仕様書 §9 の例が仕様書の期待出力と一致する。

## ケースを足すとき

`tools/oracle/cases.py` に、土台のシナリオ(`tools/oracle/base.py`、検出結果 0 件)を変える関数を `@case(グループ, 名前, 説明, [出るコード])` で足し、`make cases oracle` を実行してコミットする。

## ライブ差分テスト(`make live-diff`)

ゴールデンは固定のケースしか比べないので、`tools/oracle/live.py` でその場で作ったシナリオを Go と Lean オラクルに通して比べる。

- 入力の作り方: ランダム生成(gen.py)、ゴール・選択・エンディングの一部を空にしたもの、examples と手書きケースの変異(mutate.py)、壊した入力
- 比べる内容: 入力エラーになるかどうか / 検出結果(並び順を含む)/ Go でトップレベルの配列を並べ替えても出力が変わらないこと(定理 3)
- 件数は `N`(既定 500)、乱数の種は `SEED`(省略時は時刻)。不一致の入力は `testdata/live-failures/` に保存されるので、原因を直したら `tools/oracle/cases.py` の `regress` に回帰テストとして足す

```sh
make live-diff N=3000 SEED=2
```

Go 側だけで動くテスト(CI の Go ジョブでも実行):
- `TestGolden`: 上のすべてのケースの期待出力と Go の出力が一致する
- `TestPermutationInvariance`: ケースの配列を並べ替えても Go の出力が変わらない
- `FuzzCheck`: どんな入力でもパニックせず、出力が正規順序で重複がない(`make fuzz` で探索)
