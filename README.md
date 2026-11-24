# murder-mystery-checker

マーダーミステリーのシナリオ(タイムライン・所持品・知識・ゴール/エンディング)の矛盾を検出する CLI `mmcheck`。

仕様は [docs/spec.md](docs/spec.md)、開発計画は [docs/PLAN.md](docs/PLAN.md)。
仕様は Lean 4 (`lean/`) でモデル化・証明し、Lean 判定器をオラクルとして Go 実装 (`go/`) を差分テストする。

## 使い方

```sh
make go                                        # bin/mmcheck をビルド
bin/mmcheck check examples/yaml-demo/scenario.yaml
bin/mmcheck check --format json scenario.yaml  # 検出結果を JSON で(docs/spec.md §6)
bin/mmcheck check --strict scenario.yaml       # warning も失敗扱い
bin/mmcheck convert scenario.yaml              # YAML を正規化 JSON に変換
bin/mmcheck explain -o reading.html scenario.yaml  # 判定器の解釈を、原作と読み合わせるための HTML に(docs/explain.md)
```

シナリオは作者向け YAML([docs/yaml.md](docs/yaml.md))か、正規化 JSON(docs/spec.md §1)で書く。
終了コードは 0 = error なし、1 = error あり、2 = 入力エラー。

```text
$ bin/mmcheck check examples/yaml-demo/scenario.yaml
error   K008  証言の時刻が実際の出来事の時刻とずれている
          customer@1 / 1265 / 1270
error   T003  移動時間が足りない  [event clerk#4]
          clerk / backroom / counter / 1
2 errors, 0 warnings
```

## 開発

```sh
make lean        # 仕様・証明のビルド(証明が通らなければ失敗する)
make cases       # オラクル用テストケースの入力を作る(tools/oracle)
make oracle      # Lean オラクルで期待出力を作り、点検する
make test        # Go のテスト(Lean オラクルの期待出力との差分テストを含む)
make live-diff   # その場で作ったシナリオで Go と Lean オラクルを比べる(N=件数 SEED=種)
make fuzz        # Go のファズテスト
make diff-check  # 入力と期待出力が最新か(CI)
```

| ディレクトリ | 内容 |
|---|---|
| `docs/` | 仕様書 spec.md、YAML の書き方 yaml.md、証明の状況 PROOFS.md、計画 PLAN.md |
| `lean/` | 仕様の Lean 4 モデル、判定器、証明、オラクル |
| `go/` | Go 実装(`internal/model` 入力、`internal/check` 判定器、`internal/yamlio` YAML、`cmd/mmcheck` CLI) |
| `testdata/oracle/` | Lean オラクルを正解とするテストケース |
| `examples/` | サンプルシナリオと期待出力 |
