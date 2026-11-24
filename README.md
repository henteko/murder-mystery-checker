# murder-mystery-checker

マーダーミステリーのシナリオ(タイムライン・所持品・知識・ゴール/エンディング)の矛盾を検出する CLI `mmcheck`。

仕様は [docs/spec.md](docs/spec.md)、開発計画は [docs/PLAN.md](docs/PLAN.md)。
仕様は Lean 4 (`lean/`) でモデル化・証明し、Lean 判定器をオラクルとして Go 実装 (`go/`) を差分テストする。

```sh
make lean   # 仕様・証明のビルド
make go     # bin/mmcheck のビルド
make test   # Go テスト(オラクル差分テスト含む)
```
