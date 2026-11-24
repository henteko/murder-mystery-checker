# 開発計画

仕様(docs/spec.md) → Lean 4 でモデル化・証明 → Lean 実行可能判定器をオラクル化 → Go 実装 → 差分テスト。

## 決定事項 (2026-11-24)
1. 時刻は **分単位の絶対時刻**(自然数)。場所間の移動時間を検査する。
2. エンディング条件は **ゴール達成 + プレイヤー選択** を変数に含む。
3. **知識・手がかり** の検査を MVP に含める。
4. エンディングは全パターンで **ちょうど1つ** に決まらなければエラー(優先度による解決はしない)。

## フェーズ
- Phase 0: 環境構築(elan/Lean, Lake, Go module, Makefile, CI)
- Phase 1: 仕様書 docs/spec.md
- Phase 2: Lean モデル化(Spec: Prop 仕様 / Checker: 判定関数 / Proofs: 健全性・完全性・不変条件・決定性)
- Phase 3: オラクル(`lake exe oracle`)と手書き+生成テストケース → testdata/oracle/
- Phase 4: Go 実装(Lean 定義と 1:1 対応)、YAML フロントエンド、CLI
- Phase 5: 差分テスト(ゴールデン + Lean オラクルを呼ぶライブ差分ファズ)
- Phase 6: CI で乖離防止(証明ビルド・オラクル再生成 diff・go test)

## リポジトリ構成
```
docs/            spec.md, PLAN.md
lean/            Lake プロジェクト (MurderMystery/{Spec,Checker,Proofs}, Oracle/Main.lean)
go/              Go モジュール (cmd/mmcheck, internal/{model,check,yamlio})
testdata/oracle/ *.input.json / *.expected.json (Lean が生成)
```

## 仕様 0.2.0 (2026-11-24)
六角館サンプル(examples/hexagon-house)のモデル化で見つかった不足 A〜I をすべて取り込んだ。
J(知識の中身に基づく推論)は対象外のまま。詳細は docs/spec.md §10。
