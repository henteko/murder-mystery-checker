# Lean による形式化と証明の状況

仕様 0.3.0 (docs/spec.md) の Lean 4 による形式化。`lake build`(lean/)で全証明が検査される。

## 構成

| ファイル | 内容 |
|---|---|
| `Spec/Types.lean` | 入力モデル (§1) |
| `Spec/Semantics.lean` | 移動時間・知覚・状態・`step`・トレース・居場所の区間・`whereAt`・入手可能 (§1.2, §2) |
| `Spec/Formula.lean` | 論理式の評価、集計、定義域と数え上げ (§1.9, §4.7) |
| `Spec/Valid.lean` | 正しさの**宣言的な**定義 `Valid` (§5) |
| `Checker/*.lean` | 実行可能な判定器 `check`(R / イベントごとの T・I・K / 終了状態の T009・K・H・A / G) |
| `Json.lean`, `Oracle/Main.lean` | 正規化 JSON の入出力とオラクル (`lake exe oracle`) |
| `Proofs/*.lean` | 証明 |

## 定理の状況(spec §7 の番号)

| # | 定理 | 状況 | Lean |
|---|---|---|---|
| 1 | 健全性・完全性: 判定器が error を出さない ⇔ `Valid s` | **証明済み** | `check_valid` |
| 2 | G の網羅判定の正しさ: G001/G002 が出ない ⇔ 全パターンでエンディングがちょうど1つ | **証明済み** | `checkG_exactly_one`, `g_exactly_one`, `mem_enumerate` |
| 3 | 出力の決定性(整列済み・重複なし・入力の並べ替えに不変) | 一部: 正規化は要素の集合を変えない(`mem_normalize`) | 整列・重複なし・並べ替え不変は未証明 |
| 4 | 同時刻イベントの交換可能性 | 未証明 | |
| 5 | 知識の単調性 | **証明済み** | `step_knows_mono`, `final_knows_of_initial`, `trace_knows_final` |
| 6 | 仕様の無矛盾性(正しいシナリオが存在) | **証明済み**(`native_decide` 使用) | `exists_valid` |
| 7 | 導出制約の正しさ | **証明済み** | `realizable_iff`, `derived_iff` |
| 8 | 区間の整合 | 未証明 | |
| 9 | 移動時間の決定性 | 定義上自明(`travelTime` は関数)。R005 との関係は未証明 | |
| 10 | 集計の分割 | **証明済み** | `tally_partition` |
| 11 | 死亡の一意性 | **証明済み** | `step_dead_stable`, `runAux_dead_stable` |

`check_valid` ほか主要な定理が依存する公理は `propext`, `Classical.choice`, `Quot.sound` のみ(`sorry` なし)。
`exists_valid` のみ、具体例の評価に `native_decide` を使うため `Lean.ofReduceBool` 由来の公理にも依存する。

## `Valid` の内容と限界

`Valid s := checkR s = [] ∧ (∀ st ∈ s.trace, StepValid s st) ∧ PostValid s ∧ GValid s`

- **イベントごとの規則** (`StepValid`): T001〜T008, T010, T011, I001〜I004, K001, K002 を、判定関数を使わずに命題で書いている(例: 「参加者は同時刻の前のイベントに参加していない」「徒歩なら経路があり移動時間 ≤ arrive − at」)。
- **終了状態の規則** (`PostValid`): K003〜K008, H001/H002/H004/H006, A001。
- **G 群** (`GValid`): 「定義域に従い実効制約を満たす**すべての**割り当てでエンディングがちょうど1つ」「どのエンディング・ゴールにも到達できる」など。数え上げが全割り当てを網羅すること(`mem_enumerate`)を経由して証明している。
- **R 群は宣言的に書いていない**(`checkR s = []` のまま)。構造・参照の検査であり、意味論の前提条件として扱っている。
- 意味論そのもの(`step`, `segments`, `whereAt`, `travelTime` など)は判定器と Valid で共有している。したがって定理 1 が保証するのは「判定関数が規則の条件を正しく実装している」ことであり、意味論の定義が仕様書の文章と合っていることは、レビューと差分テスト(Python 試作判定器・Go 実装)で担保する。

## 差分による確認

Phase 2 の時点で、Lean オラクルの出力は Python の試作判定器と、両サンプル・仕様書の例・ランダムに変更した 1,200 以上のシナリオで完全に一致した(R 群は試作判定器に実装がないため対象外)。
