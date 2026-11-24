# Lean による形式化と証明の状況

仕様 0.3.1 (docs/spec.md) の Lean 4 による形式化。`lake build`(lean/)で全証明が検査される。

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
| 3 | 出力の決定性(狭義に整列・重複なし・`events` 配列の並べ替えに不変) | **証明済み** | `check_sorted`, `check_nodup`, `check_perm_events`, `diagLt_total` |
| 4 | 同時刻イベントの交換可能性 | **証明済み**(前提を追加) | `reorder_same_time`, `step_comm`, `runAux_swap` |
| 5 | 知識の単調性 | **証明済み** | `step_knows_mono`, `final_knows_of_initial`, `trace_knows_final` |
| 6 | 仕様の無矛盾性(正しいシナリオが存在) | **証明済み**(`native_decide` 使用) | `exists_valid` |
| 7 | 導出制約の正しさ | **証明済み** | `realizable_iff`, `derived_iff` |
| 8 | 区間の整合 | **証明済み**(主張を正確化) | `segments_consistent`, `segments_ordered`, `whereAt_eq_stateAt` |
| 9 | 移動時間の決定性 | 定義上自明(`travelTime` は関数)。R005 との関係は未証明 | |
| 10 | 集計の分割 | **証明済み** | `tally_partition` |
| 11 | 死亡の一意性 | **証明済み** | `step_dead_stable`, `runAux_dead_stable` |

`check_valid`、`check_perm_events`、`reorder_same_time`、`segments_consistent` ほか主要な定理が依存する公理は `propext`, `Classical.choice`, `Quot.sound` のみ(`sorry` なし)。
`exists_valid` のみ、具体例の評価に `native_decide` を使うため `Lean.ofReduceBool` 由来の公理にも依存する。

## 定理 3, 4, 8 の内容と、証明で見つかった問題(仕様 0.3.1)

### 定理 3: 出力の決定性 (`Proofs/Order.lean`, `Proofs/Perm.lean`)

- `Diag.lt` は検出結果全体の上の狭義全順序(`diagLt_total`)。正規化 `normalize` の結果は `Diag.lt` について狭義に整列し(`check_sorted`)、重複がない(`check_nodup`)。要素の集合が同じ列は、正規化すると等しい(`normalize_eq_of_mem_iff`)。
- `events` 配列を並べ替えた入力 `{ s with events := l' }` に対して、出力は等しい(`check_perm_events`)。R 群の違反がある場合も含む。R 群の違反がないときは、イベント ID が重複しないので正規順序の列と ID 検索が一致する。
- **見つかった問題 1(仕様を修正)**: 0.3.0 の正規順序は (code, event, args, witness の位置) だけで、キーが同じで中身が違う検出結果があると、並べ替えの安定性のせいで入力順が出力に残りうる。0.3.1 で severity と witness の値を加えて全順序にし、event がないものを最小にした(通常の出力は変わらない)。
- **見つかった問題 2(仕様と判定器を修正)**: R011 `arrive_on_non_move` が「最初に見つかった ID のイベント」で判定していたため、イベント ID が重複していると `events` の並び順で結果が変わった(反例: 同じ ID の move と learn を入れ替えると R011 が出たり出なかったりする)。0.3.1 で「同じ ID のイベントのいずれかが move でない」に変えた。
- 範囲: 並べ替え不変性は `events` 配列についてのみ証明した。他の配列(characters, facts など)は未証明。R 群の違反があるとき、ID の重複した要素の「最初のもの」を使う検査(`findChoice?` など)は並び順に依存しうる。

### 定理 4: 同時刻イベントの交換可能性 (`Proofs/Commute.lean`)

- 2つのイベントが **独立**(参加者が重ならない、アイテムが重ならない、一方の observe の対象を他方が move させない)なら、状態遷移は可換(`step_comm`)で、隣り合う2つを入れ替えても終了状態は同じ、イベントごとの検出結果は並べ替えを除いて等しい(`runAux_swap`)。
- これを繰り返して、時刻順を保つどの並べ方で処理しても、終了状態は同じで、検出結果は `checkEvents` の並べ替え(`reorder_same_time`)。
- 前提の「参加者・アイテムが重ならない」は T005 / I004 の違反がないこと(`NoSameTimeConflict`。`Valid` から導ける)。
- **見つかった問題 3(定理の前提を追加)**: observe の `targets` は参加者ではないので T005 の対象外だが、場所の条件(T007)は課される。「x が 10:00 に移動し、c が 10:00 に x を観察する」と、ID の順で observe が先なら違反なし、move が先なら T007(transit)になる(オラクルで確認)。0.3.1 では定理の前提に「同時刻に observe の対象が move しない」(`NoSameTimeObservedMove`)を加えた。これを検査規則(例: warning)にするかは未決定。

### 定理 8: 区間の整合 (`Proofs/Segments.lean`)

- c の move が開始時刻以降に出発し(T001)、出発 ≤ 到着(R006)、出発時に移動中でない(T006)なら(`MovesOk`。`Valid` から導ける)、
  - `segments c` は時刻順に並んで互いに重ならず、各区間は空でない(`segments_ordered`)。
  - 開始時刻 ≤ t < 終了時刻で死亡時刻より前なら、`whereAt c t` は時刻 t 以前のイベントをすべて処理した状態 `stateAt t` での居場所と一致する(`whereAt_eq_stateAt`)。
- **見つかった問題 4(定理の主張を正確化)**: 0.3.0 の「各イベント時刻での居場所と whereAt が一致」は成り立たない。同時刻にあとから move するとき、その前のイベントの処理前の状態ではまだ出発前だが、`whereAt` は出発時刻から transit になる。比べる相手を「時刻 t までのイベントを処理した状態」にした。

## `Valid` の内容と限界

`Valid s := checkR s = [] ∧ (∀ st ∈ s.trace, StepValid s st) ∧ PostValid s ∧ GValid s`

- **イベントごとの規則** (`StepValid`): T001〜T008, T010, T011, I001〜I004, K001, K002 を、判定関数を使わずに命題で書いている(例: 「参加者は同時刻の前のイベントに参加していない」「徒歩なら経路があり移動時間 ≤ arrive − at」)。
- **終了状態の規則** (`PostValid`): K003〜K008, H001/H002/H004/H006, A001。
- **G 群** (`GValid`): 「定義域に従い実効制約を満たす**すべての**割り当てでエンディングがちょうど1つ」「どのエンディング・ゴールにも到達できる」など。数え上げが全割り当てを網羅すること(`mem_enumerate`)を経由して証明している。
- **R 群は宣言的に書いていない**(`checkR s = []` のまま)。構造・参照の検査であり、意味論の前提条件として扱っている。
- 意味論そのもの(`step`, `segments`, `whereAt`, `travelTime` など)は判定器と Valid で共有している。したがって定理 1 が保証するのは「判定関数が規則の条件を正しく実装している」ことであり、意味論の定義が仕様書の文章と合っていることは、レビューと差分テスト(Python 試作判定器・Go 実装)で担保する。

## 差分による確認

Phase 2 の時点で、Lean オラクルの出力は Python の試作判定器と、両サンプル・仕様書の例・ランダムに変更した 1,200 以上のシナリオで完全に一致した(R 群は試作判定器に実装がないため対象外)。
