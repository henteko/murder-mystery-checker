# mmcheck 仕様書

- 仕様バージョン: **0.1.0**
- 本書が唯一の正(single source of truth)。Lean モデル (`lean/`) は本書を形式化し、Go 実装 (`go/`) は Lean モデルと差分テストで一致させる。
- 本書を変更した場合は仕様バージョンを上げ、Lean → オラクル → Go の順に追従させる。

## 0. 用語と全体像

| 用語 | 意味 |
|---|---|
| シナリオ | 検査対象。登場人物・場所・アイテム・情報・タイムライン・ハンドアウト・ゴール・エンディングからなる |
| タイムライン | ゲーム開始前に起きた出来事(イベント)の列。`start_time` から `end_time` まで |
| 終了状態 | タイムラインの全イベントを適用した後の状態 = ゲーム開始時点の状態 |
| ハンドアウト | 各キャラクターのプレイヤーに配られる資料。ゲーム開始時の居場所・所持品・知識を宣言する |
| 変数 | ゴール(達成したか)とプレイヤーの選択(したか)。いずれも真偽値 |
| パターン | 全変数への真偽値の割り当てのうち、制約(`constraints`)をすべて満たすもの |

検査は次の6群からなる。

| 群 | 内容 |
|---|---|
| R | 構造・参照整合(他の群の前提) |
| T | タイムライン(居場所・移動・同時刻の重複) |
| I | 所持品(アイテムの保持・受け渡し・消費) |
| K | 知識・手がかり(知らない情報での行動、解決可能性) |
| H | ハンドアウトとタイムライン終了状態の整合 |
| G | ゴール・選択・エンディングの網羅性と排他性 |

## 1. 入力: 正規化 JSON

Lean オラクルと Go 実装が共通に受け付ける入力形式。作者が書く YAML(§8)は Go 側でこの形式に変換される。

### 1.1 基本型

- **ID**: 空でない文字列。種類(kind)ごとに一意。種類が異なれば同じ文字列を使ってよい。
  - kind: `character`, `location`, `item`, `fact`, `clue`, `event`, `variable`(ゴールと選択で共有), `ending`, `handout`(キャラクター ID で識別)
- **時刻 (Time)**: 0 以上 10,000,000 以下の整数。単位は分。絶対時刻(例: 1日目 21:00 = 1260)。
- **分 (Minutes)**: 0 以上 10,000,000 以下の整数。
- 配列の順序は意味を持たない(ただしエラー検出結果は §6.3 の正規順序で出力される)。
- 未知のフィールドは無視する。`note` フィールドはどこにでも置けて、検査に使わない。

### 1.2 トップレベル

```jsonc
{
  "spec_version": "0.1.0",
  "start_time": 1080,            // Time
  "end_time": 1440,              // Time
  "characters": [{"id": "alice"}],
  "locations":  [{"id": "hall"}, {"id": "study"}],
  "travel": [                    // 有向。記載のない (from,to) の組は移動不可
    {"from": "hall", "to": "study", "minutes": 3}
  ],
  "placements": [                // 各キャラクターの start_time 時点の居場所
    {"character": "alice", "location": "hall"}
  ],
  "items": [
    {"id": "knife", "initial": {"character": "alice"}},   // 人が所持
    {"id": "key",   "initial": {"location": "study"}}     // 場所に置かれている
  ],
  "facts": [{"id": "alice_saw_bob"}],
  "initial_knowledge": [{"character": "alice", "fact": "alice_saw_bob"}],
  "events": [ /* §1.3 */ ],
  "clues": [                     // ゲーム中に調査で得られる手がかり
    {"id": "bloody_note", "location": "study", "reveals": ["alice_saw_bob"]}
  ],
  "solution_facts": ["alice_saw_bob"],   // 真相の推理に必要な情報
  "handouts": [ /* §1.4 */ ],
  "goals":   [{"id": "g_alice_escape", "owner": "alice"}],
  "choices": [{"id": "c_bob_confess", "owner": "bob"}],
  "constraints": [ /* Formula */ ],
  "endings": [{"id": "end_true", "condition": /* Formula */ {"var": "c_bob_confess"}}]
}
```

`travel`, `items`, `facts`, `initial_knowledge`, `events`, `clues`, `solution_facts`, `handouts`, `goals`, `choices`, `constraints`, `endings` は省略可能で、省略時は空配列。

`items[].initial` は `{"character": ID}` か `{"location": ID}` のどちらか一方だけを持つ(それ以外はスキーマエラー: §6.4)。

### 1.3 イベント

全イベントに共通するフィールド:

| フィールド | 型 | 説明 |
|---|---|---|
| `id` | ID | イベント ID |
| `at` | Time | 発生時刻(移動の場合は出発時刻) |
| `kind` | 文字列 | 下表のいずれか |
| `requires` | fact ID の配列(省略時は空) | **行為者**がこの時刻にすでに知っていなければならない情報 |

| kind | 固有フィールド | 参加者 | 行為者 |
|---|---|---|---|
| `move` | `character`, `to`(location), `arrive`(Time) | character | character |
| `scene` | `location`, `participants`(character の配列、1人以上、重複なし) | participants 全員 | participants 全員 |
| `transfer` | `from`, `to`(character), `item` | from, to | from |
| `pickup` | `character`, `item` | character | character |
| `drop` | `character`, `item` | character | character |
| `use` | `character`, `item` | character | character |
| `consume` | `character`, `item` | character | character |
| `learn` | `character`, `facts`(1つ以上) | character | character |
| `tell` | `from`, `to`(character), `facts`(1つ以上) | from, to | from |

- **参加者 (participants)** は同時刻の重複判定(T005)と移動中判定(T006)に使う。
- **行為者 (actors)** は `requires` の判定(K002)に使う。

### 1.4 ハンドアウト

```jsonc
{
  "character": "alice",
  "location": "hall",        // 省略可: ゲーム開始時の居場所の宣言
  "items": ["knife"],        // 省略可: ゲーム開始時の所持品の宣言(完全なリスト)
  "knows": ["alice_saw_bob"] // 省略可: ゲーム開始時に知っている情報の宣言
}
```

省略したフィールドは検査しない(`items: []` は「何も持っていない」という宣言であり、省略とは区別する)。

### 1.5 論理式 (Formula)

```
Formula := {"const": true|false}
         | {"var": <variable ID>}
         | {"not": Formula}
         | {"and": [Formula, ...]}    // 空配列なら true
         | {"or":  [Formula, ...]}    // 空配列なら false
```

## 2. 状態と操作的意味論

### 2.1 状態

```
Holder    := Char(c) | Place(l) | Consumed
Position  := { dest: location, arrive: Time, via: event ID | none }
State     := {
  pos       : character → Position,
  holder    : item → Holder,
  knows     : character → fact の集合
}
```

- キャラクター c が時刻 t に **移動中** であるとは `pos(c).via ≠ none` かつ `t < pos(c).arrive` であること。移動中でなければ、c は `pos(c).dest` にいるとみなす(初期配置は移動中にならない)。
- 初期状態:
  - `pos(c) = { dest: placements の場所, arrive: start_time, via: none }`
  - `holder(i) = items[i].initial`
  - `knows(c) = initial_knowledge のうち c のもの`

### 2.2 処理順序

イベントは **(at 昇順, id 昇順)** の正規順序で1つずつ処理する。各イベントについて次の順で行う。

1. **事前条件の検査**: 処理前の状態に対して §4 の T/I/K 規則を評価し、違反を記録する。
2. **効果の適用**: 事前条件の違反の有無に関係なく、下表の効果を**必ず**適用する(後続の検査が連鎖的に壊れないようにするため、かつ結果が一意に決まるようにするため)。

| kind | 効果 |
|---|---|
| `move` | `pos(character) := { dest: to, arrive: arrive, via: id }` |
| `scene`, `use` | なし |
| `transfer` | `holder(item) := Char(to)` |
| `pickup` | `holder(item) := Char(character)` |
| `drop` | `holder(item) := Place(pos(character).dest)` |
| `consume` | `holder(item) := Consumed` |
| `learn` | `knows(character) ∪= facts` |
| `tell` | `knows(to) ∪= facts` |

すべてのイベントを処理した後の状態を **終了状態** と呼ぶ。

### 2.3 文字列の順序

ID の昇順は **Unicode コードポイントの辞書式順序** で比べる。UTF-8 のバイト列の辞書式順序はこれと一致するので、Go の `strings.Compare` と Lean の `String.lt`(`Char` の比較による辞書式順序)はどちらもこの順序になる。

## 3. 検査の段階

1. **R 群** を検査する。R の違反が1件でもあれば **R の結果だけを出力して終了** する(参照が壊れていると状態を定義できないため)。
2. R の違反がなければ、T / I / K / H / G 群をすべて検査し、結果を合わせて出力する。

## 4. 検査規則

各規則は **エラー検出結果(diagnostic)** を出す。フィールドの意味は §6 を参照。`args` は規則ごとに決まった順序の文字列配列で、数値は10進表記の文字列にする。保持者 (Holder) は `"character:<id>"` / `"location:<id>"` / `"consumed"` と表記する。

### 4.1 R: 構造・参照整合

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| R001 | error | 同じ種類の ID が重複している(goal と choice は `variable` として合わせて数える。handout はキャラクター ID で数える) | — | [kind, id] |
| R002 | error | 存在しない ID を参照している | 参照元がイベントならその ID | [referrer, kind, id] |
| R003 | error | キャラクターの `placements` が0件または2件以上ある | — | [character] |
| R004 | error | `start_time > end_time` | — | [] |
| R005 | error | `travel` に `from == to` のエントリがある、または同じ (from, to) が重複している | — | [from, to] |
| R006 | error | イベントの形が不正(下記 reason) | id | [reason] |

- R002 の `referrer` は参照元を `"<kind>:<id>"` で表したもの: `event:e1`, `item:knife`(initial), `placement:alice`, `initial_knowledge:alice`, `clue:c1`, `solution`, `handout:alice`, `goal:g1`, `choice:c1`, `constraint`, `ending:end1`, `travel`。
- R002 は (referrer, kind, id) の組ごとに1件出す(同じ組が何度現れても1件)。
- R006 の reason:
  - `arrive_before_depart`: move で `arrive < at`
  - `self_transfer`: transfer で `from == to`
  - `self_tell`: tell で `from == to`
  - `empty_participants`: scene で participants が空
  - `duplicate_participant`: scene の participants に同じキャラクターが2回以上現れる
  - `empty_facts`: learn / tell で facts が空

### 4.2 T: タイムライン

イベント e(時刻 t = e.at)を処理前の状態 S に対して評価する。

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| T001 | error | `t < start_time` または `t > end_time`、または move で `arrive > end_time` | e | [] |
| T002 | error | move: `travel` に (`S.pos(c).dest`, `to`) のエントリがない(かつ `dest ≠ to`) | e | [character, from, to] |
| T003 | error | move: 経路はあるが `arrive − t < minutes` | e | [character, from, to, minutes] |
| T004 | error | move: `S.pos(c).dest == to` | e | [character, location] |
| T005 | error | 参加者 c が、正規順序で e より前にある同じ時刻 t のイベント e' の参加者でもある | e | [character, e'.id] |
| T006 | error | 参加者 c が時刻 t に移動中(§2.1) | e | [character, S.pos(c).via] |
| T007 | error | scene: 参加者 c が移動中ではなく、かつ `S.pos(c).dest ≠ location` | e | [character, location, S.pos(c).dest] |
| T008 | error | transfer / tell: from と to のどちらも移動中ではなく、かつ居場所が異なる | e | [from, to, from の居場所, to の居場所] |

- T005 は、e より前の同時刻のイベントのうち正規順序で**最後**のもの1つについてだけ、参加者ごとに出す。
- **移動中の抑制規則**: 参加者が移動中の場合、その参加者について居場所に依存する検査(T007, T008, I003)は行わない(T006 だけを出す)。

### 4.3 I: 所持品

**所持者 (holder role)** は、transfer では from、drop / use / consume では character。

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| I001 | error | transfer / drop / use / consume: `S.holder(item) ≠ Char(所持者)` かつ `≠ Consumed` | e | [所持者, item, holder の表記] |
| I002 | error | item を扱うイベント(transfer / pickup / drop / use / consume)で `S.holder(item) == Consumed` | e | [行為者 (transfer は from), item] |
| I003 | error | pickup: c が移動中ではなく、`S.holder(item) ≠ Place(S.pos(c).dest)` かつ `≠ Consumed` | e | [character, item, holder の表記] |
| I004 | error | 同じ item を扱うイベント e' が、正規順序で e より前に同じ時刻 t にある | e | [item, e'.id] |

- I004 も T005 と同じく、直前の1件 e' についてだけ出す。

### 4.4 K: 知識・手がかり

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| K001 | error | tell: `f ∈ facts` について `f ∉ S.knows(from)` | e | [from, f] |
| K002 | error | 行為者 a と `f ∈ requires` について `f ∉ S.knows(a)` | e | [a, f] |
| K003 | error | `f ∈ solution_facts` が、終了状態でどのキャラクターにも知られておらず、どの clue の `reveals` にも含まれない(真相にたどり着けない) | — | [f] |

### 4.5 H: ハンドアウトと終了状態の整合

E を終了状態とする。各ハンドアウト h(キャラクター c)について:

| コード | 重大度 | 条件 | args |
|---|---|---|---|
| H001 | error | `h.location` があり、`E.pos(c).dest ≠ h.location` | [c, h.location, E.pos(c).dest] |
| H002 | error | `h.items` があり、`i ∈ h.items` について `E.holder(i) ≠ Char(c)` | [c, i, holder の表記] |
| H003 | warning | `h.items` があり、`E.holder(i) == Char(c)` なのに `i ∉ h.items`(記載漏れ) | [c, i] |
| H004 | error | `h.knows` があり、`f ∈ h.knows` について `f ∉ E.knows(c)`(タイムライン上で知りえない情報) | [c, f] |
| H005 | warning | `h.knows` があり、`f ∈ E.knows(c)` なのに `f ∉ h.knows`(記載漏れ) | [c, f] |

(T001 により `arrive ≤ end_time` なので、違反がなければ終了状態で移動中のキャラクターはいない。)

### 4.6 G: ゴール・選択・エンディング

- 変数集合 V = goals の ID ∪ choices の ID。n = |V|。
- 割り当て σ: V → Bool。V を ID 昇順に v₁, …, vₙ と並べ、σ を n ビットの数 `Σ σ(vᵢ)·2^(n−i)`(v₁ が最上位ビット)とみなす。**割り当ての順序** はこの数の大小で決める(すべて false が最小)。
- **パターン**: すべての `constraints` を満たす割り当て。P をパターン全体の集合とする。
- `match(σ) = { e ∈ endings | e.condition(σ) = true }`

| コード | 重大度 | 条件 | args | witness |
|---|---|---|---|---|
| G007 | error | n > 20(数え上げの上限を超える)。このとき G001〜G006 は検査しない | [n] | — |
| G005 | error | P が空(制約が矛盾していて、どのパターンも成り立たない)。このとき G001〜G004, G006 は検査しない | [] | — |
| G001 | error | `match(σ) = ∅` となる σ ∈ P がある(**網羅性**の違反)。そのような σ のうち最小のもの1つを witness にして**1件だけ**出す | [] | σ |
| G002 | error | 相異なるエンディング e₁ < e₂(ID 順)について、`{e₁, e₂} ⊆ match(σ)` となる σ ∈ P がある(**排他性**の違反)。ペアごとに、最小の σ を witness にして1件出す | [e₁, e₂] | σ |
| G003 | error | エンディング e について、`e ∈ match(σ)` となる σ ∈ P がない(到達不能なエンディング) | [e] | — |
| G004 | error | ゴール g について、σ(g) = true となる σ ∈ P がない(達成不可能なゴール) | [g] | — |
| G006 | warning | ゴール g がすべての σ ∈ P で true(必ず達成されるゴール)、または選択 x がすべての σ ∈ P で同じ値(実質的に選べない選択) | [variable] | — |
| G008 | warning | ゴールを1つも持たないキャラクターがいる | [character] | — |

**正しいシナリオの条件(G 群)**: 任意のパターン σ ∈ P について `|match(σ)| = 1`(エンディングがちょうど1つに決まる)。これは G001 と G002 がともに出ないことと同値である。

## 5. 正しさの定義

シナリオ s が **正しい (valid)** とは、§4 の error 規則の条件がどれも成り立たないこと。Lean では、判定関数とは独立に、各規則の条件を `Prop` で書いて否定を連言した宣言的な述語 `Valid s` として定義する。warning 規則は正しさに影響しない。

「判定器が error を1件も出さない ⇔ `Valid s`」は定義ではなく、**証明すべき定理** である(§7)。

## 6. 出力: エラー検出結果 JSON

### 6.1 形式

```jsonc
{
  "spec_version": "0.1.0",
  "diagnostics": [
    {
      "code": "T003",
      "severity": "error",          // "error" | "warning"
      "event": "e2",                // 省略可
      "args": ["alice", "hall", "study", "3"],
      "witness": {"g_alice_escape": true, "c_bob_confess": false}  // G001/G002 のみ
    }
  ]
}
```

- 人間向けのメッセージは**出力に含めない**(Lean と Go の比較対象を構造化データだけにするため)。メッセージは Go CLI の表示層(text 形式)で生成する。
- witness は V の全変数を含む。

### 6.2 重複

完全に同じ検出結果(全フィールドが等しいもの)は1件にまとめる。

### 6.3 正規順序

検出結果は次のキーの辞書式順序で昇順に並べる。

1. `code`(文字列)
2. `event`(なしは `""` として扱う)
3. `args`(文字列の配列として辞書式に比べる。短い方が接頭辞なら短い方が先)
4. `witness`(V の ID 昇順に並べた真偽値の列を、false < true で辞書式に比べる。なしは空列として扱う)

### 6.4 スキーマエラー

JSON として不正な入力、必須フィールドの欠落、型の不一致、範囲外の数値、`initial` の形が不正な入力は **入力エラー** とし、エラー検出結果を出さない。Lean オラクルと Go はどちらも入力エラーを返す(終了コード 2)。差分テストでは「どちらも入力エラーになること」だけを比べる。

### 6.5 終了コード(CLI)

| コード | 意味 |
|---|---|
| 0 | error がない(warning はあってもよい) |
| 1 | error が1件以上ある |
| 2 | 入力エラー |

Go CLI の `--strict` を付けると warning も 1 として扱う(Go の表示層だけの機能)。

## 7. Lean での形式化方針(Phase 2 で行うこと)

| 仕様 | Lean |
|---|---|
| §1 入力 | `structure Scenario` ほか。ID は `String`、時刻は `Nat` |
| §2 意味論 | `step : Scenario → State → Event → State`、`run`、`finalState` |
| §4 各規則 | 規則ごとに `Prop` の述語(例: `TravelTooShort s e`)と判定関数(`checkT003 : … → List Diag`) |
| §5 正しさ | `Valid s : Prop` |
| §6 出力 | `check : Scenario → List Diag`(正規順序で、重複なし) |

証明する定理:

1. **健全性・完全性**: `(check s).all (·.severity = .warning) ↔ Valid s`。さらに規則ごとに「その規則の検出結果が出る ↔ その規則の `Prop` が成り立つ」。
2. **G の網羅判定の正しさ**: 有限の数え上げによる判定が `∀ σ ∈ P, |match σ| = 1` と同値。
3. **出力の決定性**: `check s` は §6.3 の順序でソート済みで、重複がない。入力配列の並べ替えに対して `check` は不変。
4. **同時刻イベントの交換可能性**: T005 と I004 の違反がなければ、同時刻のイベントの処理順を入れ替えても終了状態と検出結果は変わらない(タイブレークを id 昇順にしたことが本質的でないことの保証)。
5. **知識の単調性**: どのキャラクターについても、時刻が進んで知識が減ることはない。
6. **仕様の無矛盾性**: 正しいシナリオが少なくとも1つ存在する(具体例を `decide` で示す)。

## 8. 作者向け YAML(Go 側のみ。参考)

Go CLI は作者が書きやすい YAML を受け付け、§1 の正規化 JSON に変換してから検査する。変換は Go 側だけの責務で、Lean との差分テストの対象外とする(変換結果の JSON に対する単体テストで担保する)。主な変換は次のとおり。

- 時刻 `"21:00"` → 1260。`"25:30"` のように 24 時以降も書ける。`"2d 09:00"` は 2 日目(0 起算で `2*1440 + 540`)。
- `travel: [{between: [hall, study], minutes: 3}]` → 双方向の2エントリ。
- キャラクターごとのタイムライン記法(`characters[].timeline`)→ `events` に平坦化する。event ID を省略した場合は `<character>#<連番>` で自動採番する。

YAML の具体的なスキーマは Phase 4 で別紙(docs/yaml.md)として定める。

## 9. 例

```jsonc
{
  "spec_version": "0.1.0",
  "start_time": 1260, "end_time": 1320,
  "characters": [{"id": "alice"}, {"id": "bob"}],
  "locations": [{"id": "hall"}, {"id": "study"}],
  "travel": [{"from": "hall", "to": "study", "minutes": 5},
             {"from": "study", "to": "hall", "minutes": 5}],
  "placements": [{"character": "alice", "location": "hall"},
                 {"character": "bob", "location": "study"}],
  "items": [{"id": "poison", "initial": {"character": "alice"}}],
  "facts": [{"id": "poison_in_tea"}],
  "events": [
    {"id": "e1", "at": 1270, "kind": "move", "character": "alice", "to": "study", "arrive": 1272},
    {"id": "e2", "at": 1275, "kind": "transfer", "from": "alice", "to": "bob", "item": "poison"},
    {"id": "e3", "at": 1280, "kind": "use", "character": "alice", "item": "poison",
     "requires": ["poison_in_tea"]}
  ],
  "goals": [{"id": "g_alice", "owner": "alice"}, {"id": "g_bob", "owner": "bob"}],
  "endings": [{"id": "end_a", "condition": {"var": "g_alice"}}]
}
```

期待される出力:

```json
{
  "spec_version": "0.1.0",
  "diagnostics": [
    {"code": "G001", "severity": "error", "args": [], "witness": {"g_alice": false, "g_bob": false}},
    {"code": "I001", "severity": "error", "event": "e3", "args": ["alice", "poison", "character:bob"]},
    {"code": "K002", "severity": "error", "event": "e3", "args": ["alice", "poison_in_tea"]},
    {"code": "T003", "severity": "error", "event": "e1", "args": ["alice", "hall", "study", "5"]}
  ]
}
```

- T003: hall → study は 5 分かかるが、e1 は 2 分で到着している。
- I001: e2 で毒を bob に渡した後、e3 で alice が使っている。
- K002: alice は `poison_in_tea` を知らないまま e3 で行動している。
- G001: `g_alice = false` のときに該当するエンディングがない(最小の反例は全変数 false)。
- 制約がないので両ゴールとも true になりうるため、G004 は出ない。どちらのゴールも false になりうるため、G006 も出ない。
