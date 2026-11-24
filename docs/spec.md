# mmcheck 仕様書

- 仕様バージョン: **0.2.0**
- 本書が唯一の正(single source of truth)。Lean モデル (`lean/`) は本書を形式化し、Go 実装 (`go/`) は Lean モデルと差分テストで一致させる。
- 本書を変更した場合は仕様バージョンを上げ、Lean → オラクル → Go の順に追従させる。
- 変更履歴は §10。

## 0. 用語と全体像

| 用語 | 意味 |
|---|---|
| シナリオ | 検査対象。登場人物・場所・アイテム・情報・タイムライン・ハンドアウト・盤面・ゴール・エンディングからなる |
| タイムライン | ゲーム開始前に起きた出来事(イベント)の列。`start_time` から `end_time` まで |
| 終了状態 | タイムラインの全イベントを適用した後の状態 = ゲーム開始時点の状態 |
| ハンドアウト | 各キャラクターのプレイヤーに配られる資料。ゲーム開始時の居場所・所持品・知識を宣言する |
| 盤面 (board) | ゲーム開始時に各場所に置かれているアイテムの宣言(探索カードなど) |
| NPC | プレイヤーが担当しないキャラクター(被害者など)。ゴールとハンドアウトを持たなくてよい |
| エリア | 場所のまとまり(館内など)。移動時間をエリア単位で指定できる |
| 公共の場所 | 大広間・廊下など、複数人が居合わせても不自然でない場所。遭遇検査(T009)の対象外 |
| 変数 | ゴール(達成したか: 真偽値)と選択(真偽値、または列挙された値のどれか) |
| パターン | 全変数への値の割り当てのうち、制約(明示した制約 + 導出した制約)をすべて満たすもの |

検査は次の6群からなる。

| 群 | 内容 |
|---|---|
| R | 構造・参照整合(他の群の前提) |
| T | タイムライン(居場所・移動・同時刻の重複・死亡・遭遇) |
| I | 所持品(アイテムの保持・受け渡し・消費) |
| K | 知識・手がかり(知らない情報での行動、解決可能性、手がかりの所在) |
| H | ハンドアウト・盤面とタイムライン終了状態の整合 |
| G | ゴール・選択・エンディングの網羅性と排他性 |

## 1. 入力: 正規化 JSON

Lean オラクルと Go 実装が共通に受け付ける入力形式。作者が書く YAML(§8)は Go 側でこの形式に変換される。

### 1.1 基本型

- **ID**: 空でない文字列。種類(kind)ごとに一意。種類が異なれば同じ文字列を使ってよい。
  - kind: `character`, `area`, `location`, `item`, `fact`, `clue`, `event`, `variable`(ゴールと選択で共有), `ending`, `handout`(キャラクター ID で識別), `board`(場所 ID で識別)
- **値 (Value)**: 列挙型の選択がとりうる値。空でない文字列。
- **時刻 (Time)**: 0 以上 10,000,000 以下の整数。単位は分。絶対時刻(例: 1日目 21:00 = 1260)。
- **分 (Minutes)**: 0 以上 10,000,000 以下の整数。
- 配列の順序は意味を持たない(検出結果は §6.3 の正規順序で出力される)。
- 未知のフィールドは無視する。`note` フィールドはどこにでも置けて、検査に使わない。

### 1.2 トップレベル

```jsonc
{
  "spec_version": "0.2.0",
  "start_time": 1080,            // Time
  "end_time": 1440,              // Time
  "characters": [
    {"id": "alice"},
    {"id": "victim", "npc": true}             // npc は省略時 false
  ],
  "areas": [
    {"id": "mansion", "internal_minutes": 1}  // internal_minutes は省略可
  ],
  "locations": [
    {"id": "hall",  "area": "mansion", "public": true},  // area, public は省略可(public は省略時 false)
    {"id": "study", "area": "mansion"},
    {"id": "garden"}
  ],
  "travel": [                    // 場所間の移動時間(個別指定)
    {"from": "hall", "to": "garden", "minutes": 3, "bidirectional": true}  // bidirectional は省略時 false
  ],
  "area_travel": [               // エリア間の移動時間
    {"from": "mansion", "to": "forest", "minutes": 10, "bidirectional": true}
  ],
  "placements": [{"character": "alice", "location": "hall"}],
  "items": [
    {"id": "knife", "initial": {"character": "alice"}},
    {"id": "key",   "initial": {"location": "study"}}
  ],
  "facts": [{"id": "alice_saw_bob"}],
  "initial_knowledge": [{"character": "alice", "fact": "alice_saw_bob"}],
  "events": [ /* §1.3 */ ],
  "clues": [ /* §1.5 */ ],
  "solution_facts": ["alice_saw_bob"],
  "handouts": [ /* §1.4 */ ],
  "board": [ /* §1.4 */ ],
  "goals":   [ /* §1.6 */ ],
  "choices": [ /* §1.6 */ ],
  "constraints": [ /* Formula */ ],
  "endings": [{"id": "end_true", "condition": /* Formula */ {"var": "c_confess"}}]
}
```

`start_time`, `end_time`, `characters`, `locations`, `placements` 以外は省略可能。省略時は空配列。

`items[].initial` は `{"character": ID}` か `{"location": ID}` のどちらか一方だけを持つ(それ以外はスキーマエラー: §6.4)。

#### 移動時間の決定

異なる場所 a, b について、a から b への移動時間 `travel(a, b)` を次の順で決める。最初に当てはまったものを採用する。

1. `travel` に (a, b) のエントリがある(`bidirectional: true` のエントリ (b, a) を含む)→ その `minutes`
2. a と b が同じエリア X に属し、X に `internal_minutes` がある → `X.internal_minutes`
3. a がエリア X、b がエリア Y(X ≠ Y)に属し、`area_travel` に (X, Y) のエントリがある(`bidirectional` を含む)→ その `minutes`
4. どれにも当てはまらない → 経路なし

### 1.3 イベント

全イベントに共通するフィールド:

| フィールド | 型 | 説明 |
|---|---|---|
| `id` | ID | イベント ID |
| `at` | Time | 発生時刻(移動の場合は出発時刻) |
| `kind` | 文字列 | 下表のいずれか |
| `requires` | fact ID の配列(省略時は空) | **行為者**がこの時刻にすでに知っていなければならない情報 |

| kind | 固有フィールド | 参加者 | 行為者 | 場所の条件 |
|---|---|---|---|---|
| `move` | `character`, `to`(location), `arrive`(Time) | character | character | — |
| `scene` | `location`, `participants`(1人以上、重複なし), `reveals`(fact の配列、省略時は空) | participants 全員 | participants 全員 | 参加者全員が location にいる |
| `observe` | `character`, `location`, `targets`(character の配列、省略時は空、重複なし), `facts`(1つ以上) | character | character | character と targets 全員が location にいる |
| `transfer` | `from`, `to`(character), `item` | from, to | from | from と to が同じ場所にいる |
| `pickup` | `character`, `item` | character | character | item が character の居場所に置かれている |
| `drop` | `character`, `item` | character | character | — |
| `use` | `character`, `item` | character | character | — |
| `consume` | `character`, `item` | character | character | — |
| `learn` | `character`, `facts`(1つ以上) | character | character | — |
| `tell` | `from`, `to`(character), `facts`(1つ以上) | from, to | from | from と to が同じ場所にいる |
| `die` | `character` | character | character | — |

- **参加者 (participants)** は同時刻の重複(T005)、移動中(T006)、死亡後の行動(T010)、遭遇の認知(T009)の判定に使う。
- **行為者 (actors)** は `requires` の判定(K002)に使う。
- `observe` の `targets` は、気づかれずに観察される人物。参加者ではないので T005、T006、T010 の対象にならない。死亡した人物も target にできる(遺体を見るなど)。
- `learn` は場所に依存しない知識の獲得(内省、思い出すなど)に使う。何かを見て知った場合は `observe` を使う。

### 1.4 ハンドアウトと盤面

```jsonc
// handouts[]
{
  "character": "alice",
  "location": "hall",        // 省略可: ゲーム開始時の居場所の宣言
  "items": ["knife"],        // 省略可: ゲーム開始時の所持品の宣言(完全なリスト)
  "knows": ["alice_saw_bob"] // 省略可: ゲーム開始時に知っている情報の宣言(完全なリスト)
}
// board[]
{
  "location": "study",
  "items": ["key"]           // ゲーム開始時にその場所に置かれているアイテム(完全なリスト)
}
```

ハンドアウトで省略したフィールドは検査しない(`items: []` は「何も持っていない」という宣言であり、省略とは区別する)。`board` に記載のない場所は検査しない。

### 1.5 手がかり

```jsonc
{"id": "x_clock", "location": "study", "item": "clock", "reveals": ["murder_at_0100"]}
```

- `location` と `item` は少なくとも一方が必要。
- `item` を指定すると、そのアイテムから分かる手がかりになる。`location` も指定した場合は「ゲーム開始時にそのアイテムがその場所にある」ことの宣言を兼ねる(K005)。

### 1.6 ゴールと選択

```jsonc
// goals[]
{"id": "g_collect", "owner": "alice", "requires_items": ["knife", "key"]}  // requires_items は省略可
// choices[]
{"id": "c_confess", "owner": "bob"}                                        // 真偽値の選択
{"id": "c_vote", "owner": "bob", "values": ["alice", "bob", "tie"]}       // 列挙型の選択
```

- `requires_items`: このゴールの達成には、**ゲーム終了時に owner がこれらのアイテムをすべて所持している**ことが必要(必要条件。十分条件ではない)。G 群で制約を導出するのに使う(§4.6)。
- `values` があれば列挙型、なければ真偽値。`values` は空でなく、重複を含まない。

### 1.7 論理式 (Formula)

```
Formula := {"const": true|false}
         | {"var": <ゴールまたは真偽値の選択の ID>}
         | {"eq": {"var": <列挙型の選択の ID>, "value": <Value>}}
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
  pos    : character → Position,
  holder : item → Holder,
  knows  : character → fact の集合,
  dead   : character → event ID | none     // 死亡させた die イベント
}
```

- キャラクター c が時刻 t に **移動中** であるとは `pos(c).via ≠ none` かつ `t < pos(c).arrive` であること。移動中でなければ、c は `pos(c).dest` にいるとみなす(初期配置は移動中にならない)。
- 初期状態:
  - `pos(c) = { dest: placements の場所, arrive: start_time, via: none }`
  - `holder(i) = items[i].initial`
  - `knows(c) = initial_knowledge のうち c のもの`
  - `dead(c) = none`

### 2.2 処理順序

イベントは **(at 昇順, id 昇順)** の正規順序で1つずつ処理する。各イベントについて次の順で行う。

1. **事前条件の検査**: 処理前の状態に対して §4 の T/I/K 規則を評価し、違反を記録する。
2. **効果の適用**: 事前条件の違反の有無に関係なく、下表の効果を**必ず**適用する(誤りが連鎖して結果が崩れないようにするため、かつ結果が一意に決まるようにするため)。

| kind | 効果 |
|---|---|
| `move` | `pos(character) := { dest: to, arrive: arrive, via: id }` |
| `scene` | 各参加者 p について `knows(p) ∪= reveals` |
| `observe`, `learn` | `knows(character) ∪= facts` |
| `use` | なし |
| `transfer` | `holder(item) := Char(to)` |
| `pickup` | `holder(item) := Char(character)` |
| `drop` | `holder(item) := Place(pos(character).dest)` |
| `consume` | `holder(item) := Consumed` |
| `tell` | `knows(to) ∪= facts` |
| `die` | `dead(character) := id`(すでに死亡していれば変更しない) |

すべてのイベントを処理した後の状態を **終了状態** と呼び、E と書く。

### 2.3 居場所の区間

遭遇検査(T009)のために、各キャラクター c の **居場所の区間** の列を、イベント列から次のように定める。c の move イベントを正規順序で m₁, …, mₖ とする。

- 区間 0: `(placement の場所, start_time, m₁.at)`。k = 0 なら終端は `end_time`
- 区間 i(1 ≤ i ≤ k): `(mᵢ.to, mᵢ.arrive, mᵢ₊₁.at)`。i = k なら終端は `end_time`
- c が die イベント d で死亡している(E.dead(c) = d)場合、各区間の終端を `min(終端, d.at)` に切り詰める
- 始端 ≥ 終端 となった区間は捨てる

区間 (l, a, b) は「c が時刻 a から b まで l にいた」ことを表す。

### 2.4 文字列の順序

ID と値の昇順は **Unicode コードポイントの辞書式順序** で比べる。UTF-8 のバイト列の辞書式順序はこれと一致するので、Go の `strings.Compare` と Lean の `String.lt`(`Char` の比較による辞書式順序)はどちらもこの順序になる。

## 3. 検査の段階

1. **R 群** を検査する。R の違反が1件でもあれば **R の結果だけを出力して終了** する(参照が壊れていると状態を定義できないため)。
2. R の違反がなければ、T / I / K / H / G 群をすべて検査し、結果を合わせて出力する。

## 4. 検査規則

各規則は **エラー検出結果(diagnostic)** を出す。フィールドの意味は §6 を参照。`args` は規則ごとに決まった順序の文字列配列で、数値は10進表記の文字列にする。保持者 (Holder) は `"character:<id>"` / `"location:<id>"` / `"consumed"` と表記する。

### 4.1 R: 構造・参照整合

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| R001 | error | 同じ種類の ID が重複している(goal と choice は `variable` として合わせて数える。handout はキャラクター ID、board は場所 ID で数える) | — | [kind, id] |
| R002 | error | 存在しない ID を参照している | 参照元がイベントならその ID | [referrer, kind, id] |
| R003 | error | キャラクターの `placements` が0件または2件以上ある | — | [character] |
| R004 | error | `start_time > end_time` | — | [] |
| R005 | error | `travel` / `area_travel` に `from == to` のエントリがある、または bidirectional を展開した後に同じ (from, to) が重複している | — | [table, from, to] |
| R006 | error | イベントの形が不正(下記 reason) | id | [reason] |
| R007 | error | clue に `location` も `item` もない | — | [clue] |
| R008 | error | 列挙型の選択の `values` が空、または値が重複している | — | [choice] |
| R009 | error | 論理式の型の誤り: `var` が列挙型の選択を指す、`eq` がゴールや真偽値の選択を指す、`eq` の値が選択の `values` にない | — | [referrer, variable, value] |

- R002 の `referrer` は参照元を `"<kind>:<id>"` で表したもの: `event:e1`, `item:knife`(initial), `location:hall`(area), `placement:alice`, `initial_knowledge:alice`, `clue:c1`, `solution`, `handout:alice`, `board:study`, `goal:g1`, `choice:c1`, `constraint`, `ending:end1`, `travel`, `area_travel`。R002 は (referrer, kind, id) の組ごとに1件出す。
- R005 の `table` は `"travel"` または `"area_travel"`。
- R009 の `referrer` は `constraint` または `ending:<id>`。`value` は `var` の誤りなら `""`。
- R006 の reason:
  - `arrive_before_depart`: move で `arrive < at`
  - `self_transfer`: transfer で `from == to`
  - `self_tell`: tell で `from == to`
  - `self_observe`: observe で character が targets に含まれる
  - `empty_participants`: scene で participants が空
  - `duplicate_participant`: scene の participants、または observe の targets に同じキャラクターが2回以上現れる
  - `empty_facts`: learn / tell / observe で facts が空

### 4.2 T: タイムライン

イベント e(時刻 t = e.at)を処理前の状態 S に対して評価する。

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| T001 | error | `t < start_time` または `t > end_time`、または move で `arrive > end_time` | e | [] |
| T002 | error | move: `S.pos(c).dest ≠ to` かつ `travel(S.pos(c).dest, to)` が経路なし | e | [character, from, to] |
| T003 | error | move: 経路はあるが `arrive − t < travel(from, to)` | e | [character, from, to, minutes] |
| T004 | error | move: `S.pos(c).dest == to` | e | [character, location] |
| T005 | error | 参加者 c が、正規順序で e より前にある同じ時刻 t のイベント e' の参加者でもある | e | [character, e'.id] |
| T006 | error | 参加者 c が時刻 t に移動中(§2.1) | e | [character, S.pos(c).via] |
| T007 | error | scene / observe: 場所の条件の対象者 c(scene の参加者、observe の character と targets)が location にいない | e | [character, location, 実際の居場所] |
| T008 | error | transfer / tell: from と to のどちらも移動中ではなく、かつ居場所が異なる | e | [from, to, from の居場所, to の居場所] |
| T009 | warning | 遭遇を認知していない(下記) | — | [c₁, c₂, location, from, to] |
| T010 | error | 参加者 c が死亡している(`S.dead(c) = d ≠ none`) | e | [character, d] |

- T005 は、e より前の同時刻のイベントのうち正規順序で**最後**のもの1つについてだけ、参加者ごとに出す。
- T007 の「実際の居場所」は、移動中なら `"transit"`、そうでなければ `S.pos(c).dest`。
- **移動中の抑制規則**: **参加者**が移動中の場合、その参加者について居場所に依存する検査(T007, T008, I003)は行わない(T006 だけを出す)。observe の targets は参加者ではないので抑制されず、移動中なら T007(`"transit"`)になる。
- **T009 遭遇の認知**: 相異なるキャラクター c₁ < c₂(ID 順)の居場所の区間 (l, a₁, b₁), (l, a₂, b₂) が同じ場所 l で `lo = max(a₁, a₂) < hi = min(b₁, b₂)` を満たし、l が公共の場所ではないとき、次のどちらかを満たすイベントが時刻 `[lo, hi]` にない場合に出す。
  - c₁ と c₂ をどちらも参加者に含むイベント(scene / transfer / tell)
  - 一方が character で、もう一方が targets に含まれる、location が l の observe

  args は [c₁, c₂, l, lo, hi]。区間の組ごとに1件。

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
| K004 | error | `item` を持つ clue について `E.holder(item) == Consumed`(手がかりが失われている) | — | [clue, item] |
| K005 | error | `item` と `location` を両方持つ clue について `E.holder(item) ≠ Place(location)` かつ `≠ Consumed` | — | [clue, item, location, holder の表記] |

### 4.5 H: ハンドアウト・盤面と終了状態の整合

各ハンドアウト h(キャラクター c)について:

| コード | 重大度 | 条件 | args |
|---|---|---|---|
| H001 | error | `h.location` があり、`E.pos(c).dest ≠ h.location` | [c, h.location, E.pos(c).dest] |
| H002 | error | `h.items` があり、`i ∈ h.items` について `E.holder(i) ≠ Char(c)` | [c, i, holder の表記] |
| H003 | warning | `h.items` があり、`E.holder(i) == Char(c)` なのに `i ∉ h.items`(記載漏れ) | [c, i] |
| H004 | error | `h.knows` があり、`f ∈ h.knows` について `f ∉ E.knows(c)`(タイムライン上で知りえない情報) | [c, f] |
| H005 | warning | `h.knows` があり、`f ∈ E.knows(c)` なのに `f ∉ h.knows`(記載漏れ) | [c, f] |

各盤面 b(場所 l)について:

| コード | 重大度 | 条件 | args |
|---|---|---|---|
| H006 | error | `i ∈ b.items` について `E.holder(i) ≠ Place(l)` | [l, i, holder の表記] |
| H007 | warning | `E.holder(i) == Place(l)` なのに `i ∉ b.items`(記載漏れ) | [l, i] |

### 4.6 G: ゴール・選択・エンディング

#### 変数と割り当て

- 変数集合 V = goals の ID ∪ choices の ID。V を ID 昇順に v₁, …, vₙ と並べる。
- 変数 v の **定義域** dom(v): ゴールと真偽値の選択は `[false, true]`、列挙型の選択は `values` を昇順に並べたもの。
- 割り当て σ は各 vᵢ に dom(vᵢ) の値を対応させる。**割り当ての順序** は、(σ(v₁) の定義域内の位置, …, σ(vₙ) の定義域内の位置) の辞書式順序で決める(最小はすべて定義域の先頭)。
- 割り当ての総数 N = Π |dom(vᵢ)|。

#### 導出制約(requires_items から)

終了状態 E に基づいて、次の制約を `constraints` に加える。これを **実効制約** と呼ぶ。

1. ゴール g の `requires_items` に `E.holder(i) == Consumed` のアイテム i がある → `¬g`(アイテムが失われていて達成できない)
2. owner が異なるゴール g₁ < g₂ の `requires_items` に共通のアイテムがある → `¬(g₁ ∧ g₂)`(同じアイテムを2人が同時には持てない)

(どのアイテムも保持者は1人なので、owner の異なるゴールの組が同時に達成できることと、各組の requires_items が互いに交わらないことは同値になる。§7 の定理 7。)

#### パターンとエンディング

- **パターン**: 実効制約をすべて満たす割り当て。P をパターン全体の集合とする。
- `match(σ) = { e ∈ endings | e.condition(σ) = true }`

| コード | 重大度 | 条件 | args | witness |
|---|---|---|---|---|
| G007 | error | N > 1,048,576(= 2²⁰。数え上げの上限を超える)。このとき G001〜G006 は検査しない | [N] | — |
| G005 | error | P が空(実効制約が矛盾している)。このとき G001〜G004, G006 は検査しない | [] | — |
| G001 | error | `match(σ) = ∅` となる σ ∈ P がある(**網羅性**の違反)。そのような σ のうち最小のもの1つを witness にして**1件だけ**出す | [] | σ |
| G002 | error | 相異なるエンディング e₁ < e₂(ID 順)について、`{e₁, e₂} ⊆ match(σ)` となる σ ∈ P がある(**排他性**の違反)。ペアごとに、最小の σ を witness にして1件出す | [e₁, e₂] | σ |
| G003 | error | エンディング e について、`e ∈ match(σ)` となる σ ∈ P がない(到達不能なエンディング) | [e] | — |
| G004 | error | ゴール g について、σ(g) = true となる σ ∈ P がない(達成不可能なゴール) | [g] | — |
| G006 | warning | ゴール g がすべての σ ∈ P で true(必ず達成されるゴール)、または選択 x がすべての σ ∈ P で同じ値(実質的に選べない選択) | [variable] | — |
| G008 | warning | NPC ではないのに、ゴールを1つも持たないキャラクターがいる | [character] | — |
| G009 | warning | 列挙型の選択 x の値 v について、σ(x) = v となる σ ∈ P がない(選ばれることのない値) | [x, v] | — |

G009 は G006 と同じく、G005 / G007 のときは検査しない。

**正しいシナリオの条件(G 群)**: 任意のパターン σ ∈ P について `|match(σ)| = 1`(エンディングがちょうど1つに決まる)。これは G001 と G002 がともに出ないことと同値である。

## 5. 正しさの定義

シナリオ s が **正しい (valid)** とは、§4 の error 規則の条件がどれも成り立たないこと。Lean では、判定関数とは独立に、各規則の条件を `Prop` で書いて否定を連言した宣言的な述語 `Valid s` として定義する。warning 規則は正しさに影響しない。

「判定器が error を1件も出さない ⇔ `Valid s`」は定義ではなく、**証明すべき定理** である(§7)。

## 6. 出力: エラー検出結果 JSON

### 6.1 形式

```jsonc
{
  "spec_version": "0.2.0",
  "diagnostics": [
    {
      "code": "T003",
      "severity": "error",          // "error" | "warning"
      "event": "e2",                // 省略可
      "args": ["alice", "hall", "study", "3"],
      "witness": {"g_alice": true, "c_vote": "bob"}  // G001/G002 のみ。真偽値または値の文字列
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
4. `witness`(§4.6 の割り当ての順序。なしは最小として扱う)

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
| §1.2 移動時間 | `travelTime : Scenario → Loc → Loc → Option Nat` |
| §2 意味論 | `step : Scenario → State → Event → State`、`run`、`finalState`、`segments`(§2.3) |
| §4 各規則 | 規則ごとに `Prop` の述語(例: `TravelTooShort s e`)と判定関数(`checkT003 : … → List Diag`) |
| §5 正しさ | `Valid s : Prop` |
| §6 出力 | `check : Scenario → List Diag`(正規順序で、重複なし) |

証明する定理:

1. **健全性・完全性**: `(check s).all (·.severity = .warning) ↔ Valid s`。さらに規則ごとに「その規則の検出結果が出る ↔ その規則の `Prop` が成り立つ」。
2. **G の網羅判定の正しさ**: 有限の数え上げによる判定が `∀ σ ∈ P, |match σ| = 1` と同値。
3. **出力の決定性**: `check s` は §6.3 の順序でソート済みで、重複がない。入力配列の並べ替えに対して `check` は不変。
4. **同時刻イベントの交換可能性**: T005 と I004 の違反がなければ、同時刻のイベントの処理順を入れ替えても終了状態と検出結果は変わらない。
5. **知識の単調性**: どのキャラクターについても、時刻が進んで知識が減ることはない。
6. **仕様の無矛盾性**: 正しいシナリオが少なくとも1つ存在する(具体例を `decide` で示す)。
7. **導出制約の正しさ**: owner の異なるゴールの集合について、「終了時の保持者の割り当てで、全ゴールの requires_items を同時に満たすものが存在する」⇔「消費済みのアイテムを要求しておらず、各組の requires_items が交わらない」。
8. **区間の整合**: T001〜T006 の違反がなければ、各キャラクターの居場所の区間は互いに重ならず、各イベント時刻での居場所(§2.1)と一致する。
9. **移動時間の決定性**: R005 の違反がなければ `travelTime` は関数として一意に定まる。

## 8. 作者向け YAML(Go 側のみ。参考)

Go CLI は作者が書きやすい YAML を受け付け、§1 の正規化 JSON に変換してから検査する。変換は Go 側だけの責務で、Lean との差分テストの対象外とする(変換結果の JSON に対する単体テストで担保する)。主な変換は次のとおり。

- 時刻 `"21:00"` → 1260。`"25:30"` のように 24 時以降も書ける。`"2d 09:00"` は 2 日目(0 起算で `2*1440 + 540`)。
- キャラクターごとのタイムライン記法(`characters[].timeline`)→ `events` に平坦化する。event ID を省略した場合は `<character>#<連番>` で自動採番する。

YAML の具体的なスキーマは Phase 4 で別紙(docs/yaml.md)として定める。

## 9. 例

```jsonc
{
  "spec_version": "0.2.0",
  "start_time": 1260, "end_time": 1320,
  "characters": [{"id": "alice"}, {"id": "bob"}],
  "areas": [{"id": "house", "internal_minutes": 5}],
  "locations": [{"id": "hall", "area": "house"}, {"id": "study", "area": "house"}],
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
  "choices": [{"id": "c_vote", "owner": "bob", "values": ["alice", "bob"]}],
  "endings": [{"id": "end_a", "condition": {"and": [{"var": "g_alice"}, {"eq": {"var": "c_vote", "value": "bob"}}]}}]
}
```

期待される出力:

```json
{
  "spec_version": "0.2.0",
  "diagnostics": [
    {"code": "G001", "severity": "error", "args": [], "witness": {"c_vote": "alice", "g_alice": false, "g_bob": false}},
    {"code": "I001", "severity": "error", "event": "e3", "args": ["alice", "poison", "character:bob"]},
    {"code": "K002", "severity": "error", "event": "e3", "args": ["alice", "poison_in_tea"]},
    {"code": "T003", "severity": "error", "event": "e1", "args": ["alice", "hall", "study", "5"]}
  ]
}
```

- T003: hall → study はエリア house の中なので 5 分かかるが、e1 は 2 分で到着している。
- I001: e2 で毒を bob に渡した後、e3 で alice が使っている。
- K002: alice は `poison_in_tea` を知らないまま e3 で行動している。
- G001: 最小の割り当て(全変数が定義域の先頭: `c_vote = "alice"`、ゴールはすべて false)で該当するエンディングがない。
- T009 は出ない: alice と bob は 1272〜1320 に study に一緒にいるが、その間の e2(transfer)が2人を参加者に含むので、遭遇は認知されている。e2 を削除すると `T009 ["alice", "bob", "study", "1272", "1320"]` が出る。

## 10. 変更履歴

- **0.2.0**
  - A: エリア(`areas`, `locations[].area`, `area_travel`)と、移動時間の決定規則。`travel` / `area_travel` の `bidirectional`
  - B: 公共の場所(`locations[].public`)と、遭遇を認知していない状況の検査(T009)。居場所の区間(§2.3)
  - C: `observe` イベント(場所の条件付きの知識獲得。気づかれない観察対象 `targets`)
  - D: `scene.reveals`(参加者全員が知識を得る)
  - E: `characters[].npc`(G008 の対象外)、`die` イベントと死亡後の行動の検査(T010)
  - F: 盤面 `board` と、終了状態との照合(H006, H007)
  - G: 手がかりの `item`(K004, K005)。clue の `location` を省略可に(R007)
  - H: ゴールの `requires_items` と、制約の導出(§4.6)
  - I: 列挙型の選択(`choices[].values`)、論理式の `eq`、割り当ての順序の一般化、G007 の上限を割り当て数に変更、G009、R008、R009
- **0.1.0**: 初版
