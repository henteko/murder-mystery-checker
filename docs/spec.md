# mmcheck 仕様書

- 仕様バージョン: **0.5.1**
- 本書が唯一の正(single source of truth)。Lean モデル (`lean/`) は本書を形式化し、Go 実装 (`go/`) は Lean モデルと差分テストで一致させる。
- 本書を変更した場合は仕様バージョンを上げ、Lean → オラクル → Go の順に追従させる。
- 変更履歴は §10。

## 0. 用語と全体像

| 用語 | 意味 |
|---|---|
| シナリオ | 検査対象。登場人物・場所・アイテム・情報・タイムライン・ハンドアウト・盤面・主張・ゴール・エンディングからなる |
| タイムライン | ゲーム開始前に起きた出来事(イベント)の列。`start_time` から `end_time` まで。**客観的な事実**を表す |
| 終了状態 | タイムラインの全イベントを適用した後の状態 = ゲーム開始時点の状態 |
| ハンドアウト | 各キャラクターのプレイヤーに配られる資料。ゲーム開始時の居場所・所持品・知識を宣言する |
| 盤面 (board) | ゲーム開始時に各場所に置かれているアイテムの宣言(探索カードなど) |
| 知識 (fact) | キャラクターが知っている(と思っている)情報。**真偽**を持つ。偽の知識は嘘や思い込みを表す |
| 証言 (claim) | 時刻付きの知識。「何時に何をした」という情報で、タイムライン上のイベントと時刻を照合できる |
| 断言 (assertion) | 真相の解説が前提にする事実(「01:00 に X は自室にいない」など)。タイムラインと照合する |
| NPC | プレイヤーが担当しないキャラクター(被害者など)。ゴールとハンドアウトを持たなくてよく、その知識はプレイヤーには手に入らない |
| エリア | 場所のまとまり(館内など)。移動時間をエリア単位で指定できる |
| 公共の場所 | 大広間・廊下など、複数人が居合わせても不自然でない場所。遭遇の検査(T009)の対象外 |
| 知覚 (perception) | ある場所から別の場所が見える・聞こえるという関係(窓の下、教室の前の廊下など) |
| 変数 | ゴール(達成したか: 真偽値)と選択(真偽値、または列挙された値のどれか) |
| パターン | 全変数への値の割り当てのうち、制約(明示した制約 + 導出した制約)をすべて満たすもの |

検査は次の7群からなる。

| 群 | 内容 |
|---|---|
| R | 構造・参照整合(他の群の前提) |
| T | タイムライン(居場所・移動・同時刻の重複・死亡・遭遇・知覚) |
| I | 所持品(アイテムの保持・受け渡し・消費) |
| K | 知識・手がかり(知らない情報での行動、解決可能性、手がかりの所在、嘘の解明可能性、証言の時刻) |
| H | ハンドアウト・盤面とタイムライン終了状態の整合 |
| A | 真相の断言とタイムラインの整合 |
| G | ゴール・選択・エンディングの網羅性と排他性 |

## 1. 入力: 正規化 JSON

Lean オラクルと Go 実装が共通に受け付ける入力形式。作者が書く YAML(§8)は Go 側でこの形式に変換される。

### 1.1 基本型

- **ID**: 空でない文字列。種類(kind)ごとに一意。種類が異なれば同じ文字列を使ってよい。
  - kind: `character`, `area`, `location`, `item`, `fact`, `clue`, `event`, `assertion`, `variable`(ゴールと選択で共有), `ending`, `handout`(キャラクター ID で識別), `board`(場所 ID で識別)
- **値 (Value)**: 列挙型の選択がとりうる値。空でない文字列。
- **時刻 (Time)**: 0 以上 10,000,000 以下の整数。単位は分。絶対時刻(例: 1日目 21:00 = 1260)。
- **分 (Minutes)**: 0 以上 10,000,000 以下の整数。
- 配列の順序は意味を持たない(検出結果は §6.3 の正規順序で出力される)。
- 未知のフィールドは無視する。`note` フィールドはどこにでも置けて、検査に使わない。

### 1.2 トップレベル

```jsonc
{
  "spec_version": "0.5.1",
  "start_time": 1080,            // Time
  "end_time": 1440,              // Time
  "claim_tolerance": 5,          // Minutes。証言の時刻の許容誤差の既定値(省略時 0)
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
  "perception": [                // from にいると to の様子が見える・聞こえる
    {"from": "study", "to": "garden", "bidirectional": false}
  ],
  "placements": [{"character": "alice", "location": "hall"}],
  "items": [
    {"id": "knife", "initial": {"character": "alice"}},
    {"id": "key",   "initial": {"location": "study"}}
  ],
  "facts": [ /* §1.4 */ ],
  "initial_knowledge": [{"character": "alice", "fact": "alice_saw_bob"}],
  "events": [ /* §1.3 */ ],
  "clues": [ /* §1.6 */ ],
  "solution_facts": ["alice_saw_bob"],
  "assertions": [ /* §1.7 */ ],
  "handouts": [ /* §1.5 */ ],
  "board": [ /* §1.5 */ ],
  "goals":   [ /* §1.8 */ ],
  "choices": [ /* §1.8 */ ],
  "constraints": [ /* Formula */ ],
  "endings": [{"id": "end_true", "condition": /* Formula */ {"var": "c_confess"}}]
}
```

`start_time`, `end_time`, `characters`, `locations`, `placements` 以外は省略可能。配列は省略時に空配列。

`items[].initial` は `{"character": ID}` か `{"location": ID}` のどちらか一方だけを持つ(それ以外はスキーマエラー: §6.4)。

#### 移動時間の決定

異なる場所 a, b について、a から b への移動時間 `travel(a, b)` を次の順で決める。最初に当てはまったものを採用する。

1. `travel` に (a, b) のエントリがある(`bidirectional: true` のエントリ (b, a) を含む)→ その `minutes`
2. a と b が同じエリア X に属し、X に `internal_minutes` がある → `X.internal_minutes`
3. a がエリア X、b がエリア Y(X ≠ Y)に属し、`area_travel` に (X, Y) のエントリがある(`bidirectional` を含む)→ その `minutes`
4. どれにも当てはまらない → 経路なし

#### 知覚

`perceives(a, b)` は、`a == b`、または `perception` に (a, b) のエントリがある(`bidirectional` を含む)ことをいう。推移的には広げない。

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
| `move` | `character`, `to`(location), `arrive`(Time), `mode`(省略時 `"walk"`), `fatal`(省略時 false) | character | character | — |
| `scene` | `location`, `participants`(1人以上、重複なし), `reveals`(fact の配列、省略時は空) | participants 全員 | participants 全員 | 参加者全員が location にいる |
| `observe` | `character`, `location`, `target_location`(省略時は location), `targets`(character の配列、省略時は空、重複なし), `facts`(1つ以上) | character | character | character が location に、targets 全員が target_location にいる。`perceives(location, target_location)` |
| `transfer` | `from`, `to`(character), `item` | from, to | from | from と to が同じ場所にいる |
| `pickup` | `character`, `item` | character | character | item が character の居場所に置かれている |
| `drop` | `character`, `item` | character | character | — |
| `use` | `character`, `item` | character | character | — |
| `consume` | `character`, `item` | character | character | — |
| `learn` | `character`, `facts`(1つ以上) | character | character | — |
| `tell` | `from`, `to`(character), `facts`(1つ以上) | from, to | from | from と to が同じ場所にいる |
| `die` | `character` | character | character | — |

- `move.mode`: `"walk"`(徒歩)、`"fall"`(落下)、`"carried"`(運ばれる)のいずれか。`walk` 以外は移動時間と経路の検査(T002, T003)を行わない。
- `move.fatal`: true なら、到着時刻にそのキャラクターが死亡する(「落下して即死」など)。
- **参加者 (participants)** は同時刻の重複(T005)、移動中(T006)、死亡後の行動(T010)、遭遇の認知(T009)の判定に使う。
- **行為者 (actors)** は `requires` の判定(K002)に使う。
- `observe` の `targets` は、気づかれずに観察される人物。参加者ではないので T005、T006、T010 の対象にならない。死亡した人物も target にできる(遺体を見るなど)。`target_location` を location と別にすると、窓の下を見る・悲鳴を聞くといった、離れた場所の観察を表せる。
- `learn` は場所に依存しない知識の獲得(内省、思い出す、後日の伝聞など)に使う。

### 1.4 知識

```jsonc
{"id": "f_dating", "truth": false, "contradicted_by": ["f_focus_on_club"]}
{"id": "f_left_1800", "about": {"event": "s_05", "point": "at"}, "claimed_at": 1080, "tolerance": 5}
{"id": "f_plain"}
```

| フィールド | 型 | 説明 |
|---|---|---|
| `truth` | bool(省略時 true) | 偽なら、嘘・思い込み・誤認を表す |
| `contradicted_by` | fact ID の配列(省略時は空) | 偽の知識を否定する真の知識。`truth: false` の知識だけが持てる |
| `about` | `{"event": ID, "point": "at" \| "arrive"}` | 証言の対象のイベント。`point` は省略時 `"at"`。`"arrive"` は move でのみ使える |
| `claimed_at` | Time | 証言が主張する時刻。`about` と組で指定する |
| `tolerance` | Minutes | この証言の時刻の許容誤差。省略時は `claim_tolerance` |

`about` と `claimed_at` を持つ知識を **証言** と呼ぶ。

### 1.5 ハンドアウトと盤面

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

### 1.6 手がかり

```jsonc
{"id": "x_clock", "location": "study", "item": "clock", "reveals": ["murder_at_0100"]}
{"id": "x_about_alice", "deck": "アリスについて", "reveals": ["alice_secret"]}
```

- `location`、`item`、`deck` のうち少なくとも1つが必要。
- `item` を指定すると、そのアイテムから分かる手がかりになる。`location` も指定した場合は「ゲーム開始時にそのアイテムがその場所にある」ことの宣言を兼ねる(K005)。
- `deck` は場所に結び付かない探索カードの山札の名前(自由な文字列。参照ではない)。

### 1.7 断言

```jsonc
{"id": "a_alibi", "kind": "present", "location": "smoking_area", "at": 1500, "characters": ["bob", "carol"]}
{"id": "a_absent", "kind": "absent",  "location": "roof",         "at": 1080, "characters": ["bob"]}
```

- `kind`: `"present"`(全員がその時刻にその場所にいる)または `"absent"`(全員がその時刻にその場所にいない)。
- `at` は `start_time ≤ at < end_time` を満たす(R013)。

### 1.8 ゴールと選択

```jsonc
// goals[]
{"id": "g_collect", "owner": "alice", "requires_items": ["knife", "key"]}  // requires_items は省略可
// choices[]
{"id": "c_confess", "owner": "bob"}                                        // 真偽値の選択
{"id": "c_vote", "owner": "bob", "values": ["alice", "bob", "tie"]}       // 列挙型の選択
```

- `requires_items`: このゴールの達成には、**ゲーム終了時に owner がこれらのアイテムをすべて所持している**ことが必要(必要条件。十分条件ではない)。G 群で制約を導出するのに使う(§4.7)。
- `values` があれば列挙型、なければ真偽値。`values` は空でなく、重複を含まない。

### 1.9 論理式 (Formula)

```
Formula := {"const": true|false}
         | {"var": <ゴールまたは真偽値の選択の ID>}
         | {"eq": {"var": <列挙型の選択の ID>, "value": <Value>}}
         | {"plurality": {"votes": [<列挙型の選択の ID>, ...], "value": <Value>}}
         | {"tie": {"votes": [<列挙型の選択の ID>, ...]}}
         | {"not": Formula}
         | {"and": [Formula, ...]}    // 空配列なら true
         | {"or":  [Formula, ...]}    // 空配列なら false
```

**集計 (plurality / tie)**: `votes` は1つ以上の列挙型の選択で、**すべて同じ値の集合**を持つ(R012)。割り当て σ のもとで、値 w の得票数を `count(w) = |{x ∈ votes | σ(x) = w}|`、最大得票数を `M = max_w count(w)` とする。

- `plurality(v)`: `count(v) = M` かつ、`count(w) = M` となる値 w が v だけ(単独最多)。
- `tie`: `count(w) = M` となる値 w が2つ以上(最多が同数)。

votes が1つ以上あれば、各値の `plurality` と `tie` のうち、ちょうど1つが真になる(§7 の定理 10)。

## 2. 状態と操作的意味論

### 2.1 状態

```
Holder    := Char(c) | Place(l) | Consumed
Position  := { dest: location, arrive: Time, via: event ID | none }
State     := {
  pos    : character → Position,
  holder : item → Holder,
  knows  : character → fact の集合,
  dead   : character → event ID | none     // 死亡させた die イベント、または fatal な move
}
```

- キャラクター c が時刻 t に **移動中** であるとは `pos(c).via ≠ none` かつ `t < pos(c).arrive` であること。移動中でなければ、c は `pos(c).dest` にいるとみなす(初期配置は移動中にならない)。
- **死亡時刻** `deathTime(c)`: `dead(c)` が die イベント d なら `d.at`、fatal な move m なら `m.arrive`。
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
| `move` | `pos(character) := { dest: to, arrive: arrive, via: id }`。`fatal` なら、さらに `dead(character) := id`(すでに死亡していれば変更しない) |
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

各キャラクター c の **居場所の区間** の列を、イベント列から次のように定める。c の move イベントを正規順序で m₁, …, mₖ とする。

- 区間 0: `(placement の場所, start_time, m₁.at)`。k = 0 なら終端は `end_time`
- 区間 i(1 ≤ i ≤ k): `(mᵢ.to, mᵢ.arrive, mᵢ₊₁.at)`。i = k なら終端は `end_time`
- c が死亡している(E.dead(c) ≠ none)場合、各区間の終端を `min(終端, deathTime(c))` に切り詰める
- 始端 ≥ 終端 となった区間は捨てる

区間 (l, a, b) は「c が時刻 a 以上 b 未満のあいだ l にいた」ことを表す。

### 2.4 時刻 t での居場所

`whereAt(c, t)`(start_time ≤ t < end_time)を次のように定める。

- c が死亡していて `deathTime(c) ≤ t` → `"dead"`
- c の区間 (l, a, b) で `a ≤ t < b` となるものがある → `l`
- それ以外 → `"transit"`

### 2.5 プレイヤーが手に入れられる知識

知識 f が **入手可能** であるとは、終了状態で **NPC ではない** キャラクターの誰かが f を知っている(`f ∈ E.knows(c)`)か、どれかの clue の `reveals` に f が含まれることをいう。

### 2.6 文字列の順序

ID と値の昇順は **Unicode コードポイントの辞書式順序** で比べる。UTF-8 のバイト列の辞書式順序はこれと一致するので、Go の `strings.Compare` と Lean の `String.lt`(`Char` の比較による辞書式順序)はどちらもこの順序になる。

## 3. 検査の段階

1. **R001**(ID の重複)を検査する。違反があれば **R001 の結果だけを出力して終了** する(ID が重複していると参照先が1つに決まらず、他の規則の結果が入力配列の並び順に依存してしまうため)。
2. **R 群** の残りを検査する。R の違反が1件でもあれば **R の結果だけを出力して終了** する(参照が壊れていると状態を定義できないため)。
3. R の違反がなければ、T / I / K / H / A / G 群をすべて検査し、結果を合わせて出力する。

## 4. 検査規則

各規則は **エラー検出結果(diagnostic)** を出す。フィールドの意味は §6 を参照。`args` は規則ごとに決まった順序の文字列配列で、数値は10進表記の文字列にする。保持者 (Holder) は `"character:<id>"` / `"location:<id>"` / `"consumed"` と表記する。

### 4.1 R: 構造・参照整合

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| R001 | error | 同じ種類の ID が重複している(goal と choice は `variable` として合わせて数える。handout はキャラクター ID、board は場所 ID で数える) | — | [kind, id] |
| R002 | error | 存在しない ID を参照している | 参照元がイベントならその ID | [referrer, kind, id] |
| R003 | error | キャラクターの `placements` が0件または2件以上ある | — | [character] |
| R004 | error | `start_time > end_time` | — | [] |
| R005 | error | `travel` / `area_travel` / `perception` に `from == to` のエントリがある、または bidirectional を展開した後に同じ (from, to) が重複している | — | [table, from, to] |
| R006 | error | イベントの形が不正(下記 reason) | id | [reason] |
| R007 | error | clue に `location` も `item` も `deck` もない | — | [clue] |
| R008 | error | 列挙型の選択の `values` が空、または値が重複している | — | [choice] |
| R009 | error | 論理式の型の誤り: `var` が列挙型の選択を指す、`eq` がゴールや真偽値の選択を指す、`eq` の値が選択の `values` にない | — | [referrer, variable, value] |
| R010 | error | 真偽の指定の誤り: `truth: true` の知識が `contradicted_by` を持つ、または `contradicted_by` に偽の知識が含まれる | — | [fact, refuter] |
| R011 | error | 証言の形の誤り(下記 reason) | — | [fact, reason] |
| R012 | error | 集計の形の誤り(下記 reason) | — | [referrer, reason] |
| R013 | error | 断言の時刻が `start_time ≤ at < end_time` を満たさない | — | [assertion] |

- R002 の `referrer` は参照元を `"<kind>:<id>"` で表したもの: `event:e1`, `item:knife`(initial), `location:hall`(area), `placement:alice`, `initial_knowledge:alice`, `fact:f1`(contradicted_by, about), `clue:c1`, `solution`, `assertion:a1`, `handout:alice`, `board:study`, `goal:g1`, `choice:c1`, `constraint`, `ending:end1`, `travel`, `area_travel`, `perception`。R002 は (referrer, kind, id) の組ごとに1件出す。
- R005 の `table` は `"travel"`、`"area_travel"`、`"perception"` のいずれか。
- R009 / R012 の `referrer` は `constraint` または `ending:<id>`。R009 の `value` は `var` の誤りなら `""`。R010 の `refuter` は、truth: true なのに contradicted_by を持つ場合 `""`。
- R006 の reason:
  - `arrive_before_depart`: move で `arrive < at`
  - `self_transfer`: transfer で `from == to`
  - `self_tell`: tell で `from == to`
  - `self_observe`: observe で character が targets に含まれる
  - `empty_participants`: scene で participants が空
  - `duplicate_participant`: scene の participants、または observe の targets に同じキャラクターが2回以上現れる
  - `empty_facts`: learn / tell / observe で facts が空
  - `unknown_mode`: move の mode が `walk` / `fall` / `carried` 以外
- R011 の reason:
  - `about_without_claimed_at` / `claimed_at_without_about`: 片方だけがある
  - `arrive_on_non_move`: `point: "arrive"` の対象の ID を持つイベントのいずれかが move ではない(ID が重複していても、イベントの並び順によらず決まる)
  - `unknown_point`: point が `at` / `arrive` 以外
- R012 の reason:
  - `empty_votes`: votes が空
  - `not_enum`: votes に列挙型ではない選択が含まれる
  - `different_values`: votes の選択の値の集合が一致しない
  - `unknown_value`: plurality の value が、votes の列挙型の選択のいずれかの値の集合に含まれない(`different_values` と同時に出ることがある)

### 4.2 T: タイムライン

イベント e(時刻 t = e.at)を処理前の状態 S に対して評価する。

| コード | 重大度 | 条件 | event | args |
|---|---|---|---|---|
| T001 | error | `t < start_time` または `t > end_time`、または move で `arrive > end_time` | e | [] |
| T002 | error | move(mode が walk): `S.pos(c).dest ≠ to` かつ `travel(S.pos(c).dest, to)` が経路なし | e | [character, from, to] |
| T003 | error | move(mode が walk): 経路はあるが `arrive − t < travel(from, to)` | e | [character, from, to, minutes] |
| T004 | error | move: `S.pos(c).dest == to` | e | [character, location] |
| T005 | error | 参加者 c が、正規順序で e より前にある同じ時刻 t のイベント e' の参加者でもある | e | [character, e'.id] |
| T006 | error | 参加者 c が時刻 t に移動中(§2.1) | e | [character, S.pos(c).via] |
| T007 | error | scene / observe: 場所の条件の対象者 c(scene の参加者、observe の character と targets)が、条件の場所(scene の location、observe の character は location、targets は target_location)にいない | e | [character, 条件の場所, 実際の居場所] |
| T008 | error | transfer / tell: from と to のどちらも移動中ではなく、かつ居場所が異なる | e | [from, to, from の居場所, to の居場所] |
| T009 | warning | 遭遇を認知していない(下記) | — | [c₁, c₂, location, from, to] |
| T010 | error | 参加者 c が死亡している(`S.dead(c) = d ≠ none`) | e | [character, d] |
| T011 | error | observe: `perceives(location, target_location)` が成り立たない(その場所からは見えない・聞こえない) | e | [character, location, target_location] |
| T012 | warning | observe: targets の x が、同じ時刻 t に始まる move m で移動している(下記) | e | [x, m.id] |

- T005 は、e より前の同時刻のイベントのうち正規順序で**最後**のもの1つについてだけ、参加者ごとに出す。
- T007 の「実際の居場所」は、移動中なら `"transit"`、そうでなければ `S.pos(c).dest`。
- **移動中の抑制規則**: **参加者**が移動中の場合、その参加者について居場所に依存する検査(T007, T008, I003)は行わない(T006 だけを出す)。observe の targets は参加者ではないので抑制されず、移動中なら T007(`"transit"`)になる。
- **T009 遭遇の認知**: 相異なるキャラクター c₁ < c₂(ID 順)の居場所の区間 (l, a₁, b₁), (l, a₂, b₂) が同じ場所 l で `lo = max(a₁, a₂) < hi = min(b₁, b₂)` を満たし、l が公共の場所ではないとき、次のどちらかを満たすイベントが時刻 `[lo, hi]` にない場合に出す。
  - c₁ と c₂ をどちらも参加者に含むイベント(scene / transfer / tell)
  - 一方が character で、もう一方が targets に含まれ、`location = target_location = l` の observe

  args は [c₁, c₂, l, lo, hi]。区間の組ごとに1件。
- **T012 観察と同時の出発**: observe e の targets の x について、`m.at = e.at` で x が移動する move m(m の character が x)があれば、(x, m) の組ごとに1件出す。同時刻のイベントは ID の順に処理するので、このとき e の T007 の結果(x がまだ元の場所にいるか、もう移動中か)は e と m の ID の順で決まってしまう。観察か出発の時刻を1分ずらすなどして、どちらが先かを明示する。T012 は T007 の有無にかかわらず出す。

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
| K003 | error | `f ∈ solution_facts` が入手可能(§2.5)ではない(真相にたどり着けない) | — | [f] |
| K004 | error | `item` を持つ clue について `E.holder(item) == Consumed`(手がかりが失われている) | — | [clue, item] |
| K005 | error | `item` と `location` を両方持つ clue について `E.holder(item) ≠ Place(location)` かつ `≠ Consumed` | — | [clue, item, location, holder の表記] |
| K006 | error | 偽の知識 f が、終了状態で NPC ではないキャラクターに知られている、またはいずれかのハンドアウトの `knows` にあるのに、`contradicted_by` の知識がどれも入手可能ではない(嘘・思い込みを見破れない) | — | [f] |
| K007 | error | `solution_facts` に偽の知識が含まれる(真相が偽の情報に依存している) | — | [f] |
| K008 | error | 真の証言 f について、`|f.claimed_at − actual| > tol(f)`。actual は `about.event` の `at`(point が `"arrive"` なら `arrive`)、tol(f) は `f.tolerance`、なければ `claim_tolerance` | — | [f, claimed_at, actual] |

- 偽の証言は嘘や記憶違いを表すので、K008 の対象外とする。

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

### 4.6 A: 真相の断言

各断言 a と `c ∈ a.characters` について、`w = whereAt(c, a.at)`(§2.4)とする。

| コード | 重大度 | 条件 | args |
|---|---|---|---|
| A001 | error | `kind = present` かつ `w ≠ a.location`、または `kind = absent` かつ `w = a.location` | [a, c, kind, w] |

### 4.7 G: ゴール・選択・エンディング

#### 変数と割り当て

- 変数集合 V = goals の ID ∪ choices の ID。V を ID 昇順に v₁, …, vₙ と並べる。
- 変数 v の **定義域** dom(v): ゴールと真偽値の選択は `[false, true]`、列挙型の選択は `values` を昇順に並べたもの。
- 割り当て σ は各 vᵢ に dom(vᵢ) の値を対応させる。**割り当ての順序** は、(σ(v₁) の定義域内の位置, …, σ(vₙ) の定義域内の位置) の辞書式順序で決める(最小はすべて定義域の先頭)。
- 割り当ての総数 N = Π |dom(vᵢ)|。

#### 導出制約(requires_items から)

終了状態 E に基づいて、次の制約を `constraints` に加える。これを **実効制約** と呼ぶ。

1. ゴール g の `requires_items` に `E.holder(i) == Consumed` のアイテム i がある → `¬g`(アイテムが失われていて達成できない)
2. owner が異なるゴール g₁ < g₂ の `requires_items` に共通のアイテムがある → `¬(g₁ ∧ g₂)`(同じアイテムを2人が同時には持てない)

#### パターンとエンディング

- **パターン**: 実効制約をすべて満たす割り当て。P をパターン全体の集合とする。
- `match(σ) = { e ∈ endings | e.condition(σ) = true }`

| コード | 重大度 | 条件 | args | witness |
|---|---|---|---|---|
| G007 | error | N > 1,048,576(= 2²⁰。数え上げの上限を超える)。このとき G001〜G006, G009 は検査しない | [N] | — |
| G005 | error | P が空(実効制約が矛盾している)。このとき G001〜G004, G006, G009 は検査しない | [] | — |
| G001 | error | `match(σ) = ∅` となる σ ∈ P がある(**網羅性**の違反)。そのような σ のうち最小のもの1つを witness にして**1件だけ**出す | [] | σ |
| G002 | error | 相異なるエンディング e₁ < e₂(ID 順)について、`{e₁, e₂} ⊆ match(σ)` となる σ ∈ P がある(**排他性**の違反)。ペアごとに、最小の σ を witness にして1件出す | [e₁, e₂] | σ |
| G003 | error | エンディング e について、`e ∈ match(σ)` となる σ ∈ P がない(到達不能なエンディング) | [e] | — |
| G004 | error | ゴール g について、σ(g) = true となる σ ∈ P がない(達成不可能なゴール) | [g] | — |
| G006 | warning | ゴール g がすべての σ ∈ P で true(必ず達成されるゴール)、または選択 x がすべての σ ∈ P で同じ値(実質的に選べない選択) | [variable] | — |
| G008 | warning | NPC ではないのに、ゴールを1つも持たないキャラクターがいる | [character] | — |
| G009 | warning | 列挙型の選択 x の値 v について、σ(x) = v となる σ ∈ P がない(選ばれることのない値) | [x, v] | — |

**正しいシナリオの条件(G 群)**: 任意のパターン σ ∈ P について `|match(σ)| = 1`(エンディングがちょうど1つに決まる)。これは G001 と G002 がともに出ないことと同値である。

## 5. 正しさの定義

シナリオ s が **正しい (valid)** とは、§4 の error 規則の条件がどれも成り立たないこと。Lean では、判定関数とは独立に、各規則の条件を `Prop` で書いて否定を連言した宣言的な述語 `Valid s` として定義する。warning 規則は正しさに影響しない。

「判定器が error を1件も出さない ⇔ `Valid s`」は定義ではなく、**証明すべき定理** である(§7)。

## 6. 出力: エラー検出結果 JSON

### 6.1 形式

```jsonc
{
  "spec_version": "0.5.1",
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
2. `event`(なしは最小。どの ID よりも前)
3. `args`(文字列の配列として辞書式に比べる。短い方が接頭辞なら短い方が先)
4. `witness`(§4.7 の割り当ての順序。なしは最小として扱う)
5. `severity`(error が先)
6. `witness` の値(なしが最小。(変数 ID, 値) の組の列として辞書式に比べる。組は変数 ID、値の順に比べ、値は真偽値が文字列より前、false が true より前、文字列どうしは文字列の順)

5 と 6 は順序を全順序にするための規則で、通常の出力は 1〜4 で決まる。文字列は Unicode のコードポイントの列として比べる。

### 6.4 スキーマエラー

JSON として不正な入力、必須フィールドの欠落、型の不一致、範囲外の数値、`initial` の形が不正な入力は **入力エラー** とし、エラー検出結果を出さない。

- 数値(時刻・分・許容誤差)は、値が整数で 0 以上 10,000,000 以下のもの。表記は問わない(`1260`、`1260.0`、`1.26e3` はどれも 1260)。`1260.5` や負の数は入力エラー。指数部が 100,000 を超える数(`1e100001` など)も入力エラー(Lean の JSON パーサの制限。値が 0 でも同じ)。
- 同じオブジェクトに同じキーが2回以上ある入力は入力エラー。
- ID などの文字列は空文字列を許さない。値が `null` のフィールドは省略と同じ。知らないフィールドは読み飛ばす。Lean オラクルと Go はどちらも入力エラーを返す(終了コード 2)。差分テストでは「どちらも入力エラーになること」だけを比べる。

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
| §1.2 移動時間・知覚 | `travelTime : Scenario → Loc → Loc → Option Nat`、`perceives : Scenario → Loc → Loc → Bool` |
| §2 意味論 | `step : Scenario → State → Event → State`、`run`、`finalState`、`segments`(§2.3)、`whereAt`(§2.4)、`obtainable`(§2.5) |
| §4 各規則 | 規則ごとに `Prop` の述語(例: `TravelTooShort s e`)と判定関数(`checkT003 : … → List Diag`) |
| §5 正しさ | `Valid s : Prop` |
| §6 出力 | `check : Scenario → List Diag`(正規順序で、重複なし) |

証明する定理:

1. **健全性・完全性**: `(check s).all (·.severity = .warning) ↔ Valid s`。さらに R 群以外の error 規則ごとに「その規則の検出結果が出る ↔ R 群の違反がなく、その規則の `Prop` が成り立つ」。
2. **G の網羅判定の正しさ**: 有限の数え上げによる判定が `∀ σ ∈ P, |match σ| = 1` と同値。
3. **出力の決定性**: `check s` は §6.3 の順序で狭義に整列しており、重複がない。トップレベルのどの配列を並べ替えても `check` は不変(R 群の違反があっても)。配列の要素の中の配列(scene の participants、choice の values など)は対象外。
4. **同時刻イベントの交換可能性**: T005 と I004 の違反がなく、T012 も出ていなければ、時刻順を保つどの並べ方でイベントを処理しても、終了状態とイベントごとの検出結果(T / I / K 群)は変わらない。observe の対象は参加者ではないため T005 の対象外で、T012 の状況(「x が 10:00 に移動し、c が 10:00 に x を観察する」)では、ID の順によって T007 が出たり出なかったりする。
5. **知識の単調性**: どのキャラクターについても、時刻が進んで知識が減ることはない。
6. **仕様の無矛盾性**: 正しいシナリオが少なくとも1つ存在する(具体例を `decide` で示す)。
7. **導出制約の正しさ**: owner の異なるゴールの集合について、「終了時の保持者の割り当てで、全ゴールの requires_items を同時に満たすものが存在する」⇔「消費済みのアイテムを要求しておらず、各組の requires_items が交わらない」。
8. **区間の整合**: キャラクター c の move がどれも開始時刻以降に出発し(T001)、出発 ≤ 到着で(R006)、出発時に移動中でない(T006)なら、c の居場所の区間 `segments(c)` は時刻順に並んで互いに重ならず、各区間は空でない。さらに、開始時刻 ≤ t < 終了時刻で死亡時刻より前の t について、`whereAt(c, t)`(§2.4)は、時刻 t 以前のイベントをすべて処理した状態での居場所(移動中なら transit、そうでなければ最後の行き先)と一致する。イベントの処理前の状態(§2.1)とは一致しないことがある: 同じ時刻にあとから move するとき、そのイベントより前の処理前の状態ではまだ出発していないが、`whereAt` は出発時刻から transit になる。
9. **移動時間の決定性**: R005 の違反がなければ、どの (from, to) についても一致するエントリは高々1つで、移動時間・知覚はその唯一のエントリで決まり、表の並び順によらない。
10. **集計の分割**: votes が空でなければ、任意の σ について、`{plurality(v) | v ∈ 値の集合} ∪ {tie}` のうちちょうど1つが真になる。
11. **死亡の一意性**: 各キャラクターの死亡イベントは高々1つに定まり、死亡時刻以降の区間はない。

## 8. 作者向け YAML(Go 側のみ。参考)

Go CLI は作者が書きやすい YAML を受け付け、§1 の正規化 JSON に変換してから検査する。変換は Go 側だけの責務で、Lean との差分テストの対象外とする(変換結果の JSON に対する単体テストで担保する)。主な変換は次のとおり。

- 時刻 `"21:00"` → 1260。`"25:30"` のように 24 時以降も書ける。`"2d 09:00"` は 2 日目(0 起算で `2*1440 + 540`)。
- キャラクターごとのタイムライン記法(`characters[].timeline`)→ `events` に平坦化する。event ID を省略した場合は `<character>#<連番>` で自動採番する。
- ハンドアウトの時系列表の各行 → 証言(`about` + `claimed_at`)を持つ知識に変換する。

YAML の具体的なスキーマは Phase 4 で別紙(docs/yaml.md)として定める。

## 9. 例

```jsonc
{
  "spec_version": "0.5.1",
  "start_time": 1260, "end_time": 1320,
  "characters": [{"id": "alice"}, {"id": "bob"}],
  "areas": [{"id": "house", "internal_minutes": 5}],
  "locations": [{"id": "hall", "area": "house"}, {"id": "study", "area": "house"}],
  "placements": [{"character": "alice", "location": "hall"},
                 {"character": "bob", "location": "study"}],
  "items": [{"id": "poison", "initial": {"character": "alice"}}],
  "facts": [{"id": "poison_in_tea"},
            {"id": "alice_moved_1265", "about": {"event": "e1"}, "claimed_at": 1265}],
  "events": [
    {"id": "e1", "at": 1270, "kind": "move", "character": "alice", "to": "study", "arrive": 1272},
    {"id": "e2", "at": 1275, "kind": "transfer", "from": "alice", "to": "bob", "item": "poison"},
    {"id": "e3", "at": 1280, "kind": "use", "character": "alice", "item": "poison",
     "requires": ["poison_in_tea"]}
  ],
  "assertions": [{"id": "a1", "kind": "absent", "location": "study", "at": 1275, "characters": ["alice"]}],
  "goals": [{"id": "g_alice", "owner": "alice"}, {"id": "g_bob", "owner": "bob"}],
  "choices": [{"id": "c_vote", "owner": "bob", "values": ["alice", "bob"]}],
  "endings": [{"id": "end_a", "condition": {"and": [{"var": "g_alice"}, {"eq": {"var": "c_vote", "value": "bob"}}]}}]
}
```

期待される出力:

```json
{
  "spec_version": "0.5.1",
  "diagnostics": [
    {"code": "A001", "severity": "error", "args": ["a1", "alice", "absent", "study"]},
    {"code": "G001", "severity": "error", "args": [], "witness": {"c_vote": "alice", "g_alice": false, "g_bob": false}},
    {"code": "I001", "severity": "error", "event": "e3", "args": ["alice", "poison", "character:bob"]},
    {"code": "K002", "severity": "error", "event": "e3", "args": ["alice", "poison_in_tea"]},
    {"code": "K008", "severity": "error", "args": ["alice_moved_1265", "1265", "1270"]},
    {"code": "T003", "severity": "error", "event": "e1", "args": ["alice", "hall", "study", "5"]}
  ]
}
```

- A001: 断言 a1 は「1275 に alice は study にいない」だが、alice は 1272 から study にいる。
- G001: 最小の割り当て(全変数が定義域の先頭: `c_vote = "alice"`、ゴールはすべて false)で該当するエンディングがない。
- I001: e2 で毒を bob に渡した後、e3 で alice が使っている。
- K002: alice は `poison_in_tea` を知らないまま e3 で行動している。
- K008: 証言 `alice_moved_1265` は e1 の時刻を 1265 と主張するが、実際は 1270(`claim_tolerance` は省略時 0)。
- T003: hall → study はエリア house の中なので 5 分かかるが、e1 は 2 分で到着している。
- T009 は出ない: alice と bob は 1272〜1320 に study に一緒にいるが、その間の e2(transfer)が2人を参加者に含むので、遭遇は認知されている。

## 10. 変更履歴

- **0.5.1**
  - §6.4: 入力エラーの条件を明確にした。数値は値が整数なら表記を問わない(0.5.0 の Lean オラクルは `1260.0` を入力エラーにし、`1.26e3` は受け付けていた)。指数部が 100,000 を超える数とキーの重複は入力エラー

- **0.5.0**
  - §3: R001(ID の重複)があれば R001 だけを出す。ID が重複していると、R009 / R010 などの結果が配列の並び順で変わっていた(例: 同じ ID の真の知識と偽の知識の順を入れ替えると R010 が出たり出なかったりする)
  - §7 定理 3: 並べ替え不変性の対象をトップレベルのすべての配列にした

- **0.4.0**
  - T012(warning): observe の対象が同じ時刻に move を始めている。このとき結果がイベント ID の順で決まってしまうため。定理 4 の前提を「T012 が出ていない」とした

- **0.3.1**(定理 3, 4, 8 の証明に伴う修正)
  - §6.3: 正規順序を全順序にした。`event` がないものを最小とし、同じキーなら severity、witness の値で比べる
  - R011 `arrive_on_non_move`: 同じ ID のイベントのいずれかが move でなければ出す(ID が重複したとき、イベントの並び順で結果が変わっていた)
  - §7 定理 3: 並べ替え不変性の対象を `events` 配列とした
  - §7 定理 4: 前提に「同時刻に observe の対象が move しない」を加えた(反例があったため)
  - §7 定理 8: 比べる相手を「各イベント時刻での居場所」から「時刻 t までのイベントを処理した状態での居場所」に正確化し(同時刻の move の前のイベントでは一致しないため)、前提を T001 / T006 / R006 とした

- **0.3.0**
  - K1: 知識の真偽(`facts[].truth`)と、偽の知識を否定する知識(`contradicted_by`)。K006(嘘・思い込みを見破れない)、K007(真相が偽の知識に依存している)、R010
  - K2: 断言 `assertions`(present / absent)と A 群(A001)。時刻 t での居場所 `whereAt`(§2.4)、R013
  - K3: 知覚 `perception` と observe の `target_location`。T011、T007 の条件の場所の変更、T009 の observe による認知は同じ場所に限る
  - K4: 証言(`about`, `claimed_at`, `tolerance`, トップレベルの `claim_tolerance`)と K008、R011
  - K5: move の `mode`(walk / fall / carried)。walk 以外は T002 / T003 を検査しない。R006 に `unknown_mode`
  - K6: move の `fatal`(到着時刻に死亡)。死亡時刻 `deathTime`
  - K7: clue の `deck`。R007 の条件を変更
  - K8: 論理式の `plurality` と `tie`。R012
  - 入手可能(§2.5)を導入し、K003 の判定から NPC の知識を除外(NPC の知識はプレイヤーには手に入らないため)
  - 検査の群を7つに(A 群を追加)
- **0.2.0**
  - A: エリア(`areas`, `locations[].area`, `area_travel`)と、移動時間の決定規則。`travel` / `area_travel` の `bidirectional`
  - B: 公共の場所(`locations[].public`)と、遭遇を認知していない状況の検査(T009)。居場所の区間(§2.3)
  - C: `observe` イベント(場所の条件付きの知識獲得。気づかれない観察対象 `targets`)
  - D: `scene.reveals`(参加者全員が知識を得る)
  - E: `characters[].npc`(G008 の対象外)、`die` イベントと死亡後の行動の検査(T010)
  - F: 盤面 `board` と、終了状態との照合(H006, H007)
  - G: 手がかりの `item`(K004, K005)。clue の `location` を省略可に(R007)
  - H: ゴールの `requires_items` と、制約の導出(§4.7)
  - I: 列挙型の選択(`choices[].values`)、論理式の `eq`、割り当ての順序の一般化、G007 の上限を割り当て数に変更、G009、R008、R009
- **0.1.0**: 初版
