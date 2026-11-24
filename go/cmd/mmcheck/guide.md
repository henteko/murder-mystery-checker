# mmcheck シナリオの書き方(YAML)

mmcheck はマーダーミステリーのシナリオの矛盾を検出する。シナリオは YAML(または正規化 JSON)で書き、
`mmcheck check --format agent scenario.yaml` で検査する。規則の一覧は `mmcheck rules`。

## 検査のループ

1. シナリオを YAML で書く
2. `mmcheck check --format agent --strict scenario.yaml` を実行する
   - 終了コード 0: 合格(`--strict` なら warning もなし)
   - 終了コード 1: 検出結果あり。`diagnostics` の各要素の `message`・`args`・`hint` を見て直す
   - 終了コード 2: 書式の誤り。`input_error.path` の場所(例: `goals[2].owner`)を直す
3. 合格するまで 2 を繰り返す

注意: 矛盾がないことは、良いシナリオであることを意味しない。中身を削れば検出結果は減る。
キャラクター数・死亡・真相・エンディングなどの最低条件は、検査とは別に決めること。

## 基本

- ID は英数字の文字列。種類ごとに一意(ゴールと選択は同じ名前空間)
- 時刻は `"21:00"`(引用符で囲む)、`"25:30"`(24 時以降)、`"2d 09:00"`、または分の整数
- 長さ(`minutes`、`internal_minutes`、`tolerance`)は分の整数
- `name`(表示名)と `note` / `text`(説明)はどこにでも書ける。判定には使わない
- 知らないキーは無視される。同じマッピングに同じキーを2回書くと書式の誤り

## トップレベル

| キー | 内容 |
| --- | --- |
| `start_time`, `end_time` | シナリオの時間(必須) |
| `characters` | キャラクター(必須)。`npc: true` は被害者など、プレイヤーが担当しない人 |
| `areas`, `locations` | 場所(`locations` は必須)。`area` でエリアに入れる。`public: true` は誰でもいる場所 |
| `travel`, `area_travel` | 移動時間。`{from, to, minutes, bidirectional}`。同じエリア内は `areas[].internal_minutes` |
| `perception` | 離れて見える・聞こえる場所。`{from, to, bidirectional}` |
| `items` | アイテム。`initial: {character: ID}` か `{location: ID}`。`tags` で静的なタグ |
| `facts` | 知識。`truth: false` は嘘・思い込み(`contradicted_by` で否定する真の知識) |
| `events` | タイムライン(キャラクターの `timeline` にも書ける) |
| `clues` | 探索カード。`location` / `item` / `deck` のどれか + `reveals`(明かす知識) |
| `solution_facts` | 真相に必要な知識 |
| `assertions` | 真相の断言。`{id, kind: present/absent, location, at, characters}` |
| `handouts`, `board` | ハンドアウトと盤面の宣言(ゲーム開始時の居場所・持ち物・知識) |
| `goals`, `choices`, `constraints`, `endings` | ゴール・選択(投票など)・制約・エンディング |
| `exploration` | `{draws_per_player: n}` 探索フェイズで1人が引く枚数 |

## キャラクターの欄にまとめて書く

```yaml
characters:
  - id: alice
    location: hall            # 初期配置
    knows: [f_secret]         # 最初から知っていること
    timeline:                 # このキャラクターのイベント(本人が自動で入る)
      - {at: "21:10", kind: move, to: study, arrive: "21:15"}
      - {at: "21:20", kind: tell, to: bob, facts: [f_secret]}
```

## イベント

| kind | フィールド |
| --- | --- |
| `move` | `character`, `to`, `arrive`(`mode`: walk/fall/carried、`fatal: true` で到着時に死亡) |
| `scene` | `location`, `participants`(その場の全員), `reveals`(全員が知る知識) |
| `observe` | `character`, `location`, `target_location`(省略時は同じ), `targets`, `facts` |
| `transfer` | `from`, `to`, `item` |
| `pickup` / `drop` / `use` / `consume` | `character`, `item` |
| `learn` | `character`, `facts` |
| `tell` | `from`, `to`, `facts` |
| `die` | `character` |

全イベント共通: `id`, `at`(移動は出発時刻), `requires`(行為者がすでに知っているべき知識)。
同じ時刻のイベントは ID の順に処理する。観察と移動を同じ時刻にしない(T012)。

## ゴール・選択・エンディング

```yaml
goals:
  - id: g_truth
    owner: bob
    condition: {eq: {var: vote, value: alice}}     # 達成条件(ゴール ⇔ 式)
    requires_knowledge: [f_motive]                 # 入手可能でなければ達成できない
    requires_items: [knife]                        # 終了時に持っている必要がある
    requires_tagged: [{tag: private_alice, count: 2}]
    conceals: [f_bob_secret]                       # ほかのプレイヤーに知られていてはいけない
choices:
  - {id: vote, owner: bob, values: [alice, bob]}   # values なしなら真偽値
endings:
  - {id: end_a, condition: {eq: {var: vote, value: alice}}}
  - {id: end_b, condition: {eq: {var: vote, value: bob}}}
```

論理式: `{const: true}`, `{var: ID}`, `{eq: {var: ID, value: v}}`, `{plurality: {votes: [...], value: v}}`,
`{tie: {votes: [...]}}`, `{truth: 知識ID}`, `{not: 式}`, `{and: [式...]}`, `{or: [式...]}`。
どの選び方でも、エンディングはちょうど1つに決まらなければならない(G001 / G002)。

## ハンドアウトの時系列表(証言)

```yaml
handouts:
  - character: tom
    knows: [f_saw_body]
    timeline:
      - {at: "18:00", event: tom_hears_scream, text: 悲鳴を聞いた}   # 実際の出来事の時刻と比べる(K008)
```

## 最小の例(検査に合格する)

```yaml
start_time: "21:00"
end_time: "22:00"
areas:
  - {id: house, internal_minutes: 2}
locations:
  - {id: hall, area: house, public: true}
  - {id: study, area: house}
items:
  - {id: knife, initial: {location: study}}
facts:
  - {id: f_knife_blood, text: ナイフに血がついていた}
  - {id: f_bob_in_study, text: ボブは 21:10 に書斎にいた}
characters:
  - id: victim
    npc: true
    location: study
    timeline:
      - {id: victim_dies, at: "21:12", kind: die}
  - id: alice
    location: hall
    timeline:
      - {id: alice_to_study, at: "21:20", kind: move, to: study, arrive: "21:22"}
      - {id: alice_finds, at: "21:23", kind: observe, location: study, targets: [victim], facts: [f_knife_blood]}
  - id: bob
    location: hall
    knows: [f_bob_in_study]
    timeline:
      - {id: bob_to_study, at: "21:05", kind: move, to: study, arrive: "21:07"}
      - {id: bob_meets, at: "21:10", kind: scene, location: study, participants: [bob, victim]}
      - {id: bob_back, at: "21:14", kind: move, to: hall, arrive: "21:16"}
handouts:
  - {character: alice, knows: [f_knife_blood]}
  - {character: bob, knows: [f_bob_in_study]}
clues:
  - {id: x_knife, item: knife, reveals: [f_knife_blood]}
solution_facts: [f_knife_blood, f_bob_in_study]
exploration: {draws_per_player: 1}
goals:
  - {id: g_alice_solve, owner: alice, condition: {eq: {var: vote, value: bob}}}
  - {id: g_bob_escape, owner: bob, condition: {not: {eq: {var: vote, value: bob}}}}
choices:
  - {id: vote, owner: alice, values: [alice, bob]}
endings:
  - {id: end_caught, condition: {eq: {var: vote, value: bob}}}
  - {id: end_escaped, condition: {not: {eq: {var: vote, value: bob}}}}
```
