# 作者向け YAML(mmcheck)

Go CLI は、作者が書きやすい YAML を受け付けます。YAML は §1 の正規化 JSON に変換してから検査します(`mmcheck convert` で変換結果を見られます)。変換は Go 側だけの機能で、Lean との差分テストの対象外です(変換の単体テストで確かめます)。

YAML のキーは、基本的に正規化 JSON(docs/spec.md §1)と同じです。そのうえで、次の書き方ができます。

## 1. 時刻を「時:分」で書く

時刻のフィールドには、分の整数のほかに文字列を書けます。

| 書き方 | 値(分) |
|---|---|
| `"21:00"` | 1260 |
| `"25:30"` | 1530(24 時以降も書ける) |
| `"2d 09:00"` | 2 × 1440 + 540 = 3420(0 日目から数える) |
| `1260` | 1260 |

時刻のフィールド: `start_time`、`end_time`、イベントの `at` と `arrive`、知識の `claimed_at`、断言の `at`、下記のタイムライン・時系列表の `at` と `arrive`。
`minutes`、`internal_minutes`、`tolerance`、`claim_tolerance` は長さ(分)なので整数で書きます。

「時:分」の文字列はかならず引用符で囲んでください(YAML の版によっては、引用符のない `21:00` を数として読むことがあるため)。

## 2. キャラクターの欄にまとめて書く

```yaml
characters:
  - id: alice
    location: hall          # 初期配置 → placements
    knows: [f_secret]       # 最初から知っていること → initial_knowledge
    timeline:               # このキャラクターのイベント → events
      - {at: "21:10", kind: move, to: study, arrive: "21:15"}
      - {at: "21:20", kind: tell, to: bob, facts: [f_secret]}
      - {id: alice_kills, at: "21:30", kind: use, item: knife}
```

- `timeline` の各イベントは、種類に応じて本人が自動で入ります: move / observe / pickup / drop / use / consume / learn / die は `character`、transfer / tell は `from`、scene は `participants`(省略したとき `[本人]`)。
- `id` を省略したイベントは `<キャラクター>#<番号>` になります(番号はその `timeline` の中での 1 からの順番。例: `alice#1`)。
- トップレベルの `events` と併用できます。

## 3. ハンドアウトの時系列表を書く

ハンドアウトに書かれた時系列表の各行は、時刻の主張を持つ知識(証言)になります。

```yaml
handouts:
  - character: tom
    knows: [f_saw_body]
    timeline:
      - {at: "18:10", event: tom_hears_scream, text: 悲鳴を聞いた}
      - {at: "17:50", event: konomi_to_roof, point: arrive, fact: f_tom_saw_konomi, truth: false,
         contradicted_by: [f_konomi_alone]}
```

各行は次の知識に変換されます。

- `id`: `fact` があればそれ、なければ `<キャラクター>@<番号>`(番号は1から。例: `tom@1`)
- `about`: `{event: <event>, point: <point>}`(`point` は省略時 `at`)
- `claimed_at`: 行の `at`
- `truth`、`tolerance`、`contradicted_by`: 行に書いたもの(`truth` の省略時は true)

さらに、この知識をそのキャラクターの最初の知識(`initial_knowledge`)に加えます。ハンドアウトに `knows` があれば、そこにも加えます(記載漏れの警告 H005 を避けるため)。

## 4. 表示名と説明(name / note)

キャラクター・場所・アイテム・知識・イベントなどには、表示用に `name`(短い名前)と `note`(説明。`text` も同じ扱い)を書けます。

```yaml
characters:
  - {id: clerk, name: 店員}
locations:
  - {id: backroom, name: バックルーム, note: 店の奥の倉庫}
facts:
  - {id: f_opener_blood, text: ペーパーナイフに血}
```

判定には使いません。`name`・`note`・`text` と `_` で始まるキーはどこにでも書けますが、それ以外の知らないキーは書式の誤りになります(0.8.0 から。書き間違いが検査されないまま通らないように)。`mmcheck explain` の読み合わせの表示で、ID の代わりに使います(docs/explain.md)。

## 5. その他

- 正規化 JSON にないキーは書けません(`name`・`note`・`text` と `_` で始まるキーを除く)。ハンドアウトの時系列表の行に書けるのは、§3 のキーと `text` だけです。
- 探索フェイズ(`exploration`)は正規化 JSON と同じ形で書きます。調査と議論を何回か繰り返すなら `rounds` で回に分けます(spec.md §1.10、`mmcheck guide`)。
- 同じマッピングに同じキーを2回書くと入力エラーです。
- `.json` のファイルは変換せず、そのまま正規化 JSON として読みます。

## 例

`examples/yaml-demo/scenario.yaml` を参照してください。
