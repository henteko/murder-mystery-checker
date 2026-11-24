// Package report は explain の結果を、原作と読み合わせるための HTML にする。
package report

import (
	"fmt"
	"hash/fnv"
	"html/template"
	"io"
	"sort"
	"strconv"
	"strings"

	"github.com/henteko/murder-mystery-checker/internal/check"
)

type view struct {
	Title string
	check.Report
	Errors, Warnings int
	TimeLabels       []string
	Hue              map[string]template.CSS
	Glossary         []glossaryGroup
}

type glossaryRow struct{ ID, Name, Note string }

type glossaryGroup struct {
	Title string
	Rows  []glossaryRow
}

// HTML は Report を1つの HTML ファイルとして書き出す(外部の読み込みなし)。
// labels は表示用の名前と説明(入力の name / note)。判定には使わない。
func HTML(w io.Writer, title string, r check.Report, labels check.Labels) error {
	v := view{Title: title, Report: r, Hue: map[string]template.CSS{}}
	for _, d := range r.Diags {
		if d.Sev == check.Error {
			v.Errors++
		} else {
			v.Warnings++
		}
	}
	for i := 0; i+1 < len(r.Times); i++ {
		v.TimeLabels = append(v.TimeLabels, check.FormatTime(r.Times[i]))
	}
	for i, l := range r.Locations {
		v.Hue[l] = template.CSS(fmt.Sprintf("--h:%d", (i*67+20)%360))
	}
	for _, g := range []struct{ kind, title string }{
		{"character", "キャラクター"}, {"location", "場所"}, {"item", "アイテム"}, {"fact", "知識"},
		{"goal", "ゴール"}, {"choice", "選択"}, {"ending", "エンディング"},
	} {
		var rows []glossaryRow
		for id, l := range labels[g.kind] {
			rows = append(rows, glossaryRow{id, l.Name, l.Note})
		}
		sort.Slice(rows, func(i, j int) bool { return rows[i].ID < rows[j].ID })
		if len(rows) > 0 {
			v.Glossary = append(v.Glossary, glossaryGroup{g.title, rows})
		}
	}
	t, err := template.New("report").Funcs(funcs(labels)).Parse(page)
	if err != nil {
		return err
	}
	return t.Execute(w, v)
}

func hueOf(v view, label string) template.CSS {
	if h, ok := v.Hue[label]; ok {
		return h
	}
	f := fnv.New32a()
	_, _ = f.Write([]byte(label))
	return template.CSS(fmt.Sprintf("--h:%d", f.Sum32()%360))
}

// namer は ID を表示名にする(名前がなければ ID のまま)。
type namer struct{ l check.Labels }

func (n namer) name(kind, id string) string {
	if l, ok := n.l[kind][id]; ok && l.Name != "" {
		return l.Name
	}
	return id
}

func (n namer) note(kind, id string) string { return n.l[kind][id].Note }

// fact は知識を、名前 → 説明 → ID の順で表示する。
func (n namer) fact(id string) string {
	l := n.l["fact"][id]
	switch {
	case l.Name != "":
		return l.Name
	case l.Note != "":
		return l.Note
	}
	return id
}

func (n namer) names(kind string, ids []string) string {
	if len(ids) == 0 {
		return "(なし)"
	}
	out := make([]string, len(ids))
	for i, id := range ids {
		out[i] = n.name(kind, id)
	}
	return strings.Join(out, "、")
}

func (n namer) facts(ids []string) string {
	out := make([]string, len(ids))
	for i, id := range ids {
		out[i] = "「" + n.fact(id) + "」"
	}
	return strings.Join(out, "")
}

func (n namer) where(raw string) string {
	switch raw {
	case "transit":
		return "移動中"
	case "dead":
		return "死亡"
	case "":
		return "(配置なし)"
	}
	return n.name("location", raw)
}

func (n namer) holder(h check.HolderView) string {
	switch h.Kind {
	case "char":
		return n.name("character", h.ID) + " が持っている"
	case "place":
		return n.name("location", h.ID) + " に置かれている"
	}
	return "使い切られた"
}

// sentence はイベントを、表示名を使った日本語の1文にする。
func (n namer) sentence(e check.EventLine) string {
	c := func(id string) string { return n.name("character", id) }
	l := func(id string) string { return n.name("location", id) }
	it := func(id string) string { return n.name("item", id) }
	var t string
	switch e.Kind {
	case "move":
		t = fmt.Sprintf("%s が %s から %s へ移動(%s 着", c(e.Character), n.where(e.From), l(e.To), check.FormatTime(e.Arrive))
		switch e.Mode {
		case "walk":
		case "fall":
			t += "、落下"
		case "carried":
			t += "、運ばれる"
		default:
			t += "、" + e.Mode
		}
		if e.Fatal {
			t += "、到着時に死亡"
		}
		t += ")"
	case "scene":
		t = fmt.Sprintf("%s で %s が居合わせる", l(e.Location), n.names("character", e.Participants))
		if len(e.Reveals) > 0 {
			t += "。全員が" + n.facts(e.Reveals) + "を知る"
		}
	case "observe":
		if e.TargetLocation == e.Location {
			t = fmt.Sprintf("%s が %s で", c(e.Character), l(e.Location))
		} else {
			t = fmt.Sprintf("%s が %s から %s を", c(e.Character), l(e.Location), l(e.TargetLocation))
		}
		if len(e.Targets) > 0 {
			t += " " + n.names("character", e.Targets) + " を"
		}
		t += "見て、" + n.facts(e.Facts) + "を知る"
	case "transfer":
		t = fmt.Sprintf("%s が %s に %s を渡す", c(e.Src), c(e.Dst), it(e.Item))
	case "pickup":
		t = fmt.Sprintf("%s が %s を拾う", c(e.Character), it(e.Item))
	case "drop":
		t = fmt.Sprintf("%s が %s を置く", c(e.Character), it(e.Item))
	case "use":
		t = fmt.Sprintf("%s が %s を使う", c(e.Character), it(e.Item))
	case "consume":
		t = fmt.Sprintf("%s が %s を使い切る", c(e.Character), it(e.Item))
	case "learn":
		t = fmt.Sprintf("%s が%sを知る", c(e.Character), n.facts(e.Facts))
	case "tell":
		t = fmt.Sprintf("%s が %s に%sを伝える", c(e.Src), c(e.Dst), n.facts(e.Facts))
	case "die":
		t = c(e.Character) + " が死亡"
	}
	if len(e.Requires) > 0 {
		t += "(必要な知識: " + n.facts(e.Requires) + ")"
	}
	return t
}

// argKinds は規則ごとの args が何を指すか(docs/spec.md §4 の表の args 列)。
// c: キャラクター, l: 場所, i: アイテム, f: 知識, e: イベント, t: 時刻(分), h: 保持者, w: 居場所(移動中・死亡を含む),
// n: エンディング, g: ゴール, v: 変数, x: そのまま
var argKinds = map[string]string{
	"T002": "cll", "T003": "cllx", "T004": "cl", "T005": "ce", "T006": "ce", "T007": "clw", "T008": "ccll",
	"T009": "ccltt", "T010": "ce", "T011": "cll", "T012": "ce",
	"I001": "cih", "I002": "ci", "I003": "cih", "I004": "ie",
	"K001": "cf", "K002": "cf", "K003": "f", "K004": "xi", "K005": "xilh", "K006": "f", "K007": "f", "K008": "ftt",
	"H001": "cll", "H002": "cih", "H003": "ci", "H004": "cf", "H005": "cf", "H006": "lih", "H007": "li",
	"A001": "xcxw", "G002": "nn", "G003": "n", "G004": "g", "G006": "v", "G008": "c", "G009": "vx",
}

// args は検出結果の詳細を、表示名を使って読める形にする。R 群はそのまま。
func (n namer) args(d check.Diag) string {
	kinds := argKinds[d.Code]
	out := make([]string, len(d.Args))
	for i, a := range d.Args {
		k := byte('x')
		if i < len(kinds) {
			k = kinds[i]
		}
		switch k {
		case 'c':
			out[i] = n.name("character", a)
		case 'l':
			out[i] = n.name("location", a)
		case 'w':
			out[i] = n.where(a)
		case 'i':
			out[i] = n.name("item", a)
		case 'f':
			out[i] = "「" + n.fact(a) + "」"
		case 'n':
			out[i] = n.name("ending", a)
		case 'g':
			out[i] = n.name("goal", a)
		case 'v':
			if l, ok := n.l["goal"][a]; ok && l.Name != "" {
				out[i] = l.Name
			} else {
				out[i] = n.name("choice", a)
			}
		case 't':
			if t, err := strconv.Atoi(a); err == nil {
				out[i] = check.FormatTime(t)
			} else {
				out[i] = a
			}
		case 'h':
			switch {
			case strings.HasPrefix(a, "character:"):
				out[i] = n.holder(check.HolderView{Kind: "char", ID: strings.TrimPrefix(a, "character:")})
			case strings.HasPrefix(a, "location:"):
				out[i] = n.holder(check.HolderView{Kind: "place", ID: strings.TrimPrefix(a, "location:")})
			default:
				out[i] = n.holder(check.HolderView{Kind: "consumed"})
			}
		default:
			out[i] = a
		}
	}
	return strings.Join(out, " / ")
}

func funcs(labels check.Labels) template.FuncMap {
	n := namer{labels}
	return template.FuncMap{
		"time":     check.FormatTime,
		"msg":      check.Message,
		"join":     func(xs []string) string { return strings.Join(xs, " / ") },
		"hue":      hueOf,
		"sevName":  func(s check.Severity) string { return s.String() },
		"span":     func(s check.Span) int { return s.Till - s.From },
		"name":     n.name,
		"note":     n.note,
		"fact":     n.fact,
		"where":    n.where,
		"holder":   n.holder,
		"sentence": n.sentence,
		"args":     n.args,
		"deref": func(p *string) string {
			if p == nil {
				return ""
			}
			return *p
		},
	}
}

const page = `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>読み合わせ: {{.Title}}</title>
<style>
:root {
  --bg: #f7f7f5; --surface: #ffffff; --fg: #1f2328; --muted: #5d6470; --line: #d9dce1;
  --err: #b42318; --err-bg: #fdecea; --warn: #9a6700; --warn-bg: #fff4d6; --ok: #1a7f37; --ok-bg: #e6f4ea;
  --l: 90%; --s: 55%; --transit: #e8e9ec; --dead: #3a3d44; --dead-fg: #f2f2f2;
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #15171b; --surface: #1d2026; --fg: #e6e8eb; --muted: #9aa1ab; --line: #343842;
    --err: #ff8d80; --err-bg: #3b1d1b; --warn: #e3b341; --warn-bg: #3a2f12; --ok: #6fd391; --ok-bg: #173323;
    --l: 28%; --s: 35%; --transit: #2a2d34; --dead: #0b0c0e; --dead-fg: #c9ccd1;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--fg);
  font: 15px/1.7 "Hiragino Sans", "Noto Sans JP", "Yu Gothic", system-ui, sans-serif; }
main { max-width: 1100px; margin: 0 auto; padding: 32px 16px 80px; display: flex; flex-direction: column; gap: 40px; }
h1 { font-size: 26px; margin: 0; }
h2 { font-size: 19px; margin: 0 0 4px; padding-bottom: 6px; border-bottom: 2px solid var(--fg); }
h3 { font-size: 16px; margin: 18px 0 6px; }
p.note { color: var(--muted); margin: 4px 0 12px; font-size: 14px; }
section { display: flex; flex-direction: column; }
.summary { display: flex; gap: 16px; flex-wrap: wrap; color: var(--muted); }
.pill { display: inline-block; padding: 0 8px; border-radius: 999px; font-size: 13px; font-weight: 600; white-space: nowrap; }
.pill.error { background: var(--err-bg); color: var(--err); }
.pill.warning { background: var(--warn-bg); color: var(--warn); }
.pill.ok { background: var(--ok-bg); color: var(--ok); }
.banner { background: var(--err-bg); color: var(--err); padding: 10px 14px; border-radius: 6px; }
.scroll { overflow-x: auto; }
table { border-collapse: collapse; width: 100%; background: var(--surface); font-size: 14px; }
th, td { border: 1px solid var(--line); padding: 5px 8px; text-align: left; vertical-align: top; }
th { color: var(--muted); font-weight: 500; background: var(--bg); }
td.mono, code { font-family: ui-monospace, "SF Mono", Menlo, monospace; font-size: 13px; }
td.time { white-space: nowrap; font-variant-numeric: tabular-nums; }
table.grid { width: auto; table-layout: fixed; }
table.grid th.t { font-size: 11px; padding: 2px 4px; white-space: nowrap; writing-mode: vertical-rl; height: 52px; }
table.grid th.who { position: sticky; left: 0; z-index: 1; white-space: nowrap; }
table.grid td { padding: 4px 6px; font-size: 13px; white-space: nowrap; min-width: 40px; }
td.loc { background: hsl(var(--h) var(--s) var(--l)); }
td.transit { background: repeating-linear-gradient(45deg, var(--transit), var(--transit) 5px, transparent 5px, transparent 10px); color: var(--muted); }
td.dead { background: var(--dead); color: var(--dead-fg); }
.npc { color: var(--muted); font-size: 12px; margin-left: 4px; }
.fact { display: inline-block; border: 1px solid var(--line); border-radius: 4px; padding: 0 5px; margin: 1px 2px; font-size: 13px; font-family: ui-monospace, Menlo, monospace; }
.fact.false { border-color: var(--err); color: var(--err); }
.fact.solution { font-weight: 700; }
.diag { display: block; font-size: 13px; }
tr.flag td { background: var(--err-bg); }
ul.plain { margin: 0; padding-left: 1.2em; }
.memo { color: var(--muted); font-size: 13px; margin-top: 2px; }
.memo::before { content: "メモ: "; }
.eid { color: var(--muted); font-family: ui-monospace, Menlo, monospace; font-size: 11px; }
div.eid { margin-top: 2px; }
ul.facts { margin: 0; padding-left: 1.1em; font-size: 13px; }
ul.facts li.false { color: var(--err); }
ul.facts li.solution { font-weight: 700; }
.mark { display: inline-block; font-size: 11px; border: 1px solid var(--err); border-radius: 3px; padding: 0 3px; margin-right: 4px; }
.learned { margin-bottom: 6px; }
</style>
</head>
<body>
<main>
<header>
  <h1>読み合わせ: {{.Title}}</h1>
  <p class="note">判定器がこのシナリオをどう解釈しているかの一覧。原作と照らし合わせて、意図と違うところがないかを確かめるためのもの。居場所・持ち物・知識・エンディングは判定器と同じ計算で出している。</p>
  <div class="summary">
    <span>時間: {{time .StartTime}} 〜 {{time .EndTime}}</span>
    <span>イベント {{len .Events}} 件</span>
    <span><span class="pill error">error {{.Errors}}</span> <span class="pill warning">warning {{.Warnings}}</span></span>
  </div>
</header>

{{if .RGated}}<div class="banner">構造の誤り(R 群)があります。判定器はほかの検査をしていないので、以下の表は参考程度に見てください。</div>{{end}}

<section id="diagnostics">
  <h2>検出結果</h2>
  {{if .Diags}}
  <div class="scroll"><table>
    <tr><th>重大度</th><th>コード</th><th>内容</th><th>イベント</th><th>詳細</th></tr>
    {{range .Diags}}<tr><td><span class="pill {{sevName .Sev}}">{{sevName .Sev}}</span></td><td class="mono">{{.Code}}</td><td>{{msg .Code}}</td><td class="mono">{{deref .Event}}</td><td>{{args .}}{{if .Witness}}<br>例: {{range .Witness}}<code>{{.Var}}={{.Val.MarshalJSON | printf "%s"}}</code> {{end}}{{end}}</td></tr>
    {{end}}
  </table></div>
  {{else}}<p>検出結果はありません。</p>{{end}}
</section>

<section id="where">
  <h2>居場所</h2>
  <p class="note">時刻ごとに各キャラクターがどこにいるか。斜線は移動中(出発した時刻から到着の直前まで)。列の幅は時間の長さではなく区切りの数。</p>
  <div class="scroll"><table class="grid">
    <tr><th class="who">キャラクター</th>{{range .TimeLabels}}<th class="t">{{.}}</th>{{end}}</tr>
    {{$v := .}}{{range .Rows}}<tr><th class="who" title="{{note "character" .Character}}">{{name "character" .Character}}{{if .NPC}}<span class="npc">NPC</span>{{end}}</th>{{range .Spans}}<td colspan="{{span .}}" class="{{.Kind}}"{{if eq .Kind "loc"}} style="{{hue $v .Label}}" title="{{note "location" .Label}}"{{end}}>{{where .Label}}</td>{{end}}</tr>
    {{end}}
  </table></div>
</section>

<section id="events">
  <h2>イベント(処理の順)</h2>
  <p class="note">判定器の解釈(1行目)と、シナリオに書かれたメモ(2行目)を並べている。同じ時刻のイベントは ID の順に処理する。移動元は、そのイベントを処理する直前の居場所。</p>
  <div class="scroll"><table>
    <tr><th>時刻</th><th>内容</th><th>検出結果</th></tr>
    {{range .Events}}<tr{{if .Diags}} class="flag"{{end}}><td class="time">{{time .Time}}</td><td>{{sentence .}}{{with note "event" .ID}}<div class="memo">{{.}}</div>{{end}}<div class="eid">{{.ID}}</div></td><td>{{range .Diags}}<span class="diag"><span class="pill {{sevName .Sev}}">{{.Code}}</span> {{msg .Code}}<br><small>{{args .}}</small></span>{{end}}</td></tr>
    {{end}}
  </table></div>
</section>

{{if .Items}}<section id="items">
  <h2>持ち物</h2>
  <div class="scroll"><table>
    <tr><th>アイテム</th><th>はじめ</th><th>変化</th><th>終了時</th></tr>
    {{range .Items}}<tr><td>{{name "item" .ID}}{{with note "item" .ID}}<div class="memo">{{.}}</div>{{end}}<div class="eid">{{.ID}}</div></td><td>{{holder .Initial}}</td><td>{{if .Changes}}<ul class="plain">{{range .Changes}}<li>{{time .Time}} → {{holder .Holder}} <span class="eid">{{.EventID}}</span></li>{{end}}</ul>{{else}}(変化なし){{end}}</td><td>{{holder .Final}}</td></tr>
    {{end}}
  </table></div>
</section>{{end}}

<section id="knowledge">
  <h2>知識</h2>
  <p class="note">赤い印は偽の知識、太字は真相に必要な知識。</p>
  <div class="scroll"><table>
    <tr><th>キャラクター</th><th>はじめから</th><th>知ったこと</th><th>終了時</th></tr>
    {{range .Knowledge}}<tr><td>{{name "character" .Character}}{{if .NPC}}<span class="npc">NPC</span>{{end}}</td>
      <td><ul class="facts">{{range .Initial}}{{template "fact" .}}{{end}}</ul></td>
      <td>{{range .Learned}}<div class="learned">{{time .Time}} <span class="eid">{{.EventID}}</span><ul class="facts">{{range .Facts}}{{template "fact" .}}{{end}}</ul></div>{{end}}</td>
      <td><ul class="facts">{{range .Final}}{{template "fact" .}}{{end}}</ul></td></tr>
    {{end}}
  </table></div>
</section>

{{if or .Handouts .Boards}}<section id="declarations">
  <h2>ハンドアウト・盤面と終了時の状態</h2>
  {{range .Handouts}}<h3>ハンドアウト: {{name "character" .Name}}</h3>{{template "decl" .Rows}}{{end}}
  {{range .Boards}}<h3>盤面: {{name "location" .Name}}</h3>{{template "decl" .Rows}}{{end}}
</section>{{end}}

{{if .Assertions}}<section id="assertions">
  <h2>真相の断言</h2>
  <div class="scroll"><table>
    <tr><th>ID</th><th>断言</th><th>判定器の解釈</th><th></th></tr>
    {{range .Assertions}}<tr><td class="mono">{{.ID}}</td><td>{{time .Time}} に {{name "character" .Character}} は {{name "location" .Location}} に{{if eq .Kind "present"}}いる{{else}}いない{{end}}{{with note "assertion" .ID}}<div class="memo">{{.}}</div>{{end}}</td><td>{{time .Time}} の {{name "character" .Character}}: {{where .Where}}</td><td>{{if .OK}}<span class="pill ok">一致</span>{{else}}<span class="pill error">矛盾</span>{{end}}</td></tr>
    {{end}}
  </table></div>
</section>{{end}}

{{if .Claims}}<section id="claims">
  <h2>証言の時刻</h2>
  <div class="scroll"><table>
    <tr><th>知識</th><th>対象のイベント</th><th>主張</th><th>実際</th><th>許容誤差</th><th></th></tr>
    {{range .Claims}}<tr><td>{{fact .Fact}}{{if not .Truth}} (偽){{end}}<div class="eid">{{.Fact}}</div></td><td class="mono">{{.Event}}{{if eq .Point "arrive"}}(到着){{end}}</td><td class="time">{{time .Claimed}}</td><td class="time">{{if .Found}}{{time .Actual}}{{else}}(イベントがない){{end}}</td><td>{{.Tolerance}} 分</td><td>{{if not .Truth}}<span class="pill">検査対象外</span>{{else if not .Found}}{{else if .OK}}<span class="pill ok">範囲内</span>{{else}}<span class="pill error">ずれ</span>{{end}}</td></tr>
    {{end}}
  </table></div>
</section>{{end}}

<section id="endings">
  <h2>選び方とエンディング</h2>
  {{with .Endings}}{{if .Skipped}}<p>{{.Skipped}}</p>{{else}}
  <p class="note">制約(導出制約を含む)を満たす選び方 {{.Total}} 通り。エンディングがない選び方 {{.NoEnding}} 通り、2つ以上になる選び方 {{.Multiple}} 通り。{{if lt .Shown .Total}}先頭の {{.Shown}} 通りだけを表示している。{{end}}</p>
  <div class="scroll"><table>
    <tr><th>エンディング</th><th>選び方の数</th></tr>
    {{range .Counts}}<tr><td>{{name "ending" .ID}}{{with note "ending" .ID}}<div class="memo">{{.}}</div>{{end}}<div class="eid">{{.ID}}</div></td><td>{{.Count}}</td></tr>{{end}}
  </table></div>
  <h3>選び方ごとの結果</h3>
  <div class="scroll"><table>
    <tr>{{range .Vars}}<th class="mono" title="{{note "goal" .}}{{note "choice" .}}">{{.}}</th>{{end}}<th>エンディング</th></tr>
    {{range .Rows}}<tr{{if ne (len .Endings) 1}} class="flag"{{end}}>{{range .Values}}<td>{{.}}</td>{{end}}<td>{{if .Endings}}{{range $i, $e := .Endings}}{{if $i}} / {{end}}{{name "ending" $e}}{{end}}{{else}}(なし){{end}}</td></tr>
    {{end}}
  </table></div>
  {{end}}{{end}}
</section>

{{if .Glossary}}<section id="glossary">
  <h2>用語(ID と表示名・説明)</h2>
  <p class="note">シナリオの name / note(text)フィールドから。判定には使わない。</p>
  {{range .Glossary}}<h3>{{.Title}}</h3>
  <div class="scroll"><table>
    <tr><th>ID</th><th>表示名</th><th>説明</th></tr>
    {{range .Rows}}<tr><td class="mono">{{.ID}}</td><td>{{.Name}}</td><td>{{.Note}}</td></tr>{{end}}
  </table></div>{{end}}
</section>{{end}}
</main>
</body>
</html>
{{define "fact"}}<li class="{{if .False}}false{{end}}{{if .Solution}} solution{{end}}">{{if .False}}<span class="mark">偽</span>{{end}}{{fact .ID}} <span class="eid">{{.ID}}</span></li>{{end}}
{{define "decl"}}<div class="scroll"><table>
  <tr><th>項目</th><th>書かれていること</th><th>終了時の状態</th><th></th></tr>
  {{range .}}<tr><td>{{if eq .Aspect "location"}}居場所{{else if eq .Aspect "item"}}持ち物{{else}}知識{{end}}</td>
  <td>{{if not .Listed}}(書かれていない){{else if eq .Aspect "location"}}{{name "location" .Subject}}{{else if eq .Aspect "item"}}{{name "item" .Subject}}{{else}}{{fact .Subject}}{{end}}{{if .Listed}} <span class="eid">{{.Subject}}</span>{{end}}</td>
  <td>{{if eq .Aspect "location"}}{{where .ActualLoc}}{{else if eq .Aspect "item"}}{{name "item" .Subject}}: {{holder .Holder}}{{else}}{{fact .Subject}}: {{if .Known}}知っている{{else}}知らない{{end}}{{end}}</td>
  <td>{{if eq .Status "ok"}}<span class="pill ok">一致</span>{{else if eq .Status "ng"}}<span class="pill error">食い違い</span>{{else}}<span class="pill warning">記載漏れ</span>{{end}}</td></tr>
  {{end}}
</table></div>{{end}}
`
