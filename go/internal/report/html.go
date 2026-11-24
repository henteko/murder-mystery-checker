// Package report は explain の結果を、原作と読み合わせるための HTML にする。
package report

import (
	"fmt"
	"hash/fnv"
	"html/template"
	"io"
	"strings"

	"github.com/henteko/murder-mystery-checker/internal/check"
)

type view struct {
	Title string
	check.Report
	Errors, Warnings int
	TimeLabels       []string
	Hue              map[string]template.CSS
}

// HTML は Report を1つの HTML ファイルとして書き出す(外部の読み込みなし)。
func HTML(w io.Writer, title string, r check.Report) error {
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
	return tmpl.Execute(w, v)
}

func hueOf(v view, label string) template.CSS {
	if h, ok := v.Hue[label]; ok {
		return h
	}
	f := fnv.New32a()
	_, _ = f.Write([]byte(label))
	return template.CSS(fmt.Sprintf("--h:%d", f.Sum32()%360))
}

var tmpl = template.Must(template.New("report").Funcs(template.FuncMap{
	"time":    check.FormatTime,
	"msg":     check.Message,
	"join":    func(xs []string) string { return strings.Join(xs, " / ") },
	"hue":     hueOf,
	"sevName": func(s check.Severity) string { return s.String() },
	"span":    func(s check.Span) int { return s.Till - s.From },
	"deref": func(p *string) string {
		if p == nil {
			return ""
		}
		return *p
	},
	"isErr": func(s check.Severity) bool { return s == check.Error },
}).Parse(page))

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
    {{range .Diags}}<tr><td><span class="pill {{sevName .Sev}}">{{sevName .Sev}}</span></td><td class="mono">{{.Code}}</td><td>{{msg .Code}}</td><td class="mono">{{deref .Event}}</td><td>{{join .Args}}{{if .Witness}}<br>例: {{range .Witness}}<code>{{.Var}}={{.Val.MarshalJSON | printf "%s"}}</code> {{end}}{{end}}</td></tr>
    {{end}}
  </table></div>
  {{else}}<p>検出結果はありません。</p>{{end}}
</section>

<section id="where">
  <h2>居場所</h2>
  <p class="note">時刻ごとに各キャラクターがどこにいるか。斜線は移動中(出発した時刻から到着の直前まで)。列の幅は時間の長さではなく区切りの数。</p>
  <div class="scroll"><table class="grid">
    <tr><th class="who">キャラクター</th>{{range .TimeLabels}}<th class="t">{{.}}</th>{{end}}</tr>
    {{$v := .}}{{range .Rows}}<tr><th class="who">{{.Character}}{{if .NPC}}<span class="npc">NPC</span>{{end}}</th>{{range .Spans}}<td colspan="{{span .}}" class="{{.Kind}}"{{if eq .Kind "loc"}} style="{{hue $v .Label}}"{{end}}>{{.Label}}</td>{{end}}</tr>
    {{end}}
  </table></div>
</section>

<section id="events">
  <h2>イベント(処理の順)</h2>
  <p class="note">同じ時刻のイベントは ID の順に処理する。移動元は、そのイベントを処理する直前の居場所。</p>
  <div class="scroll"><table>
    <tr><th>時刻</th><th>ID</th><th>内容</th><th>検出結果</th></tr>
    {{range .Events}}<tr{{if .Diags}} class="flag"{{end}}><td class="time">{{time .Time}}</td><td class="mono">{{.ID}}</td><td>{{.Text}}</td><td>{{range .Diags}}<span class="diag"><span class="pill {{sevName .Sev}}">{{.Code}}</span> {{msg .Code}}<br><small>{{join .Args}}</small></span>{{end}}</td></tr>
    {{end}}
  </table></div>
</section>

{{if .Items}}<section id="items">
  <h2>持ち物</h2>
  <div class="scroll"><table>
    <tr><th>アイテム</th><th>はじめ</th><th>変化</th><th>終了時</th></tr>
    {{range .Items}}<tr><td class="mono">{{.ID}}</td><td>{{.Initial}}</td><td>{{if .Changes}}<ul class="plain">{{range .Changes}}<li>{{time .Time}} <code>{{.EventID}}</code> → {{.Holder}}</li>{{end}}</ul>{{else}}(変化なし){{end}}</td><td>{{.Final}}</td></tr>
    {{end}}
  </table></div>
</section>{{end}}

<section id="knowledge">
  <h2>知識</h2>
  <p class="note">赤い枠は偽の知識、太字は真相に必要な知識。</p>
  <div class="scroll"><table>
    <tr><th>キャラクター</th><th>はじめから</th><th>知ったこと</th><th>終了時</th></tr>
    {{range .Knowledge}}<tr><td>{{.Character}}{{if .NPC}}<span class="npc">NPC</span>{{end}}</td>
      <td>{{range .Initial}}{{template "fact" .}}{{end}}</td>
      <td>{{if .Learned}}<ul class="plain">{{range .Learned}}<li>{{time .Time}} <code>{{.EventID}}</code> {{range .Facts}}{{template "fact" .}}{{end}}</li>{{end}}</ul>{{end}}</td>
      <td>{{range .Final}}{{template "fact" .}}{{end}}</td></tr>
    {{end}}
  </table></div>
</section>

{{if or .Handouts .Boards}}<section id="declarations">
  <h2>ハンドアウト・盤面と終了時の状態</h2>
  {{range .Handouts}}<h3>ハンドアウト: {{.Name}}</h3>{{template "decl" .Rows}}{{end}}
  {{range .Boards}}<h3>盤面: {{.Name}}</h3>{{template "decl" .Rows}}{{end}}
</section>{{end}}

{{if .Assertions}}<section id="assertions">
  <h2>真相の断言</h2>
  <div class="scroll"><table>
    <tr><th>ID</th><th>断言</th><th>判定器の解釈</th><th></th></tr>
    {{range .Assertions}}<tr><td class="mono">{{.ID}}</td><td>{{time .Time}} に {{.Character}} は {{.Location}} に{{if eq .Kind "present"}}いる{{else}}いない{{end}}</td><td>{{time .Time}} の {{.Character}}: {{if eq .Where "transit"}}移動中{{else if eq .Where "dead"}}死亡{{else}}{{.Where}}{{end}}</td><td>{{if .OK}}<span class="pill ok">一致</span>{{else}}<span class="pill error">矛盾</span>{{end}}</td></tr>
    {{end}}
  </table></div>
</section>{{end}}

{{if .Claims}}<section id="claims">
  <h2>証言の時刻</h2>
  <div class="scroll"><table>
    <tr><th>知識</th><th>対象のイベント</th><th>主張</th><th>実際</th><th>許容誤差</th><th></th></tr>
    {{range .Claims}}<tr><td class="mono">{{.Fact}}{{if not .Truth}} (偽){{end}}</td><td class="mono">{{.Event}}{{if eq .Point "arrive"}}(到着){{end}}</td><td class="time">{{time .Claimed}}</td><td class="time">{{if .Found}}{{time .Actual}}{{else}}(イベントがない){{end}}</td><td>{{.Tolerance}} 分</td><td>{{if not .Truth}}<span class="pill">検査対象外</span>{{else if not .Found}}{{else if .OK}}<span class="pill ok">範囲内</span>{{else}}<span class="pill error">ずれ</span>{{end}}</td></tr>
    {{end}}
  </table></div>
</section>{{end}}

<section id="endings">
  <h2>選び方とエンディング</h2>
  {{with .Endings}}{{if .Skipped}}<p>{{.Skipped}}</p>{{else}}
  <p class="note">制約(導出制約を含む)を満たす選び方 {{.Total}} 通り。エンディングがない選び方 {{.NoEnding}} 通り、2つ以上になる選び方 {{.Multiple}} 通り。{{if lt .Shown .Total}}先頭の {{.Shown}} 通りだけを表示している。{{end}}</p>
  <div class="scroll"><table>
    <tr><th>エンディング</th><th>選び方の数</th></tr>
    {{range .Counts}}<tr><td class="mono">{{.ID}}</td><td>{{.Count}}</td></tr>{{end}}
  </table></div>
  <h3>選び方ごとの結果</h3>
  <div class="scroll"><table>
    <tr>{{range .Vars}}<th class="mono">{{.}}</th>{{end}}<th>エンディング</th></tr>
    {{range .Rows}}<tr{{if ne (len .Endings) 1}} class="flag"{{end}}>{{range .Values}}<td>{{.}}</td>{{end}}<td class="mono">{{if .Endings}}{{join .Endings}}{{else}}(なし){{end}}</td></tr>
    {{end}}
  </table></div>
  {{end}}{{end}}
</section>
</main>
</body>
</html>
{{define "fact"}}<span class="fact{{if .False}} false{{end}}{{if .Solution}} solution{{end}}">{{.ID}}</span>{{end}}
{{define "decl"}}<div class="scroll"><table>
  <tr><th>項目</th><th>書かれていること</th><th>終了時の状態</th><th></th></tr>
  {{range .}}<tr><td>{{.Aspect}}</td><td class="mono">{{.Declared}}</td><td>{{.Actual}}</td><td>{{if eq .Status "ok"}}<span class="pill ok">一致</span>{{else if eq .Status "ng"}}<span class="pill error">食い違い</span>{{else}}<span class="pill warning">記載漏れ</span>{{end}}</td></tr>
  {{end}}
</table></div>{{end}}
`
