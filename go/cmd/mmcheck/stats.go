package main

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"strings"

	"github.com/henteko/murder-mystery-checker/internal/check"
	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// stringList は繰り返し指定できるフラグ(--require)。
type stringList []string

func (l *stringList) String() string     { return strings.Join(*l, ", ") }
func (l *stringList) Set(v string) error { *l = append(*l, v); return nil }

// statsOutput は --format json の出力: 指標と、--require の結果。
type statsOutput struct {
	*check.Stats
	Requirements []check.Requirement `json:"requirements,omitempty"`
}

// statsAgentOutput は --format agent の出力。
type statsAgentOutput struct {
	OK                bool                `json:"ok"`
	SpecVersion       string              `json:"spec_version"`
	ComplexityVersion int                 `json:"complexity_version"`
	Error             string              `json:"error,omitempty"`
	Failed            int                 `json:"failed"`
	Requirements      []check.Requirement `json:"requirements"`
	Stats             *check.Stats        `json:"stats,omitempty"`
}

// runStats の終了コード: 0 = 条件をすべて満たす / 1 = 満たさない条件がある、または R 群の違反 /
// 2 = 入力エラー、条件式の誤り。
func runStats(path, format string, requires []string, stdin io.Reader, stdout, stderr io.Writer) int {
	agent := func(o statsAgentOutput, code int) int {
		o.SpecVersion, o.ComplexityVersion = check.SpecVersion, check.ComplexityVersion
		if o.Requirements == nil {
			o.Requirements = []check.Requirement{}
		}
		b, _ := json.MarshalIndent(o, "", "  ")
		fmt.Fprintln(stdout, string(b))
		return code
	}
	fail := func(msg string, code int) int {
		if format == "agent" {
			agent(statsAgentOutput{Error: msg}, code)
		}
		fmt.Fprintln(stderr, msg)
		return code
	}
	for _, r := range requires {
		if err := check.ParseRequirement(r); err != nil {
			return fail(err.Error(), 2)
		}
	}
	src, err := readInput(path, stdin)
	if err != nil {
		return fail(err.Error(), 2)
	}
	s, err := load(path, src)
	if err != nil {
		var ie *m.InputError
		if errors.As(err, &ie) {
			return fail(ie.Error(), 2)
		}
		return fail(err.Error(), 2)
	}
	st, err := check.ComputeStats(s)
	if err != nil {
		return fail(err.Error(), 1)
	}
	var reqs []check.Requirement
	failed := 0
	for _, e := range requires {
		r, _ := check.EvalRequirement(st, e)
		if !r.OK {
			failed++
		}
		reqs = append(reqs, r)
	}
	code := 0
	if failed > 0 {
		code = 1
	}
	switch format {
	case "agent":
		return agent(statsAgentOutput{OK: failed == 0, Failed: failed, Requirements: reqs, Stats: st}, code)
	case "json":
		b, _ := json.MarshalIndent(statsOutput{Stats: st, Requirements: reqs}, "", "  ")
		fmt.Fprintln(stdout, string(b))
	default:
		printStats(stdout, st)
		printRequirements(stdout, reqs)
	}
	return code
}

func printRequirements(w io.Writer, reqs []check.Requirement) {
	if len(reqs) == 0 {
		return
	}
	failed := 0
	fmt.Fprintln(w, "\n■ 条件")
	for _, r := range reqs {
		mark := "ok  "
		if !r.OK {
			mark = "NG  "
			failed++
		}
		v := "—"
		if r.Value != nil {
			v = fmt.Sprintf("%g", *r.Value)
		}
		fmt.Fprintf(w, "  %s%-40s 値 %s\n", mark, r.Expr, v)
		if !r.OK && r.Value == nil && r.Message != "" {
			fmt.Fprintf(w, "      %s\n", r.Message)
		}
	}
	fmt.Fprintf(w, "  %d / %d 件を満たす\n", len(reqs)-failed, len(reqs))
}

func printPadding(w io.Writer, p check.PaddingStats) {
	fmt.Fprintln(w, "\n■ 水増しの候補(複雑度には数えない)")
	fmt.Fprintf(w, "  使われていない場所: %s\n", orNone(p.UnusedLocations))
	fmt.Fprintf(w, "  何もしない往復の移動: %s\n", orNone(p.IdleMoves))
	fmt.Fprintf(w, "  誰も手に入れられず参照もされない知識: %s\n", orNone(p.UnusedFacts))
	fmt.Fprintf(w, "  何も明かさない手がかり: %s\n", orNone(p.EmptyClues))
	fmt.Fprintf(w, "  結末にもゴールにも関係しない選択: %s\n", orNone(p.IrrelevantChoices))
}

func orNone(xs []string) string {
	if len(xs) == 0 {
		return "なし"
	}
	return strings.Join(xs, ", ")
}

var axisNames = map[string]string{"size": "規模", "timeline": "タイムライン", "knowledge": "情報の流れ",
	"exploration": "探索", "branching": "分岐"}

// pad は表示幅(全角を2とする)が n になるまで空白を足す。
func pad(s string, n int) string {
	w := 0
	for _, r := range s {
		if r < 0x80 {
			w++
		} else {
			w += 2
		}
	}
	return s + strings.Repeat(" ", max(0, n-w))
}

func printComplexity(w io.Writer, c check.Complexity) {
	fmt.Fprintf(w, "■ 複雑度 %.1f / 100(式 v%d)\n", c.Score, c.Version)
	for _, a := range c.Axes {
		if !a.Applicable {
			fmt.Fprintf(w, "  %s   —   (対象外)\n", pad(axisNames[a.Name], 12))
			continue
		}
		var parts []string
		for _, t := range a.Terms {
			parts = append(parts, fmt.Sprintf("%s=%g→%.2f", t.Name, t.Value, t.Score))
		}
		fmt.Fprintf(w, "  %s %5.1f  %s\n", pad(axisNames[a.Name], 12), a.Score*100, strings.Join(parts, " "))
	}
	fmt.Fprintln(w)
}

func printStats(w io.Writer, st *check.Stats) {
	printComplexity(w, st.Complexity)
	fmt.Fprintf(w, "■ 検査(mmcheck check)error %d / warning %d\n\n", st.Check.Errors, st.Check.Warnings)
	z := st.Size
	fmt.Fprintln(w, "■ 規模")
	fmt.Fprintf(w, "  プレイヤー %d / NPC %d / 場所 %d / アイテム %d / イベント %d\n",
		z.Players, z.NPCs, z.Locations, z.Items, z.Events)
	fmt.Fprintf(w, "  知識 %d(偽 %d)/ 証言 %d(偽 %d)/ 手がかり %d / 断言 %d\n",
		z.Facts, z.FalseFacts, z.Claims, z.FalseClaims, z.Clues, z.Assertions)
	fmt.Fprintf(w, "  ゴール %d / 選択 %d / エンディング %d\n", z.Goals, z.Choices, z.Endings)

	t := st.Timeline
	fmt.Fprintln(w, "\n■ タイムライン")
	fmt.Fprintf(w, "  期間 %d 分 / 移動 %d 回 / 1人1時間あたりのイベント %.2f / 非公共の場所での遭遇 %d\n",
		t.DurationMinutes, t.Moves, t.EventsPerPlayerHour, t.Encounters)
	for _, c := range t.PerCharacter {
		npc := ""
		if c.NPC {
			npc = " (NPC)"
		}
		fmt.Fprintf(w, "  %-20s イベント %3d  移動 %3d  場所 %2d%s\n", c.ID, c.Events, c.Moves, c.Locations, npc)
	}

	k := st.Knowledge
	fmt.Fprintln(w, "\n■ 情報の流れ")
	fmt.Fprintf(w, "  伝聞の最長の段数 %d / 真相の知識の入手経路の最小 %d / 秘密(conceals)%d\n",
		k.MaxRelayDepth, k.MinSolutionSources, k.Secrets)
	for _, s := range k.Solution {
		depth := "—"
		if s.RelayDepth >= 0 {
			depth = fmt.Sprint(s.RelayDepth)
		}
		fmt.Fprintf(w, "  真相 %-24s 経路 %d(知っている: %s / 手がかり: %s)伝聞 %s\n",
			s.Fact, s.Sources, orNone(s.HeldBy), orNone(s.Clues), depth)
	}
	for _, l := range k.Lies {
		fmt.Fprintf(w, "  偽   %-24s 信じている: %s / 否定できる知識 %d\n", l.Fact, orNone(l.BelievedBy), l.Refuters)
	}

	if e := st.Exploration; e != nil {
		fmt.Fprintln(w, "\n■ 探索")
		draws, slack, cover := "—", "—", "—"
		if e.Draws != nil {
			draws = fmt.Sprint(*e.Draws)
		}
		if e.Slack != nil {
			slack = fmt.Sprint(*e.Slack)
		}
		if e.RandomCover != nil {
			cover = fmt.Sprintf("%.1f%%", *e.RandomCover*100)
		}
		minc := fmt.Sprint(e.MinCards)
		if e.MinCards < 0 {
			minc = "揃わない"
		}
		fmt.Fprintf(w, "  カード %d / 引ける枚数 %s / 手がかりからしか得られない真相 %d / 必要な最小枚数 %s / 余裕 %s\n",
			e.Cards, draws, e.ClueOnly, minc, slack)
		fmt.Fprintf(w, "  無作為に引いて真相のカードが揃う確率 %s(回ごとの制限は考えない)\n", cover)
		if len(e.Rounds) > 1 {
			for i, r := range e.Rounds {
				truth := "—"
				if r.Truth != nil {
					truth = fmt.Sprintf("%d / %d", *r.Truth, e.ClueOnly)
				}
				fmt.Fprintf(w, "  %d 回目: 引ける枚数 %d / 引けるカード %d / この回までに明かせる真相 %s\n",
					i+1, r.Draws, r.Cards, truth)
			}
		}
	}

	b := st.Branching
	fmt.Fprintln(w, "\n■ 分岐")
	fmt.Fprintf(w, "  変数 %d / 割り当て %s", b.Variables, b.Assignments)
	if !b.Enumerated {
		fmt.Fprintln(w, "(上限を超えるため数え上げない)")
		printPadding(w, st.Padding)
		return
	}
	fmt.Fprintf(w, " / パターン %d / 結末のエントロピー %.2f bit\n", b.Patterns, b.EntropyBits)
	for _, o := range b.Outcomes {
		name := o.Ending
		if name == "" {
			name = "(該当なし)"
		}
		fmt.Fprintf(w, "  結末 %-24s %6d パターン  %5.1f%%\n", name, o.Patterns, o.Share*100)
	}
	for _, p := range b.Players {
		fmt.Fprintf(w, "  %-20s 選択 %d  結末を左右する割合 %5.1f%%\n", p.ID, p.Choices, p.Pivotal*100)
	}
	if len(b.GoalConflicts) == 0 {
		fmt.Fprintln(w, "  対立するゴール: なし")
	}
	for _, c := range b.GoalConflicts {
		fmt.Fprintf(w, "  対立するゴール: %s × %s\n", c[0], c[1])
	}
	printPadding(w, st.Padding)
}
