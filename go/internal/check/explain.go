package check

import (
	"fmt"
	"math/big"
	"sort"
	"strings"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// explain: 判定器がシナリオをどう解釈しているかを、人が原作と読み合わせられる形にまとめる。
//
// 新しい判定はしない。居場所・保持者・知識・エンディングは、判定器と同じ関数
// (sortedEvents, initState, step, whereAt, domains, effectiveConstraints, eval)で計算する。
// 表示のために意味論を書き直さないことで、表示される解釈 = Lean と差分テストで一致している解釈になる。

// Report は explain の結果。
type Report struct {
	StartTime, EndTime int
	Diags              []Diag
	RGated             bool // R 群の違反がある(以下の表は参考)
	Times              []int
	Rows               []GridRow
	Locations          []string // 色分けの順
	Events             []EventLine
	Items              []ItemHistory
	Knowledge          []KnowledgeHistory
	Handouts           []DeclCheck
	Boards             []DeclCheck
	Assertions         []AssertionCheck
	Claims             []ClaimCheck
	Endings            EndingTable
	Goals              []GoalView
}

// GridRow は1人分の居場所の帯。
type GridRow struct {
	Character string
	NPC       bool
	Spans     []Span
}

// Span は Times[From] から Times[Till] までの同じ居場所。Kind は "loc" / "transit" / "dead"。
type Span struct {
	Label      string
	Kind       string
	From, Till int
}

// EventLine はイベント1件。ID のまま持ち、文章や表示名への置き換えは表示側でする。
// From は処理直前の居場所(move の移動元)。
type EventLine struct {
	Time                     int
	ID                       string
	Kind                     string
	Character, From, To      string
	Arrive                   int
	Mode                     string
	Fatal                    bool
	Location, TargetLocation string
	Participants, Targets    []string
	Reveals, Facts           []string
	Src, Dst, Item           string
	Requires                 []string
	Diags                    []Diag
}

// HolderView はアイテムの保持者。Kind は "char" / "place" / "consumed"。
type HolderView struct {
	Kind string
	ID   string
}

// HolderChange はアイテムの保持者の変化。
type HolderChange struct {
	Time    int
	EventID string
	Holder  HolderView
}

// ItemHistory はアイテム1つの保持者の推移。
type ItemHistory struct {
	ID      string
	Initial HolderView
	Changes []HolderChange
	Final   HolderView
}

// FactRef は知識の参照(真偽と、真相に必要か)。
type FactRef struct {
	ID       string
	False    bool
	Solution bool
}

// Learned はある時刻に知ったこと。
type Learned struct {
	Time    int
	EventID string
	Facts   []FactRef
}

// KnowledgeHistory はキャラクター1人の知識の推移。
type KnowledgeHistory struct {
	Character string
	NPC       bool
	Initial   []FactRef
	Learned   []Learned
	Final     []FactRef
}

// DeclRow は宣言1項目と終了状態の照合。Aspect は "location" / "item" / "fact"。
// Listed が false の行は「書かれていないが終了時にそうなっている」(記載漏れ)。
// Status は "ok" / "ng" / "missing"。
type DeclRow struct {
	Aspect    string
	Subject   string
	Listed    bool
	ActualLoc string
	Holder    HolderView
	Known     bool
	Status    string
}

// DeclCheck はハンドアウトまたは盤面1つの照合。
type DeclCheck struct {
	Name string
	Rows []DeclRow
}

// AssertionCheck は断言1件の照合。
type AssertionCheck struct {
	ID, Kind, Location, Character, Where string
	Time                                 int
	OK                                   bool
}

// ClaimCheck は証言1件の照合。
type ClaimCheck struct {
	Fact, Event, Point string
	Claimed, Actual    int
	Tolerance          int
	Truth, Found, OK   bool
}

// FormulaView は論理式。Kind は "const" / "var" / "eq" / "plurality" / "tie" / "not" / "and" / "or"。
type FormulaView struct {
	Kind  string
	Const bool
	Var   string
	Value string
	Votes []string
	Subs  []FormulaView
}

func formulaView(f m.Formula) FormulaView {
	v := FormulaView{Kind: [...]string{"const", "var", "eq", "plurality", "tie", "not", "and", "or"}[f.Kind],
		Const: f.Const, Var: f.Var, Value: f.Value, Votes: f.Votes}
	for _, g := range f.Subs {
		v.Subs = append(v.Subs, formulaView(g))
	}
	return v
}

// Knowledge は必要な知識と、それが入手可能(§2.5)か。
type Knowledge struct {
	Fact       FactRef
	Obtainable bool
}

// GoalView はゴール1つ。TrueIn は、ゴールが達成される選び方の数(Counted が false なら数えていない)。
type GoalView struct {
	ID, Owner  string
	Items      []string
	ItemsLost  []string // requires_items のうち、終了時に使い切られているもの
	Knowledge  []Knowledge
	Condition  *FormulaView
	Counted    bool
	TrueIn     int
	OfPatterns int
}

// EndingTable は選び方ごとのエンディング。
type EndingTable struct {
	Skipped  string // 表を作らなかった理由
	Vars     []string
	Rows     []EndingRow
	Total    int
	Shown    int
	Counts   []EndingCount
	NoEnding int
	Multiple int
	// GoalTrue はゴールごとの、達成される選び方の数
	GoalTrue map[string]int
}

// EndingRow は選び方1つ。
type EndingRow struct {
	Values  []string
	Endings []string
}

// EndingCount はエンディングごとのパターン数。
type EndingCount struct {
	ID    string
	Count int
}

const maxEndingRows = 256

// FormatTime は分を "HH:MM"(1日を超えれば "Nd HH:MM")にする。
func FormatTime(t int) string {
	d, r := t/1440, t%1440
	if d > 0 {
		return fmt.Sprintf("%dd %02d:%02d", d, r/60, r%60)
	}
	return fmt.Sprintf("%02d:%02d", r/60, r%60)
}

func holderView(h m.Holder) HolderView {
	switch h.Kind {
	case m.HolderChar:
		return HolderView{"char", h.ID}
	case m.HolderPlace:
		return HolderView{"place", h.ID}
	}
	return HolderView{Kind: "consumed"}
}

// Explain はシナリオの解釈をまとめる。
func Explain(s *m.Scenario) Report {
	r := Report{StartTime: s.StartTime, EndTime: s.EndTime, Diags: Check(s)}
	for _, d := range r.Diags {
		if strings.HasPrefix(d.Code, "R") {
			r.RGated = true
		}
	}
	solution := map[string]bool{}
	for _, f := range s.SolutionFacts {
		solution[f] = true
	}
	falseFact := map[string]bool{}
	for _, f := range s.Facts {
		if !f.Truth {
			falseFact[f.ID] = true
		}
	}
	ref := func(f string) FactRef { return FactRef{ID: f, False: falseFact[f], Solution: solution[f]} }
	byEvent := map[string][]Diag{}
	for _, d := range r.Diags {
		if d.Event != nil {
			byEvent[*d.Event] = append(byEvent[*d.Event], d)
		}
	}

	// イベントは判定器と同じループ(run)で処理し、処理の前後の状態から変化を記録する
	init := initState(s)
	itemIdx := map[string]int{}
	for _, it := range s.Items {
		if _, ok := itemIdx[it.ID]; !ok {
			itemIdx[it.ID] = len(r.Items)
			r.Items = append(r.Items, ItemHistory{ID: it.ID, Initial: holderView(init.Holder(it.ID))})
		}
	}
	know := map[string]*KnowledgeHistory{}
	var knowOrder []string
	for _, c := range s.Characters {
		if _, ok := know[c.ID]; ok {
			continue
		}
		k := &KnowledgeHistory{Character: c.ID, NPC: c.NPC}
		for _, f := range factIds(s) {
			if init.Knows(c.ID, f) {
				k.Initial = append(k.Initial, ref(f))
			}
		}
		know[c.ID] = k
		knowOrder = append(knowOrder, c.ID)
	}
	// 処理前に読んだもの(イベントごとに作り直す)
	var (
		who, facts []string
		before     map[m.Pair]bool
		item       string
		hasItem    bool
		oldHolder  m.Holder
	)
	recipients := func(k m.EventKind) ([]string, []string) {
		switch k.Kind {
		case m.Scene:
			return k.Participants, k.Reveals
		case m.Observe, m.Learn:
			return []string{k.Character}, k.Facts
		case m.Tell:
			return []string{k.Dst}, k.Facts
		}
		return nil, nil
	}
	final := run(s, func(st Step) {
		e, S := st.Ev, st.Pre
		k := e.Kind
		line := EventLine{Time: e.Time, ID: e.ID, Kind: kindName(k.Kind), Character: k.Character, To: k.To,
			Arrive: k.Arrive, Mode: k.Mode, Fatal: k.Fatal, Location: k.Location, TargetLocation: k.TargetLocation,
			Participants: k.Participants, Targets: k.Targets, Reveals: k.Reveals, Facts: k.Facts,
			Src: k.Src, Dst: k.Dst, Item: k.Item, Requires: e.Requires, Diags: byEvent[e.ID]}
		if k.Kind == m.Move {
			line.From = S.Pos(k.Character).Dest
		}
		r.Events = append(r.Events, line)
		who, facts = recipients(e.Kind)
		before = map[m.Pair]bool{}
		for _, c := range who {
			for _, f := range facts {
				before[m.Pair{Character: c, Fact: f}] = S.Knows(c, f)
			}
		}
		item, hasItem = itemOf(e.Kind)
		if hasItem {
			oldHolder = S.Holder(item)
		}
	}, func(st Step) {
		e, S := st.Ev, st.Pre // 処理後の状態
		if hasItem {
			if h := S.Holder(item); h != oldHolder {
				if i, ok := itemIdx[item]; ok {
					r.Items[i].Changes = append(r.Items[i].Changes, HolderChange{e.Time, e.ID, holderView(h)})
				}
			}
		}
		for _, c := range dedup(who) {
			var got []FactRef
			for _, f := range dedup(facts) {
				if !before[m.Pair{Character: c, Fact: f}] && S.Knows(c, f) {
					got = append(got, ref(f))
				}
			}
			if kh, ok := know[c]; ok && len(got) > 0 {
				kh.Learned = append(kh.Learned, Learned{e.Time, e.ID, got})
			}
		}
	})
	sorted := sortedEvents(s)
	for i := range r.Items {
		r.Items[i].Final = holderView(final.Holder(r.Items[i].ID))
	}
	for _, c := range knowOrder {
		kh := know[c]
		for _, f := range factIds(s) {
			if final.Knows(c, f) {
				kh.Final = append(kh.Final, ref(f))
			}
		}
		r.Knowledge = append(r.Knowledge, *kh)
	}

	w := &world{s: s, final: final, sorted: sorted}
	r.grid(w)
	r.declarations(w)
	for _, a := range s.Assertions {
		for _, c := range a.Characters {
			wh := w.whereAt(c, a.Time)
			ok := (a.Kind == m.Present && wh == a.Location) || (a.Kind == m.Absent && wh != a.Location)
			r.Assertions = append(r.Assertions, AssertionCheck{ID: a.ID, Kind: a.Kind.Render(), Location: a.Location,
				Character: c, Where: wh, Time: a.Time, OK: ok})
		}
	}
	for _, f := range s.Facts {
		if f.AboutEvent == nil || f.ClaimedAt == nil {
			continue
		}
		tol := s.ClaimTolerance
		if f.Tolerance != nil {
			tol = *f.Tolerance
		}
		c := ClaimCheck{Fact: f.ID, Event: *f.AboutEvent, Point: f.AboutPoint, Claimed: *f.ClaimedAt, Tolerance: tol, Truth: f.Truth}
		if e, ok := findEvent(s, *f.AboutEvent); ok {
			c.Found, c.Actual = true, actualTime(f, e)
			c.OK = absDiff(c.Claimed, c.Actual) <= tol
		}
		r.Claims = append(r.Claims, c)
	}
	r.Endings = endingTable(w)
	for _, g := range s.Goals {
		gv := GoalView{ID: g.ID, Owner: g.Owner, Items: g.RequiresItems}
		for _, i := range g.RequiresItems {
			if final.Holder(i).Kind == m.HolderConsumed {
				gv.ItemsLost = append(gv.ItemsLost, i)
			}
		}
		for _, f := range g.RequiresKnowledge {
			gv.Knowledge = append(gv.Knowledge, Knowledge{ref(f), w.obtainable(f)})
		}
		if g.Condition != nil {
			fv := formulaView(*g.Condition)
			gv.Condition = &fv
		}
		if r.Endings.Skipped == "" {
			gv.Counted, gv.TrueIn, gv.OfPatterns = true, r.Endings.GoalTrue[g.ID], r.Endings.Total
		}
		r.Goals = append(r.Goals, gv)
	}
	return r
}

func kindName(k m.Kind) string {
	return [...]string{"move", "scene", "observe", "transfer", "pickup", "drop", "use", "consume", "learn", "tell", "die"}[k]
}

// grid は居場所の表を作る。区切りの時刻の間は whereAt が一定なので、区切りごとに whereAt を読む。
func (r *Report) grid(w *world) {
	s := w.s
	set := map[int]bool{s.StartTime: true, s.EndTime: true}
	in := func(t int) bool { return s.StartTime <= t && t <= s.EndTime }
	for _, e := range w.sorted {
		if in(e.Time) {
			set[e.Time] = true
		}
		if e.Kind.Kind == m.Move && in(e.Kind.Arrive) {
			set[e.Kind.Arrive] = true
		}
	}
	for _, c := range s.Characters {
		if d, ok := w.deathTime(c.ID); ok && in(d) {
			set[d] = true
		}
	}
	for t := range set {
		r.Times = append(r.Times, t)
	}
	sort.Ints(r.Times)
	locIdx := map[string]bool{}
	for _, l := range s.Locations {
		if !locIdx[l.ID] {
			locIdx[l.ID] = true
			r.Locations = append(r.Locations, l.ID)
		}
	}
	seen := map[string]bool{}
	for _, c := range s.Characters {
		if seen[c.ID] {
			continue
		}
		seen[c.ID] = true
		row := GridRow{Character: c.ID, NPC: c.NPC}
		for i := 0; i+1 < len(r.Times); i++ {
			wh := w.whereAt(c.ID, r.Times[i])
			kind, label := "loc", wh
			if wh == "transit" || wh == "dead" {
				kind = wh
			}
			if n := len(row.Spans); n > 0 && row.Spans[n-1].Label == label && row.Spans[n-1].Kind == kind {
				row.Spans[n-1].Till = i + 1
				continue
			}
			row.Spans = append(row.Spans, Span{Label: label, Kind: kind, From: i, Till: i + 1})
		}
		r.Rows = append(r.Rows, row)
	}
}

func (r *Report) declarations(w *world) {
	s, E := w.s, w.final
	status := func(ok bool) string {
		if ok {
			return "ok"
		}
		return "ng"
	}
	for _, h := range s.Handouts {
		c := h.Character
		dc := DeclCheck{Name: c}
		if h.Location != nil {
			dc.Rows = append(dc.Rows, DeclRow{Aspect: "location", Subject: *h.Location, Listed: true,
				ActualLoc: E.Pos(c).Dest, Status: status(E.Pos(c).Dest == *h.Location)})
		}
		mine := m.Holder{Kind: m.HolderChar, ID: c}
		if h.Items != nil {
			for _, i := range *h.Items {
				dc.Rows = append(dc.Rows, DeclRow{Aspect: "item", Subject: i, Listed: true,
					Holder: holderView(E.Holder(i)), Status: status(E.Holder(i) == mine)})
			}
			for _, i := range itemIds(s) {
				if E.Holder(i) == mine && !contains(*h.Items, i) {
					dc.Rows = append(dc.Rows, DeclRow{Aspect: "item", Subject: i, Holder: holderView(mine), Status: "missing"})
				}
			}
		}
		if h.Knows != nil {
			for _, f := range *h.Knows {
				k := E.Knows(c, f)
				dc.Rows = append(dc.Rows, DeclRow{Aspect: "fact", Subject: f, Listed: true, Known: k, Status: status(k)})
			}
			for _, f := range factIds(s) {
				if E.Knows(c, f) && !contains(*h.Knows, f) {
					dc.Rows = append(dc.Rows, DeclRow{Aspect: "fact", Subject: f, Known: true, Status: "missing"})
				}
			}
		}
		r.Handouts = append(r.Handouts, dc)
	}
	for _, b := range s.Board {
		dc := DeclCheck{Name: b.Location}
		here := m.Holder{Kind: m.HolderPlace, ID: b.Location}
		for _, i := range b.Items {
			dc.Rows = append(dc.Rows, DeclRow{Aspect: "item", Subject: i, Listed: true,
				Holder: holderView(E.Holder(i)), Status: status(E.Holder(i) == here)})
		}
		for _, i := range itemIds(s) {
			if E.Holder(i) == here && !contains(b.Items, i) {
				dc.Rows = append(dc.Rows, DeclRow{Aspect: "item", Subject: i, Holder: holderView(here), Status: "missing"})
			}
		}
		r.Boards = append(r.Boards, dc)
	}
}

func valText(v Val) string {
	if v.IsStr {
		return v.S
	}
	if v.B {
		return "true"
	}
	return "false"
}

// endingTable は選び方ごとのエンディング(G 群と同じ定義域・制約・評価)。
func endingTable(w *world) EndingTable {
	var t EndingTable
	doms := domains(w.s)
	total := big.NewInt(1)
	for _, d := range doms {
		total.Mul(total, big.NewInt(int64(len(d.vals))))
	}
	if total.Cmp(big.NewInt(gLimit)) > 0 {
		t.Skipped = fmt.Sprintf("選び方が %s 通りあり、数え上げの上限を超えるため省略", total.String())
		return t
	}
	for _, d := range doms {
		t.Vars = append(t.Vars, d.v)
	}
	cons := w.effectiveConstraints()
	ends := sortedEndings(w.s)
	t.GoalTrue = map[string]int{}
	counts := make([]int, len(ends))
	vals := make([]Val, len(doms))
	var visit func(i int)
	visit = func(i int) {
		if i < len(doms) {
			for _, x := range doms[i].vals {
				vals[i] = x
				visit(i + 1)
			}
			return
		}
		sigma := toAssignment(t.Vars, vals)
		for _, c := range cons {
			if !eval(sigma, c) {
				return
			}
		}
		t.Total++
		for _, g := range w.s.Goals {
			if sigma.get(g.ID) == boolVal(true) {
				t.GoalTrue[g.ID]++
			}
		}
		var hit []string
		for k, e := range ends {
			if eval(sigma, e.Condition) {
				hit = append(hit, e.ID)
				counts[k]++
			}
		}
		switch {
		case len(hit) == 0:
			t.NoEnding++
		case len(hit) > 1:
			t.Multiple++
		}
		if len(t.Rows) < maxEndingRows {
			row := EndingRow{Endings: hit}
			for _, v := range vals {
				row.Values = append(row.Values, valText(v))
			}
			t.Rows = append(t.Rows, row)
		}
	}
	visit(0)
	t.Shown = len(t.Rows)
	for k, e := range ends {
		t.Counts = append(t.Counts, EndingCount{e.ID, counts[k]})
	}
	return t
}
