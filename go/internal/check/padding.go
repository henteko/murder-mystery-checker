package check

import (
	"sort"
	"strings"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// 水増しの検出: 複雑度のスコアを上げるが、シナリオの中で何の役にも立っていない要素。
// 自動生成のループが数字だけを稼ぐのを防ぐために数える。定義は docs/stats.md の「水増し」。

// PaddingStats は水増しの候補。どれも ID の昇順。
type PaddingStats struct {
	// UnusedLocations は、誰も一度も居らず、どのイベント・アイテム・手がかり・盤面・断言・ハンドアウトにも現れない場所
	UnusedLocations []string `json:"unused_locations"`
	// IdleMoves は、行って何もせずに元の場所へ戻る往復の、行きと帰りの move(下記)
	IdleMoves []string `json:"idle_moves"`
	// UnusedFacts は、プレイヤーが手に入れられず(§2.5)、どこからも参照されない知識
	UnusedFacts []string `json:"unused_facts"`
	// EmptyClues は、何も明かさず、アイテムにも結び付かない手がかり
	EmptyClues []string `json:"empty_clues"`
	// IrrelevantChoices は、値を変えてもどのパターンでも結末もゴールの達成も変わらない選択
	// (パターンを数え上げられないときは空)
	IrrelevantChoices []string `json:"irrelevant_choices"`
	// Total は上の件数の合計
	Total int `json:"total"`
}

func (w *world) paddingStats() PaddingStats {
	idle := w.idleMoves()
	p := PaddingStats{UnusedLocations: w.unusedLocations(idle), IdleMoves: idle,
		UnusedFacts: w.unusedFacts(), EmptyClues: []string{}, IrrelevantChoices: w.irrelevantChoices()}
	for _, cl := range w.s.Clues {
		if len(cl.Reveals) == 0 && cl.Item == nil {
			p.EmptyClues = append(p.EmptyClues, cl.ID)
		}
	}
	sort.Strings(p.EmptyClues)
	p.Total = len(p.UnusedLocations) + len(p.IdleMoves) + len(p.UnusedFacts) + len(p.EmptyClues) + len(p.IrrelevantChoices)
	return p
}

// unusedLocations は使われていない場所。往復の move(idle)で居ただけの場所も使われていないとみなす。
func (w *world) unusedLocations(idle []string) []string {
	s := w.s
	used := map[string]bool{}
	// idle な move で始まった滞在 (キャラクター, 場所, 到着時刻)
	type stay struct {
		c, l string
		at   int
	}
	idleStay := map[stay]bool{}
	for _, id := range idle {
		if e, ok := findEvent(s, id); ok {
			idleStay[stay{e.Kind.Character, e.Kind.To, e.Kind.Arrive}] = true
		}
	}
	for _, c := range s.Characters {
		for _, sg := range w.segments(c.ID) {
			if !idleStay[stay{c.ID, sg.Loc, sg.From}] {
				used[sg.Loc] = true
			}
		}
	}
	for _, e := range s.Events {
		k := e.Kind
		switch k.Kind {
		case m.Move:
			if !contains(idle, e.ID) {
				used[k.To] = true
			}
		case m.Scene:
			used[k.Location] = true
		case m.Observe:
			used[k.Location], used[k.TargetLocation] = true, true
		}
	}
	for _, it := range s.Items {
		if it.Initial.Kind == m.HolderPlace {
			used[it.Initial.ID] = true
		}
		if h := w.final.Holder(it.ID); h.Kind == m.HolderPlace {
			used[h.ID] = true
		}
	}
	for _, cl := range s.Clues {
		if cl.Location != nil {
			used[*cl.Location] = true
		}
	}
	for _, b := range s.Board {
		used[b.Location] = true
	}
	for _, a := range s.Assertions {
		used[a.Location] = true
	}
	for _, h := range s.Handouts {
		if h.Location != nil {
			used[*h.Location] = true
		}
	}
	out := []string{}
	for _, l := range s.Locations {
		if !used[l.ID] {
			out = append(out, l.ID)
		}
	}
	sort.Strings(out)
	return out
}

// idleMoves は、次をすべて満たす move(往復の行き): 次の move で出発前の場所へ戻り、致命的でない徒歩の
// 移動で、requires がなく、証言の対象でなく、到着から次の出発までの間にそのキャラクターが参加者・観察の
// 対象になるイベントも、そのキャラクターについての断言もなく、非公共の場所でほかの誰とも居合わせていない。
// 自室に戻って一晩過ごすような、何も起きないがアリバイとして意味のある滞在は往復ではないので含めない。
func (w *world) idleMoves() []string {
	s := w.s
	claimed := map[string]bool{}
	for _, f := range s.Facts {
		if f.AboutEvent != nil {
			claimed[*f.AboutEvent] = true
		}
	}
	out := []string{}
	for _, c := range s.Characters {
		var moves []m.Event
		for _, e := range w.sorted {
			if e.Kind.Kind == m.Move && e.Kind.Character == c.ID {
				moves = append(moves, e)
			}
		}
		prev := initState(s).Pos(c.ID).Dest
		for i, mv := range moves {
			k := mv.Kind
			from := prev
			prev = k.To
			if i == len(moves)-1 || moves[i+1].Kind.To != from || k.Fatal || (k.Mode != "" && k.Mode != "walk") || len(mv.Requires) > 0 || claimed[mv.ID] {
				continue
			}
			lo, hi := k.Arrive, moves[i+1].Time
			if !w.stayIsIdle(c.ID, k.To, lo, hi) {
				continue
			}
			out = append(out, mv.ID, moves[i+1].ID)
		}
	}
	sort.Strings(out)
	return append([]string{}, dedup(out)...)
}

func (w *world) stayIsIdle(c, l string, lo, hi int) bool {
	s := w.s
	for _, e := range s.Events {
		if e.Kind.Kind == m.Move || e.Time < lo || e.Time > hi {
			continue
		}
		if contains(participants(e.Kind), c) || contains(observed(e.Kind), c) {
			return false
		}
	}
	for _, a := range s.Assertions {
		if lo <= a.Time && a.Time < hi && contains(a.Characters, c) {
			return false
		}
	}
	if isPublic(s, l) {
		return true
	}
	for _, o := range s.Characters {
		if o.ID == c {
			continue
		}
		for _, sg := range w.segments(o.ID) {
			if sg.Loc == l && max(sg.From, lo) < min(sg.Till, hi) {
				return false
			}
		}
	}
	return true
}

func (w *world) unusedFacts() []string {
	s := w.s
	ref := map[string]bool{}
	mark := func(fs []string) {
		for _, f := range fs {
			ref[f] = true
		}
	}
	mark(s.SolutionFacts)
	for _, e := range s.Events {
		mark(e.Requires)
	}
	for _, g := range s.Goals {
		mark(g.RequiresKnowledge)
		mark(g.Conceals)
	}
	for _, f := range s.Facts {
		if len(f.ContradictedBy) > 0 {
			ref[f.ID] = true
			mark(f.ContradictedBy)
		}
	}
	for _, nf := range formulas(s) {
		for _, r := range formulaRefs(nf.f) {
			if r.kind == 3 {
				ref[r.v] = true
			}
		}
	}
	for _, h := range s.Handouts {
		if h.Knows != nil {
			mark(*h.Knows)
		}
	}
	out := []string{}
	for _, f := range s.Facts {
		if !ref[f.ID] && !w.obtainable(f.ID) {
			out = append(out, f.ID)
		}
	}
	sort.Strings(out)
	return out
}

// irrelevantChoices は、ほかの選択の値を固定したとき、この選択のどの値でも、パターンで実現できる
// (結末, ゴールの達成)の組の集合が同じになる選択。
func (w *world) irrelevantChoices() []string {
	out := []string{}
	pats, ok := w.patterns()
	if !ok || len(pats) == 0 {
		return out
	}
	s := w.s
	ends := sortedEndings(s)
	gs := append([]m.Goal(nil), s.Goals...)
	sort.SliceStable(gs, func(i, j int) bool { return gs[i].ID < gs[j].ID })
	res := make([]string, len(pats))
	for i, sigma := range pats {
		var b strings.Builder
		b.WriteString(outcome(sigma, ends))
		for _, g := range gs {
			if sigma.get(g.ID) == boolVal(true) {
				b.WriteString("|" + g.ID)
			}
		}
		res[i] = b.String()
	}
	for _, x := range s.Choices {
		// ほかの選択の値 → x の値 → 結果の集合
		groups := map[string]map[string]map[string]bool{}
		for i, sigma := range pats {
			var key strings.Builder
			for _, c := range s.Choices {
				if c.ID != x.ID {
					v, _ := sigma.get(c.ID).MarshalJSON()
					key.WriteString(c.ID + "=" + string(v) + ";")
				}
			}
			xv, _ := sigma.get(x.ID).MarshalJSON()
			if groups[key.String()] == nil {
				groups[key.String()] = map[string]map[string]bool{}
			}
			if groups[key.String()][string(xv)] == nil {
				groups[key.String()][string(xv)] = map[string]bool{}
			}
			groups[key.String()][string(xv)][res[i]] = true
		}
		nvals := 2
		if x.Values != nil {
			nvals = len(dedup(*x.Values))
		}
		irrelevant := true
		for _, byVal := range groups {
			if len(byVal) != nvals { // ある値がパターンに現れない: 値によって変わる
				irrelevant = false
				break
			}
			var first map[string]bool
			for _, set := range byVal {
				if first == nil {
					first = set
				} else if !sameSet(first, set) {
					irrelevant = false
					break
				}
			}
			if !irrelevant {
				break
			}
		}
		if irrelevant {
			out = append(out, x.ID)
		}
	}
	sort.Strings(out)
	return out
}

func sameSet(a, b map[string]bool) bool {
	if len(a) != len(b) {
		return false
	}
	for k := range a {
		if !b[k] {
			return false
		}
	}
	return true
}

// patterns はパターンの列(割り当ての順序)。割り当て数が上限を超えると ok = false。
func (w *world) patterns() ([]assignment, bool) {
	doms := domains(w.s)
	total := 1
	for _, d := range doms {
		total *= len(d.vals)
		if total > gLimit {
			return nil, false
		}
	}
	vars := make([]string, len(doms))
	for i, d := range doms {
		vars[i] = d.v
	}
	cons := w.effectiveConstraints()
	var out []assignment
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
		sigma := toAssignment(vars, vals)
		for _, c := range cons {
			if !eval(sigma, c) {
				return
			}
		}
		out = append(out, sigma)
	}
	visit(0)
	return out, true
}
