package check

import (
	"math/big"
	"sort"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// G 群: ゴール・選択・エンディング (§4.7)。G.lean と Formula.lean に対応する。
//
// Lean はパターン(実効制約を満たす割り当て)の列を作ってから各規則を評価する。ここでは同じ順序で
// パターンを1つずつ生成しながら、各規則に必要な情報(最初の反例、到達したエンディングなど)を集める。
// 結果は Lean と同じになる。

// gLimit は数え上げる割り当て数の上限 (G007)。
const gLimit = 1 << 20

// assignment は割り当て σ。変数に値がなければ false(toAssignment)。
type assignment map[string]Val

func (a assignment) get(v string) Val {
	if x, ok := a[v]; ok {
		return x
	}
	return boolVal(false)
}

func toAssignment(vars []string, vals []Val) assignment {
	a := assignment{}
	for i, v := range vars {
		if i >= len(vals) {
			break
		}
		if _, ok := a[v]; !ok { // 最初に見つかったもの
			a[v] = vals[i]
		}
	}
	return a
}

func count(vals []Val, w Val) int {
	n := 0
	for _, v := range vals {
		if v == w {
			n++
		}
	}
	return n
}

// winners は最多得票の値(重複なし、最初の出現順)。
func winners(vals []Val) []Val {
	ds := dedup(vals)
	mx := 0
	for _, w := range ds {
		if c := count(vals, w); c > mx {
			mx = c
		}
	}
	var out []Val
	for _, w := range ds {
		if count(vals, w) == mx {
			out = append(out, w)
		}
	}
	return out
}

func eval(sigma assignment, f m.Formula) bool {
	switch f.Kind {
	case m.FConst:
		return f.Const
	case m.FVar:
		v := sigma.get(f.Var)
		return !v.IsStr && v.B
	case m.FEq:
		return sigma.get(f.Var) == strVal(f.Value)
	case m.FPlurality, m.FTie:
		vals := make([]Val, len(f.Votes))
		for i, v := range f.Votes {
			vals[i] = sigma.get(v)
		}
		ws := winners(vals)
		if f.Kind == m.FTie {
			return len(ws) >= 2
		}
		return len(ws) == 1 && ws[0] == strVal(f.Value)
	case m.FNot:
		return !eval(sigma, f.Subs[0])
	case m.FAnd:
		for _, sub := range f.Subs {
			if !eval(sigma, sub) {
				return false
			}
		}
		return true
	case m.FOr:
		for _, sub := range f.Subs {
			if eval(sigma, sub) {
				return true
			}
		}
		return false
	}
	return false
}

type domain struct {
	v    string
	vals []Val
}

// domains は変数と定義域。変数は ID 昇順(同じ ID は入力の順)。
func domains(s *m.Scenario) []domain {
	var ds []domain
	for _, g := range s.Goals {
		ds = append(ds, domain{g.ID, []Val{boolVal(false), boolVal(true)}})
	}
	for _, c := range s.Choices {
		if c.Values == nil {
			ds = append(ds, domain{c.ID, []Val{boolVal(false), boolVal(true)}})
			continue
		}
		vs := append([]string(nil), *c.Values...)
		sort.SliceStable(vs, func(i, j int) bool { return vs[i] < vs[j] })
		d := domain{v: c.ID}
		for _, x := range vs {
			d.vals = append(d.vals, strVal(x))
		}
		ds = append(ds, d)
	}
	sort.SliceStable(ds, func(i, j int) bool { return ds[i].v < ds[j].v })
	return ds
}

func notVar(v string) m.Formula {
	return m.Formula{Kind: m.FNot, Subs: []m.Formula{{Kind: m.FVar, Var: v}}}
}

// effectiveConstraints は constraints と導出制約 (§4.7)。
func (w *world) effectiveConstraints() []m.Formula {
	s, E := w.s, w.final
	out := append([]m.Formula(nil), s.Constraints...)
	for _, g := range s.Goals {
		for _, i := range g.RequiresItems {
			if E.Holder(i).Kind == m.HolderConsumed {
				out = append(out, notVar(g.ID))
				break
			}
		}
	}
	gs := append([]m.Goal(nil), s.Goals...)
	sort.SliceStable(gs, func(i, j int) bool { return gs[i].ID < gs[j].ID })
	for i := range gs {
		for j := i + 1; j < len(gs); j++ {
			g1, g2 := gs[i], gs[j]
			if g1.Owner == g2.Owner {
				continue
			}
			for _, it := range g1.RequiresItems {
				if contains(g2.RequiresItems, it) {
					out = append(out, m.Formula{Kind: m.FNot, Subs: []m.Formula{{Kind: m.FAnd,
						Subs: []m.Formula{{Kind: m.FVar, Var: g1.ID}, {Kind: m.FVar, Var: g2.ID}}}}})
					break
				}
			}
		}
	}
	// 3. requires_knowledge に入手可能でない知識がある
	for _, g := range s.Goals {
		for _, f := range g.RequiresKnowledge {
			if !w.obtainable(f) {
				out = append(out, notVar(g.ID))
				break
			}
		}
	}
	// 4. ゴール ⇔ condition
	for _, g := range s.Goals {
		if g.Condition != nil {
			out = append(out, iff(m.Formula{Kind: m.FVar, Var: g.ID}, *g.Condition))
		}
	}
	return out
}

// iff は a ⇔ b を (a ∧ b) ∨ (¬a ∧ ¬b) で表す。
func iff(a, b m.Formula) m.Formula {
	not := func(f m.Formula) m.Formula { return m.Formula{Kind: m.FNot, Subs: []m.Formula{f}} }
	return m.Formula{Kind: m.FOr, Subs: []m.Formula{
		{Kind: m.FAnd, Subs: []m.Formula{a, b}},
		{Kind: m.FAnd, Subs: []m.Formula{not(a), not(b)}},
	}}
}

func sortedEndings(s *m.Scenario) []m.Ending {
	es := append([]m.Ending(nil), s.Endings...)
	sort.SliceStable(es, func(i, j int) bool { return es[i].ID < es[j].ID })
	return es
}

func idxOf(d []Val, x Val) int {
	for i, y := range d {
		if y == x {
			return i
		}
	}
	return len(d)
}

func (w *world) checkG() []Diag {
	s := w.s
	doms := domains(s)
	total := big.NewInt(1)
	for _, d := range doms {
		total.Mul(total, big.NewInt(int64(len(d.vals))))
	}
	var body []Diag
	if total.Cmp(big.NewInt(gLimit)) > 0 {
		body = []Diag{errD("G007", []string{total.String()}, nil)}
	} else {
		body = w.checkGPatterns(doms)
	}
	// G008
	for _, c := range s.Characters {
		owns := false
		for _, g := range s.Goals {
			if g.Owner == c.ID {
				owns = true
				break
			}
		}
		if !c.NPC && !owns {
			body = append(body, warnD("G008", []string{c.ID}, nil))
		}
	}
	return body
}

func (w *world) checkGPatterns(doms []domain) []Diag {
	s := w.s
	vars := make([]string, len(doms))
	for i, d := range doms {
		vars[i] = d.v
	}
	cons := w.effectiveConstraints()
	ends := sortedEndings(s)
	witness := func(vals []Val, d Diag) Diag {
		ws := make([]WitnessEntry, 0, len(vars))
		var key []int
		for i := 0; i < len(vars) && i < len(vals); i++ {
			ws = append(ws, WitnessEntry{vars[i], vals[i]})
			key = append(key, idxOf(doms[i].vals, vals[i]))
		}
		d.Witness, d.WKey = &ws, key
		return d
	}
	var (
		any      bool
		hasG001  bool
		g001     []Val
		pairWit  = map[[2]int][]Val{}
		reached  = make([]bool, len(ends))
		goalTrue = make([]bool, len(s.Goals))    // いずれかのパターンで true
		goalAll  = make([]bool, len(s.Goals))    // すべてのパターンで true
		chVals   = make([][]Val, len(s.Choices)) // 現れた値(重複なし、最初の出現順)
	)
	for k := range goalAll {
		goalAll[k] = true
	}
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
		pat := append([]Val(nil), vals...)
		any = true
		holds := make([]bool, len(ends))
		none := true
		for k, e := range ends {
			holds[k] = eval(sigma, e.Condition)
			if holds[k] {
				none = false
				reached[k] = true
			}
		}
		if none && !hasG001 {
			hasG001, g001 = true, pat
		}
		for a := range ends {
			for b := a + 1; b < len(ends); b++ {
				key := [2]int{a, b}
				if _, seen := pairWit[key]; !seen && holds[a] && holds[b] {
					pairWit[key] = pat
				}
			}
		}
		for k, g := range s.Goals {
			if sigma.get(g.ID) == boolVal(true) {
				goalTrue[k] = true
			} else {
				goalAll[k] = false
			}
		}
		for k, c := range s.Choices {
			if v := sigma.get(c.ID); !contains(chVals[k], v) {
				chVals[k] = append(chVals[k], v)
			}
		}
	}
	visit(0)
	if !any {
		return []Diag{errD("G005", []string{}, nil)}
	}
	var out []Diag
	if hasG001 {
		out = append(out, witness(g001, errD("G001", []string{}, nil)))
	}
	for a := range ends {
		for b := a + 1; b < len(ends); b++ {
			if pat, ok := pairWit[[2]int{a, b}]; ok {
				out = append(out, witness(pat, errD("G002", []string{ends[a].ID, ends[b].ID}, nil)))
			}
		}
	}
	for k, e := range ends {
		if !reached[k] {
			out = append(out, errD("G003", []string{e.ID}, nil))
		}
	}
	for k, g := range s.Goals {
		if !goalTrue[k] {
			out = append(out, errD("G004", []string{g.ID}, nil))
		} else if goalAll[k] {
			out = append(out, warnD("G006", []string{g.ID}, nil))
		}
	}
	for k, c := range s.Choices {
		vs := chVals[k]
		if len(vs) == 1 {
			out = append(out, warnD("G006", []string{c.ID}, nil))
		}
		if c.Values != nil {
			for _, v := range *c.Values {
				if !contains(vs, strVal(v)) {
					out = append(out, warnD("G009", []string{c.ID, v}, nil))
				}
			}
		}
	}
	return out
}
