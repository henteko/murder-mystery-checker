package check

import (
	"sort"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// R 群: 構造・参照整合 (§4.1)。R.lean に対応する。

func duplicates[T comparable](l []T) []T {
	cnt := map[T]int{}
	for _, x := range l {
		cnt[x]++
	}
	var out []T
	for _, x := range dedup(l) {
		if cnt[x] >= 2 {
			out = append(out, x)
		}
	}
	return out
}

func ids[T any](l []T, f func(T) string) []string {
	out := make([]string, 0, len(l))
	for _, x := range l {
		out = append(out, f(x))
	}
	return out
}

func characterIds(s *m.Scenario) []string {
	return ids(s.Characters, func(c m.Character) string { return c.ID })
}
func areaIds(s *m.Scenario) []string { return ids(s.Areas, func(a m.Area) string { return a.ID }) }
func locationIds(s *m.Scenario) []string {
	return ids(s.Locations, func(l m.Location) string { return l.ID })
}
func itemIds(s *m.Scenario) []string  { return ids(s.Items, func(i m.Item) string { return i.ID }) }
func factIds(s *m.Scenario) []string  { return ids(s.Facts, func(f m.Fact) string { return f.ID }) }
func eventIds(s *m.Scenario) []string { return ids(s.Events, func(e m.Event) string { return e.ID }) }
func variableIds(s *m.Scenario) []string {
	return append(ids(s.Goals, func(g m.Goal) string { return g.ID }), ids(s.Choices, func(c m.Choice) string { return c.ID })...)
}

func findFact(s *m.Scenario, f string) (m.Fact, bool) {
	for _, x := range s.Facts {
		if x.ID == f {
			return x, true
		}
	}
	return m.Fact{}, false
}

// enumValues は選択 v が列挙型ならその値の集合(最初に見つかった選択)。
func enumValues(s *m.Scenario, v string) (*[]string, bool) {
	for _, c := range s.Choices {
		if c.ID == v {
			return c.Values, c.Values != nil
		}
	}
	return nil, false
}

type rIssue struct {
	code  string
	args  []string
	event *string
}

func rerr(code string, args ...string) rIssue { return rIssue{code: code, args: args} }

// ---------------------------------------------------------------- R001

func checkR001(s *m.Scenario) []rIssue {
	kinds := []struct {
		k   string
		ids []string
	}{
		{"character", characterIds(s)}, {"area", areaIds(s)}, {"location", locationIds(s)},
		{"item", itemIds(s)}, {"fact", factIds(s)}, {"clue", ids(s.Clues, func(c m.Clue) string { return c.ID })},
		{"event", eventIds(s)}, {"assertion", ids(s.Assertions, func(a m.Assertion) string { return a.ID })},
		{"variable", variableIds(s)}, {"ending", ids(s.Endings, func(e m.Ending) string { return e.ID })},
		{"handout", ids(s.Handouts, func(h m.Handout) string { return h.Character })},
		{"board", ids(s.Board, func(b m.Board) string { return b.Location })},
	}
	var out []rIssue
	for _, k := range kinds {
		for _, id := range duplicates(k.ids) {
			out = append(out, rerr("R001", k.k, id))
		}
	}
	return out
}

// ---------------------------------------------------------------- R002

type ref struct {
	referrer, kind, id string
	event              string // 参照元がイベントならその ID
	hasEvent           bool
}

func eventRefs(e m.Event) []ref {
	r := "event:" + e.ID
	mk := func(k, id string) ref { return ref{r, k, id, e.ID, true} }
	k := e.Kind
	chars := append(append([]string{}, participants(k)...), observed(k)...)
	var locs []string
	switch k.Kind {
	case m.Move:
		locs = []string{k.To}
	case m.Scene:
		locs = []string{k.Location}
	case m.Observe:
		locs = []string{k.Location, k.TargetLocation}
	}
	facts := append([]string{}, e.Requires...)
	switch k.Kind {
	case m.Scene:
		facts = append(facts, k.Reveals...)
	case m.Observe, m.Learn, m.Tell:
		facts = append(facts, k.Facts...)
	}
	var out []ref
	for _, c := range chars {
		out = append(out, mk("character", c))
	}
	for _, l := range locs {
		out = append(out, mk("location", l))
	}
	if i, ok := itemOf(k); ok {
		out = append(out, mk("item", i))
	}
	for _, f := range facts {
		out = append(out, mk("fact", f))
	}
	return out
}

// varRef は論理式が参照する変数 (Formula.refs)。
type varRef struct {
	kind  int // 0: 真偽値として, 1: eq, 2: 集計
	v     string
	value string
	votes []string
	hasX  bool // 集計: plurality なら true
}

func formulaRefs(f m.Formula) []varRef {
	switch f.Kind {
	case m.FVar:
		return []varRef{{kind: 0, v: f.Var}}
	case m.FEq:
		return []varRef{{kind: 1, v: f.Var, value: f.Value}}
	case m.FPlurality:
		return []varRef{{kind: 2, votes: f.Votes, value: f.Value, hasX: true}}
	case m.FTie:
		return []varRef{{kind: 2, votes: f.Votes}}
	case m.FNot, m.FAnd, m.FOr:
		var out []varRef
		for _, sub := range f.Subs {
			out = append(out, formulaRefs(sub)...)
		}
		return out
	}
	return nil
}

func formulaRefRefs(referrer string, f m.Formula) []ref {
	var out []ref
	for _, r := range formulaRefs(f) {
		if r.kind == 2 {
			for _, v := range r.votes {
				out = append(out, ref{referrer: referrer, kind: "variable", id: v})
			}
		} else {
			out = append(out, ref{referrer: referrer, kind: "variable", id: r.v})
		}
	}
	return out
}

func allRefs(s *m.Scenario) []ref {
	var out []ref
	add := func(referrer, kind, id string) { out = append(out, ref{referrer: referrer, kind: kind, id: id}) }
	for _, l := range s.Locations {
		if l.Area != nil {
			add("location:"+l.ID, "area", *l.Area)
		}
	}
	for _, t := range []struct {
		tbl, kind string
		es        []m.Edge
	}{{"travel", "location", s.Travel}, {"area_travel", "area", s.AreaTravel}, {"perception", "location", s.Perception}} {
		for _, e := range t.es {
			add(t.tbl, t.kind, e.Src)
			add(t.tbl, t.kind, e.Dst)
		}
	}
	for _, p := range s.Placements {
		add("placement:"+p.Character, "character", p.Character)
		add("placement:"+p.Character, "location", p.Location)
	}
	for _, i := range s.Items {
		switch i.Initial.Kind {
		case m.HolderChar:
			add("item:"+i.ID, "character", i.Initial.ID)
		case m.HolderPlace:
			add("item:"+i.ID, "location", i.Initial.ID)
		}
	}
	for _, k := range s.InitialKnowledge {
		add("initial_knowledge:"+k.Character, "character", k.Character)
		add("initial_knowledge:"+k.Character, "fact", k.Fact)
	}
	for _, f := range s.Facts {
		for _, r := range f.ContradictedBy {
			add("fact:"+f.ID, "fact", r)
		}
		if f.AboutEvent != nil {
			add("fact:"+f.ID, "event", *f.AboutEvent)
		}
	}
	for _, e := range s.Events {
		out = append(out, eventRefs(e)...)
	}
	for _, c := range s.Clues {
		if c.Location != nil {
			add("clue:"+c.ID, "location", *c.Location)
		}
		if c.Item != nil {
			add("clue:"+c.ID, "item", *c.Item)
		}
		for _, f := range c.Reveals {
			add("clue:"+c.ID, "fact", f)
		}
	}
	for _, f := range s.SolutionFacts {
		add("solution", "fact", f)
	}
	for _, a := range s.Assertions {
		add("assertion:"+a.ID, "location", a.Location)
		for _, c := range a.Characters {
			add("assertion:"+a.ID, "character", c)
		}
	}
	for _, h := range s.Handouts {
		r := "handout:" + h.Character
		add(r, "character", h.Character)
		if h.Location != nil {
			add(r, "location", *h.Location)
		}
		if h.Items != nil {
			for _, i := range *h.Items {
				add(r, "item", i)
			}
		}
		if h.Knows != nil {
			for _, f := range *h.Knows {
				add(r, "fact", f)
			}
		}
	}
	for _, b := range s.Board {
		add("board:"+b.Location, "location", b.Location)
		for _, i := range b.Items {
			add("board:"+b.Location, "item", i)
		}
	}
	for _, g := range s.Goals {
		add("goal:"+g.ID, "character", g.Owner)
		for _, i := range g.RequiresItems {
			add("goal:"+g.ID, "item", i)
		}
		for _, f := range g.RequiresKnowledge {
			add("goal:"+g.ID, "fact", f)
		}
		if g.Condition != nil {
			out = append(out, formulaRefRefs("goal:"+g.ID, *g.Condition)...)
		}
	}
	for _, c := range s.Choices {
		add("choice:"+c.ID, "character", c.Owner)
	}
	for _, f := range s.Constraints {
		out = append(out, formulaRefRefs("constraint", f)...)
	}
	for _, e := range s.Endings {
		out = append(out, formulaRefRefs("ending:"+e.ID, e.Condition)...)
	}
	return out
}

func idsOfKind(s *m.Scenario, k string) []string {
	switch k {
	case "character":
		return characterIds(s)
	case "area":
		return areaIds(s)
	case "location":
		return locationIds(s)
	case "item":
		return itemIds(s)
	case "fact":
		return factIds(s)
	case "event":
		return eventIds(s)
	case "variable":
		return variableIds(s)
	}
	return nil
}

func checkR002(s *m.Scenario) []rIssue {
	var bad []ref
	for _, r := range allRefs(s) {
		if !contains(idsOfKind(s, r.kind), r.id) {
			bad = append(bad, r)
		}
	}
	var out []rIssue
	for _, r := range dedup(bad) {
		is := rerr("R002", r.referrer, r.kind, r.id)
		if r.hasEvent {
			is.event = ptr(r.event)
		}
		out = append(out, is)
	}
	return out
}

// ---------------------------------------------------------------- R003〜R005

func checkR003(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, c := range s.Characters {
		n := 0
		for _, p := range s.Placements {
			if p.Character == c.ID {
				n++
			}
		}
		if n != 1 {
			out = append(out, rerr("R003", c.ID))
		}
	}
	return out
}

func checkR004(s *m.Scenario) []rIssue {
	if s.StartTime > s.EndTime {
		return []rIssue{rerr("R004")}
	}
	return nil
}

func checkEdges(tbl string, es []m.Edge) []rIssue {
	var out []rIssue
	type pair struct{ a, b string }
	var pairs []pair
	for _, e := range es {
		if e.Src == e.Dst {
			out = append(out, rerr("R005", tbl, e.Src, e.Dst))
			continue
		}
		pairs = append(pairs, pair{e.Src, e.Dst})
		if e.Bidirectional {
			pairs = append(pairs, pair{e.Dst, e.Src})
		}
	}
	for _, p := range duplicates(pairs) {
		out = append(out, rerr("R005", tbl, p.a, p.b))
	}
	return out
}

func checkR005(s *m.Scenario) []rIssue {
	return append(append(checkEdges("travel", s.Travel), checkEdges("area_travel", s.AreaTravel)...),
		checkEdges("perception", s.Perception)...)
}

// ---------------------------------------------------------------- R006

func eventShapeErrors(e m.Event) []string {
	k := e.Kind
	var out []string
	switch k.Kind {
	case m.Move:
		if k.Arrive < e.Time {
			out = append(out, "arrive_before_depart")
		}
		if !contains([]string{"walk", "fall", "carried"}, k.Mode) {
			out = append(out, "unknown_mode")
		}
	case m.Transfer:
		if k.Src == k.Dst {
			out = append(out, "self_transfer")
		}
	case m.Tell:
		if k.Src == k.Dst {
			out = append(out, "self_tell")
		}
		if len(k.Facts) == 0 {
			out = append(out, "empty_facts")
		}
	case m.Observe:
		if contains(k.Targets, k.Character) {
			out = append(out, "self_observe")
		}
		if len(duplicates(k.Targets)) > 0 {
			out = append(out, "duplicate_participant")
		}
		if len(k.Facts) == 0 {
			out = append(out, "empty_facts")
		}
	case m.Scene:
		if len(k.Participants) == 0 {
			out = append(out, "empty_participants")
		}
		if len(duplicates(k.Participants)) > 0 {
			out = append(out, "duplicate_participant")
		}
	case m.Learn:
		if len(k.Facts) == 0 {
			out = append(out, "empty_facts")
		}
	}
	return out
}

func checkR006(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, e := range s.Events {
		for _, r := range eventShapeErrors(e) {
			is := rerr("R006", r)
			is.event = ptr(e.ID)
			out = append(out, is)
		}
	}
	return out
}

// ---------------------------------------------------------------- R007〜R013

func checkR007(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, c := range s.Clues {
		if c.Location == nil && c.Item == nil && c.Deck == nil {
			out = append(out, rerr("R007", c.ID))
		}
	}
	return out
}

func checkR008(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, c := range s.Choices {
		if c.Values != nil && (len(*c.Values) == 0 || len(duplicates(*c.Values)) > 0) {
			out = append(out, rerr("R008", c.ID))
		}
	}
	return out
}

func formulaTypeErrors(s *m.Scenario, referrer string, f m.Formula) []rIssue {
	var out []rIssue
	for _, r := range formulaRefs(f) {
		switch r.kind {
		case 0:
			if _, ok := enumValues(s, r.v); ok {
				out = append(out, rerr("R009", referrer, r.v, ""))
			}
		case 1:
			if !contains(variableIds(s), r.v) {
				continue
			}
			vs, ok := enumValues(s, r.v)
			if !ok || !contains(*vs, r.value) {
				out = append(out, rerr("R009", referrer, r.v, r.value))
			}
		}
	}
	return out
}

func tallyErrors(s *m.Scenario, referrer string, f m.Formula) []rIssue {
	var out []rIssue
	vids := variableIds(s)
	for _, r := range formulaRefs(f) {
		if r.kind != 2 {
			continue
		}
		var known []string
		for _, v := range r.votes {
			if contains(vids, v) {
				known = append(known, v)
			}
		}
		var enums [][]string
		notEnum := false
		for _, v := range known {
			if vs, ok := enumValues(s, v); ok {
				enums = append(enums, *vs)
			} else {
				notEnum = true
			}
		}
		var sets []string
		for _, vals := range enums {
			c := append([]string(nil), vals...)
			sort.Strings(c)
			b, _ := jsonKey(c)
			sets = append(sets, b)
		}
		if len(r.votes) == 0 {
			out = append(out, rerr("R012", referrer, "empty_votes"))
		}
		if notEnum {
			out = append(out, rerr("R012", referrer, "not_enum"))
		}
		if len(dedup(sets)) >= 2 {
			out = append(out, rerr("R012", referrer, "different_values"))
		}
		if r.hasX {
			for _, vals := range enums {
				if !contains(vals, r.value) {
					out = append(out, rerr("R012", referrer, "unknown_value"))
					break
				}
			}
		}
	}
	return out
}

type namedFormula struct {
	referrer string
	f        m.Formula
}

func formulas(s *m.Scenario) []namedFormula {
	var out []namedFormula
	for _, f := range s.Constraints {
		out = append(out, namedFormula{"constraint", f})
	}
	for _, e := range s.Endings {
		out = append(out, namedFormula{"ending:" + e.ID, e.Condition})
	}
	for _, g := range s.Goals {
		if g.Condition != nil {
			out = append(out, namedFormula{"goal:" + g.ID, *g.Condition})
		}
	}
	return out
}

func checkR009(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, nf := range formulas(s) {
		out = append(out, formulaTypeErrors(s, nf.referrer, nf.f)...)
	}
	return out
}

func checkR012(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, nf := range formulas(s) {
		out = append(out, tallyErrors(s, nf.referrer, nf.f)...)
	}
	return out
}

func checkR010(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, f := range s.Facts {
		if f.Truth {
			if len(f.ContradictedBy) > 0 {
				out = append(out, rerr("R010", f.ID, ""))
			}
			continue
		}
		for _, r := range f.ContradictedBy {
			if rf, ok := findFact(s, r); ok && !rf.Truth {
				out = append(out, rerr("R010", f.ID, r))
			}
		}
	}
	return out
}

func checkR011(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, f := range s.Facts {
		if f.AboutEvent != nil && f.ClaimedAt == nil {
			out = append(out, rerr("R011", f.ID, "about_without_claimed_at"))
		}
		if f.AboutEvent == nil && f.ClaimedAt != nil {
			out = append(out, rerr("R011", f.ID, "claimed_at_without_about"))
		}
		if f.AboutPoint != "at" && f.AboutPoint != "arrive" {
			out = append(out, rerr("R011", f.ID, "unknown_point"))
		}
		if f.AboutEvent != nil && f.AboutPoint == "arrive" {
			for _, e := range s.Events {
				if e.ID == *f.AboutEvent && e.Kind.Kind != m.Move {
					out = append(out, rerr("R011", f.ID, "arrive_on_non_move"))
					break
				}
			}
		}
	}
	return out
}

func checkR013(s *m.Scenario) []rIssue {
	var out []rIssue
	for _, a := range s.Assertions {
		if !(s.StartTime <= a.Time && a.Time < s.EndTime) {
			out = append(out, rerr("R013", a.ID))
		}
	}
	return out
}

// checkR は R 群の検出結果。R001(ID の重複)があれば R001 だけを出す (§3)。
func checkR(s *m.Scenario) []Diag {
	is := checkR001(s)
	if len(is) == 0 {
		for _, f := range []func(*m.Scenario) []rIssue{checkR002, checkR003, checkR004, checkR005, checkR006,
			checkR007, checkR008, checkR009, checkR010, checkR011, checkR012, checkR013} {
			is = append(is, f(s)...)
		}
	}
	out := make([]Diag, 0, len(is))
	for _, x := range is {
		out = append(out, errD(x.code, x.args, x.event))
	}
	return out
}
