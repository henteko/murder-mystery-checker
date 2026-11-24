package check

import (
	"sort"
	"strconv"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// 終了状態・区間に対する検査: T009 / T012 / K003〜K008 / H / A (§4.2, §4.4〜§4.6)。Post.lean に対応する。

func (w *world) acknowledged(c1, c2, l string, lo, hi int) bool {
	for _, e := range w.s.Events {
		if !(lo <= e.Time && e.Time <= hi) {
			continue
		}
		k := e.Kind
		switch k.Kind {
		case m.Scene, m.Transfer, m.Tell:
			ps := participants(k)
			if contains(ps, c1) && contains(ps, c2) {
				return true
			}
		case m.Observe:
			if k.Location == l && k.TargetLocation == l &&
				((k.Character == c1 && contains(k.Targets, c2)) || (k.Character == c2 && contains(k.Targets, c1))) {
				return true
			}
		}
	}
	return false
}

func (w *world) warningsT009() []issue {
	cs := append([]string(nil), characterIds(w.s)...)
	sort.SliceStable(cs, func(i, j int) bool { return cs[i] < cs[j] })
	var out []issue
	for i := range cs {
		for j := i + 1; j < len(cs); j++ {
			c1, c2 := cs[i], cs[j]
			for _, s1 := range w.segments(c1) {
				for _, s2 := range w.segments(c2) {
					lo, hi := max(s1.From, s2.From), min(s1.Till, s2.Till)
					if s1.Loc == s2.Loc && !isPublic(w.s, s1.Loc) && lo < hi && !w.acknowledged(c1, c2, s1.Loc, lo, hi) {
						out = append(out, iss("T009", c1, c2, s1.Loc, strconv.Itoa(lo), strconv.Itoa(hi)))
					}
				}
			}
		}
	}
	return out
}

func (w *world) held(f string) bool {
	for _, c := range w.s.Characters {
		if !c.NPC && w.final.Knows(c.ID, f) {
			return true
		}
	}
	for _, h := range w.s.Handouts {
		if h.Knows != nil && contains(*h.Knows, f) {
			return true
		}
	}
	return false
}

func absDiff(a, b int) int {
	if a <= b {
		return b - a
	}
	return a - b
}

func actualTime(f m.Fact, e m.Event) int {
	if e.Kind.Kind == m.Move && f.AboutPoint == "arrive" {
		return e.Kind.Arrive
	}
	return e.Time
}

func (w *world) postErrors() []issue {
	s, E := w.s, w.final
	var out []issue
	// K003
	for _, f := range s.SolutionFacts {
		if !w.obtainable(f) {
			out = append(out, iss("K003", f))
		}
	}
	// K004 / K005
	for _, c := range s.Clues {
		if c.Item == nil {
			continue
		}
		i := *c.Item
		h := E.Holder(i)
		if h.Kind == m.HolderConsumed {
			out = append(out, iss("K004", c.ID, i))
		} else if c.Location != nil && h != (m.Holder{Kind: m.HolderPlace, ID: *c.Location}) {
			out = append(out, iss("K005", c.ID, i, *c.Location, h.Render()))
		}
	}
	// K006
	for _, f := range s.Facts {
		if f.Truth || !w.held(f.ID) {
			continue
		}
		refuted := false
		for _, r := range f.ContradictedBy {
			if w.obtainable(r) {
				refuted = true
				break
			}
		}
		if !refuted {
			out = append(out, iss("K006", f.ID))
		}
	}
	// K007
	for _, f := range s.SolutionFacts {
		if fact, ok := findFact(s, f); ok && !fact.Truth {
			out = append(out, iss("K007", f))
		}
	}
	// K008
	for _, f := range s.Facts {
		if !f.Truth || f.AboutEvent == nil || f.ClaimedAt == nil {
			continue
		}
		e, ok := findEvent(s, *f.AboutEvent)
		if !ok {
			continue
		}
		tol := s.ClaimTolerance
		if f.Tolerance != nil {
			tol = *f.Tolerance
		}
		if act := actualTime(f, e); absDiff(*f.ClaimedAt, act) > tol {
			out = append(out, iss("K008", f.ID, strconv.Itoa(*f.ClaimedAt), strconv.Itoa(act)))
		}
	}
	// H001 / H002 / H004
	for _, h := range s.Handouts {
		c := h.Character
		if h.Location != nil && E.Pos(c).Dest != *h.Location {
			out = append(out, iss("H001", c, *h.Location, E.Pos(c).Dest))
		}
		if h.Items != nil {
			for _, i := range *h.Items {
				if hd := E.Holder(i); hd != (m.Holder{Kind: m.HolderChar, ID: c}) {
					out = append(out, iss("H002", c, i, hd.Render()))
				}
			}
		}
		if h.Knows != nil {
			for _, f := range *h.Knows {
				if !E.Knows(c, f) {
					out = append(out, iss("H004", c, f))
				}
			}
		}
	}
	// H006
	for _, b := range s.Board {
		for _, i := range b.Items {
			if hd := E.Holder(i); hd != (m.Holder{Kind: m.HolderPlace, ID: b.Location}) {
				out = append(out, iss("H006", b.Location, i, hd.Render()))
			}
		}
	}
	// A001
	for _, a := range s.Assertions {
		for _, c := range a.Characters {
			wh := w.whereAt(c, a.Time)
			violated := (a.Kind == m.Present && wh != a.Location) || (a.Kind == m.Absent && wh == a.Location)
			if violated {
				out = append(out, iss("A001", a.ID, c, a.Kind.Render(), wh))
			}
		}
	}
	return out
}

func (w *world) warningsH() []issue {
	s, E := w.s, w.final
	var out []issue
	for _, h := range s.Handouts {
		c := h.Character
		if h.Items != nil {
			for _, i := range itemIds(s) {
				if E.Holder(i) == (m.Holder{Kind: m.HolderChar, ID: c}) && !contains(*h.Items, i) {
					out = append(out, iss("H003", c, i))
				}
			}
		}
		if h.Knows != nil {
			for _, f := range factIds(s) {
				if E.Knows(c, f) && !contains(*h.Knows, f) {
					out = append(out, iss("H005", c, f))
				}
			}
		}
	}
	for _, b := range s.Board {
		for _, i := range itemIds(s) {
			if E.Holder(i) == (m.Holder{Kind: m.HolderPlace, ID: b.Location}) && !contains(b.Items, i) {
				out = append(out, iss("H007", b.Location, i))
			}
		}
	}
	return out
}

// checkT012 は observe の対象 x が、同じ時刻に始まる move で移動している場合。
func (w *world) checkT012() []Diag {
	var out []Diag
	for _, o := range w.sorted {
		for _, x := range observed(o.Kind) {
			for _, mv := range w.sorted {
				if mv.Time == o.Time && contains(moved(mv.Kind), x) {
					out = append(out, warnD("T012", []string{x, mv.ID}, ptr(o.ID)))
				}
			}
		}
	}
	return out
}

func (w *world) checkPost() []Diag {
	var out []Diag
	for _, x := range w.postErrors() {
		out = append(out, errD(x.code, x.args, nil))
	}
	for _, x := range append(w.warningsT009(), w.warningsH()...) {
		out = append(out, warnD(x.code, x.args, nil))
	}
	return append(out, w.checkT012()...)
}
