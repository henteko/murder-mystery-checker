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

// playerCount はプレイヤー(NPC 以外)の数。
func (w *world) playerCount() int {
	n := 0
	for _, c := range w.s.Characters {
		if !c.NPC {
			n++
		}
	}
	return n
}

// clueOnly は手がかりからしか手に入らない真相の知識: どのプレイヤーも終了時に知らず、どれかの手がかりが明かす。
func (w *world) clueOnly() []string {
	var out []string
	for _, f := range w.s.SolutionFacts {
		known := false
		for _, c := range w.s.Characters {
			if !c.NPC && w.final.Knows(c.ID, f) {
				known = true
				break
			}
		}
		if known {
			continue
		}
		for _, cl := range w.s.Clues {
			if contains(cl.Reveals, f) {
				out = append(out, f)
				break
			}
		}
	}
	return out
}

// coverable は、d 枚以内の手がかりで ns の知識をすべて明かせるか(Post.lean の coverable と同じ探索)。
func coverable(cl []m.Clue, ns []string, d int) bool {
	if len(ns) == 0 {
		return true
	}
	if d == 0 {
		return false
	}
	f := ns[0]
	for _, c := range cl {
		if !contains(c.Reveals, f) {
			continue
		}
		var rest []string
		for _, x := range ns {
			if !contains(c.Reveals, x) {
				rest = append(rest, x)
			}
		}
		if coverable(cl, rest, d-1) {
			return true
		}
	}
	return false
}

// coverR は、回 i で引けるカード pools[i] と回ごとの残りの枚数 caps のもとで、k 枚以内で ns の知識を
// すべて明かせるか(Post.lean の coverR と同じ探索。caps は探索の途中で書き換えて戻す)。
func coverR(pools [][]m.Clue, caps []int, ns []string, k int) bool {
	if len(ns) == 0 {
		return true
	}
	if k == 0 {
		return false
	}
	f := ns[0]
	for i := range pools {
		if caps[i] <= 0 {
			continue
		}
		for _, c := range pools[i] {
			if !contains(c.Reveals, f) {
				continue
			}
			var rest []string
			for _, x := range ns {
				if !contains(c.Reveals, x) {
					rest = append(rest, x)
				}
			}
			caps[i]--
			ok := coverR(pools, caps, rest, k-1)
			caps[i]++
			if ok {
				return true
			}
		}
	}
	return false
}

// pool は回 r で引ける探索カード(Post.lean の Scenario.pool)。
func (w *world) pool(r m.Round) []m.Clue {
	if r.Clues == nil {
		return w.s.Clues
	}
	var out []m.Clue
	for _, c := range w.s.Clues {
		if contains(*r.Clues, c.ID) {
			out = append(out, c)
		}
	}
	return out
}

// rounds は回ごとに引けるカード、回ごとに引ける枚数、その合計 D。
func (w *world) rounds(rs []m.Round) (pools [][]m.Clue, caps []int, total int) {
	for _, r := range rs {
		pools = append(pools, w.pool(r))
		caps = append(caps, r.Draws*w.playerCount())
		total += r.Draws * w.playerCount()
	}
	return
}

// drawable は探索カード c をどれかの回で引けるか(1人の枚数が 1 以上で、c がその回のカードに含まれる)。
func drawable(rs []m.Round, c m.Clue) bool {
	for _, r := range rs {
		if r.Draws > 0 && (r.Clues == nil || contains(*r.Clues, c.ID)) {
			return true
		}
	}
	return false
}

// warningsK009 / issuesK010 / warningsK011 は探索フェイズの検査 (§4.4)。
func (w *world) warningsK009() []issue {
	if w.s.Exploration == nil {
		return nil
	}
	_, _, d := w.rounds(w.s.Exploration)
	if d < len(w.s.Clues) {
		return []issue{iss("K009", strconv.Itoa(len(w.s.Clues)), strconv.Itoa(d))}
	}
	return nil
}

func (w *world) issuesK010() []issue {
	if w.s.Exploration == nil {
		return nil
	}
	pools, caps, d := w.rounds(w.s.Exploration)
	if coverR(pools, caps, w.clueOnly(), d) {
		return nil
	}
	return []issue{iss("K010", strconv.Itoa(d))}
}

func (w *world) warningsK011() []issue {
	if w.s.Exploration == nil {
		return nil
	}
	var out []issue
	for _, c := range w.s.Clues {
		if !drawable(w.s.Exploration, c) {
			out = append(out, iss("K011", c.ID))
		}
	}
	return out
}

func (w *world) checkPost() []Diag {
	var out []Diag
	for _, x := range append(w.postErrors(), w.issuesK010()...) {
		out = append(out, errD(x.code, x.args, nil))
	}
	for _, x := range append(append(append(w.warningsT009(), w.warningsH()...), w.warningsK009()...), w.warningsK011()...) {
		out = append(out, warnD(x.code, x.args, nil))
	}
	return append(out, w.checkT012()...)
}
