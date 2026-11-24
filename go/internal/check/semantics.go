package check

import (
	"sort"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// Semantics.lean に対応する: 移動時間・知覚、状態と1イベントの効果、居場所の区間、入手可能。

// ---------------------------------------------------------------- 汎用

func dedup[T comparable](l []T) []T {
	seen := map[T]bool{}
	var out []T
	for _, x := range l {
		if !seen[x] {
			seen[x] = true
			out = append(out, x)
		}
	}
	return out
}

func contains[T comparable](l []T, x T) bool {
	for _, y := range l {
		if y == x {
			return true
		}
	}
	return false
}

func ptr[T any](x T) *T { return &x }

// ---------------------------------------------------------------- イベントの属性 (§1.3)

func participants(k m.EventKind) []string {
	switch k.Kind {
	case m.Scene:
		return k.Participants
	case m.Transfer, m.Tell:
		return []string{k.Src, k.Dst}
	default:
		return []string{k.Character}
	}
}

func actors(k m.EventKind) []string {
	switch k.Kind {
	case m.Scene:
		return k.Participants
	case m.Transfer, m.Tell:
		return []string{k.Src}
	default:
		return participants(k)
	}
}

func itemOf(k m.EventKind) (string, bool) {
	switch k.Kind {
	case m.Transfer, m.Pickup, m.Drop, m.Use, m.Consume:
		return k.Item, true
	}
	return "", false
}

// holderRole はアイテムを扱うイベントの所持者(transfer は from)。
func holderRole(k m.EventKind) string {
	switch k.Kind {
	case m.Transfer:
		return k.Src
	case m.Pickup, m.Drop, m.Use, m.Consume:
		return k.Character
	}
	return ""
}

func observed(k m.EventKind) []string {
	if k.Kind == m.Observe {
		return k.Targets
	}
	return nil
}

func moved(k m.EventKind) []string {
	if k.Kind == m.Move {
		return []string{k.Character}
	}
	return nil
}

// sortedEvents は正規順序 (at 昇順, id 昇順)。同じキーは入力の順を保つ。
func sortedEvents(s *m.Scenario) []m.Event {
	out := append([]m.Event(nil), s.Events...)
	sort.SliceStable(out, func(i, j int) bool {
		a, b := out[i], out[j]
		return a.Time < b.Time || (a.Time == b.Time && a.ID < b.ID)
	})
	return out
}

func findEvent(s *m.Scenario, id string) (m.Event, bool) {
	for _, e := range s.Events {
		if e.ID == id {
			return e, true
		}
	}
	return m.Event{}, false
}

// ---------------------------------------------------------------- 移動時間と知覚 (§1.2)

func edgeLookup(es []m.Edge, a, b string) (int, bool) {
	for _, e := range es {
		if (e.Src == a && e.Dst == b) || (e.Bidirectional && e.Src == b && e.Dst == a) {
			return e.Minutes, true
		}
	}
	return 0, false
}

func findLocation(s *m.Scenario, l string) (m.Location, bool) {
	for _, x := range s.Locations {
		if x.ID == l {
			return x, true
		}
	}
	return m.Location{}, false
}

func areaOf(s *m.Scenario, l string) *string {
	if x, ok := findLocation(s, l); ok {
		return x.Area
	}
	return nil
}

func isPublic(s *m.Scenario, l string) bool {
	x, ok := findLocation(s, l)
	return ok && x.Public
}

func isNpc(s *m.Scenario, c string) bool {
	for _, x := range s.Characters {
		if x.ID == c {
			return x.NPC
		}
	}
	return false
}

func travelTime(s *m.Scenario, a, b string) (int, bool) {
	if v, ok := edgeLookup(s.Travel, a, b); ok {
		return v, true
	}
	x, y := areaOf(s, a), areaOf(s, b)
	if x == nil || y == nil {
		return 0, false
	}
	if *x == *y {
		for _, ar := range s.Areas {
			if ar.ID == *x {
				if ar.InternalMinutes != nil {
					return *ar.InternalMinutes, true
				}
				return 0, false
			}
		}
		return 0, false
	}
	return edgeLookup(s.AreaTravel, *x, *y)
}

func perceives(s *m.Scenario, a, b string) bool {
	_, ok := edgeLookup(s.Perception, a, b)
	return a == b || ok
}

// ---------------------------------------------------------------- 状態 (§2.1)

// Position はキャラクターの位置。Via は移動中の move の ID(なければ nil)。
type Position struct {
	Dest   string
	Arrive int
	Via    *string
}

// State は状態。書き換えたキーだけを持ち、それ以外は初期状態の値を返す。
type State struct {
	s      *m.Scenario
	pos    map[string]Position
	holder map[string]m.Holder
	knows  map[m.Pair]bool
	dead   map[string]string
}

func initState(s *m.Scenario) *State {
	return &State{s: s, pos: map[string]Position{}, holder: map[string]m.Holder{},
		knows: map[m.Pair]bool{}, dead: map[string]string{}}
}

func (S *State) Pos(c string) Position {
	if p, ok := S.pos[c]; ok {
		return p
	}
	for _, p := range S.s.Placements {
		if p.Character == c {
			return Position{Dest: p.Location, Arrive: S.s.StartTime}
		}
	}
	return Position{Dest: "", Arrive: S.s.StartTime}
}

func (S *State) Holder(i string) m.Holder {
	if h, ok := S.holder[i]; ok {
		return h
	}
	for _, it := range S.s.Items {
		if it.ID == i {
			return it.Initial
		}
	}
	return m.Holder{Kind: m.HolderConsumed}
}

func (S *State) Knows(c, f string) bool {
	if S.knows[m.Pair{Character: c, Fact: f}] {
		return true
	}
	return contains(S.s.InitialKnowledge, m.Pair{Character: c, Fact: f})
}

func (S *State) Dead(c string) (string, bool) {
	d, ok := S.dead[c]
	return d, ok
}

func (S *State) inTransit(c string, t int) bool {
	p := S.Pos(c)
	return p.Via != nil && t < p.Arrive
}

func (S *State) addKnows(cs, fs []string) {
	for _, c := range cs {
		for _, f := range fs {
			S.knows[m.Pair{Character: c, Fact: f}] = true
		}
	}
}

// step は1イベントの効果 (§2.2)。事前条件の違反の有無に関係なく適用する。
func (S *State) step(e m.Event) {
	k := e.Kind
	switch k.Kind {
	case m.Move:
		S.pos[k.Character] = Position{Dest: k.To, Arrive: k.Arrive, Via: ptr(e.ID)}
		if _, d := S.Dead(k.Character); k.Fatal && !d {
			S.dead[k.Character] = e.ID
		}
	case m.Scene:
		S.addKnows(k.Participants, k.Reveals)
	case m.Observe, m.Learn:
		S.addKnows([]string{k.Character}, k.Facts)
	case m.Tell:
		S.addKnows([]string{k.Dst}, k.Facts)
	case m.Transfer:
		S.holder[k.Item] = m.Holder{Kind: m.HolderChar, ID: k.Dst}
	case m.Pickup:
		S.holder[k.Item] = m.Holder{Kind: m.HolderChar, ID: k.Character}
	case m.Drop:
		S.holder[k.Item] = m.Holder{Kind: m.HolderPlace, ID: S.Pos(k.Character).Dest}
	case m.Consume:
		S.holder[k.Item] = m.Holder{Kind: m.HolderConsumed}
	case m.Die:
		if _, d := S.Dead(k.Character); !d {
			S.dead[k.Character] = e.ID
		}
	}
}

// ---------------------------------------------------------------- 実行

// Step は処理の1ステップ: 処理前の状態、イベント、正規順序でそれより前のイベント。
// Pre はこのステップの検査の間だけ有効(次のステップで書き換わる)。
type Step struct {
	Pre     *State
	Ev      m.Event
	Earlier []m.Event
}

// run は正規順序でイベントを処理し、各ステップで visit を呼んでから効果を適用する。終了状態を返す。
// after が nil でなければ、効果を適用した後にも呼ぶ(そのとき Step.Pre は処理後の状態)。
// 判定器と explain は、どちらもこの1つのループでイベントを処理する。
func run(s *m.Scenario, visit, after func(Step)) *State {
	S := initState(s)
	evs := sortedEvents(s)
	for i, e := range evs {
		st := Step{Pre: S, Ev: e, Earlier: evs[:i]}
		if visit != nil {
			visit(st)
		}
		S.step(e)
		if after != nil {
			after(st)
		}
	}
	return S
}

// ---------------------------------------------------------------- 死亡時刻・居場所の区間・時刻での居場所 (§2.3, §2.4)

type segment struct {
	Loc        string
	From, Till int
}

type world struct {
	s      *m.Scenario
	final  *State
	sorted []m.Event
}

func (w *world) deathTime(c string) (int, bool) {
	d, ok := w.final.Dead(c)
	if !ok {
		return 0, false
	}
	e, ok := findEvent(w.s, d)
	if !ok {
		return 0, false
	}
	if e.Kind.Kind == m.Move {
		return e.Kind.Arrive, true
	}
	return e.Time, true
}

func (w *world) segments(c string) []segment {
	type mv struct {
		dep int
		to  string
		arr int
	}
	var moves []mv
	for _, e := range w.sorted {
		if e.Kind.Kind == m.Move && e.Kind.Character == c {
			moves = append(moves, mv{e.Time, e.Kind.To, e.Kind.Arrive})
		}
	}
	cur := initState(w.s).Pos(c).Dest
	start := w.s.StartTime
	var raw []segment
	for _, x := range moves {
		raw = append(raw, segment{cur, start, x.dep})
		cur, start = x.to, x.arr
	}
	raw = append(raw, segment{cur, start, w.s.EndTime})
	d, dead := w.deathTime(c)
	var out []segment
	for _, sg := range raw {
		if dead && d < sg.Till {
			sg.Till = d
		}
		if sg.From < sg.Till {
			out = append(out, sg)
		}
	}
	return out
}

func (w *world) whereAlive(c string, t int) string {
	for _, sg := range w.segments(c) {
		if sg.From <= t && t < sg.Till {
			return sg.Loc
		}
	}
	return "transit"
}

func (w *world) whereAt(c string, t int) string {
	if d, ok := w.deathTime(c); ok && d <= t {
		return "dead"
	}
	return w.whereAlive(c, t)
}

// obtainable は入手可能 (§2.5): NPC 以外が終了時に知っている、またはいずれかの手がかりで明かされる。
func (w *world) obtainable(f string) bool {
	for _, c := range w.s.Characters {
		if !c.NPC && w.final.Knows(c.ID, f) {
			return true
		}
	}
	for _, cl := range w.s.Clues {
		if contains(cl.Reveals, f) {
			return true
		}
	}
	return false
}
