package check

import (
	"encoding/json"
	"strconv"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// イベントごとの検査: T / I / K 群 (§4.2〜§4.4)。Events.lean に対応する。

func jsonKey(v any) (string, error) {
	b, err := json.Marshal(v)
	return string(b), err
}

type issue struct {
	code string
	args []string
}

func iss(code string, args ...string) issue { return issue{code, args} }

// lastSameTime は正規順序で e より前にある同時刻のイベントのうち、条件を満たす最後のもの。
func lastSameTime(st Step, p func(m.Event) bool) (m.Event, bool) {
	for i := len(st.Earlier) - 1; i >= 0; i-- {
		e := st.Earlier[i]
		if e.Time == st.Ev.Time && p(e) {
			return e, true
		}
	}
	return m.Event{}, false
}

func issuesT001(s *m.Scenario, st Step) []issue {
	e := st.Ev
	late := e.Kind.Kind == m.Move && e.Kind.Arrive > s.EndTime
	if e.Time < s.StartTime || e.Time > s.EndTime || late {
		return []issue{iss("T001")}
	}
	return nil
}

func issuesMove(s *m.Scenario, st Step) []issue {
	k := st.Ev.Kind
	if k.Kind != m.Move {
		return nil
	}
	frm := st.Pre.Pos(k.Character).Dest
	if frm == k.To {
		return []issue{iss("T004", k.Character, frm)}
	}
	if k.Mode != "walk" {
		return nil
	}
	t, ok := travelTime(s, frm, k.To)
	if !ok {
		return []issue{iss("T002", k.Character, frm, k.To)}
	}
	// Nat の引き算(負になれば 0)
	d := k.Arrive - st.Ev.Time
	if d < 0 {
		d = 0
	}
	if d < t {
		return []issue{iss("T003", k.Character, frm, k.To, strconv.Itoa(t))}
	}
	return nil
}

func issuesParticipant(st Step, c string) []issue {
	var out []issue
	if e, ok := lastSameTime(st, func(e m.Event) bool { return contains(participants(e.Kind), c) }); ok {
		out = append(out, iss("T005", c, e.ID))
	}
	if st.Pre.inTransit(c, st.Ev.Time) {
		via := ""
		if v := st.Pre.Pos(c).Via; v != nil {
			via = *v
		}
		out = append(out, iss("T006", c, via))
	}
	if d, ok := st.Pre.Dead(c); ok {
		out = append(out, iss("T010", c, d))
	}
	return out
}

func issuesParticipants(st Step) []issue {
	var out []issue
	for _, c := range participants(st.Ev.Kind) {
		out = append(out, issuesParticipant(st, c)...)
	}
	return out
}

// atLoc は場所の条件。参加者は移動中なら抑制、参加者でない (targets) は移動中なら "transit"。
func atLoc(S *State, t int, c, loc string, participant bool) []issue {
	if S.inTransit(c, t) {
		if participant {
			return nil
		}
		return []issue{iss("T007", c, loc, "transit")}
	}
	if d := S.Pos(c).Dest; d != loc {
		return []issue{iss("T007", c, loc, d)}
	}
	return nil
}

func issuesPlace(s *m.Scenario, st Step) []issue {
	S, t, k := st.Pre, st.Ev.Time, st.Ev.Kind
	var out []issue
	switch k.Kind {
	case m.Scene:
		for _, c := range k.Participants {
			out = append(out, atLoc(S, t, c, k.Location, true)...)
		}
	case m.Observe:
		if !perceives(s, k.Location, k.TargetLocation) {
			out = append(out, iss("T011", k.Character, k.Location, k.TargetLocation))
		}
		out = append(out, atLoc(S, t, k.Character, k.Location, true)...)
		for _, x := range k.Targets {
			out = append(out, atLoc(S, t, x, k.TargetLocation, false)...)
		}
	case m.Transfer, m.Tell:
		a, b := k.Src, k.Dst
		if !S.inTransit(a, t) && !S.inTransit(b, t) && S.Pos(a).Dest != S.Pos(b).Dest {
			out = append(out, iss("T008", a, b, S.Pos(a).Dest, S.Pos(b).Dest))
		}
	}
	return out
}

func issuesItem(st Step) []issue {
	S, e := st.Pre, st.Ev
	i, ok := itemOf(e.Kind)
	if !ok {
		return nil
	}
	var out []issue
	if e2, ok := lastSameTime(st, func(x m.Event) bool { j, ok := itemOf(x.Kind); return ok && j == i }); ok {
		out = append(out, iss("I004", i, e2.ID))
	}
	who := holderRole(e.Kind)
	h := S.Holder(i)
	switch {
	case h.Kind == m.HolderConsumed:
		out = append(out, iss("I002", who, i))
	case e.Kind.Kind == m.Pickup:
		if !S.inTransit(who, e.Time) && h != (m.Holder{Kind: m.HolderPlace, ID: S.Pos(who).Dest}) {
			out = append(out, iss("I003", who, i, h.Render()))
		}
	case h != (m.Holder{Kind: m.HolderChar, ID: who}):
		out = append(out, iss("I001", who, i, h.Render()))
	}
	return out
}

func issuesKnowledge(st Step) []issue {
	S, e := st.Pre, st.Ev
	var out []issue
	if e.Kind.Kind == m.Tell {
		for _, f := range e.Kind.Facts {
			if !S.Knows(e.Kind.Src, f) {
				out = append(out, iss("K001", e.Kind.Src, f))
			}
		}
	}
	for _, a := range actors(e.Kind) {
		for _, f := range e.Requires {
			if !S.Knows(a, f) {
				out = append(out, iss("K002", a, f))
			}
		}
	}
	return out
}

func stepIssues(s *m.Scenario, st Step) []issue {
	var out []issue
	out = append(out, issuesT001(s, st)...)
	out = append(out, issuesMove(s, st)...)
	out = append(out, issuesParticipants(st)...)
	out = append(out, issuesPlace(s, st)...)
	out = append(out, issuesItem(st)...)
	out = append(out, issuesKnowledge(st)...)
	return out
}
