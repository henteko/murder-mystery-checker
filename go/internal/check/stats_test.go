package check

import (
	"errors"
	"math"
	"reflect"
	"strconv"
	"testing"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

const statsScenario = `{
  "spec_version": "0.8.0", "start_time": 0, "end_time": 120,
  "characters": [{"id": "a"}, {"id": "b"}, {"id": "c"}, {"id": "v", "npc": true}],
  "areas": [{"id": "house", "internal_minutes": 1}],
  "locations": [{"id": "hall", "area": "house", "public": true}, {"id": "room", "area": "house"}],
  "placements": [{"character": "a", "location": "hall"}, {"character": "b", "location": "hall"},
                 {"character": "c", "location": "room"}, {"character": "v", "location": "room"}],
  "facts": [{"id": "f1"}, {"id": "f2"}, {"id": "f3"}, {"id": "lie", "truth": false, "contradicted_by": ["f3"]}],
  "initial_knowledge": [{"character": "a", "fact": "f1"}, {"character": "a", "fact": "lie"}],
  "events": [
    {"id": "e1", "at": 10, "kind": "tell", "from": "a", "to": "b", "facts": ["f1"]},
    {"id": "e2", "at": 20, "kind": "move", "character": "b", "to": "room", "arrive": 21},
    {"id": "e3", "at": 30, "kind": "tell", "from": "b", "to": "c", "facts": ["f1"]}
  ],
  "clues": [{"id": "x1", "deck": "d", "reveals": ["f2"]}, {"id": "x2", "deck": "d", "reveals": ["f3"]},
            {"id": "x3", "deck": "d", "reveals": []}, {"id": "x4", "deck": "d", "reveals": ["f2"]}],
  "solution_facts": ["f1", "f2", "f3"],
  "exploration": {"draws_per_player": 1},
  "goals": [{"id": "ga", "owner": "a", "condition": {"eq": {"var": "vb", "value": "a"}}},
            {"id": "gb", "owner": "b", "condition": {"eq": {"var": "vb", "value": "b"}}},
            {"id": "gc", "owner": "c"}],
  "choices": [{"id": "vb", "owner": "b", "values": ["a", "b"]}, {"id": "vc", "owner": "c"}],
  "endings": [{"id": "e_a", "condition": {"eq": {"var": "vb", "value": "a"}}},
              {"id": "e_b", "condition": {"eq": {"var": "vb", "value": "b"}}}]
}`

func TestStats(t *testing.T) {
	s, err := m.ParseScenario([]byte(statsScenario))
	if err != nil {
		t.Fatal(err)
	}
	st, err := ComputeStats(s)
	if err != nil {
		t.Fatal(err)
	}
	if z := st.Size; z.Players != 3 || z.NPCs != 1 || z.FalseFacts != 1 || z.Clues != 4 {
		t.Errorf("size: %+v", z)
	}
	// b と c は 21〜30 に room で居合わせ、v もいる: (b,c), (b,v), (c,v) の3件
	if st.Timeline.Encounters != 3 || st.Timeline.Moves != 1 {
		t.Errorf("timeline: %+v", st.Timeline)
	}
	k := st.Knowledge
	if k.MaxRelayDepth != 2 {
		t.Errorf("max relay depth = %d, want 2 (a → b → c)", k.MaxRelayDepth)
	}
	if f1 := k.Solution[0]; f1.Sources != 3 || f1.RelayDepth != 0 {
		t.Errorf("f1: %+v", f1)
	}
	if k.MinSolutionSources != 1 || len(k.Lies) != 1 || k.Lies[0].Refuters != 1 {
		t.Errorf("knowledge: %+v", k)
	}
	e := st.Exploration
	// 4枚から3枚引いて {x1 か x4} と x2 が揃う確率: 1 − P(x2 なし) − P(x1, x4 ともなし) = 1 − 1/4 − 0 = 0.75
	if e.ClueOnly != 2 || e.MinCards != 2 || *e.Draws != 3 || *e.Slack != 1 || *e.RandomCover != 0.75 {
		t.Errorf("exploration: %+v draws=%v slack=%v cover=%v", e, *e.Draws, *e.Slack, *e.RandomCover)
	}
	b := st.Branching
	// vb × vc × gc = 8 パターン(ga, gb は vb で決まる)。結末は vb だけで決まる
	if !b.Enumerated || b.Patterns != 8 || b.EntropyBits != 1 {
		t.Errorf("branching: %+v", b)
	}
	piv := map[string]float64{}
	for _, p := range b.Players {
		piv[p.ID] = p.Pivotal
	}
	if piv["b"] != 1 || piv["c"] != 0 || len(b.Players) != 2 {
		t.Errorf("players: %+v", b.Players)
	}
	if len(b.GoalConflicts) != 1 || b.GoalConflicts[0] != [2]string{"ga", "gb"} {
		t.Errorf("goal conflicts: %+v", b.GoalConflicts)
	}
}

func TestComplexity(t *testing.T) {
	s, err := m.ParseScenario([]byte(statsScenario))
	if err != nil {
		t.Fatal(err)
	}
	st, err := ComputeStats(s)
	if err != nil {
		t.Fatal(err)
	}
	c := st.Complexity
	if c.Version != ComplexityVersion || len(c.Axes) != 5 || c.Score <= 0 || c.Score >= 100 {
		t.Fatalf("complexity: %+v", c)
	}
	// スコアは適用される軸の平均 × 100
	sum, n := 0.0, 0.0
	for _, a := range c.Axes {
		if a.Applicable {
			sum += a.Score
			n++
		}
	}
	if want := math.Round(sum/n*1000) / 10; c.Score != want {
		t.Errorf("score = %v, want %v", c.Score, want)
	}
	// 探索がなければ探索の軸は対象外
	s.Exploration = nil
	st2, _ := ComputeStats(s)
	if st2.Complexity.Axes[3].Applicable {
		t.Errorf("exploration axis should not apply: %+v", st2.Complexity.Axes[3])
	}
	// 使われている場所を増やすとスコアは上がる(盤面に載せた場所は使われている)
	s.Exploration = []m.Round{{Draws: 1}}
	for i := 0; i < 20; i++ {
		id := "extra" + strconv.Itoa(i)
		s.Locations = append(s.Locations, m.Location{ID: id})
		s.Board = append(s.Board, m.Board{Location: id, Items: []string{}})
	}
	if st3, _ := ComputeStats(s); st3.Complexity.Score <= c.Score {
		t.Errorf("more locations: %v <= %v", st3.Complexity.Score, c.Score)
	}
}

func TestStatsStructureError(t *testing.T) {
	s, err := m.ParseScenario([]byte(`{"spec_version": "0.8.0", "start_time": 0, "end_time": 10,
	  "characters": [{"id": "a"}], "locations": [{"id": "l"}], "placements": []}`))
	if err != nil {
		t.Fatal(err)
	}
	if _, err := ComputeStats(s); !errors.Is(err, ErrStructure) {
		t.Errorf("err = %v, want ErrStructure", err)
	}
}

// 水増しを足しても、水増しとして検出され、複雑度は上がらない。
func TestPaddingDoesNotRaiseScore(t *testing.T) {
	base, err := m.ParseScenario([]byte(statsScenario))
	if err != nil {
		t.Fatal(err)
	}
	st0, err := ComputeStats(base)
	if err != nil {
		t.Fatal(err)
	}
	// 基本のシナリオには、何も明かさないカード x3 と、結末に関係しない c の選択 vc がある
	if st0.Padding.Total != 2 {
		t.Fatalf("base padding: %+v", st0.Padding)
	}
	s, _ := m.ParseScenario([]byte(statsScenario))
	// 誰も使わない場所 cellar と、往復でだけ行く attic
	s.Locations = append(s.Locations, m.Location{ID: "cellar", Area: ptr("house")}, m.Location{ID: "attic", Area: ptr("house")})
	// a が hall → attic → hall と往復するだけ
	s.Events = append(s.Events,
		m.Event{ID: "p1", Time: 40, Kind: m.EventKind{Kind: m.Move, Character: "a", To: "attic", Arrive: 41, Mode: "walk"}},
		m.Event{ID: "p2", Time: 50, Kind: m.EventKind{Kind: m.Move, Character: "a", To: "hall", Arrive: 51, Mode: "walk"}})
	// 誰も知らず、どこからも参照されない証言
	s.Facts = append(s.Facts, m.Fact{ID: "dead_claim", Truth: true, AboutEvent: ptr("e2"), AboutPoint: "at", ClaimedAt: ptr(20)})
	// 何も明かさない手がかり
	s.Clues = append(s.Clues, m.Clue{ID: "blank", Deck: ptr("d"), Reveals: []string{}})
	// 結末にもゴールにも関係しない選択
	s.Choices = append(s.Choices, m.Choice{ID: "vz", Owner: "a"})
	st, err := ComputeStats(s)
	if err != nil {
		t.Fatal(err)
	}
	p := st.Padding
	want := PaddingStats{UnusedLocations: []string{"attic", "cellar"}, IdleMoves: []string{"p1", "p2"},
		UnusedFacts: []string{"dead_claim"}, EmptyClues: []string{"blank", "x3"}, IrrelevantChoices: []string{"vc", "vz"}, Total: 9}
	if !reflect.DeepEqual(p, want) {
		t.Errorf("padding = %+v, want %+v", p, want)
	}
	// 規模・タイムライン・情報・分岐の軸は上がらない(探索は空のカードで無作為に揃う確率が下がるので除く)
	for i, a := range st.Complexity.Axes {
		if a.Name == "exploration" {
			continue
		}
		if b := st0.Complexity.Axes[i]; a.Score > b.Score+1e-9 {
			t.Errorf("axis %s rose: %v -> %v (%+v)", a.Name, b.Score, a.Score, a.Terms)
		}
	}
}

func TestExplorationRounds(t *testing.T) {
	s, err := m.ParseScenario([]byte(statsScenario))
	if err != nil {
		t.Fatal(err)
	}
	// 1 回目は真相に関係のない x3 だけ、2 回目に x1・x2(手がかりからしか得られない真相は f2, f3)
	x3, x12 := []string{"x3"}, []string{"x1", "x2"}
	s.Exploration = []m.Round{{Draws: 1, Clues: &x3}, {Draws: 1, Clues: &x12}}
	st, err := ComputeStats(s)
	if err != nil {
		t.Fatal(err)
	}
	e := st.Exploration
	if e.Draws == nil || *e.Draws != 6 {
		t.Fatalf("draws = %v, want 6", e.Draws)
	}
	want := []RoundStats{{Draws: 3, Cards: 1, Truth: ptr(0)}, {Draws: 3, Cards: 2, Truth: ptr(2)}}
	if !reflect.DeepEqual(e.Rounds, want) {
		t.Errorf("rounds = %+v, want %+v", e.Rounds, want)
	}
	// 1 回の探索(draws_per_player)は回が 1 つ
	s.Exploration = []m.Round{{Draws: 1}}
	st, _ = ComputeStats(s)
	if want := []RoundStats{{Draws: 3, Cards: 4, Truth: ptr(2)}}; !reflect.DeepEqual(st.Exploration.Rounds, want) {
		t.Errorf("rounds = %+v, want %+v", st.Exploration.Rounds, want)
	}
}
