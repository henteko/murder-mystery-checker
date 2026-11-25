package check

import "math"

// 複雑度のスコア(0〜100)。stats の指標から計算する。式は docs/stats.md の「複雑度のスコア」。
// 式(項目・参照値・重み)を変えたら ComplexityVersion を上げる。

// ComplexityVersion は複雑度の式の版。
const ComplexityVersion = 1

// Complexity は複雑度のスコアと内訳。
type Complexity struct {
	Score   float64     `json:"score"`
	Version int         `json:"version"`
	Axes    []AxisScore `json:"axes"`
}

// AxisScore は軸1つ。Applicable が false の軸はスコアに含めない。
type AxisScore struct {
	Name       string  `json:"name"`
	Applicable bool    `json:"applicable"`
	Weight     float64 `json:"weight"`
	Score      float64 `json:"score"`
	Terms      []Term  `json:"terms"`
}

// Term は軸の項目1つ。Score は 0〜1。Ref があれば Score = Value / (Value + Ref)。
type Term struct {
	Name  string   `json:"name"`
	Value float64  `json:"value"`
	Ref   *float64 `json:"ref,omitempty"`
	Score float64  `json:"score"`
}

// sat は値 x を 0〜1 に写す: x = ref のとき 0.5。
func sat(name string, x, ref float64) Term {
	s := 0.0
	if x > 0 {
		s = x / (x + ref)
	}
	return Term{Name: name, Value: round4(x), Ref: ptr(ref), Score: round4(s)}
}

// ratio はすでに 0〜1 の値。
func ratio(name string, x float64) Term {
	x = math.Max(0, math.Min(1, x))
	return Term{Name: name, Value: round4(x), Score: round4(x)}
}

func axis(name string, applicable bool, terms ...Term) AxisScore {
	a := AxisScore{Name: name, Applicable: applicable, Terms: terms}
	if applicable && len(terms) > 0 {
		for _, t := range terms {
			a.Score += t.Score
		}
		a.Score = round4(a.Score / float64(len(terms)))
		a.Weight = 1
	}
	if a.Terms == nil {
		a.Terms = []Term{}
	}
	return a
}

func computeComplexity(st *Stats) Complexity {
	z, t, k, b, pd := st.Size, st.Timeline, st.Knowledge, st.Branching, st.Padding
	players := math.Max(1, float64(z.Players))
	// 水増し(padding.go)は数えない
	idle := float64(len(pd.IdleMoves))
	locations := float64(z.Locations - len(pd.UnusedLocations))
	events := float64(z.Events) - idle
	moves := float64(t.Moves) - idle
	eph := 0.0
	if t.playerHours > 0 {
		eph = float64(t.playerEvents-st.idlePlayerMoves) / t.playerHours
	}
	claims := 0.0
	for _, f := range st.claims {
		if !contains(pd.UnusedFacts, f) {
			claims++
		}
	}

	believed := 0
	for _, l := range k.Lies {
		if len(l.BelievedBy) > 0 {
			believed++
		}
	}
	fragile := 0.0
	for _, s := range k.Solution {
		if s.Sources <= 1 {
			fragile++
		}
	}
	if len(k.Solution) > 0 {
		fragile /= float64(len(k.Solution))
	}

	var explore AxisScore
	if e := st.Exploration; e != nil && e.Draws != nil && *e.Draws > 0 {
		tight := 1.0
		if e.MinCards >= 0 {
			tight = float64(e.MinCards) / float64(*e.Draws)
		}
		miss := 1.0
		if e.RandomCover != nil {
			miss = 1 - *e.RandomCover
		}
		explore = axis("exploration", true,
			sat("cards", float64(e.Cards-len(pd.EmptyClues)), 12),
			ratio("tightness", tight),
			ratio("random_miss", miss))
	} else {
		explore = axis("exploration", false)
	}

	var branch AxisScore
	if b.Enumerated && b.Patterns > 0 {
		piv := 0.0
		for _, p := range b.Players {
			piv += p.Pivotal
		}
		if len(b.Players) > 0 {
			piv /= float64(len(b.Players))
		}
		branch = axis("branching", true,
			sat("log2_patterns", math.Max(0, math.Log2(float64(b.Patterns))-st.irrelevantBits), 6),
			sat("entropy_bits", b.EntropyBits, 1.5),
			ratio("mean_pivotal", piv),
			sat("goal_conflicts", float64(len(b.GoalConflicts)), 3))
	} else {
		branch = axis("branching", false)
	}

	axes := []AxisScore{
		axis("size", true,
			sat("players", float64(z.Players), 4),
			sat("locations", locations, 8),
			sat("events", events, 50)),
		axis("timeline", true,
			sat("events_per_player_hour", eph, 3),
			sat("moves_per_player", moves/players, 6),
			sat("encounters", float64(t.Encounters), 5)),
		axis("knowledge", true,
			sat("believed_lies", float64(believed), 2),
			sat("claims", claims, 10),
			sat("max_relay_depth", float64(k.MaxRelayDepth), 2),
			ratio("fragile_solution", fragile)),
		explore,
		branch,
	}
	c := Complexity{Version: ComplexityVersion, Axes: axes}
	wsum := 0.0
	for _, a := range axes {
		c.Score += a.Weight * a.Score
		wsum += a.Weight
	}
	c.Score = math.Round(c.Score/wsum*1000) / 10
	return c
}
