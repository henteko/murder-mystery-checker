package check

import (
	"errors"
	"math"
	"math/big"
	"sort"
	"strings"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// シナリオの複雑度の指標(mmcheck stats)。検出結果ではない報告なので仕様(docs/spec.md)と Lean の
// 対象外で、Go 側だけの機能。指標の意味は docs/stats.md。
//
// 意味論(終了状態・区間・入手可能・実効制約・パターン)は判定器と同じ関数を使う。

// Stats はシナリオの複雑度の指標。
type Stats struct {
	Complexity  Complexity        `json:"complexity"`
	Check       CheckSummary      `json:"check"`
	Size        SizeStats         `json:"size"`
	Timeline    TimelineStats     `json:"timeline"`
	Knowledge   KnowledgeStats    `json:"knowledge"`
	Exploration *ExplorationStats `json:"exploration,omitempty"`
	Branching   BranchingStats    `json:"branching"`
	Padding     PaddingStats      `json:"padding"`

	// irrelevantBits は結末に関係しない選択の定義域の大きさの log₂ の合計(複雑度で差し引く)
	irrelevantBits float64
	// claims は証言の ID、idlePlayerMoves はプレイヤーの往復の move の数
	claims          []string
	idlePlayerMoves int
}

// CheckSummary は mmcheck check の検出結果の件数。
type CheckSummary struct {
	Errors   int `json:"errors"`
	Warnings int `json:"warnings"`
}

// SizeStats は規模。
type SizeStats struct {
	Players     int `json:"players"`
	NPCs        int `json:"npcs"`
	Locations   int `json:"locations"`
	Items       int `json:"items"`
	Events      int `json:"events"`
	Facts       int `json:"facts"`
	FalseFacts  int `json:"false_facts"`
	Claims      int `json:"claims"`
	FalseClaims int `json:"false_claims"`
	Clues       int `json:"clues"`
	Assertions  int `json:"assertions"`
	Goals       int `json:"goals"`
	Choices     int `json:"choices"`
	Endings     int `json:"endings"`
}

// TimelineStats はタイムラインの密度。
type TimelineStats struct {
	DurationMinutes int `json:"duration_minutes"`
	Moves           int `json:"moves"`
	// EventsPerPlayerHour は、プレイヤーが参加者のイベントの延べ数を、プレイヤー数 × 時間で割ったもの
	EventsPerPlayerHour float64 `json:"events_per_player_hour"`
	// Encounters は、非公共の場所で2人の居場所の区間が重なった回数(認知の有無を問わない)
	Encounters   int         `json:"encounters"`
	PerCharacter []CharStats `json:"per_character"`

	// playerEvents / playerHours は EventsPerPlayerHour の丸める前の分子と分母
	playerEvents int
	playerHours  float64
}

// CharStats はキャラクターごとのタイムライン。
type CharStats struct {
	ID        string `json:"id"`
	NPC       bool   `json:"npc,omitempty"`
	Events    int    `json:"events"`
	Moves     int    `json:"moves"`
	Locations int    `json:"locations"`
}

// KnowledgeStats は情報の流れ。
type KnowledgeStats struct {
	// MaxRelayDepth は伝聞(tell)の最長の段数。直接得た知識(初期・scene・observe・learn)を 0 とする
	MaxRelayDepth int `json:"max_relay_depth"`
	// MinSolutionSources は真相の知識の入手経路の数の最小値(真相の知識がなければ 0)
	MinSolutionSources int             `json:"min_solution_sources"`
	Solution           []SolutionStats `json:"solution"`
	Lies               []LieStats      `json:"lies"`
	Secrets            int             `json:"secrets"`
}

// SolutionStats は真相の知識1つの入手経路。
type SolutionStats struct {
	Fact string `json:"fact"`
	// HeldBy は終了時に知っているプレイヤー
	HeldBy []string `json:"held_by"`
	// Clues はこの知識を明かす手がかり
	Clues []string `json:"clues"`
	// Sources は len(HeldBy) + len(Clues)
	Sources int `json:"sources"`
	// RelayDepth は、知っているプレイヤーのうち最も浅い伝聞の段数(誰も知らなければ -1)
	RelayDepth int `json:"relay_depth"`
}

// LieStats は偽の知識1つ。
type LieStats struct {
	Fact string `json:"fact"`
	// BelievedBy は終了時に知っている(信じている)プレイヤー
	BelievedBy []string `json:"believed_by"`
	// Refuters は否定する知識のうち入手可能なものの数
	Refuters int `json:"refuters"`
}

// ExplorationStats は探索フェイズの厳しさ。
type ExplorationStats struct {
	Cards int `json:"cards"`
	// Draws は引ける合計 D(exploration がなければ nil)
	Draws *int `json:"draws,omitempty"`
	// ClueOnly は手がかりからしか手に入らない真相の知識の数
	ClueOnly int `json:"clue_only"`
	// MinCards はそれらをすべて明かすのに要る最小の枚数(明かせなければ -1)
	MinCards int `json:"min_cards"`
	// Slack は Draws − MinCards
	Slack *int `json:"slack,omitempty"`
	// RandomCover は D 枚を無作為に引いたときに真相のカードが揃う確率(計算しなかったら nil)
	RandomCover *float64 `json:"random_cover,omitempty"`
}

// BranchingStats は分岐。
type BranchingStats struct {
	Variables   int    `json:"variables"`
	Assignments string `json:"assignments"`
	// Enumerated は数え上げたか(割り当て数が G007 の上限を超えると false で、以下は空)
	Enumerated bool `json:"enumerated"`
	Patterns   int  `json:"patterns"`
	// Outcomes はパターンごとの結末(エンディングの ID。複数なら "+" で連結、なければ "")の分布
	Outcomes []OutcomeStats `json:"outcomes"`
	// EntropyBits は、パターンを等しく重み付けしたときの結末の分布のエントロピー
	EntropyBits float64 `json:"entropy_bits"`
	// Players はプレイヤーごとの選択の影響
	Players []PlayerInfluence `json:"players"`
	// GoalConflicts は owner の違うゴールの組で、どちらも達成できるが同時には達成できないもの
	GoalConflicts [][2]string `json:"goal_conflicts"`
}

// OutcomeStats は結末1つ。
type OutcomeStats struct {
	Ending   string  `json:"ending"`
	Patterns int     `json:"patterns"`
	Share    float64 `json:"share"`
}

// PlayerInfluence はプレイヤーの選択の影響。
type PlayerInfluence struct {
	ID      string `json:"id"`
	Choices int    `json:"choices"`
	// Pivotal は、ほかのプレイヤーの選択の組(パターンに現れるもの)のうち、このプレイヤーの選択で
	// 結末が変わりうるものの割合
	Pivotal float64 `json:"pivotal"`
}

// ErrStructure は R 群の違反があって指標を計算できないこと。
var ErrStructure = errors.New("R 群(構造・参照整合)の違反があるため計算できない: mmcheck check で先に直してください")

// ComputeStats はシナリオの複雑度の指標を計算する。R 群の違反があれば ErrStructure。
func ComputeStats(s *m.Scenario) (*Stats, error) {
	if len(checkR(s)) > 0 {
		return nil, ErrStructure
	}
	depth := map[m.Pair]int{}
	final := run(s, func(st Step) { relay(st, depth) }, nil)
	w := &world{s: s, final: final, sorted: sortedEvents(s)}
	st := &Stats{Size: w.sizeStats(), Timeline: w.timelineStats(), Knowledge: w.knowledgeStats(depth),
		Exploration: w.explorationStats(), Branching: w.branchingStats(), Padding: w.paddingStats()}
	for _, c := range s.Choices {
		if contains(st.Padding.IrrelevantChoices, c.ID) {
			n := 2
			if c.Values != nil {
				n = len(dedup(*c.Values))
			}
			st.irrelevantBits += math.Log2(float64(n))
		}
	}
	for _, f := range s.Facts {
		if f.AboutEvent != nil && f.ClaimedAt != nil {
			st.claims = append(st.claims, f.ID)
		}
	}
	for _, id := range st.Padding.IdleMoves {
		if e, ok := findEvent(s, id); ok && !isNpc(s, e.Kind.Character) {
			st.idlePlayerMoves++
		}
	}
	for _, d := range Check(s) {
		if d.Sev == Error {
			st.Check.Errors++
		} else {
			st.Check.Warnings++
		}
	}
	st.Complexity = computeComplexity(st)
	return st, nil
}

func (w *world) players() []string {
	var out []string
	for _, c := range w.s.Characters {
		if !c.NPC {
			out = append(out, c.ID)
		}
	}
	return out
}

func (w *world) sizeStats() SizeStats {
	s := w.s
	z := SizeStats{Locations: len(s.Locations), Items: len(s.Items), Events: len(s.Events),
		Facts: len(s.Facts), Clues: len(s.Clues), Assertions: len(s.Assertions), Goals: len(s.Goals),
		Choices: len(s.Choices), Endings: len(s.Endings)}
	for _, c := range s.Characters {
		if c.NPC {
			z.NPCs++
		} else {
			z.Players++
		}
	}
	for _, f := range s.Facts {
		claim := f.AboutEvent != nil && f.ClaimedAt != nil
		if claim {
			z.Claims++
		}
		if !f.Truth {
			z.FalseFacts++
			if claim {
				z.FalseClaims++
			}
		}
	}
	return z
}

func (w *world) timelineStats() TimelineStats {
	s := w.s
	t := TimelineStats{DurationMinutes: s.EndTime - s.StartTime}
	ps := w.players()
	playerEvents := 0
	for _, c := range s.Characters {
		cs := CharStats{ID: c.ID, NPC: c.NPC}
		locs := map[string]bool{initState(s).Pos(c.ID).Dest: true}
		for _, e := range s.Events {
			if contains(participants(e.Kind), c.ID) {
				cs.Events++
			}
			if e.Kind.Kind == m.Move && e.Kind.Character == c.ID {
				cs.Moves++
				locs[e.Kind.To] = true
			}
		}
		cs.Locations = len(locs)
		if !c.NPC {
			playerEvents += cs.Events
		}
		t.Moves += cs.Moves
		t.PerCharacter = append(t.PerCharacter, cs)
	}
	sort.SliceStable(t.PerCharacter, func(i, j int) bool { return t.PerCharacter[i].ID < t.PerCharacter[j].ID })
	t.playerEvents = playerEvents
	if hours := float64(t.DurationMinutes) / 60; len(ps) > 0 && hours > 0 {
		t.playerHours = float64(len(ps)) * hours
		t.EventsPerPlayerHour = round2(float64(playerEvents) / t.playerHours)
	}
	ids := characterIds(s)
	for i := range ids {
		for j := i + 1; j < len(ids); j++ {
			for _, s1 := range w.segments(ids[i]) {
				for _, s2 := range w.segments(ids[j]) {
					if s1.Loc == s2.Loc && !isPublic(s, s1.Loc) && max(s1.From, s2.From) < min(s1.Till, s2.Till) {
						t.Encounters++
					}
				}
			}
		}
	}
	return t
}

// relay は、イベントで新たに知った (キャラクター, 知識) に伝聞の段数をつける(効果の適用前に呼ぶ)。
func relay(st Step, depth map[m.Pair]int) {
	k := st.Ev.Kind
	set := func(c string, f string, d int) {
		p := m.Pair{Character: c, Fact: f}
		if _, ok := depth[p]; !ok && !st.Pre.Knows(c, f) {
			depth[p] = d
		}
	}
	switch k.Kind {
	case m.Tell:
		for _, f := range k.Facts {
			set(k.Dst, f, depth[m.Pair{Character: k.Src, Fact: f}]+1)
		}
	case m.Scene:
		for _, c := range k.Participants {
			for _, f := range k.Reveals {
				set(c, f, 0)
			}
		}
	case m.Observe, m.Learn:
		for _, f := range k.Facts {
			set(k.Character, f, 0)
		}
	}
}

func (w *world) knowledgeStats(depth map[m.Pair]int) KnowledgeStats {
	s := w.s
	ks := KnowledgeStats{Solution: []SolutionStats{}, Lies: []LieStats{}}
	for _, d := range depth {
		ks.MaxRelayDepth = max(ks.MaxRelayDepth, d)
	}
	ps := w.players()
	knowers := func(f string) []string {
		out := []string{}
		for _, c := range ps {
			if w.final.Knows(c, f) {
				out = append(out, c)
			}
		}
		return out
	}
	for i, f := range dedup(s.SolutionFacts) {
		ss := SolutionStats{Fact: f, HeldBy: knowers(f), Clues: []string{}, RelayDepth: -1}
		for _, cl := range s.Clues {
			if contains(cl.Reveals, f) {
				ss.Clues = append(ss.Clues, cl.ID)
			}
		}
		for _, c := range ss.HeldBy {
			d := depth[m.Pair{Character: c, Fact: f}] // 初期知識は 0
			if ss.RelayDepth < 0 || d < ss.RelayDepth {
				ss.RelayDepth = d
			}
		}
		ss.Sources = len(ss.HeldBy) + len(ss.Clues)
		if i == 0 || ss.Sources < ks.MinSolutionSources {
			ks.MinSolutionSources = ss.Sources
		}
		ks.Solution = append(ks.Solution, ss)
	}
	for _, f := range s.Facts {
		if f.Truth {
			continue
		}
		ls := LieStats{Fact: f.ID, BelievedBy: knowers(f.ID)}
		for _, r := range f.ContradictedBy {
			if w.obtainable(r) {
				ls.Refuters++
			}
		}
		ks.Lies = append(ks.Lies, ls)
	}
	sort.SliceStable(ks.Lies, func(i, j int) bool { return ks.Lies[i].Fact < ks.Lies[j].Fact })
	var secrets []string
	for _, g := range s.Goals {
		secrets = append(secrets, g.Conceals...)
	}
	ks.Secrets = len(dedup(secrets))
	return ks
}

// minCover は ns をすべて明かすのに要る最小の手がかりの枚数(明かせなければ -1)。
func minCover(cl []m.Clue, ns []string) int {
	for d := 0; d <= len(cl); d++ {
		if coverable(cl, ns, d) {
			return d
		}
	}
	return -1
}

// randomCover は n 枚から d 枚を無作為に引いて ns がすべて明かされる確率(包除原理)。
func randomCover(cl []m.Clue, ns []string, d int) float64 {
	n := len(cl)
	if d >= n {
		d = n
	}
	total := new(big.Int).Binomial(int64(n), int64(d))
	sum := new(big.Int)
	for mask := 0; mask < 1<<len(ns); mask++ {
		// mask の知識をどれも明かさないカードの数
		free := 0
		for _, c := range cl {
			hit := false
			for k, f := range ns {
				if mask&(1<<k) != 0 && contains(c.Reveals, f) {
					hit = true
					break
				}
			}
			if !hit {
				free++
			}
		}
		term := new(big.Int)
		if free >= d {
			term.Binomial(int64(free), int64(d))
		}
		if popcount(mask)%2 == 1 {
			sum.Sub(sum, term)
		} else {
			sum.Add(sum, term)
		}
	}
	p, _ := new(big.Rat).SetFrac(sum, total).Float64()
	return round4(p)
}

func popcount(x int) int {
	n := 0
	for ; x > 0; x &= x - 1 {
		n++
	}
	return n
}

func (w *world) explorationStats() *ExplorationStats {
	s := w.s
	if len(s.Clues) == 0 && s.Exploration == nil {
		return nil
	}
	ns := dedup(w.clueOnly())
	es := &ExplorationStats{Cards: len(s.Clues), ClueOnly: len(ns), MinCards: minCover(s.Clues, ns)}
	if s.Exploration != nil {
		d := *s.Exploration * w.playerCount()
		es.Draws = &d
		if es.MinCards >= 0 {
			es.Slack = ptr(d - es.MinCards)
		}
		if len(ns) <= 20 {
			es.RandomCover = ptr(randomCover(s.Clues, ns, d))
		}
	}
	return es
}

// outcome はパターンの結末の表記。
func outcome(sigma assignment, ends []m.Ending) string {
	var hit []string
	for _, e := range ends {
		if eval(sigma, e.Condition) {
			hit = append(hit, e.ID)
		}
	}
	return strings.Join(hit, "+")
}

func (w *world) branchingStats() BranchingStats {
	s := w.s
	doms := domains(s)
	total := big.NewInt(1)
	for _, d := range doms {
		total.Mul(total, big.NewInt(int64(len(d.vals))))
	}
	b := BranchingStats{Variables: len(doms), Assignments: total.String(), Outcomes: []OutcomeStats{},
		Players: []PlayerInfluence{}, GoalConflicts: [][2]string{}}
	if total.Cmp(big.NewInt(gLimit)) > 0 {
		return b
	}
	b.Enumerated = true
	vars := make([]string, len(doms))
	for i, d := range doms {
		vars[i] = d.v
	}
	cons := w.effectiveConstraints()
	ends := sortedEndings(s)
	gs := append([]m.Goal(nil), s.Goals...)
	sort.SliceStable(gs, func(i, j int) bool { return gs[i].ID < gs[j].ID })

	// プレイヤーごとの、ほかのプレイヤーの選択の組 → 現れた結末
	type ctxs map[string]map[string]bool
	owners := map[string]int{}
	for _, c := range s.Choices {
		owners[c.Owner]++
	}
	var pls []string
	for _, p := range w.players() {
		if owners[p] > 0 {
			pls = append(pls, p)
		}
	}
	sort.Strings(pls)
	seen := make([]ctxs, len(pls))
	for i := range seen {
		seen[i] = ctxs{}
	}
	counts := map[string]int{}
	goalTrue := map[string]bool{}
	coTrue := map[[2]string]bool{}

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
		b.Patterns++
		o := outcome(sigma, ends)
		counts[o]++
		for k, p := range pls {
			var key strings.Builder
			for _, c := range s.Choices {
				if c.Owner != p {
					v, _ := sigma.get(c.ID).MarshalJSON()
					key.WriteString(c.ID + "=" + string(v) + ";")
				}
			}
			if seen[k][key.String()] == nil {
				seen[k][key.String()] = map[string]bool{}
			}
			seen[k][key.String()][o] = true
		}
		for x := range gs {
			if sigma.get(gs[x].ID) != boolVal(true) {
				continue
			}
			goalTrue[gs[x].ID] = true
			for y := x + 1; y < len(gs); y++ {
				if sigma.get(gs[y].ID) == boolVal(true) {
					coTrue[[2]string{gs[x].ID, gs[y].ID}] = true
				}
			}
		}
	}
	visit(0)

	for o, n := range counts {
		share := float64(n) / float64(b.Patterns)
		b.EntropyBits -= share * math.Log2(share)
		b.Outcomes = append(b.Outcomes, OutcomeStats{Ending: o, Patterns: n, Share: round4(share)})
	}
	b.EntropyBits = round4(b.EntropyBits)
	sort.SliceStable(b.Outcomes, func(i, j int) bool {
		x, y := b.Outcomes[i], b.Outcomes[j]
		return x.Patterns > y.Patterns || (x.Patterns == y.Patterns && x.Ending < y.Ending)
	})
	for k, p := range pls {
		piv := 0
		for _, os := range seen[k] {
			if len(os) >= 2 {
				piv++
			}
		}
		pi := PlayerInfluence{ID: p, Choices: owners[p]}
		if len(seen[k]) > 0 {
			pi.Pivotal = round4(float64(piv) / float64(len(seen[k])))
		}
		b.Players = append(b.Players, pi)
	}
	for x := range gs {
		for y := x + 1; y < len(gs); y++ {
			g1, g2 := gs[x], gs[y]
			if g1.Owner != g2.Owner && goalTrue[g1.ID] && goalTrue[g2.ID] && !coTrue[[2]string{g1.ID, g2.ID}] {
				b.GoalConflicts = append(b.GoalConflicts, [2]string{g1.ID, g2.ID})
			}
		}
	}
	return b
}

func round2(x float64) float64 { return math.Round(x*100) / 100 }
func round4(x float64) float64 { return math.Round(x*10000) / 10000 }
