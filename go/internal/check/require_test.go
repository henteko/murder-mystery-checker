package check

import (
	"testing"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

func TestEvalRequirement(t *testing.T) {
	s, err := m.ParseScenario([]byte(statsScenario))
	if err != nil {
		t.Fatal(err)
	}
	st, err := ComputeStats(s)
	if err != nil {
		t.Fatal(err)
	}
	cases := []struct {
		expr  string
		ok    bool
		value *float64 // nil なら値を求められない
	}{
		{"score>=0", true, ptr(st.Complexity.Score)},
		{"score>100", false, ptr(st.Complexity.Score)},
		{"axis.branching > 0", true, ptr(round4(st.Complexity.Axes[4].Score * 100))},
		{"branching.patterns==8", true, ptr(8.0)},
		{"min(branching.players.pivotal)==0", true, ptr(0.0)}, // c の選択は結末を変えない
		{"max(branching.players.pivotal)==1", true, ptr(1.0)},
		{"avg(branching.players.pivotal)==0.5", true, ptr(0.5)},
		{"count(branching.players)==2", true, ptr(2.0)},
		{"count(padding.empty_clues)==0", false, ptr(1.0)},
		{"sum(knowledge.solution.sources)>=5", true, ptr(6.0)},
		{"check.errors>=0", true, nil},                         // 値は検査結果による
		{"branching.players.pivotal>0", false, nil},            // 集計がない
		{"padding.idle_moves==0", false, nil},                  // 配列
		{"no.such.key>0", false, nil},                          // キーがない
		{"axis.nothing>0", false, nil},                         // 軸がない
		{"count(knowledge.solution.clues)==3", true, ptr(3.0)}, // 配列を辿って平らにする: f2 の x1, x4、f3 の x2
	}
	for _, c := range cases {
		r, err := EvalRequirement(st, c.expr)
		if err != nil {
			t.Errorf("%s: %v", c.expr, err)
			continue
		}
		if r.OK != c.ok {
			t.Errorf("%s: ok=%v want %v (%+v)", c.expr, r.OK, c.ok, r)
		}
		if c.value != nil && (r.Value == nil || *r.Value != *c.value) {
			t.Errorf("%s: value=%v want %v", c.expr, r.Value, *c.value)
		}
		if c.value == nil && !c.ok && r.Value != nil {
			t.Errorf("%s: value should be unavailable, got %v", c.expr, *r.Value)
		}
		if !r.OK && r.Message == "" {
			t.Errorf("%s: failed without message", c.expr)
		}
	}
	for _, bad := range []string{"score", "score >= x", ">= 3", "score => 3", "median(score)>1"} {
		if ParseRequirement(bad) == nil {
			t.Errorf("%q should be a syntax error", bad)
		}
	}
	// 探索がなければ探索の軸は対象外: 条件は満たさない
	s.Exploration = nil
	st2, _ := ComputeStats(s)
	if r, _ := EvalRequirement(st2, "axis.exploration>=0"); r.OK || r.Value != nil {
		t.Errorf("non-applicable axis: %+v", r)
	}
}
