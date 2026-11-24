package check

import (
	"os"
	"path/filepath"
	"reflect"
	"testing"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// explain は Go だけの機能(差分テストの対象外)。ここでは、explain が示す照合の結果が、
// Lean と差分テストで一致している判定器の検出結果と食い違わないことを確かめる。
// explain が意味論を自前で計算していれば、この一致が崩れて落ちる。

func allInputs(t *testing.T) []string {
	ps := oracleInputs(t)
	ex, _ := filepath.Glob(filepath.Join("..", "..", "..", "examples", "*", "scenario.json"))
	return append(ps, ex...)
}

func has(ds []Diag, code string, args ...string) bool {
	for _, d := range ds {
		if d.Code != code || len(d.Args) < len(args) {
			continue
		}
		match := true
		for i, a := range args {
			if d.Args[i] != a {
				match = false
			}
		}
		if match {
			return true
		}
	}
	return false
}

func TestExplainAgreesWithChecker(t *testing.T) {
	n := 0
	for _, p := range allInputs(t) {
		raw, _ := os.ReadFile(p)
		s, err := m.ParseScenario(raw)
		if err != nil {
			continue
		}
		r := Explain(s)
		ds := Check(s)
		if !reflect.DeepEqual(r.Diags, ds) {
			t.Fatalf("%s: explain の検出結果が判定器と違う", p)
		}
		if r.RGated {
			continue
		}
		n++
		// 断言: 「矛盾」⇔ A001
		for _, a := range r.Assertions {
			if got := has(ds, "A001", a.ID, a.Character); a.OK == got {
				t.Errorf("%s: assertion %s/%s: explain ok=%v, checker A001=%v", p, a.ID, a.Character, a.OK, got)
			}
		}
		// 証言: 真で、対象があり、「ずれ」⇔ K008
		for _, c := range r.Claims {
			if c.Truth && c.Found && c.OK == has(ds, "K008", c.Fact) {
				t.Errorf("%s: claim %s: explain ok=%v vs K008", p, c.Fact, c.OK)
			}
		}
		// ハンドアウト: 「食い違い」⇔ H001/H002/H004、「記載漏れ」⇔ H003/H005
		code := map[[2]string]string{{"location", "ng"}: "H001", {"item", "ng"}: "H002", {"fact", "ng"}: "H004",
			{"item", "missing"}: "H003", {"fact", "missing"}: "H005"}
		for _, h := range r.Handouts {
			for _, row := range h.Rows {
				for _, st := range []string{"ng", "missing"} {
					c := code[[2]string{row.Aspect, st}]
					if c == "" {
						continue
					}
					if (row.Status == st) != has(ds, c, h.Name, row.Subject) {
						t.Errorf("%s: handout %s %s %s: status %s vs %s", p, h.Name, row.Aspect, row.Subject, row.Status, c)
					}
				}
			}
		}
		// 盤面: 「食い違い」⇔ H006、「記載漏れ」⇔ H007
		for _, b := range r.Boards {
			for _, row := range b.Rows {
				if (row.Status == "ng") != has(ds, "H006", b.Name, row.Subject) ||
					(row.Status == "missing") != has(ds, "H007", b.Name, row.Subject) {
					t.Errorf("%s: board %s %s: status %s", p, b.Name, row.Subject, row.Status)
				}
			}
		}
		// ゴール: 達成される選び方が 0 ⇔ G004、すべて ⇔ G006(パターンがあるときだけ数える)
		for _, g := range r.Goals {
			if !g.Counted || g.OfPatterns == 0 || r.RGated {
				continue
			}
			if (g.TrueIn == 0) != has(ds, "G004", g.ID) || (g.TrueIn == g.OfPatterns) != has(ds, "G006", g.ID) {
				t.Errorf("%s: goal %s true in %d/%d disagrees with G004/G006", p, g.ID, g.TrueIn, g.OfPatterns)
			}
		}
		// エンディング: 選び方 0 通り ⇔ G005、エンディングなしがある ⇔ G001、2つ以上がある ⇔ G002
		if e := r.Endings; e.Skipped == "" {
			if (e.Total == 0) != has(ds, "G005") || (e.NoEnding > 0) != has(ds, "G001") || (e.Multiple > 0) != has(ds, "G002") {
				t.Errorf("%s: endings total=%d none=%d multi=%d disagree with G001/G002/G005", p, e.Total, e.NoEnding, e.Multiple)
			}
			for _, c := range e.Counts {
				if (c.Count == 0 && e.Total > 0) != has(ds, "G003", c.ID) {
					t.Errorf("%s: ending %s count=%d vs G003", p, c.ID, c.Count)
				}
			}
		} else if !has(ds, "G007") {
			t.Errorf("%s: endings skipped but no G007", p)
		}
		// 居場所の表: どの区切りの時刻でも、表の値は判定器の whereAt と同じ
		w := &world{s: s, final: run(s, nil, nil), sorted: sortedEvents(s)}
		for _, row := range r.Rows {
			for _, sp := range row.Spans {
				for i := sp.From; i < sp.Till; i++ {
					got := w.whereAt(row.Character, r.Times[i])
					if got != sp.Label {
						t.Fatalf("%s: grid %s at %d = %q, whereAt = %q", p, row.Character, r.Times[i], sp.Label, got)
					}
				}
			}
		}
	}
	if n < 200 {
		t.Fatalf("too few cases checked: %d", n)
	}
}
