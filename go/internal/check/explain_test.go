package check

import (
	"os"
	"path/filepath"
	"reflect"
	"strings"
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
		for _, h := range r.Handouts {
			for _, row := range h.Rows {
				var want bool
				switch {
				case row.Aspect == "居場所(終了時)":
					want = has(ds, "H001", h.Name, row.Declared)
				case row.Aspect == "持ち物" && row.Status != "missing":
					want = has(ds, "H002", h.Name, row.Declared)
				case row.Aspect == "知識" && row.Status != "missing":
					want = has(ds, "H004", h.Name, row.Declared)
				case row.Aspect == "持ち物":
					want = has(ds, "H003", h.Name, strings.TrimSuffix(row.Actual, " を所持"))
				case row.Aspect == "知識":
					want = has(ds, "H005", h.Name, strings.TrimSuffix(row.Actual, " を知っている"))
				}
				if (row.Status != "ok") != want {
					t.Errorf("%s: handout %s %s %s: status %s, checker %v", p, h.Name, row.Aspect, row.Declared, row.Status, want)
				}
			}
		}
		// 盤面: 「食い違い」⇔ H006、「記載漏れ」⇔ H007
		for _, b := range r.Boards {
			for _, row := range b.Rows {
				var want bool
				if row.Status == "missing" {
					want = has(ds, "H007", b.Name, strings.TrimSuffix(row.Actual, " がある"))
				} else {
					want = has(ds, "H006", b.Name, row.Declared)
				}
				if (row.Status != "ok") != want {
					t.Errorf("%s: board %s %s: status %s, checker %v", p, b.Name, row.Declared, row.Status, want)
				}
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
					label := map[string]string{"transit": "移動中", "dead": "死亡"}[got]
					if label == "" {
						label = got
					}
					if label != sp.Label {
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
