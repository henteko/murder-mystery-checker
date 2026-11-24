package check

import (
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// TestRulesMatchSpec は、規則の説明(コード・重大度・引数の数)が仕様書 §4 の表とそろっていることを確かめる。
func TestRulesMatchSpec(t *testing.T) {
	b, err := os.ReadFile(filepath.Join("..", "..", "..", "docs", "spec.md"))
	if err != nil {
		t.Fatal(err)
	}
	row := regexp.MustCompile(`(?m)^\| ([RTIKHAG]\d{3}) \|(.*)\|\s*$`)
	argsCol := regexp.MustCompile(`^\[(.*)\]$`)
	spec := map[string]bool{}
	for _, m := range row.FindAllStringSubmatch(string(b), -1) {
		code := m[1]
		spec[code] = true
		cols := strings.Split(m[2], "|")
		sev := strings.TrimSpace(cols[0])
		n := -1
		for _, c := range cols {
			if a := argsCol.FindStringSubmatch(strings.TrimSpace(c)); a != nil {
				n = 0
				if strings.TrimSpace(a[1]) != "" {
					n = len(strings.Split(a[1], ","))
				}
				break
			}
		}
		var r *Rule
		for _, x := range Rules() {
			if x.Code == code {
				x := x
				r = &x
			}
		}
		if r == nil {
			t.Errorf("%s: 仕様書にあるが説明がない", code)
			continue
		}
		if r.Severity != sev {
			t.Errorf("%s: 重大度 %s(仕様書は %s)", code, r.Severity, sev)
		}
		if n >= 0 && len(r.Args) != n {
			t.Errorf("%s: 引数の名前 %d 個(仕様書は %d 個)", code, len(r.Args), n)
		}
		if r.Message == "" || r.Hint == "" {
			t.Errorf("%s: 説明かヒントが空", code)
		}
	}
	for _, r := range Rules() {
		if !spec[r.Code] {
			t.Errorf("%s: 説明があるが仕様書にない", r.Code)
		}
	}
	if len(spec) != len(Rules()) {
		t.Errorf("規則の数 %d(仕様書は %d)", len(Rules()), len(spec))
	}
}
