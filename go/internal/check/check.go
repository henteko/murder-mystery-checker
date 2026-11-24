package check

import (
	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// SpecVersion は実装している仕様のバージョン。
const SpecVersion = "0.7.0"

// Check は判定器の入口 (§3)。R の違反があれば R のみ。結果は正規順序で、重複なし。
func Check(s *m.Scenario) []Diag {
	if r := checkR(s); len(r) > 0 {
		return normalize(r)
	}
	var out []Diag
	final := run(s, func(st Step) {
		for _, x := range stepIssues(s, st) {
			out = append(out, errD(x.code, x.args, ptr(st.Ev.ID)))
		}
	}, nil)
	w := &world{s: s, final: final, sorted: sortedEvents(s)}
	out = append(out, w.checkPost()...)
	out = append(out, w.checkG()...)
	return normalize(out)
}
