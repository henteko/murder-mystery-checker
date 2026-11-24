// Package check は判定器。lean/MurderMystery/Checker/*.lean と1対1に対応する。
package check

import (
	"encoding/json"
	"sort"
)

// Severity は重大度。
type Severity int

const (
	Error Severity = iota
	Warning
)

func (s Severity) String() string {
	if s == Error {
		return "error"
	}
	return "warning"
}

// Val は割り当ての値: 真偽値、または列挙型の値。
type Val struct {
	IsStr bool
	B     bool
	S     string
}

func boolVal(b bool) Val  { return Val{B: b} }
func strVal(s string) Val { return Val{IsStr: true, S: s} }
func (v Val) MarshalJSON() ([]byte, error) {
	if v.IsStr {
		return json.Marshal(v.S)
	}
	return json.Marshal(v.B)
}

// WitnessEntry は G001 / G002 の witness の1項目(変数, 値)。
type WitnessEntry struct {
	Var string
	Val Val
}

// Diag は検出結果。
type Diag struct {
	Code    string
	Sev     Severity
	Event   *string
	Args    []string
	Witness *[]WitnessEntry // nil ならなし(空の witness とは区別する)
	WKey    []int           // witness の並べ替えキー。出力しない
}

func errD(code string, args []string, event *string) Diag {
	return Diag{Code: code, Sev: Error, Event: event, Args: args}
}

func warnD(code string, args []string, event *string) Diag {
	return Diag{Code: code, Sev: Warning, Event: event, Args: args}
}

// ---------------------------------------------------------------- 正規順序 (§6.3, Diag.lean の keyLt)

func cmpStr(a, b string) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

func cmpInt(a, b int) int {
	switch {
	case a < b:
		return -1
	case a > b:
		return 1
	}
	return 0
}

// cmpList は辞書式比較(短い方が接頭辞なら短い方が先)。
func cmpList[T any](a, b []T, cmp func(T, T) int) int {
	for i := 0; i < len(a) && i < len(b); i++ {
		if c := cmp(a[i], b[i]); c != 0 {
			return c
		}
	}
	return cmpInt(len(a), len(b))
}

func cmpVal(a, b Val) int {
	switch {
	case !a.IsStr && !b.IsStr:
		return cmpInt(btoi(a.B), btoi(b.B))
	case !a.IsStr:
		return -1
	case !b.IsStr:
		return 1
	}
	return cmpStr(a.S, b.S)
}

func btoi(b bool) int {
	if b {
		return 1
	}
	return 0
}

func cmpOptStr(a, b *string) int {
	switch {
	case a == nil && b == nil:
		return 0
	case a == nil:
		return -1
	case b == nil:
		return 1
	}
	return cmpStr(*a, *b)
}

func cmpWitness(a, b *[]WitnessEntry) int {
	switch {
	case a == nil && b == nil:
		return 0
	case a == nil:
		return -1
	case b == nil:
		return 1
	}
	return cmpList(*a, *b, func(x, y WitnessEntry) int {
		if c := cmpStr(x.Var, y.Var); c != 0 {
			return c
		}
		return cmpVal(x.Val, y.Val)
	})
}

// Compare は正規順序: code, event(なしが最小), args, witness の位置, severity, witness の値。
func Compare(a, b Diag) int {
	if c := cmpStr(a.Code, b.Code); c != 0 {
		return c
	}
	if c := cmpOptStr(a.Event, b.Event); c != 0 {
		return c
	}
	if c := cmpList(a.Args, b.Args, cmpStr); c != 0 {
		return c
	}
	if c := cmpList(a.WKey, b.WKey, cmpInt); c != 0 {
		return c
	}
	if c := cmpInt(int(a.Sev), int(b.Sev)); c != 0 {
		return c
	}
	return cmpWitness(a.Witness, b.Witness)
}

// normalize は正規順序に並べ、重複を除く(Diag.lean の normalize)。
// Compare は全順序なので、比較が 0 の2件は同じ検出結果。
func normalize(ds []Diag) []Diag {
	out := append([]Diag{}, ds...)
	sort.SliceStable(out, func(i, j int) bool { return Compare(out[i], out[j]) < 0 })
	res := out[:0]
	for i, d := range out {
		if i > 0 && Compare(out[i-1], d) == 0 {
			continue
		}
		res = append(res, d)
	}
	return res
}

// ---------------------------------------------------------------- 出力 (§6.1)

type diagJSON struct {
	Code     string          `json:"code"`
	Severity string          `json:"severity"`
	Event    *string         `json:"event,omitempty"`
	Args     []string        `json:"args"`
	Witness  json.RawMessage `json:"witness,omitempty"`
}

// MarshalJSON は検出結果を §6.1 の形で出す。witness は変数をキーとするオブジェクト。
func (d Diag) MarshalJSON() ([]byte, error) {
	j := diagJSON{Code: d.Code, Severity: d.Sev.String(), Event: d.Event, Args: d.Args}
	if j.Args == nil {
		j.Args = []string{}
	}
	if d.Witness != nil {
		buf := []byte{'{'}
		for i, w := range *d.Witness {
			if i > 0 {
				buf = append(buf, ',')
			}
			k, _ := json.Marshal(w.Var)
			v, _ := json.Marshal(w.Val)
			buf = append(append(append(buf, k...), ':'), v...)
		}
		j.Witness = append(buf, '}')
	}
	return json.Marshal(j)
}

// Output は判定器の出力全体。
type Output struct {
	SpecVersion string `json:"spec_version"`
	Diagnostics []Diag `json:"diagnostics"`
}
