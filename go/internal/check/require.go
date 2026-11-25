package check

import (
	"encoding/json"
	"fmt"
	"math"
	"regexp"
	"strconv"
	"strings"
)

// mmcheck stats --require の条件式。docs/stats.md の「条件」。
//
//	条件   := 値 比較 数
//	値     := パス | 集計 "(" パス ")"
//	パス   := stats の JSON のキーを "." でつないだもの。途中の配列は要素ごとに辿る
//	          別名: score = complexity.score、axis.<name> = 軸のスコア × 100、
//	                check.errors / check.warnings = mmcheck check の件数
//	集計   := min | max | sum | avg | count(配列の要素数、または辿った値の数)
//	比較   := >= | <= | > | < | == | !=

// Requirement は条件1つの評価結果。Value は値(求められなければ nil)。
type Requirement struct {
	Expr    string   `json:"expr"`
	OK      bool     `json:"ok"`
	Value   *float64 `json:"value"`
	Op      string   `json:"op"`
	Target  float64  `json:"target"`
	Message string   `json:"message,omitempty"`
}

var reqRe = regexp.MustCompile(`^\s*(?:(min|max|sum|avg|count)\(\s*([A-Za-z0-9_.]+)\s*\)|([A-Za-z0-9_.]+))\s*(>=|<=|==|!=|>|<)\s*(-?[0-9]+(?:\.[0-9]+)?)\s*$`)

// ParseRequirement は条件式の形だけを検査する(値は求めない)。
func ParseRequirement(expr string) error {
	if !reqRe.MatchString(expr) {
		return fmt.Errorf("条件式の形が不正です: %q(例: 'score>=50'、'min(branching.players.pivotal)>0'、'count(padding.idle_moves)==0')", expr)
	}
	return nil
}

// EvalRequirement は条件式を指標に対して評価する。式の形が不正ならエラー。
func EvalRequirement(st *Stats, expr string) (Requirement, error) {
	g := reqRe.FindStringSubmatch(expr)
	if g == nil {
		return Requirement{}, ParseRequirement(expr)
	}
	agg, path := g[1], g[2]
	if path == "" {
		path = g[3]
	}
	target, _ := strconv.ParseFloat(g[5], 64)
	r := Requirement{Expr: strings.TrimSpace(expr), Op: g[4], Target: target}

	vals, err := resolve(st, path)
	if err != nil {
		r.Message = err.Error()
		return r, nil
	}
	var v float64
	switch agg {
	case "count":
		if len(vals) == 1 {
			if arr, ok := vals[0].([]any); ok {
				vals = arr
			}
		}
		v = float64(len(vals))
	default:
		nums, err := numbers(vals)
		if err != nil {
			r.Message = fmt.Sprintf("%s: %v", path, err)
			return r, nil
		}
		switch {
		case agg == "" && len(nums) == 1:
			v = nums[0]
		case agg == "":
			r.Message = fmt.Sprintf("%s は %d 個の値になります。min / max / sum / avg / count で集計してください", path, len(nums))
			return r, nil
		case len(nums) == 0:
			r.Message = fmt.Sprintf("%s に値がないため %s を求められません", path, agg)
			return r, nil
		default:
			v = aggregate(agg, nums)
		}
	}
	r.Value = ptr(round4(v))
	r.OK = compare(v, r.Op, target)
	if !r.OK {
		r.Message = fmt.Sprintf("%s = %g で、%s %g を満たしません", path, round4(v), r.Op, target)
	}
	return r, nil
}

// resolve はパスを辿った値の列(配列を辿ると複数になる)。
func resolve(st *Stats, path string) ([]any, error) {
	keys := strings.Split(path, ".")
	switch {
	case path == "score":
		return []any{st.Complexity.Score}, nil
	case keys[0] == "axis" && len(keys) == 2:
		for _, a := range st.Complexity.Axes {
			if a.Name == keys[1] {
				if !a.Applicable {
					return nil, fmt.Errorf("軸 %s はこのシナリオでは対象外です", keys[1])
				}
				return []any{a.Score * 100}, nil
			}
		}
		return nil, fmt.Errorf("軸 %s はありません(size / timeline / knowledge / exploration / branching)", keys[1])
	}
	b, _ := json.Marshal(st)
	var root any
	_ = json.Unmarshal(b, &root)
	cur := []any{root}
	for i, k := range keys {
		var next []any
		for _, x := range cur {
			obj, ok := x.(map[string]any)
			if !ok {
				return nil, fmt.Errorf("%s はオブジェクトではありません", strings.Join(keys[:i], "."))
			}
			v, ok := obj[k]
			if !ok {
				return nil, fmt.Errorf("%s というキーはありません", strings.Join(keys[:i+1], "."))
			}
			// 最後のキー以外で配列なら、要素ごとに辿る
			if arr, isArr := v.([]any); isArr && i < len(keys)-1 {
				next = append(next, arr...)
			} else if v != nil {
				next = append(next, v)
			}
		}
		cur = next
	}
	return cur, nil
}

func numbers(vals []any) ([]float64, error) {
	var out []float64
	for _, v := range vals {
		switch x := v.(type) {
		case float64:
			out = append(out, x)
		case bool:
			if x {
				out = append(out, 1)
			} else {
				out = append(out, 0)
			}
		case []any:
			return nil, fmt.Errorf("配列です。要素数は count(...) で数えてください")
		default:
			return nil, fmt.Errorf("数ではありません")
		}
	}
	return out, nil
}

func aggregate(agg string, nums []float64) float64 {
	v := nums[0]
	switch agg {
	case "min":
		for _, x := range nums {
			v = math.Min(v, x)
		}
	case "max":
		for _, x := range nums {
			v = math.Max(v, x)
		}
	case "sum", "avg":
		v = 0
		for _, x := range nums {
			v += x
		}
		if agg == "avg" {
			v /= float64(len(nums))
		}
	}
	return v
}

func compare(v float64, op string, t float64) bool {
	const eps = 1e-9
	switch op {
	case ">=":
		return v >= t-eps
	case "<=":
		return v <= t+eps
	case ">":
		return v > t+eps
	case "<":
		return v < t-eps
	case "==":
		return math.Abs(v-t) <= eps
	case "!=":
		return math.Abs(v-t) > eps
	}
	return false
}
