package model

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"strings"
)

// InputError は入力エラー (§6.4)。CLI は終了コード 2 を返す。
// InputError は入力の誤り。Path はその場所(例: goals[2].requires_tagged[0])。空なら場所なし。
type InputError struct {
	Msg  string
	Path string
}

func (e *InputError) Error() string {
	if e.Path != "" {
		return "input error: " + e.Path + ": " + e.Msg
	}
	return "input error: " + e.Msg
}

// withPath は入力の誤りに場所 seg を前に付ける(それ以外の誤りはそのまま)。
func withPath(err error, seg string) error {
	ie, ok := err.(*InputError)
	if !ok {
		return err
	}
	path := seg
	if ie.Path != "" {
		if strings.HasPrefix(ie.Path, "[") {
			path += ie.Path
		} else {
			path += "." + ie.Path
		}
	}
	return &InputError{Msg: ie.Msg, Path: path}
}

func inErr(format string, a ...any) error { return &InputError{Msg: fmt.Sprintf(format, a...)} }

// MaxTime は数値の上限 (§6.4)。
const MaxTime = 10000000

// ---------------------------------------------------------------- JSON の木(キーの重複を検出する)

type nodeKind int

const (
	nNull nodeKind = iota
	nBool
	nNum
	nStr
	nArr
	nObj
)

type node struct {
	kind nodeKind
	b    bool
	s    string // 文字列、または数値の表記
	arr  []*node
	obj  map[string]*node
}

func readNode(dec *json.Decoder) (*node, error) {
	tok, err := dec.Token()
	if err != nil {
		return nil, err
	}
	switch t := tok.(type) {
	case nil:
		return &node{kind: nNull}, nil
	case bool:
		return &node{kind: nBool, b: t}, nil
	case json.Number:
		return &node{kind: nNum, s: string(t)}, nil
	case string:
		return &node{kind: nStr, s: t}, nil
	case json.Delim:
		switch t {
		case '[':
			n := &node{kind: nArr}
			for dec.More() {
				c, err := readNode(dec)
				if err != nil {
					return nil, err
				}
				n.arr = append(n.arr, c)
			}
			if _, err := dec.Token(); err != nil {
				return nil, err
			}
			return n, nil
		case '{':
			n := &node{kind: nObj, obj: map[string]*node{}}
			for dec.More() {
				kt, err := dec.Token()
				if err != nil {
					return nil, err
				}
				k := kt.(string)
				if _, dup := n.obj[k]; dup {
					return nil, fmt.Errorf("duplicate object key %q", k)
				}
				c, err := readNode(dec)
				if err != nil {
					return nil, err
				}
				n.obj[k] = c
			}
			if _, err := dec.Token(); err != nil {
				return nil, err
			}
			return n, nil
		}
	}
	return nil, fmt.Errorf("unexpected token %v", tok)
}

func parseTree(data []byte) (*node, error) {
	dec := json.NewDecoder(bytes.NewReader(data))
	dec.UseNumber()
	n, err := readNode(dec)
	if err != nil {
		return nil, inErr("%v", err)
	}
	if _, err := dec.Token(); !errors.Is(err, io.EOF) {
		return nil, inErr("trailing data after JSON value")
	}
	return n, nil
}

// ---------------------------------------------------------------- フィールドの読み取り(Lean の Json.lean と同じ規則)

// field は値が null のフィールドを省略と同じに扱う。
func field(j *node, k string) *node {
	if j == nil || j.kind != nObj {
		return nil
	}
	v := j.obj[k]
	if v == nil || v.kind == nNull {
		return nil
	}
	return v
}

func req(j *node, k string) (*node, error) {
	if v := field(j, k); v != nil {
		return v, nil
	}
	return nil, inErr("missing field '%s'", k)
}

func asStr(k string, v *node) (string, error) {
	if v.kind != nStr {
		return "", inErr("'%s' must be a string", k)
	}
	if v.s == "" {
		return "", inErr("'%s' must be non-empty", k)
	}
	return v.s, nil
}

// asNat は値が整数で 0 以上 MaxTime 以下の数を受け付ける(1260、1260.0、1.26e3 はどれも 1260)。
func asNat(k string, v *node) (int, error) {
	if v.kind != nNum {
		return 0, inErr("'%s' must be a non-negative integer", k)
	}
	n, ok, inRange := parseIntegral(v.s)
	if !ok {
		return 0, inErr("'%s' must be a non-negative integer", k)
	}
	if !inRange {
		return 0, inErr("'%s' out of range", k)
	}
	return n, nil
}

// parseIntegral は JSON の数の表記を読み、値が 0 以上の整数か(ok)と、MaxTime 以下か(inRange)を返す。
func parseIntegral(s string) (n int, ok, inRange bool) {
	neg := strings.HasPrefix(s, "-")
	s = strings.TrimPrefix(s, "-")
	mant, exp := s, 0
	if i := strings.IndexAny(s, "eE"); i >= 0 {
		mant = s[:i]
		e := s[i+1:]
		sign := 1
		if strings.HasPrefix(e, "+") {
			e = e[1:]
		} else if strings.HasPrefix(e, "-") {
			sign, e = -1, e[1:]
		}
		v := 0
		for _, c := range e {
			if v < 1<<40 {
				v = v*10 + int(c-'0')
			}
		}
		// Lean の JSON パーサは正の指数が 100,000 を超えると読めない (§6.4)
		if sign > 0 && v > 100000 {
			return 0, false, false
		}
		exp = sign * v
	}
	digits := mant
	if i := strings.IndexByte(mant, '.'); i >= 0 {
		digits = mant[:i] + mant[i+1:]
		exp -= len(mant) - i - 1
	}
	digits = strings.TrimLeft(digits, "0")
	if digits == "" {
		return 0, true, true // 値は 0(-0 も)
	}
	for strings.HasSuffix(digits, "0") {
		digits = digits[:len(digits)-1]
		exp++
	}
	if exp < 0 || neg {
		return 0, false, false
	}
	if len(digits)+exp > 8 {
		return 0, true, false
	}
	for _, c := range digits {
		n = n*10 + int(c-'0')
	}
	for i := 0; i < exp; i++ {
		n *= 10
	}
	return n, true, n <= MaxTime
}

func asBool(k string, v *node) (bool, error) {
	if v.kind != nBool {
		return false, inErr("'%s' must be a boolean", k)
	}
	return v.b, nil
}

func asArr(k string, v *node) ([]*node, error) {
	if v.kind != nArr {
		return nil, inErr("'%s' must be an array", k)
	}
	return v.arr, nil
}

func str(j *node, k string) (string, error) {
	v, err := req(j, k)
	if err != nil {
		return "", err
	}
	return asStr(k, v)
}

func nat(j *node, k string) (int, error) {
	v, err := req(j, k)
	if err != nil {
		return 0, err
	}
	return asNat(k, v)
}

func strOpt(j *node, k string) (*string, error) {
	v := field(j, k)
	if v == nil {
		return nil, nil
	}
	s, err := asStr(k, v)
	return &s, err
}

func natOpt(j *node, k string) (*int, error) {
	v := field(j, k)
	if v == nil {
		return nil, nil
	}
	n, err := asNat(k, v)
	return &n, err
}

func boolD(j *node, k string, d bool) (bool, error) {
	v := field(j, k)
	if v == nil {
		return d, nil
	}
	return asBool(k, v)
}

func arrD(j *node, k string) ([]*node, error) {
	v := field(j, k)
	if v == nil {
		return nil, nil
	}
	return asArr(k, v)
}

func strList(k string, vs []*node) ([]string, error) {
	out := make([]string, 0, len(vs))
	for _, v := range vs {
		s, err := asStr(k, v)
		if err != nil {
			return nil, err
		}
		out = append(out, s)
	}
	return out, nil
}

func strs(j *node, k string) ([]string, error) {
	vs, err := arrD(j, k)
	if err != nil {
		return nil, err
	}
	return strList(k, vs)
}

func strsReq(j *node, k string) ([]string, error) {
	v, err := req(j, k)
	if err != nil {
		return nil, err
	}
	vs, err := asArr(k, v)
	if err != nil {
		return nil, err
	}
	return strList(k, vs)
}

func strsOpt(j *node, k string) (*[]string, error) {
	v := field(j, k)
	if v == nil {
		return nil, nil
	}
	vs, err := asArr(k, v)
	if err != nil {
		return nil, err
	}
	l, err := strList(k, vs)
	return &l, err
}

// ---------------------------------------------------------------- 要素ごとの読み取り

// p は最初のエラーを覚えて、以降の読み取りを飛ばすための小さな補助。
type p struct{ err error }

func (r *p) str(j *node, k string) string {
	if r.err != nil {
		return ""
	}
	s, err := str(j, k)
	r.err = err
	return s
}
func (r *p) nat(j *node, k string) int {
	if r.err != nil {
		return 0
	}
	n, err := nat(j, k)
	r.err = err
	return n
}
func (r *p) strOpt(j *node, k string) *string {
	if r.err != nil {
		return nil
	}
	s, err := strOpt(j, k)
	r.err = err
	return s
}
func (r *p) natOpt(j *node, k string) *int {
	if r.err != nil {
		return nil
	}
	n, err := natOpt(j, k)
	r.err = err
	return n
}
func (r *p) boolD(j *node, k string, d bool) bool {
	if r.err != nil {
		return d
	}
	b, err := boolD(j, k, d)
	r.err = err
	return b
}
func (r *p) strs(j *node, k string) []string {
	if r.err != nil {
		return nil
	}
	l, err := strs(j, k)
	r.err = err
	return l
}
func (r *p) strsReq(j *node, k string) []string {
	if r.err != nil {
		return nil
	}
	l, err := strsReq(j, k)
	r.err = err
	return l
}
func (r *p) strsOpt(j *node, k string) *[]string {
	if r.err != nil {
		return nil
	}
	l, err := strsOpt(j, k)
	r.err = err
	return l
}

func list[T any](j *node, k string, required bool, f func(*node) (T, error)) ([]T, error) {
	var vs []*node
	var err error
	if required {
		var v *node
		if v, err = req(j, k); err != nil {
			return nil, err
		}
		vs, err = asArr(k, v)
	} else {
		vs, err = arrD(j, k)
	}
	if err != nil {
		return nil, err
	}
	out := make([]T, 0, len(vs))
	for i, v := range vs {
		x, err := f(v)
		if err != nil {
			seg := fmt.Sprintf("%s[%d]", k, i)
			if id := field(v, "id"); id != nil && id.kind == nStr && id.s != "" {
				seg += "(id=" + id.s + ")" // YAML の timeline から変換したイベントでも場所が分かるように
			}
			return nil, withPath(err, seg)
		}
		out = append(out, x)
	}
	return out, nil
}

func parseEdge(withMinutes bool) func(*node) (Edge, error) {
	return func(j *node) (Edge, error) {
		var r p
		e := Edge{Src: r.str(j, "from"), Dst: r.str(j, "to")}
		if withMinutes {
			e.Minutes = r.nat(j, "minutes")
		}
		e.Bidirectional = r.boolD(j, "bidirectional", false)
		return e, r.err
	}
}

func parseHolder(j *node) (Holder, error) {
	c, l := field(j, "character"), field(j, "location")
	switch {
	case c != nil && l == nil:
		s, err := asStr("character", c)
		return Holder{Kind: HolderChar, ID: s}, err
	case c == nil && l != nil:
		s, err := asStr("location", l)
		return Holder{Kind: HolderPlace, ID: s}, err
	}
	return Holder{}, inErr("'initial' must have exactly one of 'character' or 'location'")
}

func parseFact(j *node) (Fact, error) {
	var r p
	f := Fact{AboutPoint: "at"}
	if a := field(j, "about"); a != nil {
		ev := r.str(a, "event")
		f.AboutEvent = &ev
		if pt := r.strOpt(a, "point"); pt != nil {
			f.AboutPoint = *pt
		}
	}
	f.ID = r.str(j, "id")
	f.Truth = r.boolD(j, "truth", true)
	f.ContradictedBy = r.strs(j, "contradicted_by")
	f.ClaimedAt = r.natOpt(j, "claimed_at")
	f.Tolerance = r.natOpt(j, "tolerance")
	return f, r.err
}

func parseEvent(j *node) (Event, error) {
	var r p
	e := Event{ID: r.str(j, "id"), Time: r.nat(j, "at"), Requires: r.strs(j, "requires")}
	kind := r.str(j, "kind")
	if r.err != nil {
		return e, r.err
	}
	k := &e.Kind
	switch kind {
	case "move":
		k.Kind, k.Character, k.To, k.Arrive = Move, r.str(j, "character"), r.str(j, "to"), r.nat(j, "arrive")
		k.Mode = "walk"
		if m := r.strOpt(j, "mode"); m != nil {
			k.Mode = *m
		}
		k.Fatal = r.boolD(j, "fatal", false)
	case "scene":
		k.Kind, k.Location, k.Participants, k.Reveals = Scene, r.str(j, "location"), r.strsReq(j, "participants"), r.strs(j, "reveals")
	case "observe":
		k.Kind, k.Character, k.Location = Observe, r.str(j, "character"), r.str(j, "location")
		k.TargetLocation = k.Location
		if tl := r.strOpt(j, "target_location"); tl != nil {
			k.TargetLocation = *tl
		}
		k.Targets, k.Facts = r.strs(j, "targets"), r.strsReq(j, "facts")
	case "transfer":
		k.Kind, k.Src, k.Dst, k.Item = Transfer, r.str(j, "from"), r.str(j, "to"), r.str(j, "item")
	case "pickup", "drop", "use", "consume":
		k.Kind = map[string]Kind{"pickup": Pickup, "drop": Drop, "use": Use, "consume": Consume}[kind]
		k.Character, k.Item = r.str(j, "character"), r.str(j, "item")
	case "learn":
		k.Kind, k.Character, k.Facts = Learn, r.str(j, "character"), r.strsReq(j, "facts")
	case "tell":
		k.Kind, k.Src, k.Dst, k.Facts = Tell, r.str(j, "from"), r.str(j, "to"), r.strsReq(j, "facts")
	case "die":
		k.Kind, k.Character = Die, r.str(j, "character")
	default:
		return e, inErr("unknown event kind '%s'", kind)
	}
	return e, r.err
}

func parseFormula(j *node) (Formula, error) {
	if j.kind != nObj {
		return Formula{}, inErr("formula must be an object")
	}
	if len(j.obj) != 1 {
		return Formula{}, inErr("formula must have exactly one key")
	}
	var r p
	if v := field(j, "const"); v != nil {
		b, err := asBool("const", v)
		return Formula{Kind: FConst, Const: b}, err
	}
	if v := field(j, "var"); v != nil {
		s, err := asStr("var", v)
		return Formula{Kind: FVar, Var: s}, err
	}
	if v := field(j, "eq"); v != nil {
		f := Formula{Kind: FEq, Var: r.str(v, "var"), Value: r.str(v, "value")}
		return f, r.err
	}
	if v := field(j, "plurality"); v != nil {
		f := Formula{Kind: FPlurality, Votes: r.strsReq(v, "votes"), Value: r.str(v, "value")}
		return f, r.err
	}
	if v := field(j, "tie"); v != nil {
		f := Formula{Kind: FTie, Votes: r.strsReq(v, "votes")}
		return f, r.err
	}
	if v := field(j, "truth"); v != nil {
		s, err := asStr("truth", v)
		return Formula{Kind: FTruth, Var: s}, err
	}
	if v := field(j, "not"); v != nil {
		sub, err := parseFormula(v)
		if err != nil {
			return Formula{}, withPath(err, "not")
		}
		return Formula{Kind: FNot, Subs: []Formula{sub}}, nil
	}
	for _, k := range []string{"and", "or"} {
		if v := field(j, k); v != nil {
			vs, err := asArr(k, v)
			if err != nil {
				return Formula{}, err
			}
			f := Formula{Kind: FAnd}
			if k == "or" {
				f.Kind = FOr
			}
			for i, sv := range vs {
				sub, err := parseFormula(sv)
				if err != nil {
					return Formula{}, withPath(err, fmt.Sprintf("%s[%d]", k, i))
				}
				f.Subs = append(f.Subs, sub)
			}
			return f, nil
		}
	}
	return Formula{}, inErr("unknown formula")
}

// ParseScenario は正規化 JSON を読む。形式の誤りは *InputError を返す。
func ParseScenario(data []byte) (*Scenario, error) {
	j, err := parseTree(data)
	if err != nil {
		return nil, err
	}
	var r p
	s := &Scenario{StartTime: r.nat(j, "start_time"), EndTime: r.nat(j, "end_time")}
	if ct := r.natOpt(j, "claim_tolerance"); ct != nil {
		s.ClaimTolerance = *ct
	}
	s.SolutionFacts = r.strs(j, "solution_facts")
	if r.err != nil {
		return nil, r.err
	}
	steps := []func() error{
		func() (err error) {
			s.Characters, err = list(j, "characters", true, func(c *node) (Character, error) {
				var r p
				x := Character{ID: r.str(c, "id"), NPC: r.boolD(c, "npc", false)}
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Areas, err = list(j, "areas", false, func(a *node) (Area, error) {
				var r p
				x := Area{ID: r.str(a, "id"), InternalMinutes: r.natOpt(a, "internal_minutes")}
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Locations, err = list(j, "locations", true, func(l *node) (Location, error) {
				var r p
				x := Location{ID: r.str(l, "id"), Area: r.strOpt(l, "area"), Public: r.boolD(l, "public", false)}
				return x, r.err
			})
			return
		},
		func() (err error) { s.Travel, err = list(j, "travel", false, parseEdge(true)); return },
		func() (err error) { s.AreaTravel, err = list(j, "area_travel", false, parseEdge(true)); return },
		func() (err error) { s.Perception, err = list(j, "perception", false, parseEdge(false)); return },
		func() (err error) {
			s.Placements, err = list(j, "placements", true, func(pl *node) (Placement, error) {
				var r p
				x := Placement{Character: r.str(pl, "character"), Location: r.str(pl, "location")}
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Items, err = list(j, "items", false, func(i *node) (Item, error) {
				var r p
				x := Item{ID: r.str(i, "id")}
				if r.err != nil {
					return x, r.err
				}
				in, err := req(i, "initial")
				if err != nil {
					return x, err
				}
				if x.Initial, err = parseHolder(in); err != nil {
					return x, err
				}
				x.Tags = r.strs(i, "tags")
				return x, r.err
			})
			return
		},
		func() (err error) { s.Facts, err = list(j, "facts", false, parseFact); return },
		func() (err error) {
			s.InitialKnowledge, err = list(j, "initial_knowledge", false, func(k *node) (Pair, error) {
				var r p
				x := Pair{Character: r.str(k, "character"), Fact: r.str(k, "fact")}
				return x, r.err
			})
			return
		},
		func() (err error) { s.Events, err = list(j, "events", false, parseEvent); return },
		func() (err error) {
			s.Clues, err = list(j, "clues", false, func(c *node) (Clue, error) {
				var r p
				x := Clue{ID: r.str(c, "id"), Location: r.strOpt(c, "location"), Item: r.strOpt(c, "item"),
					Deck: r.strOpt(c, "deck"), Reveals: r.strs(c, "reveals")}
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Assertions, err = list(j, "assertions", false, func(a *node) (Assertion, error) {
				var r p
				kind := r.str(a, "kind")
				x := Assertion{}
				switch {
				case r.err != nil:
					return x, r.err
				case kind == "present":
					x.Kind = Present
				case kind == "absent":
					x.Kind = Absent
				default:
					return x, inErr("unknown assertion kind '%s'", kind)
				}
				x.ID, x.Location, x.Time, x.Characters = r.str(a, "id"), r.str(a, "location"), r.nat(a, "at"), r.strsReq(a, "characters")
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Handouts, err = list(j, "handouts", false, func(h *node) (Handout, error) {
				var r p
				x := Handout{Character: r.str(h, "character"), Location: r.strOpt(h, "location"),
					Items: r.strsOpt(h, "items"), Knows: r.strsOpt(h, "knows")}
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Board, err = list(j, "board", false, func(b *node) (Board, error) {
				var r p
				x := Board{Location: r.str(b, "location"), Items: r.strsReq(b, "items")}
				return x, r.err
			})
			return
		},
		func() (err error) {
			s.Goals, err = list(j, "goals", false, func(g *node) (Goal, error) {
				var r p
				x := Goal{ID: r.str(g, "id"), Owner: r.str(g, "owner"), RequiresItems: r.strs(g, "requires_items"),
					RequiresKnowledge: r.strs(g, "requires_knowledge")}
				if r.err != nil {
					return x, r.err
				}
				tr, err := list(g, "requires_tagged", false, func(t *node) (TagReq, error) {
					var r p
					x := TagReq{Tag: r.str(t, "tag"), Count: r.nat(t, "count")}
					return x, r.err
				})
				if err != nil {
					return x, err
				}
				x.RequiresTagged = tr
				if x.Conceals = r.strs(g, "conceals"); r.err != nil {
					return x, r.err
				}
				if c := field(g, "condition"); c != nil {
					f, err := parseFormula(c)
					if err != nil {
						return x, withPath(err, "condition")
					}
					x.Condition = &f
				}
				return x, nil
			})
			return
		},
		func() (err error) {
			s.Choices, err = list(j, "choices", false, func(c *node) (Choice, error) {
				var r p
				x := Choice{ID: r.str(c, "id"), Owner: r.str(c, "owner"), Values: r.strsOpt(c, "values")}
				return x, r.err
			})
			return
		},
		func() (err error) { s.Constraints, err = list(j, "constraints", false, parseFormula); return },
		func() (err error) {
			s.Endings, err = list(j, "endings", false, func(e *node) (Ending, error) {
				var r p
				x := Ending{ID: r.str(e, "id")}
				if r.err != nil {
					return x, r.err
				}
				c, err := req(e, "condition")
				if err != nil {
					return x, err
				}
				if x.Condition, err = parseFormula(c); err != nil {
					return x, withPath(err, "condition")
				}
				return x, nil
			})
			return
		},
	}
	for _, st := range steps {
		if err := st(); err != nil {
			return nil, err
		}
	}
	if x := field(j, "exploration"); x != nil {
		var r p
		n := r.nat(x, "draws_per_player")
		if r.err != nil {
			return nil, r.err
		}
		s.Exploration = &n
	}
	resolveTruth(s)
	return s, nil
}

// resolveTruth は {"truth": f} の値を facts から決める(最初に見つかった f の truth。なければ false)。
func resolveTruth(s *Scenario) {
	truth := func(id string) bool {
		for _, f := range s.Facts {
			if f.ID == id {
				return f.Truth
			}
		}
		return false
	}
	var walk func(f *Formula)
	walk = func(f *Formula) {
		if f.Kind == FTruth {
			f.Const = truth(f.Var)
		}
		for i := range f.Subs {
			walk(&f.Subs[i])
		}
	}
	for i := range s.Constraints {
		walk(&s.Constraints[i])
	}
	for i := range s.Endings {
		walk(&s.Endings[i].Condition)
	}
	for i := range s.Goals {
		if s.Goals[i].Condition != nil {
			walk(s.Goals[i].Condition)
		}
	}
}
