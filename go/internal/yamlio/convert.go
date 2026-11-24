// Package yamlio は作者向け YAML (docs/yaml.md) を正規化 JSON (docs/spec.md §1) に変換する。
package yamlio

import (
	"encoding/json"
	"fmt"
	"regexp"
	"strconv"

	"gopkg.in/yaml.v3"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

type obj = map[string]any

func inErr(format string, a ...any) error { return &m.InputError{Msg: fmt.Sprintf(format, a...)} }

var timeRe = regexp.MustCompile(`^\s*(?:(\d+)d\s*)?(\d+):(\d{2})\s*$`)

// ParseTime は "21:00"、"25:30"、"2d 09:00" を分に変換する。
func ParseTime(s string) (int, error) {
	g := timeRe.FindStringSubmatch(s)
	if g == nil {
		return 0, inErr("invalid time %q (use \"HH:MM\" or \"Nd HH:MM\")", s)
	}
	d := 0
	if g[1] != "" {
		d, _ = strconv.Atoi(g[1])
	}
	h, _ := strconv.Atoi(g[2])
	mi, _ := strconv.Atoi(g[3])
	if mi >= 60 {
		return 0, inErr("invalid time %q: minutes must be < 60", s)
	}
	return d*1440 + h*60 + mi, nil
}

// timeField は時刻のフィールドの文字列を分にする(数はそのまま)。
func timeField(o obj, k string) error {
	if s, ok := o[k].(string); ok {
		t, err := ParseTime(s)
		if err != nil {
			return inErr("'%s': %v", k, err.(*m.InputError).Msg)
		}
		o[k] = t
	}
	return nil
}

func objs(v any, what string) ([]obj, error) {
	if v == nil {
		return nil, nil
	}
	l, ok := v.([]any)
	if !ok {
		return nil, inErr("'%s' must be a list", what)
	}
	out := make([]obj, 0, len(l))
	for _, x := range l {
		o, ok := x.(obj)
		if !ok {
			return nil, inErr("each entry of '%s' must be a mapping", what)
		}
		out = append(out, o)
	}
	return out, nil
}

func appendList(root obj, k string, vs ...any) {
	l, _ := root[k].([]any)
	root[k] = append(l, vs...)
}

// ToJSON は YAML を正規化 JSON に変換する。
func ToJSON(src []byte) ([]byte, error) {
	var doc any
	if err := yaml.Unmarshal(src, &doc); err != nil {
		return nil, inErr("%v", err)
	}
	root, ok := doc.(obj)
	if !ok {
		return nil, inErr("the top level must be a mapping")
	}
	if err := convert(root); err != nil {
		return nil, err
	}
	out, err := json.MarshalIndent(root, "", "  ")
	if err != nil {
		return nil, inErr("%v", err)
	}
	return out, nil
}

// Load は YAML を読んでシナリオにする。
func Load(src []byte) (*m.Scenario, error) {
	j, err := ToJSON(src)
	if err != nil {
		return nil, err
	}
	return m.ParseScenario(j)
}

func ownerField(kind string) string {
	switch kind {
	case "transfer", "tell":
		return "from"
	case "scene":
		return "participants"
	}
	return "character"
}

func convert(root obj) error {
	for _, k := range []string{"start_time", "end_time"} {
		if err := timeField(root, k); err != nil {
			return err
		}
	}
	chars, err := objs(root["characters"], "characters")
	if err != nil {
		return err
	}
	for _, c := range chars {
		id, _ := c["id"].(string)
		if loc, ok := c["location"]; ok {
			appendList(root, "placements", obj{"character": id, "location": loc})
			delete(c, "location")
		}
		if knows, ok := c["knows"]; ok {
			l, ok := knows.([]any)
			if !ok {
				return inErr("'characters[].knows' must be a list")
			}
			for _, f := range l {
				appendList(root, "initial_knowledge", obj{"character": id, "fact": f})
			}
			delete(c, "knows")
		}
		if tl, ok := c["timeline"]; ok {
			evs, err := objs(tl, "characters[].timeline")
			if err != nil {
				return err
			}
			for n, e := range evs {
				kind, _ := e["kind"].(string)
				f := ownerField(kind)
				if _, has := e[f]; !has {
					if f == "participants" {
						e[f] = []any{id}
					} else {
						e[f] = id
					}
				}
				if _, has := e["id"]; !has {
					e["id"] = fmt.Sprintf("%s#%d", id, n+1)
				}
				appendList(root, "events", e)
			}
			delete(c, "timeline")
		}
	}
	evs, err := objs(root["events"], "events")
	if err != nil {
		return err
	}
	for _, e := range evs {
		for _, k := range []string{"at", "arrive"} {
			if err := timeField(e, k); err != nil {
				return err
			}
		}
	}
	hs, err := objs(root["handouts"], "handouts")
	if err != nil {
		return err
	}
	for _, h := range hs {
		tl, ok := h["timeline"]
		if !ok {
			continue
		}
		rows, err := objs(tl, "handouts[].timeline")
		if err != nil {
			return err
		}
		id, _ := h["character"].(string)
		for n, r := range rows {
			if err := timeField(r, "at"); err != nil {
				return err
			}
			fid, ok := r["fact"]
			if !ok {
				fid = fmt.Sprintf("%s@%d", id, n+1)
			}
			about := obj{"event": r["event"]}
			if pt, ok := r["point"]; ok {
				about["point"] = pt
			}
			f := obj{"id": fid, "about": about, "claimed_at": r["at"]}
			for _, k := range []string{"truth", "tolerance", "contradicted_by", "text"} {
				if v, ok := r[k]; ok {
					f[k] = v
				}
			}
			appendList(root, "facts", f)
			appendList(root, "initial_knowledge", obj{"character": id, "fact": fid})
			if knows, ok := h["knows"].([]any); ok {
				h["knows"] = append(knows, fid)
			}
		}
		delete(h, "timeline")
	}
	facts, err := objs(root["facts"], "facts")
	if err != nil {
		return err
	}
	for _, f := range facts {
		if err := timeField(f, "claimed_at"); err != nil {
			return err
		}
	}
	as, err := objs(root["assertions"], "assertions")
	if err != nil {
		return err
	}
	for _, a := range as {
		if err := timeField(a, "at"); err != nil {
			return err
		}
	}
	return nil
}
