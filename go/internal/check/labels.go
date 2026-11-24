package check

import "encoding/json"

// Label は表示用の名前と説明。正規化 JSON の任意フィールド name と note(text も同じ扱い)から読む。
// 判定器はこれらのフィールドを読まない(知らないフィールドは読み飛ばす)。explain の表示だけが使う。
type Label struct {
	Name, Note string
}

// Labels は種類("character", "location", "item", "fact", "event" など)→ ID → Label。
type Labels map[string]map[string]Label

var labelKinds = map[string]string{
	"characters": "character", "areas": "area", "locations": "location", "items": "item", "facts": "fact",
	"events": "event", "clues": "clue", "assertions": "assertion", "goals": "goal", "choices": "choice",
	"endings": "ending",
}

// ParseLabels は正規化 JSON から表示用の名前と説明を集める。読めない形は無視する(入力エラーは判定器の読み込みが扱う)。
func ParseLabels(data []byte) Labels {
	ls := Labels{}
	var doc map[string]json.RawMessage
	if json.Unmarshal(data, &doc) != nil {
		return ls
	}
	for key, kind := range labelKinds {
		var xs []map[string]any
		if json.Unmarshal(doc[key], &xs) != nil {
			continue
		}
		for _, x := range xs {
			id, _ := x["id"].(string)
			if id == "" {
				continue
			}
			var l Label
			l.Name, _ = x["name"].(string)
			if n, ok := x["note"].(string); ok {
				l.Note = n
			} else if t, ok := x["text"].(string); ok {
				l.Note = t
			}
			if l.Name == "" && l.Note == "" {
				continue
			}
			if ls[kind] == nil {
				ls[kind] = map[string]Label{}
			}
			if _, dup := ls[kind][id]; !dup {
				ls[kind][id] = l
			}
		}
	}
	return ls
}
