package yamlio

import (
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"reflect"
	"testing"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

func TestParseTime(t *testing.T) {
	for in, want := range map[string]int{"21:00": 1260, "00:00": 0, "25:30": 1530, "2d 09:00": 3420, "1d00:05": 1445} {
		got, err := ParseTime(in)
		if err != nil || got != want {
			t.Errorf("ParseTime(%q) = %d, %v; want %d", in, got, err, want)
		}
	}
	for _, in := range []string{"21", "21:60", "9:5", "abc", "-1:00"} {
		if _, err := ParseTime(in); err == nil {
			t.Errorf("ParseTime(%q) should fail", in)
		}
	}
}

func toMap(t *testing.T, src string) map[string]any {
	t.Helper()
	j, err := ToJSON([]byte(src))
	if err != nil {
		t.Fatal(err)
	}
	var out map[string]any
	if err := json.Unmarshal(j, &out); err != nil {
		t.Fatal(err)
	}
	return out
}

func asJSON(t *testing.T, v any) string {
	b, _ := json.Marshal(v)
	return string(b)
}

func TestCharacterShorthands(t *testing.T) {
	out := toMap(t, `
start_time: "21:00"
end_time: 1320
characters:
  - id: alice
    location: hall
    knows: [f1]
    timeline:
      - {at: "21:10", kind: move, to: study, arrive: "21:15"}
      - {at: "21:20", kind: tell, to: bob, facts: [f1]}
      - {id: s1, at: "21:30", kind: scene, location: study}
      - {at: "21:40", kind: transfer, from: bob, to: alice, item: knife}
`)
	if out["start_time"] != 1260.0 {
		t.Errorf("start_time = %v", out["start_time"])
	}
	if got := asJSON(t, out["placements"]); got != `[{"character":"alice","location":"hall"}]` {
		t.Errorf("placements = %s", got)
	}
	if got := asJSON(t, out["initial_knowledge"]); got != `[{"character":"alice","fact":"f1"}]` {
		t.Errorf("initial_knowledge = %s", got)
	}
	want := `[{"arrive":1275,"at":1270,"character":"alice","id":"alice#1","kind":"move","to":"study"},` +
		`{"at":1280,"facts":["f1"],"from":"alice","id":"alice#2","kind":"tell","to":"bob"},` +
		`{"at":1290,"id":"s1","kind":"scene","location":"study","participants":["alice"]},` +
		`{"at":1300,"from":"bob","id":"alice#4","item":"knife","kind":"transfer","to":"alice"}]`
	if got := asJSON(t, out["events"]); got != want {
		t.Errorf("events =\n%s\nwant\n%s", got, want)
	}
	c := out["characters"].([]any)[0].(map[string]any)
	if len(c) != 1 {
		t.Errorf("YAML-only keys should be removed: %v", c)
	}
}

func TestHandoutTimeline(t *testing.T) {
	out := toMap(t, `
handouts:
  - character: tom
    knows: [f0]
    timeline:
      - {at: "18:10", event: e1, text: 悲鳴}
      - {at: "17:50", event: e2, point: arrive, fact: f_saw, truth: false, contradicted_by: [f9], tolerance: 3}
`)
	want := `[{"about":{"event":"e1"},"claimed_at":1090,"id":"tom@1","text":"悲鳴"},` +
		`{"about":{"event":"e2","point":"arrive"},"claimed_at":1070,"contradicted_by":["f9"],"id":"f_saw","tolerance":3,"truth":false}]`
	if got := asJSON(t, out["facts"]); got != want {
		t.Errorf("facts =\n%s\nwant\n%s", got, want)
	}
	if got := asJSON(t, out["initial_knowledge"]); got != `[{"character":"tom","fact":"tom@1"},{"character":"tom","fact":"f_saw"}]` {
		t.Errorf("initial_knowledge = %s", got)
	}
	if got := asJSON(t, out["handouts"]); got != `[{"character":"tom","knows":["f0","tom@1","f_saw"]}]` {
		t.Errorf("handouts = %s", got)
	}
}

func TestInputErrors(t *testing.T) {
	for name, src := range map[string]string{
		"duplicate key": "start_time: 1\nstart_time: 2\n",
		"bad time":      "start_time: \"21:75\"\n",
		"not a mapping": "- 1\n- 2\n",
		"bad timeline":  "characters:\n  - id: a\n    timeline: 3\n",
	} {
		_, err := Load([]byte(src))
		var ie *m.InputError
		if !errors.As(err, &ie) {
			t.Errorf("%s: want input error, got %v", name, err)
		}
	}
}

// TestDemo は examples/yaml-demo/scenario.yaml の変換結果が、コミット済みの scenario.json と一致することを確かめる。
// scenario.json は Lean オラクルの入力にもなる(expected.json)。
func TestDemo(t *testing.T) {
	dir := filepath.Join("..", "..", "..", "examples", "yaml-demo")
	src, err := os.ReadFile(filepath.Join(dir, "scenario.yaml"))
	if err != nil {
		t.Fatal(err)
	}
	j, err := ToJSON(src)
	if err != nil {
		t.Fatal(err)
	}
	committed, err := os.ReadFile(filepath.Join(dir, "scenario.json"))
	if err != nil {
		t.Fatal(err)
	}
	var a, b any
	_ = json.Unmarshal(j, &a)
	_ = json.Unmarshal(committed, &b)
	if !reflect.DeepEqual(a, b) {
		t.Fatal("examples/yaml-demo/scenario.json is out of date: run `mmcheck convert examples/yaml-demo/scenario.yaml`")
	}
}
