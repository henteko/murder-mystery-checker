package main

import (
	"bytes"
	"encoding/json"
	"github.com/henteko/murder-mystery-checker/internal/check"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func cli(args ...string) (int, string, string) {
	var out, errb bytes.Buffer
	code := run(args, strings.NewReader(""), &out, &errb)
	return code, out.String(), errb.String()
}

var root = filepath.Join("..", "..", "..")

func TestExitCodes(t *testing.T) {
	clean := filepath.Join(root, "testdata", "oracle", "edge", "clean_base.input.json")
	withErr := filepath.Join(root, "examples", "yaml-demo", "scenario.yaml")
	warnOnly := filepath.Join(root, "testdata", "oracle", "rules", "G008_character_without_goal.input.json")
	bad := filepath.Join(root, "testdata", "oracle", "schema", "invalid_json.input.json")
	cases := []struct {
		args []string
		want int
	}{
		{[]string{"check", clean}, 0},
		{[]string{"check", withErr}, 1},
		{[]string{"check", warnOnly}, 0},
		{[]string{"check", "--strict", warnOnly}, 1},
		{[]string{"check", bad}, 2},
		{[]string{"check", "no-such-file.yaml"}, 2},
		{[]string{"check", "--format", "xml", clean}, 2},
		{[]string{}, 2},
		{[]string{"version"}, 0},
		{[]string{"explain", "-o", filepath.Join(os.TempDir(), "mmcheck-explain-test.html"), withErr}, 0},
		{[]string{"explain", bad}, 2},
	}
	for _, c := range cases {
		if got, _, _ := cli(c.args...); got != c.want {
			t.Errorf("mmcheck %v: exit %d, want %d", c.args, got, c.want)
		}
	}
}

func TestJSONFormat(t *testing.T) {
	code, out, _ := cli("check", "--format", "json", filepath.Join(root, "examples", "yaml-demo", "scenario.yaml"))
	if code != 1 {
		t.Fatalf("exit %d", code)
	}
	var v struct {
		SpecVersion string `json:"spec_version"`
		Diagnostics []struct {
			Code string `json:"code"`
		} `json:"diagnostics"`
	}
	if err := json.Unmarshal([]byte(out), &v); err != nil {
		t.Fatal(err)
	}
	if len(v.Diagnostics) != 2 || v.Diagnostics[0].Code != "K008" || v.Diagnostics[1].Code != "T003" {
		t.Errorf("unexpected diagnostics: %s", out)
	}
}

func TestTextFormat(t *testing.T) {
	_, out, _ := cli("check", filepath.Join(root, "examples", "yaml-demo", "scenario.yaml"))
	for _, want := range []string{"T003  移動時間が足りない  [event clerk#4]", "2 errors, 0 warnings"} {
		if !strings.Contains(out, want) {
			t.Errorf("text output lacks %q:\n%s", want, out)
		}
	}
}

// TestAgentFormat は AI 向けの出力の形と終了コードを確かめる。
func TestAgentFormat(t *testing.T) {
	code, out, _ := cli("check", "--format", "agent", "../../../examples/araki-konomi/scenario.json")
	var o agentOutput
	if err := json.Unmarshal([]byte(out), &o); err != nil {
		t.Fatalf("JSON として読めない: %v\n%s", err, out)
	}
	if code != 1 || o.OK || o.Errors != 2 || o.Warnings != 1 || len(o.Diagnostics) != 3 {
		t.Fatalf("code=%d ok=%v errors=%d warnings=%d", code, o.OK, o.Errors, o.Warnings)
	}
	d := o.Diagnostics[0]
	if d.Code != "K008" || d.Message == "" || d.Hint == "" || len(d.Args) != 3 ||
		d.Args[1].Name != "claimed_at" || d.Args[1].Time != "17:50" {
		t.Fatalf("検出結果の形が違う: %+v", d)
	}
}

// TestAgentInputError は、書式の誤りが場所つきで JSON に出て、終了コードが 2 になることを確かめる。
func TestAgentInputError(t *testing.T) {
	dir := t.TempDir()
	p := filepath.Join(dir, "bad.json")
	src := `{"start_time": 0, "end_time": 10, "characters": [{"id": "a"}], "locations": [{"id": "l"}],
	  "placements": [{"character": "a", "location": "l"}], "goals": [{"id": "g", "owner": "a"}, {"id": "g2"}]}`
	if err := os.WriteFile(p, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	code, out, errOut := cli("check", "--format", "agent", p)
	var o agentOutput
	if err := json.Unmarshal([]byte(out), &o); err != nil {
		t.Fatalf("JSON として読めない: %v\n%s", err, out)
	}
	if code != 2 || o.OK || o.InputError == nil || o.InputError.Path != "goals[1](id=g2)" ||
		!strings.Contains(errOut, "goals[1](id=g2): missing field 'owner'") {
		t.Fatalf("code=%d out=%s err=%s", code, out, errOut)
	}
}

// TestRulesCommand は規則の一覧が全規則を含むことを確かめる。
func TestRulesCommand(t *testing.T) {
	code, out, _ := cli("rules", "--format", "json")
	var rs []check.Rule
	if err := json.Unmarshal([]byte(out), &rs); err != nil || code != 0 {
		t.Fatalf("code=%d err=%v", code, err)
	}
	if len(rs) != len(check.Rules()) || len(rs) < 56 {
		t.Fatalf("規則 %d 個", len(rs))
	}
}

// TestGuideExample は、書き方ガイドの最小の例が --strict で合格することを確かめる。
func TestGuideExample(t *testing.T) {
	code, out, _ := cli("guide")
	if code != 0 {
		t.Fatal(code)
	}
	parts := strings.Split(out, "## 最小の例(検査に合格する)")
	if len(parts) != 2 {
		t.Fatal("最小の例の節がない")
	}
	ex := strings.SplitN(strings.SplitN(parts[1], "```yaml", 2)[1], "```", 2)[0]
	p := filepath.Join(t.TempDir(), "example.yaml")
	if err := os.WriteFile(p, []byte(ex), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out, errOut := cli("check", "--strict", "--format", "agent", p); code != 0 {
		t.Fatalf("最小の例が合格しない: code=%d\n%s\n%s", code, out, errOut)
	}
}
