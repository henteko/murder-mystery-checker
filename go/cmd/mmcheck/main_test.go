package main

import (
	"bytes"
	"encoding/json"
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
