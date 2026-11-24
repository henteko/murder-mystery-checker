package check

import (
	"encoding/json"
	"errors"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// TestGolden は Lean オラクルの期待出力(testdata/oracle と examples)と Go の出力を比べる差分テスト。
func TestGolden(t *testing.T) {
	root := filepath.Join("..", "..", "..")
	var cases [][2]string
	_ = filepath.WalkDir(filepath.Join(root, "testdata", "oracle"), func(p string, d os.DirEntry, err error) error {
		if err == nil && strings.HasSuffix(p, ".input.json") {
			cases = append(cases, [2]string{p, strings.TrimSuffix(p, ".input.json") + ".expected.json"})
		}
		return nil
	})
	ex, _ := filepath.Glob(filepath.Join(root, "examples", "*", "scenario.json"))
	for _, p := range ex {
		cases = append(cases, [2]string{p, filepath.Join(filepath.Dir(p), "expected.json")})
	}
	if len(cases) < 100 {
		t.Fatalf("too few golden cases: %d", len(cases))
	}
	for _, c := range cases {
		name, _ := filepath.Rel(root, c[0])
		t.Run(name, func(t *testing.T) {
			in, err := os.ReadFile(c[0])
			if err != nil {
				t.Fatal(err)
			}
			wantRaw, err := os.ReadFile(c[1])
			if err != nil {
				t.Fatal(err)
			}
			var want map[string]any
			if err := json.Unmarshal(wantRaw, &want); err != nil {
				t.Fatal(err)
			}
			s, err := m.ParseScenario(in)
			if want["input_error"] == true {
				var ie *m.InputError
				if !errors.As(err, &ie) {
					t.Fatalf("want input error, got err=%v", err)
				}
				return
			}
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			gotRaw, _ := json.Marshal(Output{SpecVersion: SpecVersion, Diagnostics: Check(s)})
			var got map[string]any
			_ = json.Unmarshal(gotRaw, &got)
			if !reflect.DeepEqual(got, want) {
				g, _ := json.MarshalIndent(got["diagnostics"], "", " ")
				w, _ := json.MarshalIndent(want["diagnostics"], "", " ")
				t.Errorf("mismatch\n--- go\n%s\n--- lean\n%s", g, w)
			}
		})
	}
}
