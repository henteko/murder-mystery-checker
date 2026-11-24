package report

import (
	"bytes"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/henteko/murder-mystery-checker/internal/check"
	m "github.com/henteko/murder-mystery-checker/internal/model"
)

// TestImportsOnlyChecker は、HTML を作るこのパッケージが判定器の結果(check.Report)だけを使い、
// 入力のモデルや YAML から自前で意味を計算しないことを固定する。
func TestImportsOnlyChecker(t *testing.T) {
	files, _ := filepath.Glob("*.go")
	for _, f := range files {
		if strings.HasSuffix(f, "_test.go") {
			continue
		}
		af, err := parser.ParseFile(token.NewFileSet(), f, nil, parser.ImportsOnly)
		if err != nil {
			t.Fatal(err)
		}
		for _, im := range af.Imports {
			p := strings.Trim(im.Path.Value, `"`)
			if strings.Contains(p, ".") && p != "github.com/henteko/murder-mystery-checker/internal/check" {
				t.Errorf("%s imports %s: report は internal/check の結果だけを使う", f, p)
			}
		}
	}
}

func render(t *testing.T, s *m.Scenario) string {
	var b bytes.Buffer
	if err := HTML(&b, "test", check.Explain(s)); err != nil {
		t.Fatal(err)
	}
	return b.String()
}

// TestRenderAll は、すべてのテストケースとサンプルで HTML が作れることを確かめる。
func TestRenderAll(t *testing.T) {
	root := filepath.Join("..", "..", "..")
	var ps []string
	_ = filepath.WalkDir(filepath.Join(root, "testdata", "oracle"), func(p string, d os.DirEntry, err error) error {
		if err == nil && strings.HasSuffix(p, ".input.json") {
			ps = append(ps, p)
		}
		return nil
	})
	ex, _ := filepath.Glob(filepath.Join(root, "examples", "*", "scenario.json"))
	n := 0
	for _, p := range append(ps, ex...) {
		raw, _ := os.ReadFile(p)
		s, err := m.ParseScenario(raw)
		if err != nil {
			continue
		}
		out := render(t, s)
		for _, id := range []string{`id="diagnostics"`, `id="where"`, `id="events"`, `id="knowledge"`, `id="endings"`} {
			if !strings.Contains(out, id) {
				t.Fatalf("%s: %s がない", p, id)
			}
		}
		n++
	}
	if n < 200 {
		t.Fatalf("too few cases: %d", n)
	}
}

// TestEscapes は、ID などに含まれる記号が HTML として解釈されないことを確かめる。
func TestEscapes(t *testing.T) {
	s, err := m.ParseScenario([]byte(`{"start_time": 0, "end_time": 10,
		"characters": [{"id": "<script>alert(1)</script>"}], "locations": [{"id": "a&b"}],
		"placements": [{"character": "<script>alert(1)</script>", "location": "a&b"}]}`))
	if err != nil {
		t.Fatal(err)
	}
	out := render(t, s)
	if strings.Contains(out, "<script>alert") {
		t.Fatal("ID がエスケープされていない")
	}
	if !strings.Contains(out, "&lt;script&gt;") || !strings.Contains(out, "a&amp;b") {
		t.Fatal("エスケープされた ID が見つからない")
	}
}

// TestSampleContent は、YAML の見本で主な解釈が表に出ることを確かめる。
func TestSampleContent(t *testing.T) {
	raw, _ := os.ReadFile(filepath.Join("..", "..", "..", "examples", "yaml-demo", "scenario.json"))
	s, err := m.ParseScenario(raw)
	if err != nil {
		t.Fatal(err)
	}
	out := render(t, s)
	for _, want := range []string{
		"clerk が backroom から counter へ移動(21:30 着)", // 移動元は処理前の居場所
		"移動中", "死亡", "K008", "T003",
		"letter_opener", "clerk が所持", // 持ち物の推移
		"ずれ", // 証言の照合(このサンプルでは「ずれ」が1件)
	} {
		if !strings.Contains(out, want) {
			t.Errorf("出力に %q がない", want)
		}
	}
}
