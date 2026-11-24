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

func render(t *testing.T, s *m.Scenario, raw []byte) string {
	var b bytes.Buffer
	if err := HTML(&b, "test", check.Explain(s), check.ParseLabels(raw)); err != nil {
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
		out := render(t, s, raw)
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
	raw := []byte(`{"start_time": 0, "end_time": 10,
		"characters": [{"id": "<script>alert(1)</script>", "name": "<b>x</b>"}], "locations": [{"id": "a&b", "note": "<i>n</i>"}],
		"placements": [{"character": "<script>alert(1)</script>", "location": "a&b"}]}`)
	s, err := m.ParseScenario(raw)
	if err != nil {
		t.Fatal(err)
	}
	out := render(t, s, raw)
	if strings.Contains(out, "<b>x</b>") || strings.Contains(out, "<i>n</i>") {
		t.Fatal("表示名・説明がエスケープされていない")
	}
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
	out := render(t, s, raw)
	for _, want := range []string{
		"店員 が バックルーム から カウンター へ移動(21:30 着)", // 表示名を使い、移動元は処理前の居場所
		"移動中", "死亡", "K008", "T003",
		"ペーパーナイフ", "店員 が持っている", // 持ち物の推移
		"ずれ", // 証言の照合(このサンプルでは「ずれ」が1件)
		"店員は 21:20 にバックルームにいた", // 知識は説明文(text)で表示する
		"用語(ID と表示名・説明)",
	} {
		if !strings.Contains(out, want) {
			t.Errorf("出力に %q がない", want)
		}
	}
}

// TestDiagnosticArgsUseNames は、検出結果の詳細が表示名で出ることを確かめる(六角館のサンプル)。
func TestDiagnosticArgsUseNames(t *testing.T) {
	raw, _ := os.ReadFile(filepath.Join("..", "..", "..", "examples", "hexagon-house", "scenario.json"))
	s, err := m.ParseScenario(raw)
	if err != nil {
		t.Fatal(err)
	}
	out := render(t, s, raw)
	for _, want := range []string{"シメジ / 睡眠薬", "シメジの部屋 / 睡眠薬 / シメジ が持っている",
		"カイチョウ: ストーカーを特定する",            // ゴールの表示名
		"達成条件: 犯人投票の最多 が「kaichou」ではない", // 達成条件
	} {
		if !strings.Contains(out, want) {
			t.Errorf("出力に %q がない", want)
		}
	}
}
