package check

import (
	"encoding/json"
	"math/rand"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	m "github.com/henteko/murder-mystery-checker/internal/model"
)

func oracleInputs(t testing.TB) []string {
	var ps []string
	_ = filepath.WalkDir(filepath.Join("..", "..", "..", "testdata", "oracle"), func(p string, d os.DirEntry, err error) error {
		if err == nil && strings.HasSuffix(p, ".input.json") {
			ps = append(ps, p)
		}
		return nil
	})
	return ps
}

// checkSorted は出力が正規順序で狭義に整列している(重複がない)ことを確かめる(定理 3)。
func checkSorted(t testing.TB, ds []Diag) {
	for i := 1; i < len(ds); i++ {
		if Compare(ds[i-1], ds[i]) >= 0 {
			t.Fatalf("output not strictly sorted at %d: %+v / %+v", i, ds[i-1], ds[i])
		}
	}
}

// TestPermutationInvariance はトップレベルの配列を並べ替えても出力が変わらないことを確かめる(定理 3)。
func TestPermutationInvariance(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	for _, p := range oracleInputs(t) {
		raw, _ := os.ReadFile(p)
		s, err := m.ParseScenario(raw)
		if err != nil {
			continue
		}
		want, _ := json.Marshal(Check(s))
		var doc map[string]any
		if json.Unmarshal(raw, &doc) != nil {
			continue
		}
		for k := 0; k < 3; k++ {
			for _, v := range doc {
				if l, ok := v.([]any); ok {
					rng.Shuffle(len(l), func(i, j int) { l[i], l[j] = l[j], l[i] })
				}
			}
			shuffled, _ := json.Marshal(doc)
			s2, err := m.ParseScenario(shuffled)
			if err != nil {
				t.Fatalf("%s: shuffled input rejected: %v", p, err)
			}
			if got, _ := json.Marshal(Check(s2)); string(got) != string(want) {
				t.Fatalf("%s: output changed after shuffling\n got %s\nwant %s", p, got, want)
			}
		}
	}
}

// FuzzCheck はどんな入力でもパニックせず、出力が正規順序で重複がないことを確かめる。
// 通常の go test ではシード(testdata/oracle の入力)だけを試す。go test -fuzz=FuzzCheck で探索する。
func FuzzCheck(f *testing.F) {
	for _, p := range oracleInputs(f) {
		raw, _ := os.ReadFile(p)
		f.Add(raw)
	}
	f.Fuzz(func(t *testing.T, data []byte) {
		s, err := m.ParseScenario(data)
		if err != nil {
			if _, ok := err.(*m.InputError); !ok {
				t.Fatalf("non-input error: %v", err)
			}
			return
		}
		ds := Check(s)
		checkSorted(t, ds)
		if !reflect.DeepEqual(ds, normalize(ds)) {
			t.Fatal("normalize is not idempotent")
		}
	})
}
