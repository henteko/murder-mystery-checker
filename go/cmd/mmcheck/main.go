// Command mmcheck はマーダーミステリーのシナリオの矛盾を検出する CLI。
// 仕様は docs/spec.md、作者向け YAML は docs/yaml.md、形式モデルは lean/ を参照。
package main

import (
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/henteko/murder-mystery-checker/internal/check"
	m "github.com/henteko/murder-mystery-checker/internal/model"
	"github.com/henteko/murder-mystery-checker/internal/report"
	"github.com/henteko/murder-mystery-checker/internal/yamlio"
)

const usage = `usage:
  mmcheck check [--format text|json] [--strict] <scenario.yaml|scenario.json|->
  mmcheck convert <scenario.yaml>     YAML を正規化 JSON に変換して出力する
  mmcheck explain [-o out.html] <scenario.yaml|scenario.json>
                                      判定器の解釈を、原作と読み合わせるための HTML にする
  mmcheck version

終了コード: 0 = error なし / 1 = error あり(--strict なら warning も)/ 2 = 入力エラー`

func main() { os.Exit(run(os.Args[1:], os.Stdin, os.Stdout, os.Stderr)) }

func run(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) == 0 {
		fmt.Fprintln(stderr, usage)
		return 2
	}
	switch args[0] {
	case "version":
		fmt.Fprintf(stdout, "mmcheck (spec %s)\n", check.SpecVersion)
		return 0
	case "convert":
		if len(args) != 2 {
			fmt.Fprintln(stderr, usage)
			return 2
		}
		src, err := readInput(args[1], stdin)
		if err == nil {
			var out []byte
			if out, err = yamlio.ToJSON(src); err == nil {
				fmt.Fprintln(stdout, string(out))
				return 0
			}
		}
		fmt.Fprintln(stderr, err)
		return 2
	case "explain":
		fs := flag.NewFlagSet("explain", flag.ContinueOnError)
		fs.SetOutput(stderr)
		out := fs.String("o", "", "output HTML file (default: stdout)")
		if err := fs.Parse(args[1:]); err != nil || fs.NArg() != 1 {
			fmt.Fprintln(stderr, usage)
			return 2
		}
		return runExplain(fs.Arg(0), *out, stdin, stdout, stderr)
	case "check":
		fs := flag.NewFlagSet("check", flag.ContinueOnError)
		fs.SetOutput(stderr)
		format := fs.String("format", "text", "output format: text or json")
		strict := fs.Bool("strict", false, "treat warnings as failures (exit code 1)")
		if err := fs.Parse(args[1:]); err != nil || fs.NArg() != 1 || (*format != "text" && *format != "json") {
			fmt.Fprintln(stderr, usage)
			return 2
		}
		return runCheck(fs.Arg(0), *format, *strict, stdin, stdout, stderr)
	}
	fmt.Fprintln(stderr, usage)
	return 2
}

func readInput(path string, stdin io.Reader) ([]byte, error) {
	if path == "-" {
		return io.ReadAll(stdin)
	}
	return os.ReadFile(path)
}

func load(path string, src []byte) (*m.Scenario, error) {
	ext := strings.ToLower(filepath.Ext(path))
	if ext == ".yaml" || ext == ".yml" {
		return yamlio.Load(src)
	}
	return m.ParseScenario(src)
}

func runExplain(path, out string, stdin io.Reader, stdout, stderr io.Writer) int {
	src, err := readInput(path, stdin)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	// 表示名と説明(name / note)は正規化 JSON から読む。YAML は変換してから読む
	j := src
	if ext := strings.ToLower(filepath.Ext(path)); ext == ".yaml" || ext == ".yml" {
		if j, err = yamlio.ToJSON(src); err != nil {
			fmt.Fprintln(stderr, err)
			return 2
		}
	}
	s, err := m.ParseScenario(j)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	w := stdout
	if out != "" {
		f, err := os.Create(out)
		if err != nil {
			fmt.Fprintln(stderr, err)
			return 2
		}
		defer f.Close()
		w = f
	}
	if err := report.HTML(w, filepath.Base(path), check.Explain(s), check.ParseLabels(j)); err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	return 0
}

func runCheck(path, format string, strict bool, stdin io.Reader, stdout, stderr io.Writer) int {
	src, err := readInput(path, stdin)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 2
	}
	s, err := load(path, src)
	if err != nil {
		var ie *m.InputError
		if !errors.As(err, &ie) {
			err = &m.InputError{Msg: err.Error()}
		}
		fmt.Fprintln(stderr, err)
		return 2
	}
	ds := check.Check(s)
	if format == "json" {
		out, _ := json.MarshalIndent(check.Output{SpecVersion: check.SpecVersion, Diagnostics: ds}, "", "  ")
		fmt.Fprintln(stdout, string(out))
	} else {
		printText(stdout, ds)
	}
	errs, warns := 0, 0
	for _, d := range ds {
		if d.Sev == check.Error {
			errs++
		} else {
			warns++
		}
	}
	if errs > 0 || (strict && warns > 0) {
		return 1
	}
	return 0
}
