// Command mmcheck はマーダーミステリーのシナリオの矛盾を検出する CLI。
// 仕様は docs/spec.md、作者向け YAML は docs/yaml.md、形式モデルは lean/ を参照。
package main

import (
	_ "embed"
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

//go:embed guide.md
var guide string

const usage = `usage:
  mmcheck check [--format text|json|agent] [--strict] <scenario.yaml|scenario.json|->
                                      agent: AI 向けの JSON(合否・説明・引数名・直し方のヒント)
  mmcheck rules [--format text|json]  全規則のコード・重大度・説明・引数・ヒント
  mmcheck guide                       シナリオの書き方(YAML)と最小の例
  mmcheck convert <scenario.yaml>     YAML を正規化 JSON に変換して出力する
  mmcheck explain [-o out.html] <scenario.yaml|scenario.json>
                                      判定器の解釈を、原作と読み合わせるための HTML にする
  mmcheck stats [--format text|json|agent] [--require '<条件>']... <scenario.yaml|scenario.json|->
                                      複雑度の指標と水増しの候補。--require は 'score>=50'、
                                      'axis.branching>=60'、'count(padding.idle_moves)==0' など。
                                      条件をすべて満たせば 0、満たさなければ 1(docs/stats.md)
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
	case "rules":
		fs := flag.NewFlagSet("rules", flag.ContinueOnError)
		fs.SetOutput(stderr)
		format := fs.String("format", "text", "output format: text or json")
		if err := fs.Parse(args[1:]); err != nil || fs.NArg() != 0 || (*format != "text" && *format != "json") {
			fmt.Fprintln(stderr, usage)
			return 2
		}
		printRules(stdout, *format)
		return 0
	case "guide":
		if len(args) != 1 {
			fmt.Fprintln(stderr, usage)
			return 2
		}
		fmt.Fprint(stdout, guide)
		return 0
	case "stats":
		fs := flag.NewFlagSet("stats", flag.ContinueOnError)
		fs.SetOutput(stderr)
		format := fs.String("format", "text", "output format: text, json or agent")
		var requires stringList
		fs.Var(&requires, "require", "condition such as 'score>=50' (repeatable)")
		if err := fs.Parse(args[1:]); err != nil || fs.NArg() != 1 || (*format != "text" && *format != "json" && *format != "agent") {
			fmt.Fprintln(stderr, usage)
			return 2
		}
		return runStats(fs.Arg(0), *format, requires, stdin, stdout, stderr)
	case "check":
		fs := flag.NewFlagSet("check", flag.ContinueOnError)
		fs.SetOutput(stderr)
		format := fs.String("format", "text", "output format: text, json or agent")
		strict := fs.Bool("strict", false, "treat warnings as failures (exit code 1)")
		if err := fs.Parse(args[1:]); err != nil || fs.NArg() != 1 || (*format != "text" && *format != "json" && *format != "agent") {
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
	if err == nil {
		var s *m.Scenario
		if s, err = load(path, src); err == nil {
			return reportDiags(check.Check(s), format, strict, stdout)
		}
	}
	var ie *m.InputError
	if !errors.As(err, &ie) {
		ie = &m.InputError{Msg: err.Error()}
	}
	if format == "agent" {
		writeAgent(stdout, agentOutput{OK: false, SpecVersion: check.SpecVersion,
			InputError:  &agentInputError{Message: ie.Msg, Path: ie.Path},
			Diagnostics: []agentDiag{}})
	}
	fmt.Fprintln(stderr, ie)
	return 2
}

func reportDiags(ds []check.Diag, format string, strict bool, stdout io.Writer) int {
	if format == "agent" {
		return writeAgent(stdout, agentReport(ds, strict))
	}
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

// ---------------------------------------------------------------- AI 向けの出力(--format agent)

type agentInputError struct {
	Message string `json:"message"`
	Path    string `json:"path,omitempty"`
}

type agentDiag struct {
	Code     string               `json:"code"`
	Severity string               `json:"severity"`
	Message  string               `json:"message"`
	Hint     string               `json:"hint"`
	Event    *string              `json:"event,omitempty"`
	Args     []check.NamedArg     `json:"args"`
	Witness  map[string]check.Val `json:"witness,omitempty"`
}

type agentOutput struct {
	OK          bool             `json:"ok"`
	SpecVersion string           `json:"spec_version"`
	Errors      int              `json:"errors"`
	Warnings    int              `json:"warnings"`
	InputError  *agentInputError `json:"input_error,omitempty"`
	Diagnostics []agentDiag      `json:"diagnostics"`
}

func agentReport(ds []check.Diag, strict bool) agentOutput {
	out := agentOutput{SpecVersion: check.SpecVersion, Diagnostics: []agentDiag{}}
	for _, d := range ds {
		if d.Sev == check.Error {
			out.Errors++
		} else {
			out.Warnings++
		}
		ad := agentDiag{Code: d.Code, Severity: d.Sev.String(), Message: check.Message(d.Code),
			Hint: check.Hint(d.Code), Event: d.Event, Args: check.NameArgs(d)}
		if d.Witness != nil {
			ad.Witness = map[string]check.Val{}
			for _, e := range *d.Witness {
				ad.Witness[e.Var] = e.Val
			}
		}
		out.Diagnostics = append(out.Diagnostics, ad)
	}
	out.OK = out.Errors == 0 && !(strict && out.Warnings > 0)
	return out
}

// writeAgent は AI 向けの JSON を書き、終了コード(0 合格 / 1 不合格 / 2 入力エラー)を返す。
func writeAgent(w io.Writer, o agentOutput) int {
	b, _ := json.MarshalIndent(o, "", "  ")
	fmt.Fprintln(w, string(b))
	switch {
	case o.InputError != nil:
		return 2
	case o.OK:
		return 0
	}
	return 1
}

func printRules(w io.Writer, format string) {
	rs := check.Rules()
	if format == "json" {
		b, _ := json.MarshalIndent(rs, "", "  ")
		fmt.Fprintln(w, string(b))
		return
	}
	for _, r := range rs {
		fmt.Fprintf(w, "%s  %-7s  %s\n", r.Code, r.Severity, r.Message)
		if len(r.Args) > 0 {
			fmt.Fprintf(w, "      args: %s\n", strings.Join(r.Args, ", "))
		}
		fmt.Fprintf(w, "      hint: %s\n", r.Hint)
	}
}
