package main

import (
	"fmt"
	"io"
	"strings"

	"github.com/henteko/murder-mystery-checker/internal/check"
)

func printText(w io.Writer, ds []check.Diag) {
	errs, warns := 0, 0
	for _, d := range ds {
		var b strings.Builder
		fmt.Fprintf(&b, "%-7s %s  %s", d.Sev, d.Code, check.Message(d.Code))
		if d.Event != nil {
			fmt.Fprintf(&b, "  [event %s]", *d.Event)
		}
		if len(d.Args) > 0 {
			fmt.Fprintf(&b, "\n          %s", strings.Join(d.Args, " / "))
		}
		if d.Witness != nil {
			var parts []string
			for _, e := range *d.Witness {
				v, _ := e.Val.MarshalJSON()
				parts = append(parts, e.Var+"="+string(v))
			}
			fmt.Fprintf(&b, "\n          例: %s", strings.Join(parts, ", "))
		}
		fmt.Fprintln(w, b.String())
		if d.Sev == check.Error {
			errs++
		} else {
			warns++
		}
	}
	fmt.Fprintf(w, "%d errors, %d warnings\n", errs, warns)
}
