// Command mmcheck はマーダーミステリーのシナリオの矛盾を検出する CLI。
// 仕様は docs/spec.md、形式モデルは lean/ を参照。
package main

import (
	"fmt"
	"os"
)

const specVersion = "0.2.0"

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: mmcheck check <scenario.yaml> [--format text|json]")
		os.Exit(2)
	}
	switch os.Args[1] {
	case "version":
		fmt.Printf("mmcheck (spec %s)\n", specVersion)
	default:
		fmt.Fprintf(os.Stderr, "not implemented yet: %s\n", os.Args[1])
		os.Exit(2)
	}
}
