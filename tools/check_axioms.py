"""証明の監査。

1. lean/ のソースに sorry / admit / 独自の axiom がない
2. 主要な定理(lean/scripts/Axioms.lean)が標準の公理だけに依存する

使い方: python3 tools/check_axioms.py(lean/ が lake build 済みであること)
"""
import os
import re
import subprocess
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), ".."))
LEAN = os.path.join(ROOT, "lean")
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
# exists_valid は具体例の評価に native_decide を使う。native_decide はコンパイラを信頼する公理を
# 「<補題名>._native.native_decide.ax_…」という名前で作る
NATIVE_OK = {"MurderMystery.exists_valid"}


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def main():
    problems = []
    for d, _, files in os.walk(os.path.join(LEAN, "MurderMystery")):
        for f in files:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                src = strip_comments(open(p, encoding="utf-8").read())
                for word in ("sorry", "admit"):
                    if re.search(rf"\b{word}\b", src):
                        problems.append(f"{os.path.relpath(p, ROOT)}: uses {word}")
                if re.search(r"^\s*(private\s+)?axiom\s", src, re.M):
                    problems.append(f"{os.path.relpath(p, ROOT)}: declares an axiom")
    r = subprocess.run(["lake", "env", "lean", "scripts/Axioms.lean"], cwd=LEAN, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"lean failed:\n{r.stdout}\n{r.stderr}")
    out = r.stdout.replace("\n ", " ")
    checked = 0
    for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        checked += 1
        got = {x.strip() for x in deps.split(",") if x.strip()}
        bad = {a for a in got - STANDARD
               if not (name in NATIVE_OK and (".native_decide." in a or a in ("Lean.ofReduceBool", "Lean.trustCompiler")))}
        if bad:
            problems.append(f"{name} depends on non-standard axioms: {sorted(bad)}")
    for name in re.findall(r"'([^']+)' does not depend on any axioms", out):
        checked += 1
    expected = len(re.findall(r"^#print axioms", open(os.path.join(LEAN, "scripts", "Axioms.lean")).read(), re.M))
    if checked != expected:
        problems.append(f"expected {expected} theorems in the axiom report, found {checked}:\n{r.stdout}")
    for p in problems:
        print("NG", p)
    print(f"{checked} theorems audited, {len(problems)} problems")
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
