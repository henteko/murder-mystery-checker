"""オラクル用テストケースの点検。

1. どの入力にも期待出力がある
2. 各ケースの "expect" のコードが期待出力に含まれる(入力エラーのケースは入力エラーになる)
3. 仕様書 §4 の全規則のコードが、手書きケース(rules/)の期待出力のどこかに現れる
4. 仕様書 §9 の例の期待出力が、オラクルの出力と一致する

使い方: python3 tools/oracle/check.py
"""
import glob
import json
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))
ORACLE = os.path.join(ROOT, "testdata", "oracle")


def spec_codes():
    text = open(os.path.join(ROOT, "docs", "spec.md"), encoding="utf-8").read()
    return sorted(set(re.findall(r"^\| ([RTIKHAG]\d{3}) \|", text, re.M)))


def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def case_meta(inp):
    side = inp[: -len(".input.json")] + ".case.json"
    if os.path.exists(side):
        return load(side)
    try:
        return load(inp).get("_case")
    except (json.JSONDecodeError, AttributeError):
        return None


def main():
    problems = []
    seen = {}
    inputs = sorted(glob.glob(os.path.join(ORACLE, "**", "*.input.json"), recursive=True))
    for inp in inputs:
        rel = os.path.relpath(inp, ROOT)
        exp_path = inp[: -len(".input.json")] + ".expected.json"
        if not os.path.exists(exp_path):
            problems.append(f"{rel}: expected file missing (run make oracle)")
            continue
        exp = load(exp_path)
        codes = set() if exp.get("input_error") else {d["code"] for d in exp["diagnostics"]}
        group = os.path.basename(os.path.dirname(inp))
        for c in codes:
            seen.setdefault(c, set()).add(group)
        meta = case_meta(inp)
        if not meta:
            continue
        want = meta.get("expect")
        if want is None:  # ランダム生成のケースは期待コードを持たない
            continue
        if want == ["input_error"]:
            if not exp.get("input_error"):
                problems.append(f"{rel}: expected an input error")
        elif exp.get("input_error"):
            problems.append(f"{rel}: unexpected input error")
        else:
            missing = [c for c in want if c not in codes]
            if missing:
                problems.append(f"{rel}: missing {missing}, got {sorted(codes)}")
            if not want and codes:
                problems.append(f"{rel}: expected no diagnostics, got {sorted(codes)}")
    all_codes = spec_codes()
    uncovered = [c for c in all_codes if "rules" not in seen.get(c, set())]
    if uncovered:
        problems.append(f"rules not covered by testdata/oracle/rules: {uncovered}")
    spec_out = os.path.join(ORACLE, "spec", "example.expected.json")
    spec_want = os.path.join(ORACLE, "spec", "example.spec_expected.json")
    if load(spec_out) != load(spec_want):
        problems.append("docs/spec.md §9: the expected output in the spec differs from the oracle")
    for p in problems:
        print("NG", p)
    print(f"{len(inputs)} cases, {len(all_codes)} rules, "
          f"{len(all_codes) - len(uncovered)} covered by rules/, {len(problems)} problems")
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
