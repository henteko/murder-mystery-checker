"""ライブ差分テスト: その場で作ったシナリオで、Go 実装と Lean オラクルの出力を比べる。

ゴールデン(testdata/oracle)は固定のケースしか比べないので、こちらで新しい入力を大量に試す。
入力の作り方:
  gen        ランダム生成 (tools/oracle/gen.py)
  gen-empty  ランダム生成で、ゴール・選択・エンディング・制約の一部を空にしたもの
  example    examples/*/scenario.json を変異 (tools/oracle/mutate.py)
  case       手書きケース (testdata/oracle/{rules,edge,regress}) を変異
  broken     壊した入力(入力エラーの判定が一致するか)

比べる内容:
  - Lean と Go で、入力エラーになるかどうかが一致する
  - 入力エラーでなければ、検出結果(並び順を含む)が完全に一致する
  - Go について、トップレベルの配列を並べ替えても出力が変わらない(定理 3)

不一致の入力は --out に保存する。testdata/oracle/regress/ に回帰テストとして足すとよい。

使い方: python3 tools/oracle/live.py --oracle lean/.lake/build/bin/oracle --mmcheck bin/mmcheck [--count 500] [--seed N]
"""
import argparse
import collections
import glob
import json
import os
import random
import re
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(__file__))
import gen  # noqa: E402
from mutate import corrupt, mutate, shuffle_arrays  # noqa: E402

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))


def load_json(p):
    with open(p, encoding="utf-8") as f:
        return json.load(f)


class Runner:
    def __init__(self, oracle, mmcheck, tmp):
        self.oracle, self.mmcheck, self.tmp = oracle, mmcheck, tmp

    def lean(self, text):
        r = subprocess.run([self.oracle], input=text.encode(), capture_output=True, timeout=120)
        if r.returncode == 2:
            return "input_error"
        if r.returncode != 0:
            raise RuntimeError(f"oracle crashed: {r.stderr.decode()[:300]}")
        return json.loads(r.stdout)

    def go(self, text):
        path = os.path.join(self.tmp, "case.json")
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        r = subprocess.run([self.mmcheck, "check", "--format", "json", path], capture_output=True, timeout=120)
        if r.returncode == 2:
            return "input_error"
        if r.returncode not in (0, 1):
            raise RuntimeError(f"mmcheck crashed: {r.stderr.decode()[:300]}")
        return json.loads(r.stdout)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--oracle", required=True)
    ap.add_argument("--mmcheck", required=True)
    ap.add_argument("--count", type=int, default=500)
    ap.add_argument("--seed", type=int, default=None)
    ap.add_argument("--out", default=os.path.join(ROOT, "testdata", "live-failures"))
    args = ap.parse_args()
    seed = args.seed if args.seed is not None else int(time.time())
    rng = random.Random(seed)
    examples = [load_json(p) for p in sorted(glob.glob(os.path.join(ROOT, "examples", "*", "scenario.json")))]
    cases = []
    for p in sorted(glob.glob(os.path.join(ROOT, "testdata", "oracle", "*", "*.input.json"))):
        if os.path.basename(os.path.dirname(p)) in ("rules", "edge", "regress"):
            cases.append(load_json(p))
    sources = ["gen"] * 4 + ["gen-empty"] + ["example"] * 2 + ["case"] * 2 + ["broken"]
    stats = collections.Counter()
    failures = []
    codes = collections.Counter()
    with tempfile.TemporaryDirectory() as tmp:
        run = Runner(args.oracle, args.mmcheck, tmp)
        for i in range(args.count):
            src = rng.choice(sources)
            if src in ("gen", "gen-empty"):
                s = gen.gen(rng, i)
                if src == "gen-empty":
                    for k in rng.sample(["goals", "choices", "endings", "constraints"], k=rng.randint(1, 4)):
                        s[k] = []
            elif src == "example":
                s = mutate(rng, rng.choice(examples))
            elif src == "case":
                s = mutate(rng, rng.choice(cases))
            else:
                s = mutate(rng, rng.choice(cases + examples), steps=1)
            text = corrupt(rng, s) if src == "broken" else json.dumps(s, ensure_ascii=False)
            lean, go = run.lean(text), run.go(text)
            stats[src] += 1
            stats["input_error"] += lean == "input_error"
            if lean != "input_error":
                codes.update({d["code"] for d in lean["diagnostics"]})
            problem = None
            if (lean == "input_error") != (go == "input_error"):
                problem = f"input error: lean={lean == 'input_error'} go={go == 'input_error'}"
            elif lean != "input_error" and lean != go:
                problem = "diagnostics differ"
            elif lean != "input_error" and src != "broken" and rng.random() < 0.3:
                stats["shuffled"] += 1
                if run.go(json.dumps(shuffle_arrays(rng, s), ensure_ascii=False)) != go:
                    problem = "go output changed after shuffling top-level arrays (theorem 3)"
            if problem:
                os.makedirs(args.out, exist_ok=True)
                name = os.path.join(args.out, f"live_{seed}_{i}")
                with open(name + ".input.json", "w", encoding="utf-8") as f:
                    f.write(text)
                with open(name + ".txt", "w", encoding="utf-8") as f:
                    f.write(f"{problem}\nsource: {src}\n--- lean\n{json.dumps(lean, ensure_ascii=False, indent=1)}\n"
                            f"--- go\n{json.dumps(go, ensure_ascii=False, indent=1)}\n")
                failures.append(f"{name}.input.json: {problem}")
    print(f"seed {seed}: {args.count} cases "
          f"({', '.join(f'{k} {stats[k]}' for k in ['gen', 'gen-empty', 'example', 'case', 'broken'])}; "
          f"input errors {stats['input_error']}, shuffled {stats['shuffled']}), {len(failures)} mismatches")
    with open(os.path.join(ROOT, "docs", "spec.md"), encoding="utf-8") as f:
        all_codes = sorted(set(re.findall(r"^\| ([RTIKHAG]\d{3}) \|", f.read(), re.M)))
    missing = [c for c in all_codes if c not in codes]
    print(f"rules exercised: {len(all_codes) - len(missing)}/{len(all_codes)}" + (f" (not seen: {' '.join(missing)})" if missing else ""))
    for f in failures[:20]:
        print("NG", f)
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
