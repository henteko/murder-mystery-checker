"""Lean オラクルで期待出力を作り直す。

testdata/oracle/**/NAME.input.json → NAME.expected.json
examples/*/scenario.json          → expected.json

入力エラー(オラクルの終了コード 2)は {"input_error": true} と書く。
使い方: python3 tools/oracle/regen.py <oracle の実行ファイル>
"""
import glob
import os
import subprocess
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", ".."))


def targets():
    for inp in sorted(glob.glob(os.path.join(ROOT, "testdata", "oracle", "**", "*.input.json"), recursive=True)):
        yield inp, inp[: -len(".input.json")] + ".expected.json"
    for inp in sorted(glob.glob(os.path.join(ROOT, "examples", "*", "scenario.json"))):
        yield inp, os.path.join(os.path.dirname(inp), "expected.json")


def main():
    oracle = sys.argv[1]
    n = errors = 0
    for inp, out in targets():
        with open(inp, "rb") as f:
            r = subprocess.run([oracle], stdin=f, capture_output=True)
        if r.returncode == 0:
            body = r.stdout
        elif r.returncode == 2:
            body = b'{"input_error": true}\n'
            errors += 1
        else:
            sys.exit(f"oracle failed on {inp} (exit {r.returncode}): {r.stderr.decode()}")
        with open(out, "wb") as f:
            f.write(body)
        n += 1
    print(f"regenerated {n} expected files ({errors} input errors)")


if __name__ == "__main__":
    main()
