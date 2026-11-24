"""仕様バージョンが、仕様書・Lean・Go・入力例でそろっていることを確かめる。

使い方: python3 tools/check_versions.py
"""
import glob
import json
import os
import re
import sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), ".."))


def read(p):
    return open(os.path.join(ROOT, p), encoding="utf-8").read()


def main():
    spec = re.search(r"仕様バージョン: \*\*([\d.]+)\*\*", read("docs/spec.md")).group(1)
    found = {
        "lean/MurderMystery/Spec/Basic.lean": re.search(r'specVersion : String := "([\d.]+)"',
                                                         read("lean/MurderMystery/Spec/Basic.lean")).group(1),
        "go/internal/check/check.go": re.search(r'SpecVersion = "([\d.]+)"', read("go/internal/check/check.go")).group(1),
        "tools/oracle/base.py": re.search(r'"spec_version": "([\d.]+)"', read("tools/oracle/base.py")).group(1),
        "tools/oracle/gen.py": re.search(r'"spec_version": "([\d.]+)"', read("tools/oracle/gen.py")).group(1),
    }
    for p in re.findall(r'"spec_version": "([\d.]+)"', read("docs/spec.md")):
        found.setdefault("docs/spec.md (examples)", p) if p == spec else found.update({"docs/spec.md (examples)": p})
    for p in sorted(glob.glob(os.path.join(ROOT, "examples", "*", "scenario.*"))):
        m = re.search(r'spec_version"?\s*:\s*"([\d.]+)"', open(p, encoding="utf-8").read())
        if m:
            found[os.path.relpath(p, ROOT)] = m.group(1)
    bad = {k: v for k, v in found.items() if v != spec}
    for k, v in bad.items():
        print(f"NG {k}: {v} (docs/spec.md: {spec})")
    print(f"spec version {spec}: {len(found)} places checked, {len(bad)} mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
