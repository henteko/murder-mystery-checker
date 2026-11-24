import MurderMystery

/-- Phase 3 で実装: stdin の正規化JSON を読み診断JSON を出力する。 -/
def main : IO Unit := do
  IO.println s!"\{\"spec_version\":\"{MurderMystery.specVersion}\",\"diagnostics\":[]}"
