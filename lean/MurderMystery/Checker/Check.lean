import MurderMystery.Checker.G

/-!
# 判定器の入口 (docs/spec.md §3)
-/
namespace MurderMystery

/-- 正規化前の検出結果。R の違反があれば R のみ。 -/
def checkRaw (s : Scenario) : List Diag :=
  let r := checkR s
  if r.isEmpty then checkEvents s ++ checkPost s ++ checkG s else r

/-- 判定器: 正規順序で、重複なし (§6.2, §6.3)。 -/
def check (s : Scenario) : List Diag := normalize (checkRaw s)

end MurderMystery
