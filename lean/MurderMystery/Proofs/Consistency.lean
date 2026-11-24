import MurderMystery.Proofs.Main

/-!
# 定理 6: 仕様の無矛盾性

正しいシナリオが少なくとも1つ存在する(`Valid` が空虚な条件ではない)。
この定理だけは `native_decide` を使うため、標準の公理に加えて `Lean.ofReduceBool` に依存する。
-/
namespace MurderMystery

/-- 1人・1か所・ゴール1つ・エンディング1つの最小のシナリオ。 -/
def tinyScenario : Scenario where
  startTime := 0
  endTime := 60
  characters := [{ id := "alice" }]
  locations := [{ id := "hall" }]
  placements := [{ character := "alice", location := "hall" }]
  goals := [{ id := "g", owner := "alice" }]
  endings := [{ id := "end", condition := .const true }]

/-- 判定器は検出結果を出さない。マージソートなどの整礎再帰のためカーネルでは評価が止まるので、
`native_decide`(コンパイル済みコードによる評価。公理 `Lean.ofReduceBool` に依存)で確かめる。 -/
theorem tinyScenario_check : check tinyScenario = [] := by native_decide

theorem exists_valid : ∃ s, Valid s :=
  ⟨tinyScenario, (check_valid tinyScenario).mp (by simp [tinyScenario_check])⟩

end MurderMystery
