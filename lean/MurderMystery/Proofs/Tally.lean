import MurderMystery.Proofs.Basic

/-!
# 定理 10: 集計の分割

票が1つ以上あり、どの票も値の集合 values のどれかであれば、
`tie` が真で全ての `plurality` が偽になるか、`tie` が偽でちょうど1つの値 x について `plurality x` が真になる。
したがって「各値の plurality」と「tie」をエンディングに割り当てれば、エンディングは必ずちょうど1つに決まる。
-/
namespace MurderMystery

theorem mem_winners (vals : List Val) (w : Val) (h : w ∈ winners vals) : w ∈ vals := by
  simp only [winners, List.mem_filter] at h
  exact (mem_dedup w vals).mp h.1

theorem winners_ne_nil (vals : List Val) (hv : vals ≠ []) : winners vals ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hv
  have hds : dedup (x :: xs) ≠ [] := by
    intro h
    have : x ∈ dedup (x :: xs) := (mem_dedup x _).mpr (by simp)
    simp [h] at this
  have hmap : (dedup (x :: xs)).map (count (x :: xs)) ≠ [] := by simpa using hds
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp (mt List.max?_eq_none_iff.mp hmap)
  have hmem := List.max?_mem hm
  obtain ⟨w, hw, hcw⟩ := List.mem_map.mp hmem
  simp only [winners, hm, Option.getD_some]
  intro h
  have : w ∈ (dedup (x :: xs)).filter (fun w => count (x :: xs) w == m) := by
    simp [hw, hcw]
  simp [h] at this

theorem tally_partition (σ : Assignment) (votes : List Id) (values : List String)
    (hv : votes ≠ []) (hwt : ∀ v ∈ votes, ∃ x ∈ values, σ v = .str x) :
    ((Formula.tie votes).eval σ = true ∧ ∀ x, (Formula.plurality votes x).eval σ = false) ∨
    ((Formula.tie votes).eval σ = false ∧ ∃ x ∈ values, (Formula.plurality votes x).eval σ = true ∧
      ∀ y, y ≠ x → (Formula.plurality votes y).eval σ = false) := by
  simp only [Formula.eval]
  have hne : winners (votes.map σ) ≠ [] := winners_ne_nil _ (by simpa using hv)
  match hw : winners (votes.map σ) with
  | [] => exact absurd hw hne
  | [w] =>
    right
    have hwmem : w ∈ votes.map σ := mem_winners _ w (by simp [hw])
    obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hwmem
    obtain ⟨x, hx, hσ⟩ := hwt v hv'
    refine ⟨by simp, x, hx, by simp [hσ], fun y hy => ?_⟩
    simp [hσ, Ne.symm hy]
  | _ :: _ :: _ =>
    left
    refine ⟨by simp, fun x => by simp⟩

end MurderMystery
