import MurderMystery.Proofs.Events

/-!
# 終了状態・区間に対する規則: 判定関数 ⇔ 宣言的な仕様
-/
namespace MurderMystery

theorem issuesK003_nil (s : Scenario) :
    issuesK003 s = [] ↔ ∀ f ∈ s.solutionFacts, s.obtainable f = true := by
  simp only [issuesK003, List.filterMap_eq_nil_iff]
  apply forall_congr'; intro f; apply forall_congr'; intro _
  by_cases h : s.obtainable f <;> simp [h]

theorem issuesK004K005_nil (s : Scenario) :
    issuesK004K005 s = [] ↔ ∀ c ∈ s.clues, ∀ i, c.item = some i →
      s.final.holder i ≠ .consumed ∧ ∀ l, c.location = some l → s.final.holder i = .place l := by
  simp only [issuesK004K005, List.flatMap_eq_nil_iff]
  apply forall_congr'; intro c; apply forall_congr'; intro _
  cases hi : c.item with
  | none => simp
  | some i =>
    simp only [Option.some.injEq, forall_eq']
    by_cases hc : s.final.holder i = .consumed
    · simp [hc]
    · simp only [hc, beq_iff_eq, ite_false, ne_eq, not_false_eq_true, true_and]
      cases hl : c.location with
      | none => simp
      | some l =>
        simp only [Option.some.injEq, forall_eq']
        by_cases hp : s.final.holder i = .place l <;> simp [hp]

theorem issuesK006_nil (s : Scenario) :
    issuesK006 s = [] ↔ ∀ f ∈ s.facts, f.truth = false → s.held f.id = true →
      ∃ r ∈ f.contradictedBy, s.obtainable r = true := by
  simp only [issuesK006, List.filterMap_eq_nil_iff]
  apply forall_congr'; intro f; apply forall_congr'; intro _
  cases ht : f.truth <;> cases hh : s.held f.id <;> simp [List.any_eq_true]

theorem issuesK007_nil (s : Scenario) :
    issuesK007 s = [] ↔ ∀ f ∈ s.solutionFacts, ∀ fact, s.findFact? f = some fact → fact.truth = true := by
  simp only [issuesK007, List.filterMap_eq_nil_iff]
  apply forall_congr'; intro f; apply forall_congr'; intro _
  cases hf : s.findFact? f with
  | none => simp
  | some fact =>
    simp only [Option.some.injEq, forall_eq']
    cases fact.truth <;> simp

theorem issuesK008_nil (s : Scenario) :
    issuesK008 s = [] ↔ ∀ f ∈ s.facts, f.truth = true → ∀ eid claimed e,
      f.aboutEvent = some eid → f.claimedAt = some claimed → s.findEvent? eid = some e →
      absDiff claimed (f.actualTime e) ≤ f.tolerance.getD s.claimTolerance := by
  simp only [issuesK008, List.filterMap_eq_nil_iff]
  apply forall_congr'; intro f; apply forall_congr'; intro _
  cases ht : f.truth
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, forall_const]
    cases ha : f.aboutEvent with
    | none => simp
    | some eid =>
      cases hc : f.claimedAt with
      | none => simp
      | some claimed =>
        simp only [Option.some.injEq]
        cases he : s.findEvent? eid with
        | none =>
          simp only [true_iff]
          intro eid' claimed' e' h1 _ h3
          subst h1
          simp [he] at h3
        | some e =>
          constructor
          · intro h eid' claimed' e' h1 h2 h3
            subst h1 h2
            rw [he] at h3
            simp only [Option.some.injEq] at h3
            subst h3
            by_cases hlt : absDiff claimed (f.actualTime e) > f.tolerance.getD s.claimTolerance
            · simp [hlt] at h
            · exact Nat.le_of_not_lt hlt
          · intro h
            have := h eid claimed e rfl rfl he
            simp [Nat.not_lt.mpr this]

theorem issuesH_nil (s : Scenario) :
    issuesH s = [] ↔
      (∀ h ∈ s.handouts,
        (∀ l, h.location = some l → (s.final.pos h.character).dest = l) ∧
        (∀ is, h.items = some is → ∀ i ∈ is, s.final.holder i = .char h.character) ∧
        (∀ ks, h.knows = some ks → ∀ f ∈ ks, s.final.knows h.character f = true)) ∧
      (∀ b ∈ s.board, ∀ i ∈ b.items, s.final.holder i = .place b.location) := by
  unfold issuesH
  dsimp only
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, and_assoc]
  apply and_congr
  · apply forall_congr'; intro h; apply forall_congr'; intro _
    apply and_congr
    · cases h.location with
      | none => simp
      | some l => by_cases hd : (s.final.pos h.character).dest = l <;> simp [hd]
    · apply and_congr
      · cases h.items with
        | none => simp
        | some is =>
          simp only [Option.some.injEq, forall_eq', List.filterMap_eq_nil_iff]
          apply forall_congr'; intro i; apply forall_congr'; intro _
          by_cases hc : s.final.holder i = .char h.character <;> simp [hc]
      · cases h.knows with
        | none => simp
        | some ks =>
          simp only [Option.some.injEq, forall_eq', List.filterMap_eq_nil_iff]
          apply forall_congr'; intro f; apply forall_congr'; intro _
          by_cases hc : s.final.knows h.character f <;> simp [hc]
  · apply forall_congr'; intro b; apply forall_congr'; intro _
    simp only [List.filterMap_eq_nil_iff]
    apply forall_congr'; intro i; apply forall_congr'; intro _
    by_cases hc : s.final.holder i = .place b.location <;> simp [hc]

theorem issuesA_nil (s : Scenario) :
    issuesA s = [] ↔
      ∀ a ∈ s.assertions, ∀ c ∈ a.characters, a.kind.violated (s.whereAt c a.time) a.location = false := by
  simp only [issuesA, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  apply forall_congr'; intro a; apply forall_congr'; intro _
  apply forall_congr'; intro c; apply forall_congr'; intro _
  cases a.kind.violated (s.whereAt c a.time) a.location <;> simp

theorem postErrors_nil (s : Scenario) : postErrors s = [] ↔ PostValid s := by
  unfold postErrors PostValid
  simp only [List.append_eq_nil_iff, issuesK003_nil, issuesK004K005_nil, issuesK006_nil,
    issuesK007_nil, issuesK008_nil, issuesH_nil, issuesA_nil, and_assoc]

theorem sev_checkT012 (s : Scenario) : ∀ d ∈ checkT012 s, d.sev = .warning := by
  intro d hd
  simp only [checkT012, List.mem_flatMap, List.mem_map] at hd
  obtain ⟨_, _, _, _, _, _, rfl⟩ := hd
  rfl

/-- 終了状態に対する検査が error を出さない ⇔ `PostValid`。 -/
theorem checkPost_valid (s : Scenario) :
    (∀ d ∈ checkPost s, d.sev = .warning) ↔ PostValid s := by
  rw [← postErrors_nil]
  unfold checkPost
  simp only [List.mem_append, List.mem_map]
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have := h _ (Or.inl (Or.inl ⟨x, hx, rfl⟩))
    simp [err] at this
  · intro h d hd
    rcases hd with (⟨x, hx, _⟩ | ⟨x, _, rfl⟩) | hd
    · simp [h] at hx
    · simp [warn]
    · exact sev_checkT012 s d hd

end MurderMystery
