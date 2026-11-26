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
  unfold clueIssues
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
  unfold issuesH handoutIssues handoutH001 handoutH002 handoutH004 boardIssues
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

theorem getD_set_nat (l : List Nat) (i j v : Nat) :
    (l.set i v).getD j 0 = if i = j ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h; by_cases h' : i < l.length
    · simp [h']
    · simp [h']
  · simp [h]

theorem lt_of_getD_pos {l : List Nat} {i : Nat} (h : 0 < l.getD i 0) : i < l.length := by
  apply Nat.lt_of_not_le; intro hn
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hn)] at h

theorem lt_of_mem_getD {pools : List (List Clue)} {i : Nat} {c : Clue} (h : c ∈ pools.getD i []) :
    i < pools.length := by
  apply Nat.lt_of_not_le; intro hn
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hn)] at h

/-- 探索の被覆の判定は、宣言的な条件と同値: 回 i で引くカードは pools[i] から caps[i] 枚以内、合計 k 枚以内。 -/
theorem coverR_iff (pools : List (List Clue)) : ∀ (k : Nat) (caps : List Nat) (N : List Id),
    coverR pools caps N k = true ↔
      ∃ ps : List (Nat × Clue), (∀ p ∈ ps, p.2 ∈ pools.getD p.1 []) ∧ ps.length ≤ k ∧
        (∀ i, ps.countP (·.1 == i) ≤ caps.getD i 0) ∧ ∀ f ∈ N, ∃ p ∈ ps, f ∈ p.2.reveals := by
  intro k
  induction k with
  | zero =>
    intro caps N
    cases N with
    | nil => simp only [coverR, true_iff]; exact ⟨[], by simp, by simp, by simp, by simp⟩
    | cons f rest =>
      simp only [coverR, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro ps _ hl _ hc
      obtain ⟨p, hp, _⟩ := hc f (by simp)
      have : ps = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
      subst this; simp at hp
  | succ k ih =>
    intro caps N
    cases N with
    | nil => simp only [coverR, true_iff]; exact ⟨[], by simp, by simp, by simp, by simp⟩
    | cons f rest =>
      simp only [coverR, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
        List.mem_filter, List.contains_iff_mem]
      constructor
      · rintro ⟨i, _, hcap, c, ⟨hcp, hf⟩, hcov⟩
        obtain ⟨ps, hm, hl, hcnt, hcs⟩ := (ih _ _).mp hcov
        have hi := lt_of_getD_pos hcap
        refine ⟨(i, c) :: ps, ?_, by simp; omega, ?_, ?_⟩
        · intro p hp; simp only [List.mem_cons] at hp; rcases hp with rfl | hp
          · exact hcp
          · exact hm p hp
        · intro j
          have := hcnt j
          rw [getD_set_nat] at this
          by_cases hij : i = j
          · subst hij
            rw [ite_eq_left ⟨rfl, hi⟩] at this
            rw [List.countP_cons, ite_eq_left (by simp)]; omega
          · rw [ite_eq_right (fun h => hij h.1)] at this
            rw [List.countP_cons, ite_eq_right (by simp [hij])]; omega
        · intro x hx
          by_cases hr : x ∈ c.reveals
          · exact ⟨(i, c), by simp, hr⟩
          · obtain ⟨p, hp, hx'⟩ := hcs x (by simp [List.mem_filter, hx, hr])
            exact ⟨p, by simp [hp], hx'⟩
      · rintro ⟨ps, hm, hl, hcnt, hcs⟩
        obtain ⟨⟨i, c⟩, hp, hf⟩ := hcs f (by simp)
        have hcp := hm _ hp
        have hperm := List.perm_cons_erase hp
        have hci : 0 < ps.countP (·.1 == i) := List.countP_pos_iff.mpr ⟨(i, c), hp, by simp⟩
        have hcap : 0 < caps.getD i 0 := Nat.lt_of_lt_of_le hci (hcnt i)
        refine ⟨i, lt_of_mem_getD hcp, hcap, c, ⟨hcp, hf⟩, (ih _ _).mpr ⟨ps.erase (i, c), ?_, ?_, ?_, ?_⟩⟩
        · intro p hp'; exact hm p (List.mem_of_mem_erase hp')
        · rw [List.length_erase_of_mem hp]; omega
        · intro j
          have hc := hperm.countP_eq (·.1 == j)
          rw [List.countP_cons] at hc
          have := hcnt j
          rw [getD_set_nat]
          by_cases hij : i = j
          · subst hij
            rw [ite_eq_left ⟨rfl, lt_of_getD_pos hcap⟩]
            rw [ite_eq_left (by simp)] at hc; omega
          · rw [ite_eq_right (fun h => hij h.1)]
            rw [ite_eq_right (by simp [hij])] at hc; omega
        · intro x hx
          simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_iff_mem,
            decide_eq_false_iff_not] at hx
          obtain ⟨hx, hr⟩ := hx
          obtain ⟨p, hp', hx'⟩ := hcs x hx
          have hne : p ≠ (i, c) := fun h => by subst h; simp [hx'] at hr
          exact ⟨p, (List.mem_erase_of_ne hne).mpr hp', hx'⟩

theorem issuesK010_nil (s : Scenario) :
    issuesK010 s = [] ↔ ∀ rs, s.exploration = some rs → s.CanDraw rs := by
  unfold issuesK010 Scenario.CanDraw
  cases s.exploration with
  | none => simp
  | some rs =>
    simp only [Option.some.injEq, forall_eq']
    rw [← coverR_iff]
    cases coverR (s.pools rs) (s.caps rs) s.clueOnly (s.draws rs) <;> simp

theorem postErrors_nil (s : Scenario) : postErrors s = [] ↔ PostValid s := by
  unfold postErrors PostValid
  simp only [List.append_eq_nil_iff, issuesK003_nil, issuesK004K005_nil, issuesK006_nil,
    issuesK007_nil, issuesK008_nil, issuesH_nil, issuesA_nil, issuesK010_nil, and_assoc]

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
