import MurderMystery.Proofs.Post

/-!
# 定理 1: 健全性・完全性

判定器が error を1件も出さない ⇔ シナリオが宣言的な意味で正しい (`Valid`)。
-/
namespace MurderMystery

/-! ## G 群 -/

theorem sev_witness (g : GCtx) (p : List Val) (d : Diag) : (g.witness p d).sev = d.sev := rfl

theorem sev_checkG001 (s : Scenario) (g : GCtx) : ∀ d ∈ checkG001 s g, d.sev = .error := by
  unfold checkG001; split <;> simp [GCtx.witness, err]

theorem sev_checkG002 (s : Scenario) (g : GCtx) : ∀ d ∈ checkG002 s g, d.sev = .error := by
  unfold checkG002
  intro d hd
  simp only [List.mem_filterMap] at hd
  obtain ⟨⟨e₁, e₂⟩, _, h⟩ := hd
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp [GCtx.witness, err]
  · cases h

theorem sev_checkG008 (s : Scenario) : ∀ d ∈ checkG008 s, d.sev = .warning := by
  unfold checkG008
  intro d hd
  simp only [List.mem_filterMap] at hd
  obtain ⟨_, _, h⟩ := hd
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp [warn]
  · cases h

/-- 全要素が error の列について、「全部 warning」⇔ 空。 -/
theorem allWarning_iff_nil (l : List Diag) (h : ∀ d ∈ l, d.sev = .error) :
    (∀ d ∈ l, d.sev = .warning) ↔ l = [] := by
  constructor
  · intro hw
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro d hd
    have := hw d hd
    rw [h d hd] at this
    cases this
  · intro hl d hd; simp [hl] at hd

theorem checkGRest_valid (s : Scenario) (g : GCtx) :
    (∀ d ∈ checkGRest s g, d.sev = .warning) ↔
      (∀ e ∈ s.sortedEndings, g.pats.any (fun p => e.condition.eval (g.σ p)) = true) ∧
      (∀ gl ∈ s.goals, (g.pats.map fun p => g.σ p gl.id).contains (.bool true) = true) := by
  unfold checkGRest
  dsimp only
  simp only [List.mem_append]
  constructor
  · intro h
    refine ⟨fun e he => ?_, fun gl hgl => ?_⟩
    · refine Classical.byContradiction fun hc => ?_
      have hmem : err "G003" [e.id] ∈ s.sortedEndings.filterMap (fun e =>
          if g.pats.any (fun p => e.condition.eval (g.σ p)) then none else some (err "G003" [e.id])) :=
        List.mem_filterMap.mpr ⟨e, he, by simp [hc]⟩
      have := h _ (Or.inl (Or.inl hmem))
      simp [err] at this
    · refine Classical.byContradiction fun hc => ?_
      have hmem : err "G004" [gl.id] ∈ s.goals.filterMap (fun gl =>
          if !(g.pats.map fun p => g.σ p gl.id).contains (.bool true) then some (err "G004" [gl.id])
          else if (g.pats.map fun p => g.σ p gl.id).all (· == .bool true) then some (warn "G006" [gl.id])
          else none) :=
        List.mem_filterMap.mpr ⟨gl, hgl, by rw [Bool.not_eq_true] at hc; simp only [hc, Bool.not_false, ite_true]⟩
      have := h _ (Or.inl (Or.inr hmem))
      simp [err] at this
  · rintro ⟨h3, h4⟩ d hd
    rcases hd with (hd | hd) | hd
    · obtain ⟨e, he, h⟩ := List.mem_filterMap.mp hd
      simp [h3 e he] at h
    · obtain ⟨gl, hgl, h⟩ := List.mem_filterMap.mp hd
      simp only [h4 gl hgl, Bool.not_true, Bool.false_eq_true, ite_false] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; simp [warn]
      · cases h
    · obtain ⟨c, _, hd⟩ := List.mem_flatMap.mp hd
      simp only [List.mem_append] at hd
      rcases hd with hd | hd
      · split at hd
        · simp at hd; subst hd; simp [warn]
        · simp at hd
      · split at hd
        · obtain ⟨_, _, h⟩ := List.mem_filterMap.mp hd
          split at h
          · cases h
          · simp only [Option.some.injEq] at h; subst h; simp [warn]
        · simp at hd

theorem exists_pattern_iff (s : Scenario) : (∃ p, s.IsPattern p) ↔ s.gctx.pats ≠ [] := by
  constructor
  · rintro ⟨p, hw, hs⟩ hn
    have : p ∈ s.gctx.pats := (mem_patterns _ _ _).mpr ⟨hw, hs⟩
    simp [hn] at this
  · intro hn
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hn
    exact ⟨p, (mem_patterns _ _ _).mp hp⟩

theorem checkG_valid (s : Scenario) : (∀ d ∈ checkG s, d.sev = .warning) ↔ GValid s := by
  unfold checkG GValid
  dsimp only
  simp only [List.mem_append]
  have h8 := sev_checkG008 s
  by_cases hn : s.gCount > gLimit
  · simp only [hn, ite_true, List.mem_singleton]
    constructor
    · intro h; have := h _ (Or.inl rfl); simp [err] at this
    · rintro ⟨hle, _⟩; exact absurd hn (Nat.not_lt.mpr hle)
  · simp only [hn, ite_false]
    by_cases hp : s.gctx.pats.isEmpty
    · simp only [hp, ite_true, List.mem_singleton]
      have hne : ¬ ∃ p, s.IsPattern p := by
        rw [exists_pattern_iff]; simpa using hp
      constructor
      · intro h; have := h _ (Or.inl rfl); simp [err] at this
      · rintro ⟨_, hex, _⟩; exact absurd hex hne
    · simp only [hp, Bool.false_eq_true, ite_false, checkGPatterns, List.mem_append]
      have hpne : s.gctx.pats ≠ [] := by simpa using hp
      have hsplit : (∀ d, ((d ∈ checkG001 s s.gctx ∨ d ∈ checkG002 s s.gctx) ∨ d ∈ checkGRest s s.gctx) ∨
            d ∈ checkG008 s → d.sev = .warning) ↔
          (checkG001 s s.gctx = [] ∧ checkG002 s s.gctx = []) ∧
            (∀ d ∈ checkGRest s s.gctx, d.sev = .warning) := by
        rw [← allWarning_iff_nil _ (sev_checkG001 s _), ← allWarning_iff_nil _ (sev_checkG002 s _)]
        constructor
        · intro h
          exact ⟨⟨fun d hd => h d (Or.inl (Or.inl (Or.inl hd))), fun d hd => h d (Or.inl (Or.inl (Or.inr hd)))⟩,
            fun d hd => h d (Or.inl (Or.inr hd))⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩ d (((hd | hd) | hd) | hd)
          · exact h1 d hd
          · exact h2 d hd
          · exact h3 d hd
          · exact h8 d hd
      rw [hsplit, g_exactly_one, checkGRest_valid]
      have hpat : ∀ p, p ∈ s.gctx.pats ↔ s.IsPattern p := fun p => mem_patterns _ _ _
      constructor
      · rintro ⟨hone, h3, h4⟩
        refine ⟨Nat.le_of_not_lt hn, (exists_pattern_iff s).mpr hpne,
          fun p hp => hone p ((hpat p).mpr hp), fun e he => ?_, fun gl hgl => ?_⟩
        · obtain ⟨p, hp, hev⟩ := List.any_eq_true.mp (h3 e he)
          exact ⟨p, (hpat p).mp hp, hev⟩
        · have := h4 gl hgl
          simp only [List.contains_iff_mem, List.mem_map] at this
          obtain ⟨p, hp, hev⟩ := this
          exact ⟨p, (hpat p).mp hp, hev⟩
      · rintro ⟨_, _, hone, h3, h4⟩
        refine ⟨fun p hp => hone p ((hpat p).mp hp), fun e he => ?_, fun gl hgl => ?_⟩
        · obtain ⟨p, hp, hev⟩ := h3 e he
          exact List.any_eq_true.mpr ⟨p, (hpat p).mpr hp, hev⟩
        · obtain ⟨p, hp, hev⟩ := h4 gl hgl
          simp only [List.contains_iff_mem, List.mem_map]
          exact ⟨p, (hpat p).mpr hp, hev⟩

/-! ## 全体 -/

theorem sev_checkR (s : Scenario) : ∀ d ∈ checkR s, d.sev = .error := by
  unfold checkR
  intro d hd
  simp only [List.mem_map] at hd
  obtain ⟨⟨c, a, e⟩, _, rfl⟩ := hd
  rfl

/-- **定理 1**: 判定器が error を1件も出さない ⇔ シナリオが正しい。 -/
theorem check_valid (s : Scenario) : (∀ d ∈ check s, d.sev = .warning) ↔ Valid s := by
  rw [check_noError_iff]
  unfold checkRaw Valid
  dsimp only
  by_cases hr : checkR s = []
  · simp only [hr, List.isEmpty_nil, ite_true, true_and, List.mem_append]
    rw [← checkEvents_valid, ← checkPost_valid, ← checkG_valid]
    constructor
    · intro h
      exact ⟨fun d hd => h d (Or.inl (Or.inl hd)), fun d hd => h d (Or.inl (Or.inr hd)),
        fun d hd => h d (Or.inr hd)⟩
    · rintro ⟨h1, h2, h3⟩ d ((hd | hd) | hd)
      · exact h1 d hd
      · exact h2 d hd
      · exact h3 d hd
  · have hne : (checkR s).isEmpty = false := by simpa using hr
    simp only [hne, Bool.false_eq_true, ite_false, hr, false_and, iff_false]
    intro h
    exact hr ((allWarning_iff_nil _ (sev_checkR s)).mp h)

end MurderMystery
