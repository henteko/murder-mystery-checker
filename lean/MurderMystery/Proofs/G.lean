import MurderMystery.Proofs.Basic

/-!
# G 群の正しさ

- 定理 2: 数え上げは、定義域に従うすべての割り当てをちょうど列挙する。
  G001 と G002 がどちらも出ないこと ⇔ すべてのパターンでエンディングがちょうど1つに決まること。
-/
namespace MurderMystery

/-! ## 数え上げの完全性 -/

/-- 割り当て vals が定義域 doms に従う。 -/
def WellTyped : List (List Val) → List Val → Prop
  | [], [] => True
  | d :: ds, x :: xs => x ∈ d ∧ WellTyped ds xs
  | _, _ => False

theorem mem_enumerate : ∀ (doms : List (List Val)) (vals : List Val),
    vals ∈ enumerate doms ↔ WellTyped doms vals
  | [], vals => by cases vals <;> simp [enumerate, WellTyped]
  | d :: ds, vals => by
    cases vals with
    | nil => simp [enumerate, WellTyped]
    | cons x xs =>
      have ih := mem_enumerate ds xs
      simp [enumerate, List.mem_flatMap, ih, WellTyped]

/-- G 群が調べるパターンは、定義域に従い実効制約を満たす割り当てにちょうど一致する。 -/
theorem mem_patterns (doms : List (List Val)) (sat : List Val → Bool) (p : List Val) :
    p ∈ (enumerate doms).filter sat ↔ WellTyped doms p ∧ sat p = true := by
  simp [mem_enumerate]

/-! ## 「ちょうど1つ」と組の条件 -/

theorem mem_pairs {α} : ∀ (l : List α) (x y : α),
    (x, y) ∈ pairs l ↔ ∃ l₁ l₂ l₃, l = l₁ ++ x :: l₂ ++ y :: l₃
  | [], x, y => by simp [pairs]
  | a :: t, x, y => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq, mem_pairs t]
    constructor
    · rintro (⟨b, hb, rfl, rfl⟩ | ⟨l₁, l₂, l₃, rfl⟩)
      · obtain ⟨l₂, l₃, rfl⟩ := List.append_of_mem hb
        exact ⟨[], l₂, l₃, by simp⟩
      · exact ⟨a :: l₁, l₂, l₃, by simp⟩
    · rintro ⟨l₁, l₂, l₃, h⟩
      cases l₁ with
      | nil =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        left; exact ⟨y, by simp, rfl, rfl⟩
      | cons b l₁ =>
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        right; exact ⟨l₁, l₂, l₃, by simp⟩

/-- フィルタの結果がちょうど1要素 ⇔ 条件を満たす要素があり、どの組も同時には満たさない。 -/
theorem filter_length_eq_one_iff {α} (P : α → Bool) : ∀ l : List α,
    (l.filter P).length = 1 ↔ (∃ x ∈ l, P x = true) ∧ ∀ q ∈ pairs l, ¬(P q.1 = true ∧ P q.2 = true)
  | [] => by simp [pairs]
  | a :: t => by
    have ih := filter_length_eq_one_iff P t
    simp only [List.filter_cons, pairs, List.mem_cons, List.mem_append, List.mem_map]
    by_cases ha : P a = true
    · simp only [ha, ite_true, List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff,
        List.filter_eq_nil_iff]
      constructor
      · intro h
        refine ⟨⟨a, Or.inl rfl, ha⟩, ?_⟩
        rintro q (⟨b, hb, rfl⟩ | hq) ⟨_, h2⟩
        · exact h b hb h2
        · obtain ⟨l₁, l₂, l₃, ht⟩ := (mem_pairs t q.1 q.2).1 hq
          exact h q.2 (by rw [ht]; simp) h2
      · rintro ⟨_, h⟩ b hb hpb
        exact h (a, b) (Or.inl ⟨b, hb, rfl⟩) ⟨ha, hpb⟩
    · simp only [ha, Bool.false_eq_true, ite_false]
      rw [ih]
      constructor
      · rintro ⟨⟨x, hx, hpx⟩, h⟩
        refine ⟨⟨x, Or.inr hx, hpx⟩, ?_⟩
        rintro q (⟨b, _, rfl⟩ | hq) hpq
        · exact ha hpq.1
        · exact h q hq hpq
      · rintro ⟨⟨x, hx | hx, hpx⟩, h⟩
        · subst hx; exact absurd hpx ha
        · exact ⟨⟨x, hx, hpx⟩, fun q hq => h q (Or.inr hq)⟩

/-! ## G001 / G002 -/

theorem checkG001_eq_nil_iff (s : Scenario) (g : GCtx) :
    checkG001 s g = [] ↔ ∀ p ∈ g.pats, ∃ e ∈ s.sortedEndings, g.holds e p = true := by
  unfold checkG001
  split
  · rename_i p hp
    have hmem := List.mem_of_find?_eq_some hp
    have hall := List.find?_some hp
    simp only [reduceCtorEq, false_iff]
    intro h
    obtain ⟨e, he, hh⟩ := h p hmem
    simp [List.all_eq_true] at hall
    simp [hall e he] at hh
  · rename_i hn
    simp only [true_iff]
    intro p hp
    have := List.find?_eq_none.mp hn p hp
    simpa [List.all_eq_true] using this

theorem checkG002_eq_nil_iff (s : Scenario) (g : GCtx) :
    checkG002 s g = [] ↔
      ∀ q ∈ pairs s.sortedEndings, ∀ p ∈ g.pats, ¬(g.holds q.1 p = true ∧ g.holds q.2 p = true) := by
  unfold checkG002
  rw [List.filterMap_eq_nil_iff]
  apply forall_congr'; intro q; apply forall_congr'; intro _
  obtain ⟨e₁, e₂⟩ := q
  simp only
  split
  · rename_i p hp
    simp only [reduceCtorEq, false_iff, Classical.not_forall, Classical.not_not]
    exact ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩
  · rename_i hn
    simp only [true_iff]
    intro p hp
    simpa using List.find?_eq_none.mp hn p hp

/-- **定理 2**: G001 と G002 がどちらも出ない ⇔ すべてのパターンでエンディングがちょうど1つ成り立つ。 -/
theorem g_exactly_one (s : Scenario) (g : GCtx) :
    checkG001 s g = [] ∧ checkG002 s g = [] ↔
      ∀ p ∈ g.pats, (s.sortedEndings.filter (fun e => g.holds e p)).length = 1 := by
  rw [checkG001_eq_nil_iff, checkG002_eq_nil_iff]
  simp only [filter_length_eq_one_iff]
  constructor
  · rintro ⟨h1, h2⟩ p hp
    exact ⟨h1 p hp, fun q hq => h2 q hq p hp⟩
  · intro h
    exact ⟨fun p hp => (h p hp).1, fun q hq p hp => (h p hp).2 q hq⟩

/-! ## 判定器の出力との対応 -/

theorem code_checkG001 (s : Scenario) (g : GCtx) : ∀ d ∈ checkG001 s g, d.code = "G001" := by
  unfold checkG001; split <;> simp [GCtx.witness, err]

theorem code_checkG002 (s : Scenario) (g : GCtx) : ∀ d ∈ checkG002 s g, d.code = "G002" := by
  unfold checkG002
  intro d hd
  simp only [List.mem_filterMap] at hd
  obtain ⟨⟨e₁, e₂⟩, _, h⟩ := hd
  split at h <;> simp_all [GCtx.witness, err]
  rw [← h]

theorem code_checkGRest (s : Scenario) (g : GCtx) :
    ∀ d ∈ checkGRest s g, d.code ≠ "G001" ∧ d.code ≠ "G002" := by
  unfold checkGRest
  intro d hd
  simp only [List.mem_append, List.mem_filterMap, List.mem_flatMap] at hd
  rcases hd with (⟨_, _, h⟩ | ⟨_, _, h⟩) | ⟨_, _, h⟩
  · try dsimp only at h
    repeat' split at h
    all_goals (simp at h; try (subst h; simp [err, warn]))
  · try dsimp only at h
    repeat' split at h
    all_goals (simp at h; try (subst h; simp [err, warn]))
  · rcases h with h | h
    · split at h
      · simp at h; subst h; simp [warn]
      · simp at h
    · split at h
      · simp only [List.mem_filterMap] at h
        obtain ⟨_, _, h⟩ := h
        split at h
        · simp at h
        · simp at h; subst h; simp [warn]
      · simp at h

theorem code_checkG008 (s : Scenario) : ∀ d ∈ checkG008 s, d.code = "G008" := by
  unfold checkG008
  intro d hd
  simp only [List.mem_filterMap] at hd
  obtain ⟨_, _, h⟩ := hd
  split at h <;> simp at h; rw [← h]; simp [warn]

/-- **定理 2(判定器の出力として)**: 数え上げの上限内で、制約が矛盾していないとき、
判定器が G001 も G002 も出さない ⇔ 定義域に従い実効制約を満たすすべての割り当てで、
エンディングがちょうど1つ成り立つ。 -/
theorem checkG_exactly_one (s : Scenario) (hn : ¬ s.gCount > gLimit) (hp : s.gctx.pats ≠ []) :
    (∀ d ∈ checkG s, d.code ≠ "G001" ∧ d.code ≠ "G002") ↔
      ∀ vals, WellTyped s.gDoms vals → s.satisfies vals = true →
        (s.sortedEndings.filter fun e => e.condition.eval (toAssignment s.gVars vals)).length = 1 := by
  have hp' : s.gctx.pats.isEmpty = false := by simpa using hp
  have hsplit : (∀ d ∈ checkG s, d.code ≠ "G001" ∧ d.code ≠ "G002") ↔
      checkG001 s s.gctx = [] ∧ checkG002 s s.gctx = [] := by
    simp only [checkG, hn, ite_false, hp', Bool.false_eq_true, checkGPatterns, List.mem_append]
    constructor
    · intro h
      constructor
      · apply List.eq_nil_iff_forall_not_mem.mpr
        intro d hd
        exact (h d (Or.inl (Or.inl (Or.inl hd)))).1 (code_checkG001 _ _ d hd)
      · apply List.eq_nil_iff_forall_not_mem.mpr
        intro d hd
        exact (h d (Or.inl (Or.inl (Or.inr hd)))).2 (code_checkG002 _ _ d hd)
    · rintro ⟨h1, h2⟩ d hd
      rcases hd with ((hd | hd) | hd) | hd
      · simp [h1] at hd
      · simp [h2] at hd
      · exact code_checkGRest _ _ d hd
      · rw [code_checkG008 s d hd]; decide
  rw [hsplit, g_exactly_one]
  constructor
  · intro h vals hw hs
    exact h vals ((mem_patterns _ _ _).mpr ⟨hw, hs⟩)
  · intro h p hp
    obtain ⟨hw, hs⟩ := (mem_patterns _ _ _).mp hp
    exact h p hw hs

end MurderMystery
