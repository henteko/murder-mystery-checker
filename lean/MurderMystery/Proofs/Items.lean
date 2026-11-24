import MurderMystery.Proofs.G

/-!
# 定理 7: 導出制約の正しさ

ゴールの集合が「ゲーム終了時に同時に達成可能」(消費済みのアイテムは消費済みのまま、
各ゴールの requires_items をその owner が持つような保持者の割り当てがある)であることは、
「消費済みのアイテムを要求せず、owner の異なるゴールどうしで requires_items が交わらない」ことと同値。
さらに、判定器の導出制約 `derivedConstraints` を割り当てが満たすことは、次の3つの連言と同値。
- その割り当てで真のゴールの集合が同時に達成可能(requires_items)
- 真のゴールの requires_knowledge はどれも入手可能(§2.5)
- condition を持つゴールは、その値が condition の値と等しい
-/
namespace MurderMystery

/-- ゴールの集合 G が終了時の保持者 E のもとで同時に達成可能。 -/
def Realizable (E : Id → Holder) (G : List Goal) : Prop :=
  ∃ h : Id → Holder, (∀ i, E i = .consumed → h i = .consumed) ∧
    ∀ g ∈ G, ∀ i ∈ g.requiresItems, h i = .char g.owner

def Compatible (E : Id → Holder) (G : List Goal) : Prop :=
  (∀ g ∈ G, ∀ i ∈ g.requiresItems, E i ≠ .consumed) ∧
  (∀ g₁ ∈ G, ∀ g₂ ∈ G, g₁.owner ≠ g₂.owner → ∀ i ∈ g₁.requiresItems, i ∉ g₂.requiresItems)

theorem realizable_iff (E : Id → Holder) (G : List Goal) : Realizable E G ↔ Compatible E G := by
  constructor
  · rintro ⟨h, hc, hg⟩
    refine ⟨fun g hg' i hi hE => ?_, fun g₁ h₁ g₂ h₂ ho i hi₁ hi₂ => ?_⟩
    · have := hg g hg' i hi
      rw [hc i hE] at this
      cases this
    · have e₁ := hg g₁ h₁ i hi₁
      have e₂ := hg g₂ h₂ i hi₂
      rw [e₁] at e₂
      injection e₂ with heq
      exact ho heq
  · rintro ⟨hc, hd⟩
    let pick (i : Id) : Holder :=
      match G.find? (fun g => g.requiresItems.contains i) with
      | some g => .char g.owner
      | none => E i
    refine ⟨pick, fun i hE => ?_, fun g hg i hi => ?_⟩
    · simp only [pick]
      split
      · rename_i g' hf
        have hmem := List.mem_of_find?_eq_some hf
        have hi := List.find?_some hf
        simp only [List.contains_iff_mem] at hi
        exact absurd hE (hc g' hmem i hi)
      · exact hE
    · simp only [pick]
      split
      · rename_i g' hf
        have hmem := List.mem_of_find?_eq_some hf
        have hi' := List.find?_some hf
        simp only [List.contains_iff_mem] at hi'
        by_cases ho : g'.owner = g.owner
        · rw [ho]
        · exact absurd hi (hd g' hmem g hg ho i hi')
      · rename_i hn
        have := List.find?_eq_none.mp hn g hg
        simp [hi] at this

/-! ## 判定器の導出制約との対応 -/

/-- l の相異なる位置にある2要素は、どちらかの順で pairs に現れる。 -/
theorem pairs_of_ne {α} [DecidableEq α] : ∀ (l : List α) (x y : α), x ∈ l → y ∈ l → x ≠ y →
    (x, y) ∈ pairs l ∨ (y, x) ∈ pairs l
  | [], _, _, hx, _, _ => by simp at hx
  | a :: t, x, y, hx, hy, hxy => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact Or.inl (Or.inl ⟨y, hy, rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, hx, rfl, rfl⟩)
    · rcases pairs_of_ne t x y hx hy hxy with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

theorem mem_of_mem_pairs {α} : ∀ (l : List α) (x y : α), (x, y) ∈ pairs l → x ∈ l ∧ y ∈ l := by
  intro l x y h
  obtain ⟨l₁, l₂, l₃, rfl⟩ := (mem_pairs l x y).mp h
  simp

/-- 割り当て σ でゴール g が真。 -/
def goalOn (σ : Assignment) (g : Goal) : Bool := (Formula.var g.id).eval σ

theorem eval_not_var (σ : Assignment) (g : Goal) :
    (Formula.not (.var g.id)).eval σ = !goalOn σ g := by
  simp [Formula.eval, goalOn]

theorem eval_not_and (σ : Assignment) (g₁ g₂ : Goal) :
    (Formula.not (.and [.var g₁.id, .var g₂.id])).eval σ = !(goalOn σ g₁ && goalOn σ g₂) := by
  simp [Formula.eval, goalOn, List.attach]

theorem any_contains_iff (a b : List Id) : a.any b.contains = true ↔ ∃ i ∈ a, i ∈ b := by
  simp [List.any_eq_true]

/-- requires_items の導出制約を満たす ⇔ 真のゴールの集合が `Compatible`(よって `Realizable`)。 -/
theorem items_iff (s : Scenario) (σ : Assignment) :
    (s.itemConstraints.all fun c => c.eval σ) = true ↔
      Compatible s.final.holder (s.goals.filter (goalOn σ)) := by
  have hperm : ∀ g, g ∈ s.goals.mergeSort (fun a b => decide (a.id ≤ b.id)) ↔ g ∈ s.goals :=
    fun g => List.mem_mergeSort
  simp only [Scenario.itemConstraints, List.all_append, Bool.and_eq_true, List.all_eq_true,
    List.mem_filterMap, Compatible, List.mem_filter]
  constructor
  · rintro ⟨hl, hc⟩
    refine ⟨fun g ⟨hg, hon⟩ i hi hE => ?_, fun g₁ ⟨h₁, on₁⟩ g₂ ⟨h₂, on₂⟩ ho i hi₁ hi₂ => ?_⟩
    · have hcond : (g.requiresItems.any fun i => s.final.holder i == Holder.consumed) = true :=
        List.any_eq_true.mpr ⟨i, hi, by simp [hE]⟩
      have := hl (Formula.not (.var g.id)) ⟨g, hg, by simp [hcond]⟩
      rw [eval_not_var, hon] at this
      cases this
    · have hne : g₁ ≠ g₂ := fun h => ho (h ▸ rfl)
      rcases pairs_of_ne _ g₁ g₂ ((hperm g₁).mpr h₁) ((hperm g₂).mpr h₂) hne with hp | hp
      · have := hc (Formula.not (.and [.var g₁.id, .var g₂.id])) ⟨(g₁, g₂), hp, by simp; exact ⟨ho, i, hi₁, hi₂⟩⟩
        rw [eval_not_and, on₁, on₂] at this
        cases this
      · have := hc (Formula.not (.and [.var g₂.id, .var g₁.id])) ⟨(g₂, g₁), hp, by simp; exact ⟨Ne.symm ho, i, hi₂, hi₁⟩⟩
        rw [eval_not_and, on₁, on₂] at this
        cases this
  · rintro ⟨hl, hc⟩
    refine ⟨fun c ⟨g, hg, hcg⟩ => ?_, fun c ⟨⟨g₁, g₂⟩, hp, hcg⟩ => ?_⟩
    · split at hcg
      · rename_i hany
        simp only [Option.some.injEq] at hcg
        subst hcg
        rw [eval_not_var]
        cases hon : goalOn σ g
        · rfl
        · obtain ⟨i, hi, hE⟩ := List.any_eq_true.mp hany
          exact absurd (by simpa using hE) (hl g ⟨hg, hon⟩ i hi)
      · cases hcg
    · split at hcg
      · rename_i hcond
        simp only [Option.some.injEq] at hcg
        subst hcg
        rw [eval_not_and]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, any_contains_iff] at hcond
        obtain ⟨ho, i, hi₁, hi₂⟩ := hcond
        obtain ⟨m₁, m₂⟩ := mem_of_mem_pairs _ _ _ hp
        cases on₁ : goalOn σ g₁ <;> cases on₂ : goalOn σ g₂ <;> try rfl
        exact absurd hi₂ (hc g₁ ⟨(hperm g₁).mp m₁, on₁⟩ g₂ ⟨(hperm g₂).mp m₂, on₂⟩ ho i hi₁)
      · cases hcg

/-- requires_knowledge の導出制約を満たす ⇔ 真のゴールが要求する知識はどれも入手可能。 -/
theorem knowledge_iff (s : Scenario) (σ : Assignment) :
    (s.knowledgeConstraints.all fun c => c.eval σ) = true ↔
      ∀ g ∈ s.goals, goalOn σ g = true → ∀ f ∈ g.requiresKnowledge, s.obtainable f = true := by
  simp only [Scenario.knowledgeConstraints, List.all_eq_true, List.mem_filterMap]
  constructor
  · intro h g hg hon f hf
    cases ho : s.obtainable f
    · have hany : (g.requiresKnowledge.any fun f => !s.obtainable f) = true :=
        List.any_eq_true.mpr ⟨f, hf, by simp [ho]⟩
      have := h (Formula.not (.var g.id)) ⟨g, hg, by simp [hany]⟩
      rw [eval_not_var, hon] at this
      cases this
    · rfl
  · rintro h c ⟨g, hg, hcg⟩
    split at hcg
    · rename_i hany
      simp only [Option.some.injEq] at hcg
      subst hcg
      rw [eval_not_var]
      cases hon : goalOn σ g
      · rfl
      · obtain ⟨f, hf, ho⟩ := List.any_eq_true.mp hany
        simp [h g hg hon f hf] at ho
    · cases hcg

theorem eval_iff (σ : Assignment) (a b : Formula) : (Formula.iff a b).eval σ = (a.eval σ == b.eval σ) := by
  cases ha : a.eval σ <;> cases hb : b.eval σ <;> simp [Formula.iff, Formula.eval, List.attach, ha, hb]

/-- condition の導出制約を満たす ⇔ condition を持つゴールの値は condition の値と等しい。 -/
theorem condition_iff (s : Scenario) (σ : Assignment) :
    (s.conditionConstraints.all fun c => c.eval σ) = true ↔
      ∀ g ∈ s.goals, ∀ c, g.condition = some c → goalOn σ g = c.eval σ := by
  simp only [Scenario.conditionConstraints, List.all_eq_true, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · intro h g hg c hc
    have := h _ ⟨g, hg, c, hc, rfl⟩
    rw [eval_iff] at this
    simpa [goalOn] using this
  · rintro h _ ⟨g, hg, c, hc, rfl⟩
    rw [eval_iff]
    simpa [goalOn] using h g hg c hc

/-- **定理 7**: 導出制約を満たす ⇔ 3つの条件の連言。 -/
theorem derived_iff (s : Scenario) (σ : Assignment) :
    (s.derivedConstraints.all fun c => c.eval σ) = true ↔
      Compatible s.final.holder (s.goals.filter (goalOn σ)) ∧
      (∀ g ∈ s.goals, goalOn σ g = true → ∀ f ∈ g.requiresKnowledge, s.obtainable f = true) ∧
      (∀ g ∈ s.goals, ∀ c, g.condition = some c → goalOn σ g = c.eval σ) := by
  rw [← items_iff, ← knowledge_iff, ← condition_iff]
  simp only [Scenario.derivedConstraints, List.all_append, Bool.and_eq_true, and_assoc]

end MurderMystery
