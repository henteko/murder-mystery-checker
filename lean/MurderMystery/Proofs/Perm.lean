import MurderMystery.Proofs.Order

/-!
# 定理 3 (後半): イベント配列の並べ替えに対する不変性

`s.events` を並べ替えた入力 `{ s with events := l' }` に対して、判定器の出力は変わらない。

- R 群: 各規則の検出結果の集合が変わらない(R011 は同じ ID のイベントの「いずれか」で判定する)。
- R 群の違反がないとき: イベント ID が重複しないので、正規順序に並べたイベント列と ID による検索が一致し、
  以降の検査はすべて同じ値になる。
-/
namespace MurderMystery

/-! ## リストの補題 -/

theorem mem_duplicates [DecidableEq α] (l : List α) (x : α) :
    x ∈ duplicates l ↔ x ∈ l ∧ (l.filter (· == x)).length ≥ 2 := by
  simp [duplicates, mem_dedup]

theorem mem_duplicates_perm [DecidableEq α] {l l' : List α} (hp : l.Perm l') (x : α) :
    x ∈ duplicates l ↔ x ∈ duplicates l' := by
  rw [mem_duplicates, mem_duplicates, hp.mem_iff, (hp.filter _).length_eq]

theorem nodup_of_duplicates_nil [DecidableEq α] (l : List α) (h : duplicates l = []) : l.Nodup := by
  rw [List.nodup_iff_count]
  intro a
  refine Classical.byContradiction fun hc => ?_
  have hpos : 0 < l.count a := by omega
  have ha : a ∈ l := List.count_pos_iff.mp hpos
  have : a ∈ duplicates l := by
    rw [mem_duplicates]
    refine ⟨ha, ?_⟩
    rw [← List.count_eq_length_filter]
    omega
  simp [h] at this

/-- キーが重複しない列で、キーの等しい2要素は等しい。 -/
theorem eq_of_mem_of_nodup_map {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by cases ha
  | x :: xs, hn, a, b, ha, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp ha with ea | ea <;> rcases List.mem_cons.mp hb with eb | eb
    · rw [ea, eb]
    · subst ea; exact absurd hab.symm (hn.1 b eb)
    · subst eb; exact absurd hab (hn.1 a ea)
    · exact eq_of_mem_of_nodup_map hn.2 ea eb hab

/-- 高々1つの要素しか条件を満たさない列では、`find?` は並べ替えで変わらない。 -/
theorem find?_perm {p : α → Bool} {l l' : List α} (hp : l.Perm l')
    (huniq : ∀ a ∈ l, ∀ b ∈ l, p a = true → p b = true → a = b) : l.find? p = l'.find? p := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.find?_cons]
    split
    · rfl
    · exact ih fun a ha b hb => huniq a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
  | swap x y l =>
    simp only [List.find?_cons]
    by_cases hx : p x <;> by_cases hy : p y <;> simp only [hx, hy]
    rw [huniq y (List.mem_cons_self ..) x (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hy hx]
  | trans h₁ _ ih₁ ih₂ =>
    rw [ih₁ huniq]
    exact ih₂ fun a ha b hb => huniq a (h₁.mem_iff.mpr ha) b (h₁.mem_iff.mpr hb)

/-- 反対称な関係で整列した、並べ替えの関係にある2つの列は等しい。 -/
theorem eq_of_perm_of_pairwise {r : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise r → l₂.Pairwise r →
      (∀ a ∈ l₁, ∀ b ∈ l₁, r a b → r b a → a = b) → l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hp, _, _, _ => by simpa using hp.length_eq
  | _ :: _, [], hp, _, _, _ => by simpa using hp.length_eq
  | a :: t₁, b :: t₂, hp, h₁, h₂, ha => by
    have hab : a = b := by
      refine Classical.byContradiction fun hne => ?_
      have ha2 : a ∈ t₂ := by
        rcases List.mem_cons.mp (hp.mem_iff.mp (List.mem_cons_self ..)) with e | e
        · exact absurd e hne
        · exact e
      have hb1 : b ∈ t₁ := by
        rcases List.mem_cons.mp (hp.mem_iff.mpr (List.mem_cons_self ..)) with e | e
        · exact absurd e.symm hne
        · exact e
      exact hne (ha a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb1)
        (List.rel_of_pairwise_cons h₁ hb1) (List.rel_of_pairwise_cons h₂ ha2))
    subst hab
    congr 1
    exact eq_of_perm_of_pairwise (List.Perm.cons_inv hp) (List.Pairwise.of_cons h₁) (List.Pairwise.of_cons h₂)
      fun x hx y hy => ha x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

/-! ## 正規順序 `evLe` -/

theorem evLe_trans (a b c : Event) (h₁ : evLe a b = true) (h₂ : evLe b c = true) : evLe a c = true := by
  simp only [evLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact Or.inl (Nat.lt_trans h₁ h₂)
  · rw [← e₂]; exact Or.inl h₁
  · rw [e₁]; exact Or.inl h₂
  · exact Or.inr ⟨e₁.trans e₂, Std.le_trans h₁ h₂⟩

theorem evLe_total (a b : Event) : (evLe a b || evLe b a) = true := by
  simp only [evLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  by_cases h : a.time < b.time
  · exact Or.inl (Or.inl h)
  · by_cases h' : b.time < a.time
    · exact Or.inr (Or.inl h')
    · have e : a.time = b.time := Nat.le_antisymm (Nat.not_lt.mp h') (Nat.not_lt.mp h)
      rcases Std.le_total (a := a.id) (b := b.id) with h'' | h''
      · exact Or.inl (Or.inr ⟨e, h''⟩)
      · exact Or.inr (Or.inr ⟨e.symm, h''⟩)

theorem evLe_antisymm (a b : Event) (h₁ : evLe a b = true) (h₂ : evLe b a = true) : a.id = b.id := by
  simp only [evLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  rcases h₁ with h₁ | ⟨e₁, h₁⟩ <;> rcases h₂ with h₂ | ⟨e₂, h₂⟩
  · exact absurd h₂ (Nat.lt_asymm h₁)
  · rw [e₂] at h₁; exact absurd h₁ (Nat.lt_irrefl _)
  · rw [e₁] at h₂; exact absurd h₂ (Nat.lt_irrefl _)
  · exact Std.le_antisymm h₁ h₂

theorem pairwise_sortedEvents (l : List Event) : (l.mergeSort evLe).Pairwise (fun a b => evLe a b = true) :=
  List.pairwise_mergeSort evLe_trans evLe_total l

/-- ID が重複しなければ、並べ替えた列を整列した結果は等しい。 -/
theorem mergeSort_evLe_perm {l l' : List Event} (hp : l.Perm l') (hn : (l.map (·.id)).Nodup) :
    l.mergeSort evLe = l'.mergeSort evLe := by
  apply eq_of_perm_of_pairwise _ (pairwise_sortedEvents l) (pairwise_sortedEvents l')
  · intro a ha b hb hab hba
    rw [List.mem_mergeSort] at ha hb
    exact eq_of_mem_of_nodup_map hn ha hb (evLe_antisymm a b hab hba)
  · exact (List.mergeSort_perm l evLe).trans (hp.trans (List.mergeSort_perm l' evLe).symm)

theorem any_perm {l l' : List α} (hp : l.Perm l') (p : α → Bool) : l.any p = l'.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, hp.mem_iff]

/-! ## イベント配列の並べ替え -/

section
variable (s : Scenario) (l' : List Event) (hp : s.events.Perm l')
include hp

/-! ### R 群 -/

theorem checkR001_perm (x : RIssue) : x ∈ checkR001 { s with events := l' } ↔ x ∈ checkR001 s := by
  have h := mem_duplicates_perm (hp.map (·.id))
  simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
    Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
    List.mem_map, h]

theorem idsOfKind_contains_perm (k i : Id) :
    (Scenario.idsOfKind { s with events := l' } k).contains i = (s.idsOfKind k).contains i := by
  unfold Scenario.idsOfKind
  split <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp only [Scenario.eventIds, List.contains_iff_mem, (hp.map (·.id)).mem_iff]

theorem allRefs_perm (r : Ref) : r ∈ allRefs { s with events := l' } ↔ r ∈ allRefs s := by
  simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, hp.mem_iff]

theorem checkR002_perm (x : RIssue) : x ∈ checkR002 { s with events := l' } ↔ x ∈ checkR002 s := by
  simp only [checkR002, List.mem_map, mem_dedup, List.mem_filter, allRefs_perm s l' hp,
    idsOfKind_contains_perm s l' hp]

theorem checkR006_perm (x : RIssue) : x ∈ checkR006 { s with events := l' } ↔ x ∈ checkR006 s := by
  simp only [checkR006, List.mem_flatMap, hp.mem_iff]

theorem checkR011_perm : checkR011 { s with events := l' } = checkR011 s := by
  simp only [checkR011, any_perm hp.symm]

theorem rIssues_perm (x : RIssue) : x ∈ rIssues { s with events := l' } ↔ x ∈ rIssues s := by
  unfold rIssues
  simp only [List.mem_append, checkR001_perm s l' hp, checkR002_perm s l' hp, checkR006_perm s l' hp,
    checkR011_perm s l' hp]
  rfl

theorem checkR_perm (d : Diag) : d ∈ checkR { s with events := l' } ↔ d ∈ checkR s := by
  have h1 : (checkR001 { s with events := l' }).isEmpty = (checkR001 s).isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem, checkR001_perm s l' hp]
  unfold checkR
  rw [h1]
  split
  · simp only [List.mem_map, rIssues_perm s l' hp]
  · simp only [List.mem_map, checkR001_perm s l' hp]

/-! ### R 群の違反がないとき -/

omit hp in
theorem eventIds_nodup_of_checkR (h : checkR s = []) : (s.events.map (·.id)).Nodup := by
  apply nodup_of_duplicates_nil
  have h1 : checkR001 s = [] := by
    rw [checkR_eq_nil_iff] at h
    simp only [rIssues, List.append_eq_nil_iff, and_assoc] at h
    exact h.1
  simp only [checkR001, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h1
  exact h1 ("event", s.eventIds) (by simp)

omit hp in
theorem sortedEvents_perm' (hn : (s.events.map (·.id)).Nodup) (hp : s.events.Perm l') :
    Scenario.sortedEvents { s with events := l' } = s.sortedEvents :=
  (mergeSort_evLe_perm hp hn).symm

omit hp in
theorem findEvent_perm' (hn : (s.events.map (·.id)).Nodup) (hp : s.events.Perm l') (x : Id) :
    Scenario.findEvent? { s with events := l' } x = s.findEvent? x := by
  unfold Scenario.findEvent?
  refine (find?_perm hp ?_).symm
  intro a ha b hb hpa hpb
  simp only [beq_iff_eq] at hpa hpb
  exact eq_of_mem_of_nodup_map hn ha hb (hpa.trans hpb.symm)

/-- R 群の違反がないとき、イベント以外の検査はすべて同じ値になる。 -/
theorem checkRaw_perm_of_R (hR : checkR s = []) :
    checkEvents { s with events := l' } ++ checkPost { s with events := l' } ++ checkG { s with events := l' } =
      checkEvents s ++ checkPost s ++ checkG s := by
  have hn := eventIds_nodup_of_checkR s hR
  have hsorted := sortedEvents_perm' s l' hn hp
  have hfind := findEvent_perm' s l' hn hp
  have hany := fun p => any_perm hp.symm p
  have hrun : Scenario.run { s with events := l' } = s.run := by
    unfold Scenario.run; rw [hsorted]; rfl
  have htrace : Scenario.trace { s with events := l' } = s.trace := by
    unfold Scenario.trace; rw [hrun]
  have hfinal : Scenario.final { s with events := l' } = s.final := by
    unfold Scenario.final; rw [hrun]
  have hdeath : ∀ c, Scenario.deathTime { s with events := l' } c = s.deathTime c := by
    intro c; unfold Scenario.deathTime; rw [hfinal]; simp only [hfind]; try rfl
  have hseg : ∀ c, Scenario.segments { s with events := l' } c = s.segments c := by
    intro c; unfold Scenario.segments Scenario.movesOf; rw [hsorted, hdeath]; try rfl
  have hwhere : ∀ c t, Scenario.whereAt { s with events := l' } c t = s.whereAt c t := by
    intro c t; unfold Scenario.whereAt Scenario.whereAlive; rw [hdeath]; simp only [hseg]
  have hobt : ∀ f, Scenario.obtainable { s with events := l' } f = s.obtainable f := by
    intro f; unfold Scenario.obtainable; rw [hfinal]
  have hobtF : Scenario.obtainable { s with events := l' } = s.obtainable := funext hobt
  have hheld : ∀ f, Scenario.held { s with events := l' } f = s.held f := by
    intro f; unfold Scenario.held; rw [hfinal]
  have hack : ∀ c₁ c₂ l lo hi, acknowledged { s with events := l' } c₁ c₂ l lo hi = acknowledged s c₁ c₂ l lo hi := by
    intro c₁ c₂ l lo hi; unfold acknowledged; rw [hany]
  have hE : checkEvents { s with events := l' } = checkEvents s := by
    unfold checkEvents; rw [htrace]; rfl
  have hP : checkPost { s with events := l' } = checkPost s := by
    simp only [checkPost, postErrors, postWarnings, warningsT009, issuesK003, issuesK004K005, issuesK006,
      issuesK007, issuesK008, issuesH, warningsH, issuesA, checkT012, issuesK010, warningsK009,
      Scenario.clueOnly, Scenario.draws, hfinal, hfind, hseg, hwhere, hobt, hobtF, hheld, hack, hsorted]
    rfl
  have hG : checkG { s with events := l' } = checkG s := by
    have hd : Scenario.derivedConstraints { s with events := l' } = s.derivedConstraints := by
      simp only [Scenario.derivedConstraints, Scenario.itemConstraints, Scenario.knowledgeConstraints, Scenario.conditionConstraints, Scenario.tagConstraints, Scenario.avail,
        Scenario.concealConstraints, Scenario.exposed, hfinal, hobtF]; try rfl
    have hsat : Scenario.satisfies { s with events := l' } = s.satisfies := by
      funext v; unfold Scenario.satisfies Scenario.effectiveConstraints; rw [hd]; rfl
    have hctx : Scenario.gctx { s with events := l' } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    unfold checkG; rw [hctx]; rfl
  rw [hE, hP, hG]

/-- **定理 3 (並べ替え不変)**: イベント配列を並べ替えても、判定器の出力は変わらない。 -/
theorem check_perm_events : check { s with events := l' } = check s := by
  apply check_eq_of_mem_iff
  intro d
  unfold checkRaw
  dsimp only
  by_cases hR : checkR s = []
  · have hR' : checkR { s with events := l' } = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun d hd => by
        rw [checkR_perm s l' hp, hR] at hd; cases hd
    rw [hR, hR', List.isEmpty_nil]
    simp only [ite_true]
    rw [checkRaw_perm_of_R s l' hp hR]
  · have hR' : (checkR { s with events := l' }).isEmpty = false := by
      cases h : checkR { s with events := l' } with
      | nil =>
        exfalso; apply hR
        exact List.eq_nil_iff_forall_not_mem.mpr fun d hd => by
          rw [← checkR_perm s l' hp, h] at hd; cases hd
      | cons _ _ => rfl
    have hR2 : (checkR s).isEmpty = false := by simpa using hR
    rw [hR', hR2]
    simp only [Bool.false_eq_true, ite_false]
    exact checkR_perm s l' hp d

end

end MurderMystery
