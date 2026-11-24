import MurderMystery.Spec.Valid

/-!
# イベントごとの規則: 判定関数 ⇔ 宣言的な仕様
-/
namespace MurderMystery

theorem issuesT001_nil (s : Scenario) (st : Step) : issuesT001 s st = [] ↔ T001Ok s st := by
  unfold issuesT001 T001Ok
  dsimp only
  cases hk : st.ev.kind <;> simp [EventKind.arrive?, and_assoc, Nat.not_lt]

theorem issuesMove_nil (s : Scenario) (st : Step) : issuesMove s st = [] ↔ MoveOk s st := by
  unfold issuesMove MoveOk
  dsimp only
  cases hk : st.ev.kind with
  | move c to arr m f =>
    simp only [EventKind.move.injEq]
    constructor
    · intro h c' to' arr' m' f' ⟨hc, ht, ha, hm, hf⟩
      subst hc ht ha hm hf
      by_cases heq : (st.pre.pos c).dest = to
      · simp [heq] at h
      · simp only [heq, beq_iff_eq, ite_false] at h
        refine ⟨heq, fun hw => ?_⟩
        simp only [hw, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
        split at h
        · simp at h
        · rename_i t ht
          refine ⟨t, ht, ?_⟩
          split at h
          · simp at h
          · rename_i hlt
            exact Nat.le_of_not_lt hlt
    · intro h
      obtain ⟨hne, hw⟩ := h c to arr m f ⟨rfl, rfl, rfl, rfl, rfl⟩
      simp only [hne, beq_iff_eq, ite_false]
      by_cases hm : m = "walk"
      · obtain ⟨t, ht, hle⟩ := hw hm
        simp only [hm, bne_self_eq_false, Bool.false_eq_true, ite_false, ht]
        rw [if_neg (Nat.not_lt.mpr hle)]
      · simp [hm]
  | _ => simp

theorem lastSameTime_none (st : Step) (p : Event → Bool) :
    lastSameTime st p = none ↔ ∀ e' ∈ st.earlier, e'.time = st.ev.time → p e' = false := by
  simp only [lastSameTime, List.getLast?_eq_none_iff, List.filter_eq_nil_iff, Bool.and_eq_true,
    beq_iff_eq, not_and, Bool.not_eq_true]

theorem issuesT005_nil (st : Step) (c : Id) :
    issuesT005 st c = [] ↔ ∀ e' ∈ st.earlier, e'.time = st.ev.time → c ∉ e'.kind.participants := by
  unfold issuesT005
  split
  · rename_i e' he
    simp only [reduceCtorEq, false_iff, Classical.not_forall, Classical.not_not]
    have hmem := List.mem_of_getLast? he
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hmem
    exact ⟨e', hmem.1, hmem.2.1, hmem.2.2⟩
  · rename_i he
    simp only [true_iff]
    intro e' he' ht hc
    have := (lastSameTime_none st _).mp he e' he' ht
    simp [hc] at this

theorem issuesT006_nil (st : Step) (c : Id) :
    issuesT006 st c = [] ↔ st.pre.inTransit c st.ev.time = false := by
  unfold issuesT006; split <;> simp_all

theorem issuesT010_nil (st : Step) (c : Id) : issuesT010 st c = [] ↔ st.pre.dead c = none := by
  unfold issuesT010; split <;> simp_all

theorem issuesParticipants_nil (st : Step) : issuesParticipants st = [] ↔ ParticipantsOk st := by
  unfold issuesParticipants ParticipantsOk issuesParticipant
  simp only [List.flatMap_eq_nil_iff, List.append_eq_nil_iff, issuesT005_nil, issuesT006_nil,
    issuesT010_nil, and_assoc]

theorem atLoc_true_nil (S : State) (t : Time) (c l : Id) :
    atLoc S t c l true = [] ↔ (S.inTransit c t = false → (S.pos c).dest = l) := by
  unfold atLoc
  by_cases h : S.inTransit c t <;> simp [h]

theorem atLoc_false_nil (S : State) (t : Time) (c l : Id) :
    atLoc S t c l false = [] ↔ S.inTransit c t = false ∧ (S.pos c).dest = l := by
  unfold atLoc
  by_cases h : S.inTransit c t <;> simp [h]

theorem issuesPlace_nil (s : Scenario) (st : Step) : issuesPlace s st = [] ↔ PlaceOk s st := by
  unfold issuesPlace PlaceOk
  dsimp only
  cases hk : st.ev.kind with
  | scene l ps rv =>
    simp only [List.flatMap_eq_nil_iff, atLoc_true_nil, EventKind.scene.injEq, reduceCtorEq,
      false_imp_iff, implies_true, and_true]
    constructor
    · rintro h l' ps' rv' ⟨rfl, rfl, rfl⟩; exact h
    · intro h; exact h l ps rv ⟨rfl, rfl, rfl⟩
  | observe c l tl ts fs =>
    simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, atLoc_true_nil, atLoc_false_nil,
      EventKind.observe.injEq, reduceCtorEq, false_imp_iff, implies_true, and_true, true_and]
    constructor
    · rintro ⟨⟨hp, hc⟩, hx⟩ c' l' tl' ts' fs' ⟨rfl, rfl, rfl, rfl, rfl⟩
      refine ⟨?_, hc, hx⟩
      by_cases h : s.perceives l tl <;> simp_all
    · intro h
      obtain ⟨hp, hc, hx⟩ := h c l tl ts fs ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨⟨by simp [hp], hc⟩, hx⟩
  | transfer a b i =>
    simp only [EventKind.transfer.injEq, reduceCtorEq, false_imp_iff, implies_true, and_true, true_and]
    constructor
    · rintro h a' b' i' ⟨rfl, rfl, rfl⟩ ha hb
      by_cases hd : (st.pre.pos a).dest = (st.pre.pos b).dest
      · exact hd
      · simp [ha, hb, hd] at h
    · intro h
      have := h a b i ⟨rfl, rfl, rfl⟩
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
        exact absurd (this hc.1.1 hc.1.2) hc.2
      · rfl
  | tell a b fs =>
    simp only [EventKind.tell.injEq, reduceCtorEq, false_imp_iff, implies_true, and_true, true_and]
    constructor
    · rintro h a' b' fs' ⟨rfl, rfl, rfl⟩ ha hb
      by_cases hd : (st.pre.pos a).dest = (st.pre.pos b).dest
      · exact hd
      · simp [ha, hb, hd] at h
    · intro h
      have := h a b fs ⟨rfl, rfl, rfl⟩
      split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hc
        exact absurd (this hc.1.1 hc.1.2) hc.2
      · rfl
  | _ => simp

theorem issuesItem_nil (st : Step) : issuesItem st = [] ↔ ItemOk st := by
  unfold issuesItem ItemOk
  dsimp only
  split
  · rename_i hn
    simp [hn]
  · rename_i i hi
    simp only [hi, Option.some.injEq, forall_eq', List.append_eq_nil_iff]
    have h4 : issuesI004 st i = [] ↔
        ∀ e' ∈ st.earlier, e'.time = st.ev.time → e'.kind.item? ≠ some i := by
      unfold issuesI004
      split
      · rename_i e' he
        simp only [reduceCtorEq, false_iff, Classical.not_forall, Classical.not_not]
        have hmem := List.mem_of_getLast? he
        simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hmem
        exact ⟨e', hmem.1, hmem.2.1, hmem.2.2⟩
      · rename_i he
        simp only [true_iff]
        intro e' he' ht hc
        have := (lastSameTime_none st _).mp he e' he' ht
        simp [hc] at this
    rw [h4]
    simp only [and_congr_right_iff]
    intro _
    by_cases hc : st.pre.holder i = .consumed
    · simp [hc]
    · simp only [hc, beq_iff_eq, ite_false, ne_eq, not_false_eq_true, true_and]
      cases hp : st.ev.kind.isPickup
      · simp
      · simp only [ite_true, Bool.false_eq_true, false_imp_iff, and_true, forall_const]
        by_cases ht : st.pre.inTransit st.ev.kind.holderRole st.ev.time <;> simp [ht]

theorem issuesKnowledge_nil (st : Step) : issuesKnowledge st = [] ↔ KnowledgeOk st := by
  unfold issuesKnowledge KnowledgeOk
  dsimp only
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  apply and_congr
  · cases hk : st.ev.kind with
    | tell a b fs =>
      simp only [List.filterMap_eq_nil_iff, EventKind.tell.injEq]
      constructor
      · rintro h a' b' fs' ⟨rfl, rfl, rfl⟩ f hf
        have := h f hf
        split at this <;> simp_all
      · intro h f hf
        have := h a b fs ⟨rfl, rfl, rfl⟩ f hf
        simp [this]
    | _ => simp
  · apply forall_congr'; intro a; apply forall_congr'; intro _
    apply forall_congr'; intro f; apply forall_congr'; intro _
    by_cases h : st.pre.knows a f <;> simp [h]

theorem stepIssues_nil (s : Scenario) (st : Step) : stepIssues s st = [] ↔ StepValid s st := by
  unfold stepIssues StepValid
  simp only [List.append_eq_nil_iff, issuesT001_nil, issuesMove_nil, issuesParticipants_nil,
    issuesPlace_nil, issuesItem_nil, issuesKnowledge_nil, and_assoc]

/-- イベントごとの検査が error を出さない ⇔ すべてのステップが `StepValid`。 -/
theorem checkEvents_valid (s : Scenario) :
    (∀ d ∈ checkEvents s, d.sev = .warning) ↔ ∀ st ∈ s.trace, StepValid s st := by
  unfold checkEvents
  simp only [List.mem_flatMap, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h st hst
    rw [← stepIssues_nil]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    have := h _ st hst x hx rfl
    simp [err] at this
  · intro h d st hst x hx hd
    rw [(stepIssues_nil s st).mpr (h st hst)] at hx
    simp at hx

end MurderMystery
