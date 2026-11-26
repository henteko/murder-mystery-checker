import MurderMystery.Spec.Rules
import MurderMystery.Proofs.Main
import MurderMystery.Proofs.Commute

/-!
# 定理 1 (後半): 規則ごとの健全性・完全性

R 群以外の error 規則 c について、判定器がコード c の検出結果を出す ⇔
R 群の違反がなく、規則 c の違反条件(`Spec/Rules.lean`)が成り立つ。
-/
namespace MurderMystery

/-- 列にコード c の検出結果がある。 -/
def hasCode (c : String) (l : List Issue) : Prop := ∃ x ∈ l, c = x.1

@[simp] theorem hasCode_nil (c : String) : hasCode c [] ↔ False := by simp [hasCode]
@[simp] theorem hasCode_cons (c : String) (x : Issue) (l : List Issue) :
    hasCode c (x :: l) ↔ c = x.1 ∨ hasCode c l := by simp [hasCode]
@[simp] theorem hasCode_append (c : String) (l₁ l₂ : List Issue) :
    hasCode c (l₁ ++ l₂) ↔ hasCode c l₁ ∨ hasCode c l₂ := by
  simp only [hasCode, List.mem_append]; constructor
  · rintro ⟨x, hx | hx, h⟩
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exact ⟨x, Or.inl hx, h⟩
    · exact ⟨x, Or.inr hx, h⟩
@[simp] theorem hasCode_flatMap (c : String) (l : List α) (f : α → List Issue) :
    hasCode c (l.flatMap f) ↔ ∃ y ∈ l, hasCode c (f y) := by
  simp only [hasCode, List.mem_flatMap]
  constructor
  · rintro ⟨x, ⟨y, hy, hx⟩, h⟩; exact ⟨y, hy, x, hx, h⟩
  · rintro ⟨y, hy, x, hx, h⟩; exact ⟨x, ⟨y, hy, hx⟩, h⟩
@[simp] theorem hasCode_filterMap (c : String) (l : List α) (f : α → Option Issue) :
    hasCode c (l.filterMap f) ↔ ∃ y ∈ l, ∃ x, f y = some x ∧ c = x.1 := by
  simp only [hasCode, List.mem_filterMap]
  constructor
  · rintro ⟨x, ⟨y, hy, hx⟩, h⟩; exact ⟨y, hy, x, hx, h⟩
  · rintro ⟨y, hy, x, hx, h⟩; exact ⟨x, ⟨y, hy, hx⟩, h⟩

@[simp] theorem hasCode_ite (c : String) (p : Prop) [Decidable p] (l₁ l₂ : List Issue) :
    hasCode c (if p then l₁ else l₂) ↔ (p ∧ hasCode c l₁) ∨ (¬p ∧ hasCode c l₂) := by
  by_cases h : p <;> simp [h]

/-- 1種類のコードしか出さない列。 -/
theorem hasCode_single {X : String} {l : List Issue} (h : ∀ x ∈ l, x.1 = X) (c : String) :
    hasCode c l ↔ c = X ∧ l ≠ [] := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨h x hx, List.ne_nil_of_mem hx⟩
  · rintro ⟨rfl, hl⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
    exact ⟨x, hx, (h x hx).symm⟩

/-! ## イベントごとの検査 -/

section
variable (s : Scenario) (st : Step) (c : String)

theorem hasCode_T001 : hasCode c (issuesT001 s st) ↔ c = "T001" ∧ T001V s st := by
  obtain ⟨S, ⟨id, t, k, r⟩, E⟩ := st
  unfold issuesT001 T001V
  cases k <;> simp [EventKind.arrive?, or_assoc, and_comm]

theorem hasCode_Move : hasCode c (issuesMove s st) ↔
    (c = "T002" ∧ T002V s st) ∨ (c = "T003" ∧ T003V s st) ∨ (c = "T004" ∧ T004V st) := by
  obtain ⟨S, ⟨id, t, k, r⟩, E⟩ := st
  unfold issuesMove T002V T003V T004V
  cases k with
  | move ch to arr md f =>
    simp only [EventKind.move.injEq]
    by_cases hd : (S.pos ch).dest = to
    · simp [hd, and_assoc]
    · by_cases hw : md = "walk"
      · subst hw
        cases ht : s.travelTime (S.pos ch).dest to with
        | none => simp [hd, ht, and_assoc]
        | some m => by_cases hm : arr - t < m <;> simp [hd, ht, hm, and_assoc]
      · simp [hd, hw, and_assoc]
  | _ => simp

theorem hasCode_Participants : hasCode c (issuesParticipants st) ↔
    (c = "T005" ∧ T005V st) ∨ (c = "T006" ∧ T006V st) ∨ (c = "T010" ∧ T010V st) := by
  have h5 : ∀ p, hasCode c (issuesT005 st p) ↔
      c = "T005" ∧ ∃ e' ∈ st.earlier, e'.time = st.ev.time ∧ p ∈ e'.kind.participants := by
    intro p
    rw [hasCode_single (X := "T005") (by unfold issuesT005; split <;> simp) c, Ne, issuesT005_nil]
    simp only [Classical.not_forall, Classical.not_not, exists_prop]
  have h6 : ∀ p, hasCode c (issuesT006 st p) ↔ c = "T006" ∧ st.pre.inTransit p st.ev.time = true := by
    intro p
    rw [hasCode_single (X := "T006") (by unfold issuesT006; split <;> simp) c, Ne, issuesT006_nil]
    simp
  have h10 : ∀ p, hasCode c (issuesT010 st p) ↔ c = "T010" ∧ st.pre.dead p ≠ none := by
    intro p
    rw [hasCode_single (X := "T010") (by unfold issuesT010; split <;> simp) c, Ne, issuesT010_nil]
  unfold issuesParticipants issuesParticipant T005V T006V T010V
  simp only [hasCode_flatMap, hasCode_append, h5, h6, h10]
  constructor
  · rintro ⟨p, hp, (h | h) | h⟩
    · exact Or.inl ⟨h.1, p, hp, h.2⟩
    · exact Or.inr (Or.inl ⟨h.1, p, hp, h.2⟩)
    · exact Or.inr (Or.inr ⟨h.1, p, hp, h.2⟩)
  · rintro (⟨hc, p, hp, h⟩ | ⟨hc, p, hp, h⟩ | ⟨hc, p, hp, h⟩)
    · exact ⟨p, hp, Or.inl (Or.inl ⟨hc, h⟩)⟩
    · exact ⟨p, hp, Or.inl (Or.inr ⟨hc, h⟩)⟩
    · exact ⟨p, hp, Or.inr ⟨hc, h⟩⟩

theorem hasCode_atLoc_true (S : State) (t : Time) (x l : Id) :
    hasCode c (atLoc S t x l true) ↔ c = "T007" ∧ S.inTransit x t = false ∧ (S.pos x).dest ≠ l := by
  unfold atLoc
  cases h : S.inTransit x t <;> by_cases hd : (S.pos x).dest = l <;> simp [h, hd]

theorem hasCode_atLoc_false (S : State) (t : Time) (x l : Id) :
    hasCode c (atLoc S t x l false) ↔ c = "T007" ∧ (S.inTransit x t = true ∨ (S.pos x).dest ≠ l) := by
  unfold atLoc
  cases h : S.inTransit x t <;> by_cases hd : (S.pos x).dest = l <;> simp [h, hd]

theorem hasCode_Place : hasCode c (issuesPlace s st) ↔
    (c = "T007" ∧ T007V st) ∨ (c = "T008" ∧ T008V st) ∨ (c = "T011" ∧ T011V s st) := by
  obtain ⟨S, ⟨id, t, k, r⟩, E⟩ := st
  unfold issuesPlace T007V T008V T011V apart
  cases k with
  | scene l ps rv =>
    simp only [hasCode_flatMap, hasCode_atLoc_true]
    simp [and_assoc]
    grind
  | observe ch l tl ts fs =>
    simp only [hasCode_append, hasCode_flatMap, hasCode_atLoc_true, hasCode_atLoc_false, hasCode_ite,
      hasCode_nil, hasCode_cons]
    by_cases hp : s.perceives l tl = true
    · simp [hp, and_assoc]
      grind
    · simp only [Bool.not_eq_true] at hp
      simp [hp, and_assoc]
      grind
  | transfer a b i =>
    by_cases ha : S.inTransit a t = true <;> by_cases hb : S.inTransit b t = true <;>
      by_cases hd : (S.pos a).dest = (S.pos b).dest <;> simp [ha, hb, hd, and_assoc]
  | tell a b fs =>
    by_cases ha : S.inTransit a t = true <;> by_cases hb : S.inTransit b t = true <;>
      by_cases hd : (S.pos a).dest = (S.pos b).dest <;> simp [ha, hb, hd, and_assoc]
  | _ => simp

theorem hasCode_Item : hasCode c (issuesItem st) ↔
    (c = "I001" ∧ I001V st) ∨ (c = "I002" ∧ I002V st) ∨ (c = "I003" ∧ I003V st) ∨ (c = "I004" ∧ I004V st) := by
  unfold issuesItem I001V I002V I003V I004V
  dsimp only
  cases hi : st.ev.kind.item? with
  | none => simp
  | some i =>
    have h4 : hasCode c (issuesI004 st i) ↔ c = "I004" ∧ I004V st := by
      unfold issuesI004 I004V
      split
      · rename_i e' he
        have hmem := List.mem_of_getLast? he
        simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hmem
        simp only [hasCode_cons, hasCode_nil, or_false, hi, Option.some.injEq, exists_eq_left']
        exact ⟨fun hc => ⟨hc, e', hmem.1, hmem.2⟩, fun h => h.1⟩
      · rename_i he
        have hn := (lastSameTime_none st _).mp he
        simp only [hasCode_nil, false_iff, not_and, hi, Option.some.injEq, exists_eq_left']
        rintro _ ⟨e', he', ht, hit⟩
        have := hn e' he' ht
        simp [hit] at this
    simp only [hasCode_append, h4]
    unfold I004V
    simp only [hi, Option.some.injEq, exists_eq_left']
    by_cases hc : st.pre.holder i = .consumed
    · simp [hc]; grind
    · cases hp : st.ev.kind.isPickup
      · by_cases hh : st.pre.holder i = .char st.ev.kind.holderRole <;> simp [hc, hp, hh] <;> grind
      · cases ht : st.pre.inTransit st.ev.kind.holderRole st.ev.time <;>
          by_cases hh : st.pre.holder i = .place (st.pre.pos st.ev.kind.holderRole).dest <;>
          simp [hc, hp, hh, ht] <;> grind

theorem hasCode_Knowledge : hasCode c (issuesKnowledge st) ↔ (c = "K001" ∧ K001V st) ∨ (c = "K002" ∧ K002V st) := by
  obtain ⟨S, ⟨id, t, k, r⟩, E⟩ := st
  unfold issuesKnowledge K001V K002V
  simp only [hasCode_append, hasCode_flatMap, hasCode_filterMap]
  have hk2 : (∃ y ∈ k.actors, ∃ y_1 ∈ r, ∃ x,
      (if S.knows y y_1 = true then none else some ("K002", [y, y_1])) = some x ∧ c = x.1) ↔
      c = "K002" ∧ ∃ a ∈ k.actors, ∃ f ∈ r, S.knows a f = false := by
    constructor
    · rintro ⟨a, ha, f, hf, x, hx, rfl⟩
      cases hkn : S.knows a f <;> simp [hkn] at hx
      subst hx; exact ⟨rfl, a, ha, f, hf, hkn⟩
    · rintro ⟨rfl, a, ha, f, hf, hkn⟩
      exact ⟨a, ha, f, hf, ("K002", [a, f]), by simp [hkn], rfl⟩
  rw [hk2]
  cases k with
  | tell a b fs =>
    simp only [EventKind.tell.injEq]
    have hk1 : (∃ y ∈ fs, ∃ x, (if S.knows a y = true then none else some ("K001", [a, y])) = some x ∧ c = x.1) ↔
        c = "K001" ∧ ∃ f ∈ fs, S.knows a f = false := by
      constructor
      · rintro ⟨f, hf, x, hx, rfl⟩
        cases hkn : S.knows a f <;> simp [hkn] at hx
        subst hx; exact ⟨rfl, f, hf, hkn⟩
      · rintro ⟨rfl, f, hf, hkn⟩
        exact ⟨f, hf, ("K001", [a, f]), by simp [hkn], rfl⟩
    simp only [hasCode_filterMap] at *
    rw [hk1]
    simp [and_assoc]
  | _ => simp

/-- 1ステップの検出結果にコード c がある ⇔ 規則 c の違反。 -/
theorem hasCode_step : hasCode c (stepIssues s st) ↔ StepViolates s st c := by
  unfold stepIssues
  simp only [hasCode_append, hasCode_T001, hasCode_Move, hasCode_Participants, hasCode_Place, hasCode_Item,
    hasCode_Knowledge]
  unfold StepViolates
  split <;> simp_all

end

/-! ## 終了状態の検査 -/

section
variable (s : Scenario) (c : String)

theorem hasCode_K003 : hasCode c (issuesK003 s) ↔ c = "K003" ∧ PostViolates s "K003" := by
  rw [hasCode_single (X := "K003") (by unfold issuesK003; intro x hx; simp at hx; grind) c, Ne, issuesK003_nil]
  simp [PostViolates]

theorem hasCode_K006 : hasCode c (issuesK006 s) ↔ c = "K006" ∧ PostViolates s "K006" := by
  rw [hasCode_single (X := "K006") (by unfold issuesK006; intro x hx; simp at hx; grind) c, Ne, issuesK006_nil]
  simp only [PostViolates]
  simp only [Classical.not_forall, Classical.not_imp, not_exists, not_and, exists_prop, Bool.not_eq_true]

theorem hasCode_K007 : hasCode c (issuesK007 s) ↔ c = "K007" ∧ PostViolates s "K007" := by
  rw [hasCode_single (X := "K007") (by unfold issuesK007; intro x hx; simp at hx; grind) c, Ne, issuesK007_nil]
  simp only [PostViolates]
  simp only [Classical.not_forall, Classical.not_imp, exists_prop, Bool.not_eq_true]

theorem hasCode_K008 : hasCode c (issuesK008 s) ↔ c = "K008" ∧ PostViolates s "K008" := by
  rw [hasCode_single (X := "K008") (by unfold issuesK008; intro x hx; simp at hx; grind) c, Ne, issuesK008_nil]
  simp only [PostViolates]
  simp only [Classical.not_forall, Classical.not_imp, exists_prop, Nat.not_le]

theorem hasCode_K010 : hasCode c (issuesK010 s) ↔ c = "K010" ∧ PostViolates s "K010" := by
  rw [hasCode_single (X := "K010") (by
      unfold issuesK010; intro x hx; split at hx
      · split at hx
        · cases hx
        · simp at hx; subst hx; rfl
      · cases hx) c, Ne, issuesK010_nil]
  simp only [PostViolates, Classical.not_forall, Classical.not_imp, exists_prop]

theorem hasCode_A001 : hasCode c (issuesA s) ↔ c = "A001" ∧ PostViolates s "A001" := by
  rw [hasCode_single (X := "A001") (by unfold issuesA; intro x hx; simp at hx; grind) c, Ne, issuesA_nil]
  simp only [PostViolates]
  simp only [Classical.not_forall, Classical.not_imp, exists_prop, Bool.not_eq_false]

theorem hasCode_clue (E : State) (cl : Clue) : hasCode c (clueIssues E cl) ↔
    (c = "K004" ∧ ∃ i, cl.item = some i ∧ E.holder i = .consumed) ∨
    (c = "K005" ∧ ∃ i l, cl.item = some i ∧ cl.location = some l ∧ E.holder i ≠ .consumed ∧ E.holder i ≠ .place l) := by
  unfold clueIssues
  cases hi : cl.item with
  | none => simp
  | some i =>
    by_cases hc : E.holder i = .consumed
    · simp [hc]
    · cases hl : cl.location with
      | none => simp [hc]
      | some l => by_cases hp : E.holder i = .place l <;> simp [hc, hp]

theorem hasCode_K004K005 : hasCode c (issuesK004K005 s) ↔
    (c = "K004" ∧ PostViolates s "K004") ∨ (c = "K005" ∧ PostViolates s "K005") := by
  unfold issuesK004K005
  simp only [hasCode_flatMap, hasCode_clue, PostViolates]
  grind

theorem hasCode_handout (E : State) (h : Handout) : hasCode c (handoutIssues E h) ↔
    (c = "H001" ∧ ∃ l, h.location = some l ∧ (E.pos h.character).dest ≠ l) ∨
    (c = "H002" ∧ ∃ is, h.items = some is ∧ ∃ i ∈ is, E.holder i ≠ .char h.character) ∨
    (c = "H004" ∧ ∃ ks, h.knows = some ks ∧ ∃ f ∈ ks, E.knows h.character f = false) := by
  have h1 : hasCode c (handoutH001 E h) ↔ c = "H001" ∧ ∃ l, h.location = some l ∧ (E.pos h.character).dest ≠ l := by
    unfold handoutH001
    cases h.location with
    | none => simp
    | some l => by_cases hd : (E.pos h.character).dest = l <;> simp [hd]
  have h2 : hasCode c (handoutH002 E h) ↔
      c = "H002" ∧ ∃ is, h.items = some is ∧ ∃ i ∈ is, E.holder i ≠ .char h.character := by
    unfold handoutH002
    cases h.items with
    | none => simp
    | some is =>
      simp only [hasCode_filterMap, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨i, hi, x, hx, rfl⟩
        by_cases hh : E.holder i = .char h.character <;> simp [hh] at hx
        subst hx; exact ⟨rfl, i, hi, hh⟩
      · rintro ⟨rfl, i, hi, hh⟩
        exact ⟨i, hi, ("H002", [h.character, i, (E.holder i).render]), by simp [hh], rfl⟩
  have h4 : hasCode c (handoutH004 E h) ↔
      c = "H004" ∧ ∃ ks, h.knows = some ks ∧ ∃ f ∈ ks, E.knows h.character f = false := by
    unfold handoutH004
    cases h.knows with
    | none => simp
    | some ks =>
      simp only [hasCode_filterMap, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨f, hf, x, hx, rfl⟩
        cases hk : E.knows h.character f <;> simp [hk] at hx
        subst hx; exact ⟨rfl, f, hf, hk⟩
      · rintro ⟨rfl, f, hf, hk⟩
        exact ⟨f, hf, ("H004", [h.character, f]), by simp [hk], rfl⟩
  unfold handoutIssues
  rw [hasCode_append, hasCode_append, h1, h2, h4, or_assoc]

theorem hasCode_board (E : State) (b : Board) : hasCode c (boardIssues E b) ↔
    c = "H006" ∧ ∃ i ∈ b.items, E.holder i ≠ .place b.location := by
  unfold boardIssues
  simp only [hasCode_filterMap]
  constructor
  · rintro ⟨i, hi, x, hx, rfl⟩
    by_cases hh : E.holder i = .place b.location <;> simp [hh] at hx
    subst hx; exact ⟨rfl, i, hi, hh⟩
  · rintro ⟨rfl, i, hi, hh⟩
    exact ⟨i, hi, ("H006", [b.location, i, (E.holder i).render]), by simp [hh], rfl⟩

theorem hasCode_H : hasCode c (issuesH s) ↔
    (c = "H001" ∧ PostViolates s "H001") ∨ (c = "H002" ∧ PostViolates s "H002") ∨
    (c = "H004" ∧ PostViolates s "H004") ∨ (c = "H006" ∧ PostViolates s "H006") := by
  unfold issuesH
  simp only [hasCode_append, hasCode_flatMap, hasCode_handout, hasCode_board, PostViolates]
  grind

/-- 終了状態の error の検査にコード c がある ⇔ 規則 c の違反。 -/
theorem hasCode_postErrors : hasCode c (postErrors s) ↔ PostViolates s c := by
  unfold postErrors
  simp only [hasCode_append, hasCode_K003, hasCode_K004K005, hasCode_K006, hasCode_K007, hasCode_K008,
    hasCode_H, hasCode_A001, hasCode_K010]
  constructor
  · rintro (((((((⟨rfl, h⟩ | (⟨rfl, h⟩ | ⟨rfl, h⟩)) | ⟨rfl, h⟩) | ⟨rfl, h⟩) | ⟨rfl, h⟩) |
      (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)) | ⟨rfl, h⟩) | ⟨rfl, h⟩) <;> exact h
  · intro h
    unfold PostViolates at h
    split at h <;> first
      | (simp only [PostViolates]; simp only [true_and]; grind)
      | exact absurd h id

theorem hasCode_warningsTH (h : hasCode c (warningsT009 s ++ warningsH s)) :
    c = "T009" ∨ c = "H003" ∨ c = "H005" ∨ c = "H007" := by
  obtain ⟨x, hx, rfl⟩ := h
  unfold warningsT009 warningsH at hx
  simp only [List.mem_append, List.mem_flatMap, List.mem_filterMap] at hx
  rcases hx with ⟨_, _, _, _, _, _, hx⟩ | ((⟨h, _, hx⟩ | ⟨b, _, i, _, hx⟩))
  · split at hx
    · simp only [Option.some.injEq] at hx; subst hx; simp
    · cases hx
  · rcases hx with hx | hx
    · split at hx
      · obtain ⟨i, _, hx⟩ := List.mem_filterMap.mp hx
        split at hx
        · simp only [Option.some.injEq] at hx; subst hx; simp
        · cases hx
      · cases hx
    · split at hx
      · obtain ⟨i, _, hx⟩ := List.mem_filterMap.mp hx
        split at hx
        · simp only [Option.some.injEq] at hx; subst hx; simp
        · cases hx
      · cases hx
  · split at hx
    · simp only [Option.some.injEq] at hx; subst hx; simp
    · cases hx


theorem hasCode_postWarnings (h : hasCode c (postWarnings s)) :
    c = "T009" ∨ c = "H003" ∨ c = "H005" ∨ c = "H007" ∨ c = "K009" ∨ c = "K011" := by
  unfold postWarnings at h
  rcases (hasCode_append c _ _).mp h with h | h
  · rcases (hasCode_append c _ _).mp h with h | h
    · rcases hasCode_warningsTH s c h with h | h | h | h <;> simp [h]
    · obtain ⟨x, hx, rfl⟩ := h
      unfold warningsK009 at hx
      split at hx
      · split at hx
        · simp at hx; subst hx; simp
        · cases hx
      · cases hx
  · obtain ⟨x, hx, rfl⟩ := h
    unfold warningsK011 at hx
    split at hx
    · obtain ⟨cl, _, hx⟩ := List.mem_filterMap.mp hx
      split at hx
      · cases hx
      · simp only [Option.some.injEq] at hx; subst hx; simp
    · cases hx
end

/-! ## 検出結果の列(`Diag`) -/

/-- 検出結果の列にコード c のものがある。 -/
def hasCodeD (c : String) (l : List Diag) : Prop := ∃ d ∈ l, c = d.code

@[simp] theorem hasCodeD_append (c : String) (l₁ l₂ : List Diag) :
    hasCodeD c (l₁ ++ l₂) ↔ hasCodeD c l₁ ∨ hasCodeD c l₂ := by
  simp only [hasCodeD, List.mem_append]
  constructor
  · rintro ⟨d, hd | hd, h⟩
    · exact Or.inl ⟨d, hd, h⟩
    · exact Or.inr ⟨d, hd, h⟩
  · rintro (⟨d, hd, h⟩ | ⟨d, hd, h⟩)
    · exact ⟨d, Or.inl hd, h⟩
    · exact ⟨d, Or.inr hd, h⟩

theorem hasCodeD_map (c : String) (l : List Issue) (f : Issue → Diag) (hf : ∀ x, (f x).code = x.1) :
    hasCodeD c (l.map f) ↔ hasCode c l := by
  simp only [hasCodeD, hasCode, List.mem_map]
  constructor
  · rintro ⟨d, ⟨x, hx, rfl⟩, h⟩; exact ⟨x, hx, by rw [h, hf]⟩
  · rintro ⟨x, hx, h⟩; exact ⟨f x, ⟨x, hx, rfl⟩, by rw [h, hf]⟩

theorem hasCodeD_single {X : String} {l : List Diag} (h : ∀ d ∈ l, d.code = X) (c : String) :
    hasCodeD c l ↔ c = X ∧ l ≠ [] := by
  constructor
  · rintro ⟨d, hd, rfl⟩; exact ⟨h d hd, List.ne_nil_of_mem hd⟩
  · rintro ⟨rfl, hl⟩
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil l hl
    exact ⟨d, hd, (h d hd).symm⟩

theorem hasCodeD_checkEvents (s : Scenario) (c : String) :
    hasCodeD c (checkEvents s) ↔ ∃ st ∈ s.trace, StepViolates s st c := by
  unfold checkEvents
  simp only [hasCodeD, List.mem_flatMap]
  constructor
  · rintro ⟨d, ⟨st, hst, hd⟩, rfl⟩
    refine ⟨st, hst, (hasCode_step s st _).mp ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
    exact ⟨x, hx, rfl⟩
  · rintro ⟨st, hst, h⟩
    obtain ⟨x, hx, hc⟩ := (hasCode_step s st c).mpr h
    exact ⟨_, ⟨st, hst, List.mem_map.mpr ⟨x, hx, rfl⟩⟩, hc⟩

/-- 警告のコード。 -/
def warningCodes : List String := ["T009", "T012", "H003", "H005", "H007", "K009", "K011", "G006", "G008", "G009"]

theorem errorCode_not_warning {c : String} (hc : c ∈ errorCodes) : c ∉ warningCodes := by
  simp only [errorCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem hasCodeD_checkPost (s : Scenario) (c : String) (hc : c ∈ errorCodes) :
    hasCodeD c (checkPost s) ↔ PostViolates s c := by
  have hw := errorCode_not_warning hc
  unfold checkPost
  simp only [hasCodeD_append, hasCodeD_map c _ (fun x => err x.1 x.2) (fun _ => rfl),
    hasCodeD_map c _ (fun x => warn x.1 x.2) (fun _ => rfl), hasCode_postErrors]
  have h1 : ¬ hasCode c (postWarnings s) := fun h => by
    rcases hasCode_postWarnings s c h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [warningCodes] at hw
  have h2 : ¬ hasCodeD c (checkT012 s) := fun h => by
    rw [hasCodeD_single (X := "T012") (fun d hd => by
      simp only [checkT012, List.mem_flatMap, List.mem_map] at hd
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hd; rfl)] at h
    rw [h.1] at hw; simp [warningCodes] at hw
  simp only [h1, h2, or_false]

/-! ## G 群 -/

theorem rel_of_mem_pairs {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {x y}, (x, y) ∈ pairs l → R x y
  | [], _, _, _, h => by simp [pairs] at h
  | a :: t, hp, x, y, h => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨z, hz, rfl, rfl⟩ | h
    · exact List.rel_of_pairwise_cons hp hz
    · exact rel_of_mem_pairs (List.Pairwise.of_cons hp) h

theorem mem_pairs_of_ne : ∀ {l : List α} {x y : α}, x ∈ l → y ∈ l → x ≠ y → (x, y) ∈ pairs l ∨ (y, x) ∈ pairs l
  | [], _, _, hx, _, _ => by cases hx
  | a :: t, x, y, hx, hy, hne => by
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.mp hx with ex | ex <;> rcases List.mem_cons.mp hy with ey | ey
    · exact absurd (ex.trans ey.symm) hne
    · exact Or.inl (Or.inl ⟨y, ey, ex.symm, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, ex, ey.symm, rfl⟩)
    · rcases mem_pairs_of_ne ex ey hne with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

theorem endingIds_nodup_of_checkR (s : Scenario) (h : checkR s = []) : (s.endings.map (·.id)).Nodup := by
  apply nodup_of_duplicates_nil
  have h1 : checkR001 s = [] := by
    rw [checkR_eq_nil_iff] at h
    simp only [rIssues, List.append_eq_nil_iff, and_assoc] at h
    exact h.1
  simp only [checkR001, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h1
  exact h1 ("ending", s.endings.map (·.id)) (by simp)

theorem mem_sortedEndings (s : Scenario) (e : Ending) : e ∈ s.sortedEndings ↔ e ∈ s.endings := by
  simp [Scenario.sortedEndings]

theorem hasCodeD_checkGRest (s : Scenario) (g : GCtx) (c : String) :
    hasCodeD c (checkGRest s g) ↔
      (c = "G003" ∧ ∃ e ∈ s.sortedEndings, g.pats.any (fun p => e.condition.eval (g.σ p)) = false) ∨
      (c = "G004" ∧ ∃ gl ∈ s.goals, (g.pats.map fun p => g.σ p gl.id).contains (.bool true) = false) ∨
      ((c = "G006" ∨ c = "G009") ∧ hasCodeD c (checkGRest s g)) := by
  constructor
  · intro h
    have h' := h
    obtain ⟨d, hd, rfl⟩ := h
    unfold checkGRest at hd
    dsimp only at hd
    simp only [List.mem_append, List.mem_filterMap, List.mem_flatMap] at hd
    rcases hd with (⟨e, he, hx⟩ | ⟨gl, hgl, hx⟩) | ⟨ch, _, hx⟩
    · split at hx
      · cases hx
      · rename_i hn
        simp only [Option.some.injEq] at hx; subst hx
        exact Or.inl ⟨rfl, e, he, by simpa using hn⟩
    · split at hx
      · rename_i hn
        simp only [Option.some.injEq] at hx; subst hx
        exact Or.inr (Or.inl ⟨rfl, gl, hgl, by simpa using hn⟩)
      · split at hx
        · simp only [Option.some.injEq] at hx; subst hx
          exact Or.inr (Or.inr ⟨Or.inl rfl, h'⟩)
        · cases hx
    · rcases hx with hx | hx
      · split at hx
        · simp only [List.mem_singleton] at hx; subst hx
          exact Or.inr (Or.inr ⟨Or.inl rfl, h'⟩)
        · cases hx
      · split at hx
        · obtain ⟨v, _, hv⟩ := List.mem_filterMap.mp hx
          split at hv
          · cases hv
          · simp only [Option.some.injEq] at hv; subst hv
            exact Or.inr (Or.inr ⟨Or.inr rfl, h'⟩)
        · cases hx
  · rintro (⟨rfl, e, he, hn⟩ | ⟨rfl, gl, hgl, hn⟩ | ⟨_, h⟩)
    · refine ⟨err "G003" [e.id], ?_, rfl⟩
      unfold checkGRest
      simp only [List.mem_append, List.mem_filterMap, or_assoc]
      exact Or.inl ⟨e, he, by simp [hn]⟩
    · refine ⟨err "G004" [gl.id], ?_, rfl⟩
      unfold checkGRest
      simp only [List.mem_append, List.mem_filterMap, or_assoc]
      exact Or.inr (Or.inl ⟨gl, hgl, by simp only [hn, Bool.not_false, ite_true]⟩)
    · exact h

section
variable (s : Scenario)

theorem mem_gctx_pats (p : List Val) : p ∈ s.gctx.pats ↔ s.IsPattern p := mem_patterns _ _ _

theorem g001_iff : checkG001 s s.gctx ≠ [] ↔ ∃ p, s.IsPattern p ∧ ∀ e ∈ s.endings, s.holdsAt e p = false := by
  rw [Ne, checkG001_eq_nil_iff]
  simp only [Classical.not_forall, not_exists, not_and, exists_prop, mem_gctx_pats, mem_sortedEndings]
  constructor
  · rintro ⟨p, hp, h⟩; exact ⟨p, hp, fun e he => Bool.eq_false_iff.mpr (h e he)⟩
  · rintro ⟨p, hp, h⟩; exact ⟨p, hp, fun e he hh => by rw [show s.gctx.holds e p = s.holdsAt e p from rfl, h e he] at hh; cases hh⟩

theorem g002_iff (hR : checkR s = []) : checkG002 s s.gctx ≠ [] ↔
    ∃ p, s.IsPattern p ∧ ∃ e₁ ∈ s.endings, ∃ e₂ ∈ s.endings, e₁.id ≠ e₂.id ∧
      s.holdsAt e₁ p = true ∧ s.holdsAt e₂ p = true := by
  have hnd := endingIds_nodup_of_checkR s hR
  have hsnd : s.sortedEndings.Pairwise (fun a b => a.id ≠ b.id) := by
    have : (s.sortedEndings.map (·.id)).Nodup := by
      unfold Scenario.sortedEndings
      exact ((List.mergeSort_perm _ _).map (fun e : Ending => e.id)).nodup_iff.mpr hnd
    exact List.pairwise_map.mp this
  rw [Ne, checkG002_eq_nil_iff]
  simp only [Classical.not_forall, Classical.not_not, exists_prop, mem_gctx_pats]
  constructor
  · rintro ⟨⟨e₁, e₂⟩, hq, p, hp, h₁, h₂⟩
    obtain ⟨l₁, l₂, l₃, hl⟩ := (mem_pairs _ e₁ e₂).mp hq
    have hm₁ : e₁ ∈ s.sortedEndings := by rw [hl]; simp
    have hm₂ : e₂ ∈ s.sortedEndings := by rw [hl]; simp
    exact ⟨p, hp, e₁, (mem_sortedEndings s e₁).mp hm₁, e₂, (mem_sortedEndings s e₂).mp hm₂,
      rel_of_mem_pairs hsnd hq, h₁, h₂⟩
  · rintro ⟨p, hp, e₁, he₁, e₂, he₂, hne, h₁, h₂⟩
    have hne' : e₁ ≠ e₂ := fun h => hne (by rw [h])
    rcases mem_pairs_of_ne ((mem_sortedEndings s e₁).mpr he₁) ((mem_sortedEndings s e₂).mpr he₂) hne' with hq | hq
    · exact ⟨(e₁, e₂), hq, p, hp, h₁, h₂⟩
    · exact ⟨(e₂, e₁), hq, p, hp, h₂, h₁⟩

theorem g003_iff : (∃ e ∈ s.sortedEndings, s.gctx.pats.any (fun p => e.condition.eval (s.gctx.σ p)) = false) ↔
    ∃ e ∈ s.endings, ∀ p, s.IsPattern p → s.holdsAt e p = false := by
  simp only [mem_sortedEndings, Bool.eq_false_iff, ne_eq, List.any_eq_true, not_exists, not_and, mem_gctx_pats]
  rfl

theorem g004_iff : (∃ gl ∈ s.goals, (s.gctx.pats.map fun p => s.gctx.σ p gl.id).contains (.bool true) = false) ↔
    ∃ gl ∈ s.goals, ∀ p, s.IsPattern p → toAssignment s.gVars p gl.id ≠ .bool true := by
  simp only [Bool.eq_false_iff, ne_eq, List.contains_iff_mem, List.mem_map, not_exists, not_and, mem_gctx_pats]
  rfl

theorem hasCodeD_checkG (hR : checkR s = []) (c : String) (hc : c ∈ errorCodes) :
    hasCodeD c (checkG s) ↔ GViolates s c := by
  have hw := errorCode_not_warning hc
  have h8 : ¬ hasCodeD c (checkG008 s) := fun h => by
    rw [hasCodeD_single (X := "G008") (fun d hd => by
      simp only [checkG008, List.mem_filterMap] at hd
      obtain ⟨_, _, hd⟩ := hd
      split at hd
      · simp only [Option.some.injEq] at hd; subst hd; rfl
      · cases hd)] at h
    rw [h.1] at hw; simp [warningCodes] at hw
  unfold checkG
  dsimp only
  rw [hasCodeD_append]
  simp only [h8, or_false]
  by_cases hn : s.gCount > gLimit
  · simp only [hn, ite_true]
    simp only [hasCodeD, List.mem_singleton, exists_eq_left, err]
    unfold GViolates
    split <;> simp_all [Nat.not_le.mpr hn]
  · simp only [hn, ite_false]
    have hle : s.gCount ≤ gLimit := Nat.le_of_not_lt hn
    by_cases hp : s.gctx.pats.isEmpty
    · simp only [hp, ite_true]
      have hne : ¬ ∃ p, s.IsPattern p := by rw [exists_pattern_iff]; simpa using hp
      simp only [hasCodeD, List.mem_singleton, exists_eq_left, err]
      unfold GViolates
      split <;> simp_all
    · simp only [hp, Bool.false_eq_true, ite_false, checkGPatterns, hasCodeD_append]
      have hex : ∃ p, s.IsPattern p := (exists_pattern_iff s).mpr (by simpa using hp)
      have h1 : hasCodeD c (checkG001 s s.gctx) ↔ c = "G001" ∧ checkG001 s s.gctx ≠ [] :=
        hasCodeD_single (fun d hd => by
          unfold checkG001 at hd; split at hd
          · simp only [List.mem_singleton] at hd; subst hd; rfl
          · cases hd) c
      have h2 : hasCodeD c (checkG002 s s.gctx) ↔ c = "G002" ∧ checkG002 s s.gctx ≠ [] :=
        hasCodeD_single (fun d hd => by
          unfold checkG002 at hd
          obtain ⟨⟨e₁, e₂⟩, _, hd⟩ := List.mem_filterMap.mp hd
          simp only at hd
          split at hd
          · simp only [Option.some.injEq] at hd; subst hd; rfl
          · cases hd) c
      rw [h1, h2, hasCodeD_checkGRest, g001_iff, g002_iff s hR, g003_iff, g004_iff]
      have hw6 : ¬ (c = "G006" ∨ c = "G009") := by
        rintro (rfl | rfl) <;> simp [warningCodes] at hw
      simp only [hw6, false_and, or_false]
      unfold GViolates
      split <;> simp_all

end

/-! ## 定理 1 (規則ごと) -/

theorem rIssue_code_ne (c : String) (hc : c ∈ errorCodes) (rc : RCode) : c ≠ rc.str := by
  simp only [errorCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
  cases rc <;> rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **定理 1 (規則ごと)**: R 群以外の error 規則 c について、判定器がコード c の検出結果を出す ⇔
R 群の違反がなく、規則 c の違反条件が成り立つ。 -/
theorem check_rule (s : Scenario) (c : String) (hc : c ∈ errorCodes) :
    (∃ d ∈ check s, d.code = c) ↔ checkR s = [] ∧ Violates s c := by
  have hmem : (∃ d ∈ check s, d.code = c) ↔ hasCodeD c (checkRaw s) := by
    simp only [check, mem_normalize, hasCodeD, eq_comm]
  rw [hmem]
  unfold checkRaw
  dsimp only
  by_cases hR : checkR s = []
  · simp only [hR, List.isEmpty_nil, ite_true, true_and, hasCodeD_append, hasCodeD_checkEvents,
      hasCodeD_checkPost s c hc, hasCodeD_checkG s hR c hc, Violates, or_assoc]
  · have hne : (checkR s).isEmpty = false := by simpa using hR
    simp only [hne, Bool.false_eq_true, ite_false, hR, false_and, iff_false]
    rintro ⟨d, hd, rfl⟩
    simp only [checkR, List.mem_map] at hd
    obtain ⟨⟨rc, a, e⟩, _, rfl⟩ := hd
    exact rIssue_code_ne _ hc rc rfl

end MurderMystery
