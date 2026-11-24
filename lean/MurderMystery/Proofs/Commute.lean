import MurderMystery.Proofs.Perm
import MurderMystery.Spec.Valid

/-!
# 定理 4: 同時刻イベントの交換可能性

同時刻のイベントどうしが **独立**(参加者とアイテムが重ならず、一方の observe の対象を他方が move させない)
なら、それらの処理順を入れ替えても、終了状態とイベントごとの検出結果(T/I/K 群)は変わらない。

独立の条件のうち、参加者とアイテムが重ならないことは T005 / I004 の違反がないことと同じ。
observe の対象についての条件は T005 / I004 からは出ない(対象は参加者ではないため)。この条件がないと、
「x が 10:00 に移動し、c が 10:00 に x を観察する」で、ID の順によって T007 が出たり出なかったりする。
-/
namespace MurderMystery

/-- move で位置が変わるキャラクター。 -/
def EventKind.moved : EventKind → List Id
  | .move c .. => [c]
  | _ => []

/-- observe の対象(参加者ではないが、場所の条件を課される)。 -/
def EventKind.observed : EventKind → List Id
  | .observe _ _ _ ts _ => ts
  | _ => []

/-- 2つのイベントが独立。 -/
structure Independent (e₁ e₂ : Event) : Prop where
  chars : ∀ c ∈ e₁.kind.participants, c ∉ e₂.kind.participants
  items : ∀ i, e₁.kind.item? = some i → e₂.kind.item? ≠ some i
  obs₁ : ∀ c ∈ e₁.kind.observed, c ∉ e₂.kind.moved
  obs₂ : ∀ c ∈ e₂.kind.observed, c ∉ e₁.kind.moved

theorem Independent.symm {e₁ e₂ : Event} (h : Independent e₁ e₂) : Independent e₂ e₁ where
  chars c h₂ h₁ := h.chars c h₁ h₂
  items i h₂ h₁ := h.items i h₁ h₂
  obs₁ := h.obs₂
  obs₂ := h.obs₁

/-! ## イベントの属性 -/

theorem moved_sub (k : EventKind) : ∀ c ∈ k.moved, c ∈ k.participants := by
  cases k <;> simp [EventKind.moved, EventKind.participants]

theorem actors_sub (k : EventKind) : ∀ c ∈ k.actors, c ∈ k.participants := by
  cases k <;> simp [EventKind.actors, EventKind.participants]

theorem holderRole_mem (k : EventKind) (i : Id) (h : k.item? = some i) : k.holderRole ∈ k.participants := by
  cases k <;> simp_all [EventKind.item?, EventKind.holderRole, EventKind.participants]

/-! ## 1ステップの効果は局所的 -/

theorem State.ext' {A B : State} (hp : ∀ z, A.pos z = B.pos z) (hh : ∀ i, A.holder i = B.holder i)
    (hk : ∀ z, A.knows z = B.knows z) (hd : ∀ z, A.dead z = B.dead z) : A = B := by
  cases A; cases B
  simp only [State.mk.injEq]
  exact ⟨funext hp, funext hh, funext hk, funext hd⟩

theorem step_pos_of_not_moved (S : State) (e : Event) (c : Id) (h : c ∉ e.kind.moved) :
    (step S e).pos c = S.pos c := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp_all [step, EventKind.moved, update] <;> split <;> rfl

theorem step_pos_congr (S S' : State) (e : Event) (c : Id) (h : S.pos c = S'.pos c) :
    (step S e).pos c = (step S' e).pos c := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp_all [step, update] <;> (try split) <;> (try split) <;> simp_all

theorem step_dead_of_not_participant (S : State) (e : Event) (c : Id) (h : c ∉ e.kind.participants) :
    (step S e).dead c = S.dead c := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp_all [step, EventKind.participants, update] <;> (try split) <;> simp_all [update]

theorem step_dead_congr (S S' : State) (e : Event) (c : Id) (h : S.dead c = S'.dead c) :
    (step S e).dead c = (step S' e).dead c := by
  obtain ⟨_, _, k, _⟩ := e
  cases k with
  | move c' _ _ _ fatal =>
    simp only [step]
    by_cases hc : c = c'
    · subst hc
      by_cases hn : (S'.dead c).isNone = true
      · have hn' : (S.dead c).isNone = true := by rw [h]; exact hn
        cases fatal <;> simp [hn, hn', update, h]
      · have hn' : ¬ (S.dead c).isNone = true := by rw [h]; exact hn
        simp only [hn, hn', Bool.and_false, Bool.false_eq_true, ite_false]; exact h
    · have e1 : ∀ (D : Id → Option Id) (b : Bool) v, (if b = true then update D c' v else D) c = D c := by
        intro D b v; split <;> simp [update, hc]
      rw [e1, e1, h]
  | die c' =>
    simp only [step]
    by_cases hc : c = c'
    · subst hc
      by_cases hn : (S'.dead c).isNone = true
      · have hn' : (S.dead c).isNone = true := by rw [h]; exact hn
        simp [hn, hn', update]
      · have hn' : ¬ (S.dead c).isNone = true := by rw [h]; exact hn
        simp only [hn, hn', ite_false]; exact h
    · have e1 : ∀ (T : State) v, (if (T.dead c').isNone = true then { T with dead := update T.dead c' v } else T).dead c = T.dead c := by
        intro T v; split <;> simp [update, hc]
      rw [e1, e1, h]
  | _ => exact h

theorem addKnows_of_not_mem (k : Id → Id → Bool) (cs fs : List Id) (c : Id) (h : c ∉ cs) :
    addKnows k cs fs c = k c := by
  funext f; simp [addKnows, h]

theorem addKnows_congr (k k' : Id → Id → Bool) (cs fs : List Id) (c : Id) (h : k c = k' c) :
    addKnows k cs fs c = addKnows k' cs fs c := by
  funext f; simp only [addKnows]; rw [h]

theorem step_knows_of_not_participant (S : State) (e : Event) (c : Id) (h : c ∉ e.kind.participants) :
    (step S e).knows c = S.knows c := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp only [step] <;> (try split) <;>
    first
    | rfl
    | (apply addKnows_of_not_mem; simp_all [EventKind.participants])

theorem step_knows_congr (S S' : State) (e : Event) (c : Id) (h : S.knows c = S'.knows c) :
    (step S e).knows c = (step S' e).knows c := by
  obtain ⟨_, _, k, _⟩ := e
  cases k with
  | die c' => simp only [step]; split <;> split <;> exact h
  | _ => simp only [step] <;> first | exact h | exact addKnows_congr _ _ _ _ _ h

theorem step_holder_of_ne (S : State) (e : Event) (i : Id) (h : e.kind.item? ≠ some i) :
    (step S e).holder i = S.holder i := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp_all [step, EventKind.item?, update] <;> (try split) <;> (try simp_all) <;> grind

theorem step_holder_congr (S S' : State) (e : Event) (i : Id) (hh : S.holder i = S'.holder i)
    (hp : ∀ c ∈ e.kind.participants, S.pos c = S'.pos c) :
    (step S e).holder i = (step S' e).holder i := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp_all [step, EventKind.participants, update] <;> (try split) <;> (try split) <;> simp_all

/-! ## 状態遷移の交換 -/

/-- 参加者とアイテムが重ならない2イベントは、処理順を入れ替えても同じ状態になる。 -/
theorem step_comm (S : State) (e₁ e₂ : Event)
    (hc : ∀ c ∈ e₁.kind.participants, c ∉ e₂.kind.participants)
    (hi : ∀ i, e₁.kind.item? = some i → e₂.kind.item? ≠ some i) :
    step (step S e₁) e₂ = step (step S e₂) e₁ := by
  have hm₁ : ∀ c ∈ e₁.kind.moved, c ∉ e₂.kind.moved := fun c h h' =>
    hc c (moved_sub _ c h) (moved_sub _ c h')
  apply State.ext'
  · intro z
    by_cases h₁ : z ∈ e₁.kind.moved
    · have h₂ : z ∉ e₂.kind.moved := hm₁ z h₁
      rw [step_pos_of_not_moved _ _ _ h₂]
      exact step_pos_congr _ _ _ _ (step_pos_of_not_moved _ _ _ h₂).symm
    · rw [step_pos_of_not_moved _ _ _ h₁]
      exact step_pos_congr _ _ _ _ (step_pos_of_not_moved _ _ _ h₁)
  · intro i
    have hpos₁ : ∀ c ∈ e₂.kind.participants, (step S e₁).pos c = S.pos c := fun c h =>
      step_pos_of_not_moved _ _ _ fun h' => hc c (moved_sub _ c h') h
    have hpos₂ : ∀ c ∈ e₁.kind.participants, (step S e₂).pos c = S.pos c := fun c h =>
      step_pos_of_not_moved _ _ _ fun h' => hc c h (moved_sub _ c h')
    by_cases h₁ : e₁.kind.item? = some i
    · rw [step_holder_of_ne _ _ _ (hi i h₁)]
      exact step_holder_congr _ _ _ _ (step_holder_of_ne _ _ _ (hi i h₁)).symm
        (fun c h => (hpos₂ c h).symm)
    · rw [step_holder_of_ne _ _ _ h₁]
      exact step_holder_congr _ _ _ _ (step_holder_of_ne _ _ _ h₁) hpos₁
  · intro z
    by_cases h₁ : z ∈ e₁.kind.participants
    · have h₂ : z ∉ e₂.kind.participants := hc z h₁
      rw [step_knows_of_not_participant _ _ _ h₂]
      exact step_knows_congr _ _ _ _ (step_knows_of_not_participant _ _ _ h₂).symm
    · rw [step_knows_of_not_participant _ _ _ h₁]
      exact step_knows_congr _ _ _ _ (step_knows_of_not_participant _ _ _ h₁)
  · intro z
    by_cases h₁ : z ∈ e₁.kind.participants
    · have h₂ : z ∉ e₂.kind.participants := hc z h₁
      rw [step_dead_of_not_participant _ _ _ h₂]
      exact step_dead_congr _ _ _ _ (step_dead_of_not_participant _ _ _ h₂).symm
    · rw [step_dead_of_not_participant _ _ _ h₁]
      exact step_dead_congr _ _ _ _ (step_dead_of_not_participant _ _ _ h₁)

/-! ## 検出結果は関係するキャラクター・アイテムの状態だけで決まる -/

/-- 処理前の状態 S と S' が、イベントの検査が読む部分で一致する。 -/
structure AgreeOn (S S' : State) (k : EventKind) : Prop where
  pos : ∀ c, c ∈ k.participants ∨ c ∈ k.observed → S.pos c = S'.pos c
  dead : ∀ c ∈ k.participants, S.dead c = S'.dead c
  knows : ∀ c ∈ k.participants, S.knows c = S'.knows c
  holder : ∀ i, k.item? = some i → S.holder i = S'.holder i

theorem flatMap_congr' {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem filterMap_congr' {l : List α} {f g : α → Option β} (h : ∀ x ∈ l, f x = g x) :
    l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem inTransit_congr {S S' : State} {c : Id} (t : Time) (h : S.pos c = S'.pos c) :
    S.inTransit c t = S'.inTransit c t := by
  simp only [State.inTransit, h]

theorem atLoc_congr {S S' : State} {c : Id} (t : Time) (l : Id) (p : Bool) (h : S.pos c = S'.pos c) :
    atLoc S t c l p = atLoc S' t c l p := by
  simp only [atLoc, inTransit_congr t h, h]

section
variable (s : Scenario) (S S' : State) (e : Event) (E : List Event) (hA : AgreeOn S S' e.kind)
include hA

theorem issuesMove_congr : issuesMove s ⟨S, e, E⟩ = issuesMove s ⟨S', e, E⟩ := by
  obtain ⟨_, _, k, _⟩ := e
  cases k with
  | move c _ _ _ _ =>
    simp only [issuesMove]
    rw [hA.pos c (Or.inl (by simp [EventKind.participants]))]
  | _ => rfl

theorem issuesParticipants_congr : issuesParticipants ⟨S, e, E⟩ = issuesParticipants ⟨S', e, E⟩ := by
  unfold issuesParticipants
  apply flatMap_congr'
  intro c hc
  have hp := hA.pos c (Or.inl hc)
  simp only [issuesParticipant, issuesT006, issuesT010, inTransit_congr _ hp, hp, hA.dead c hc]
  rfl

theorem issuesPlace_congr : issuesPlace s ⟨S, e, E⟩ = issuesPlace s ⟨S', e, E⟩ := by
  obtain ⟨_, _, k, _⟩ := e
  have hpos := hA.pos
  cases k with
  | scene l ps rv =>
    simp only [issuesPlace]
    exact flatMap_congr' fun c hc => atLoc_congr _ _ _ (hpos c (Or.inl hc))
  | observe c l tl ts fs =>
    simp only [issuesPlace]
    rw [atLoc_congr _ _ _ (hpos c (Or.inl (by simp [EventKind.participants]))),
      flatMap_congr' (l := ts) fun x hx =>
        atLoc_congr _ _ _ (hpos x (Or.inr (by simpa [EventKind.observed] using hx)))]
  | transfer a b i =>
    simp only [issuesPlace]
    have ha := hpos a (Or.inl (by simp [EventKind.participants]))
    have hb := hpos b (Or.inl (by simp [EventKind.participants]))
    rw [inTransit_congr _ ha, inTransit_congr _ hb, ha, hb]
  | tell a b fs =>
    simp only [issuesPlace]
    have ha := hpos a (Or.inl (by simp [EventKind.participants]))
    have hb := hpos b (Or.inl (by simp [EventKind.participants]))
    rw [inTransit_congr _ ha, inTransit_congr _ hb, ha, hb]
  | _ => rfl

theorem issuesItem_congr : issuesItem ⟨S, e, E⟩ = issuesItem ⟨S', e, E⟩ := by
  unfold issuesItem
  dsimp only
  cases hi : e.kind.item? with
  | none => rfl
  | some i =>
    have hw := hA.pos _ (Or.inl (holderRole_mem _ _ hi))
    simp only [hA.holder i hi, inTransit_congr _ hw, hw]
    rfl

theorem issuesKnowledge_congr : issuesKnowledge ⟨S, e, E⟩ = issuesKnowledge ⟨S', e, E⟩ := by
  unfold issuesKnowledge
  dsimp only
  have hk2 : (e.kind.actors.flatMap fun a =>
      e.requires.filterMap fun f => if S.knows a f = true then none else some ("K002", [a, f])) =
      (e.kind.actors.flatMap fun a =>
      e.requires.filterMap fun f => if S'.knows a f = true then none else some ("K002", [a, f])) := by
    apply flatMap_congr'
    intro a ha
    rw [hA.knows a (actors_sub _ a ha)]
  rw [hk2]
  congr 1
  obtain ⟨_, _, k, _⟩ := e
  cases k with
  | tell a b fs =>
    simp only
    rw [hA.knows a (by simp [EventKind.participants])]
  | _ => rfl

/-- 処理前の状態が検査の読む部分で一致すれば、検出結果は同じ。 -/
theorem stepIssues_congr : stepIssues s ⟨S, e, E⟩ = stepIssues s ⟨S', e, E⟩ := by
  unfold stepIssues
  rw [issuesMove_congr s S S' e E hA, issuesParticipants_congr S S' e E hA, issuesPlace_congr s S S' e E hA,
    issuesItem_congr S S' e E hA, issuesKnowledge_congr S S' e E hA]
  rfl

end

/-- 独立なイベント e₂ を処理しても、e₁ の検査が読む部分は変わらない。 -/
theorem agreeOn_step (S : State) {e₁ e₂ : Event} (h : Independent e₁ e₂) : AgreeOn (step S e₂) S e₁.kind where
  pos c hc := by
    apply step_pos_of_not_moved
    rcases hc with hc | hc
    · exact fun h' => h.chars c hc (moved_sub _ c h')
    · exact h.obs₁ c hc
  dead c hc := step_dead_of_not_participant _ _ _ (h.chars c hc)
  knows c hc := step_knows_of_not_participant _ _ _ (h.chars c hc)
  holder i hi := step_holder_of_ne _ _ _ (h.items i hi)

/-! ## 前のイベントの列への依存 -/

theorem lastSameTime_append_irrel (S : State) (e x : Event) (E : List Event) (p : Event → Bool)
    (hx : p x = false) : lastSameTime ⟨S, e, E ++ [x]⟩ p = lastSameTime ⟨S, e, E⟩ p := by
  simp [lastSameTime, List.filter_append, hx]

theorem lastSameTime_swap (S : State) (e x y : Event) (P M : List Event) (p : Event → Bool)
    (h : ¬ (p x = true ∧ p y = true)) :
    lastSameTime ⟨S, e, P ++ [x] ++ [y] ++ M⟩ p = lastSameTime ⟨S, e, P ++ [y] ++ [x] ++ M⟩ p := by
  simp only [lastSameTime, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases hx : p x = true <;> by_cases hy : p y = true <;> simp_all

/-- 検出結果が前のイベントの列に依存するのは、T005 と I004 の「同時刻の直前のイベント」だけ。 -/
theorem stepIssues_earlier (s : Scenario) (S : State) (e : Event) (E E' : List Event)
    (h5 : ∀ c ∈ e.kind.participants, lastSameTime ⟨S, e, E⟩ (fun e' => e'.kind.participants.contains c) =
      lastSameTime ⟨S, e, E'⟩ (fun e' => e'.kind.participants.contains c))
    (h4 : ∀ i, e.kind.item? = some i → lastSameTime ⟨S, e, E⟩ (fun e' => e'.kind.item? == some i) =
      lastSameTime ⟨S, e, E'⟩ (fun e' => e'.kind.item? == some i)) :
    stepIssues s ⟨S, e, E⟩ = stepIssues s ⟨S, e, E'⟩ := by
  have hP : issuesParticipants ⟨S, e, E⟩ = issuesParticipants ⟨S, e, E'⟩ := by
    unfold issuesParticipants
    apply flatMap_congr'
    intro c hc
    simp only [issuesParticipant, issuesT005, h5 c hc]
    rfl
  have hI : issuesItem ⟨S, e, E⟩ = issuesItem ⟨S, e, E'⟩ := by
    unfold issuesItem
    dsimp only
    cases hi : e.kind.item? with
    | none => rfl
    | some i => simp only [issuesI004, h4 i hi]
  unfold stepIssues
  rw [hP, hI]
  rfl

/-- 1ステップの検出結果(`checkEvents` の各ステップの分)。 -/
def stepDiags (s : Scenario) (st : Step) : List Diag :=
  (stepIssues s st).map fun (c, a) => err c a (some st.ev.id)

theorem checkEvents_eq (s : Scenario) : checkEvents s = s.trace.flatMap (stepDiags s) := rfl

/-- 独立な x, y について、x の検出結果は y を先に処理しても変わらない。 -/
theorem stepDiags_after (s : Scenario) (S : State) {x y : Event} (P : List Event) (h : Independent x y) :
    stepDiags s ⟨step S y, x, P ++ [y]⟩ = stepDiags s ⟨S, x, P⟩ := by
  unfold stepDiags
  rw [stepIssues_congr s _ _ x _ (agreeOn_step S h)]
  rw [stepIssues_earlier s S x (P ++ [y]) P]
  · intro c hc
    apply lastSameTime_append_irrel
    simp only [List.contains_iff_mem, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
    exact fun h' => h.chars c hc h'
  · intro i hi
    apply lastSameTime_append_irrel
    simp only [Bool.eq_false_iff, ne_eq, beq_iff_eq]
    exact h.items i hi

theorem runAux_swap_prev (s : Scenario) {x y : Event} (hxy : Independent x y) :
    ∀ (R : List Event) (S : State) (P M : List Event),
      (runAux S (P ++ [x] ++ [y] ++ M) R).2 = (runAux S (P ++ [y] ++ [x] ++ M) R).2 ∧
      (runAux S (P ++ [x] ++ [y] ++ M) R).1.flatMap (stepDiags s) =
        (runAux S (P ++ [y] ++ [x] ++ M) R).1.flatMap (stepDiags s)
  | [], _, _, _ => by simp [runAux]
  | e :: R, S, P, M => by
    have ih := runAux_swap_prev s hxy R (step S e) P (M ++ [e])
    simp only [← List.append_assoc] at ih
    simp only [runAux, List.flatMap_cons]
    refine ⟨ih.1, ?_⟩
    rw [ih.2]
    congr 1
    unfold stepDiags
    rw [stepIssues_earlier s S e (P ++ [x] ++ [y] ++ M) (P ++ [y] ++ [x] ++ M)]
    · intro c _
      apply lastSameTime_swap
      simp only [List.contains_iff_mem, decide_eq_true_eq]
      exact fun ⟨h₁, h₂⟩ => hxy.chars c h₁ h₂
    · intro i _
      apply lastSameTime_swap
      simp only [beq_iff_eq]
      exact fun ⟨h₁, h₂⟩ => hxy.items i h₁ h₂

/-! ## 隣り合う独立なイベントの入れ替え -/

/-- 2つの実行が同じ終了状態になり、検出結果が並べ替えを除いて等しい。 -/
def RunEquiv (s : Scenario) (r₁ r₂ : List Step × State) : Prop :=
  r₁.2 = r₂.2 ∧ (r₁.1.flatMap (stepDiags s)).Perm (r₂.1.flatMap (stepDiags s))

theorem RunEquiv.refl (s : Scenario) (r : List Step × State) : RunEquiv s r r := ⟨rfl, List.Perm.refl _⟩

theorem RunEquiv.symm {s : Scenario} {r₁ r₂} (h : RunEquiv s r₁ r₂) : RunEquiv s r₂ r₁ := ⟨h.1.symm, h.2.symm⟩

theorem RunEquiv.trans {s : Scenario} {r₁ r₂ r₃} (h₁ : RunEquiv s r₁ r₂) (h₂ : RunEquiv s r₂ r₃) :
    RunEquiv s r₁ r₃ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem RunEquiv.cons (s : Scenario) (S : State) (P : List Event) (e : Event) {X Y : List Event}
    (h : RunEquiv s (runAux (step S e) (P ++ [e]) X) (runAux (step S e) (P ++ [e]) Y)) :
    RunEquiv s (runAux S P (e :: X)) (runAux S P (e :: Y)) := by
  simp only [RunEquiv, runAux, List.flatMap_cons] at *
  exact ⟨h.1, h.2.append_left _⟩

/-- 隣り合う独立なイベントを入れ替えても、終了状態と検出結果は変わらない。 -/
theorem runAux_swap (s : Scenario) {x y : Event} (hxy : Independent x y) (S : State) (P R : List Event) :
    RunEquiv s (runAux S P (x :: y :: R)) (runAux S P (y :: x :: R)) := by
  have hp := runAux_swap_prev s hxy R (step (step S x) y) P []
  simp only [List.append_nil] at hp
  simp only [RunEquiv, runAux, List.flatMap_cons]
  rw [step_comm S x y hxy.chars hxy.items] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rw [hp.2, stepDiags_after s S P hxy, stepDiags_after s S P hxy.symm]
  simp only [← List.append_assoc]
  exact List.Perm.append_right _ List.perm_append_comm

/-! ## 時刻順の任意の並べ方 -/

theorem runAux_bubble (s : Scenario) (e : Event) (B : List Event) :
    ∀ (A : List Event) (S : State) (P : List Event), (∀ a ∈ A, Independent a e) →
      RunEquiv s (runAux S P (A ++ e :: B)) (runAux S P (e :: (A ++ B)))
  | [], S, P, _ => RunEquiv.refl s _
  | a :: A, S, P, h => by
    have ih := runAux_bubble s e B A (step S a) (P ++ [a]) fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    exact (RunEquiv.cons s S P a ih).trans (runAux_swap s (h a (List.mem_cons_self ..)) S P (A ++ B))

theorem pairwise_append_cons {R : α → α → Prop} {A B : List α} {e : α} (h : (A ++ e :: B).Pairwise R) :
    (A ++ B).Pairwise R ∧ ∀ a ∈ A, R a e := by
  rw [List.pairwise_append] at h
  obtain ⟨hA, heB, hx⟩ := h
  refine ⟨List.pairwise_append.mpr ⟨hA, List.Pairwise.of_cons heB, fun a ha b hb =>
    hx a ha b (List.mem_cons_of_mem _ hb)⟩, fun a ha => hx a ha e (List.mem_cons_self ..)⟩

/-- 時刻順に並んだ2つの並べ方で、同時刻のイベントがどれも独立なら、
終了状態は同じで、検出結果は並べ替えを除いて等しい。 -/
theorem runAux_reorder (s : Scenario) :
    ∀ (l l' : List Event) (S : State) (P : List Event), l.Perm l' →
      l.Pairwise (fun a b => a.time ≤ b.time) → l'.Pairwise (fun a b => a.time ≤ b.time) →
      l.Pairwise (fun a b => a.time = b.time → Independent a b) →
      RunEquiv s (runAux S P l) (runAux S P l')
  | [], l', S, P, hp, _, _, _ => by
    rw [List.Perm.nil_eq hp]; exact RunEquiv.refl s _
  | e :: l, l', S, P, hp, hs, hs', hind => by
    obtain ⟨A, B, rfl⟩ := List.append_of_mem (hp.mem_iff.mp (List.mem_cons_self ..))
    have hl : l.Perm (A ++ B) := (List.perm_cons e).mp (hp.trans List.perm_middle)
    obtain ⟨hsAB, hAe⟩ := pairwise_append_cons hs'
    have hindA : ∀ a ∈ A, Independent a e := by
      intro a ha
      have hal : a ∈ l := hl.mem_iff.mpr (List.mem_append_left _ ha)
      have hle : e.time ≤ a.time := List.rel_of_pairwise_cons hs hal
      exact (List.rel_of_pairwise_cons hind hal (Nat.le_antisymm hle (hAe a ha))).symm
    have ih := runAux_reorder s l (A ++ B) (step S e) (P ++ [e]) hl (List.Pairwise.of_cons hs) hsAB
      (List.Pairwise.of_cons hind)
    exact (RunEquiv.cons s S P e ih).trans (runAux_bubble s e B A S P hindA).symm

/-! ## 定理 4 -/

/-- T005 / I004 の違反がない: 同時刻の前のイベントと参加者・アイテムが重ならない。 -/
def NoSameTimeConflict (s : Scenario) : Prop :=
  ∀ st ∈ s.trace,
    (∀ c ∈ st.ev.kind.participants, ∀ e' ∈ st.earlier, e'.time = st.ev.time → c ∉ e'.kind.participants) ∧
    (∀ i, st.ev.kind.item? = some i → ∀ e' ∈ st.earlier, e'.time = st.ev.time → e'.kind.item? ≠ some i)

/-- 同時刻に、observe の対象のキャラクターが move していない。 -/
def NoSameTimeObservedMove (s : Scenario) : Prop :=
  ∀ a ∈ s.events, ∀ b ∈ s.events, a.time = b.time → ∀ c ∈ a.kind.observed, c ∉ b.kind.moved

theorem NoSameTimeConflict.of_valid {s : Scenario} (h : Valid s) : NoSameTimeConflict s := by
  intro st hst
  have hv := h.2.1 st hst
  exact ⟨fun c hc => (hv.2.2.1 c hc).1, fun i hi => (hv.2.2.2.2.1 i hi).1⟩

theorem mem_runAux_of_eq_append (b : Event) (B : List Event) :
    ∀ (A : List Event) (S : State) (P : List Event), ∃ S', (⟨S', b, P ++ A⟩ : Step) ∈ (runAux S P (A ++ b :: B)).1
  | [], S, P => ⟨S, by simp [runAux]⟩
  | a :: A, S, P => by
    obtain ⟨S', h⟩ := mem_runAux_of_eq_append b B A (step S a) (P ++ [a])
    refine ⟨S', ?_⟩
    simp only [List.cons_append, runAux, List.mem_cons]
    right
    simpa using h

theorem pairwise_of_prefix {R : α → α → Prop} :
    ∀ (L : List α), (∀ A b B, L = A ++ b :: B → ∀ a ∈ A, R a b) → L.Pairwise R
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    refine List.Pairwise.cons (fun y hy => ?_) (pairwise_of_prefix xs fun A b B he a ha =>
      h (x :: A) b B (by rw [he]; rfl) a (List.mem_cons_of_mem _ ha))
    obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hy
    exact h (x :: B₁) y B₂ (by simp) x (List.mem_cons_self ..)

theorem pairwise_timeLe_sortedEvents (s : Scenario) :
    s.sortedEvents.Pairwise (fun a b => a.time ≤ b.time) := by
  apply (pairwise_sortedEvents s.events).imp
  intro a b h
  simp only [evLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨h, _⟩
  · exact Nat.le_of_lt h
  · exact Nat.le_of_eq h

/-- T005 / I004 の違反がなく、observe の対象が同時刻に move しなければ、同時刻のイベントはどれも独立。 -/
theorem independent_of_noConflict (s : Scenario) (h₁ : NoSameTimeConflict s) (h₂ : NoSameTimeObservedMove s) :
    s.sortedEvents.Pairwise (fun a b => a.time = b.time → Independent a b) := by
  apply pairwise_of_prefix
  intro A b B hL a ha ht
  obtain ⟨S', hst⟩ := mem_runAux_of_eq_append b B A s.initState []
  rw [← hL] at hst
  have h := h₁ _ hst
  simp only [List.nil_append] at h
  have hmem : ∀ x, x ∈ s.sortedEvents → x ∈ s.events := fun x hx => List.mem_mergeSort.mp hx
  have haE := hmem a (by rw [hL]; exact List.mem_append_left _ ha)
  have hbE := hmem b (by rw [hL]; simp)
  exact {
    chars := fun c hca hcb => h.1 c hcb a ha ht hca
    items := fun i hia hib => h.2 i hib a ha ht hia
    obs₁ := h₂ a haE b hbE ht
    obs₂ := h₂ b hbE a haE ht.symm }

/-- **定理 4**: T005 / I004 の違反がなく、observe の対象が同時刻に move しなければ、
時刻順を保つどんな並べ方でイベントを処理しても、終了状態は同じで、
イベントごとの検出結果は(並べ替えを除いて)`checkEvents` と等しい。 -/
theorem reorder_same_time (s : Scenario) (h₁ : NoSameTimeConflict s) (h₂ : NoSameTimeObservedMove s)
    (l : List Event) (hp : s.sortedEvents.Perm l) (hl : l.Pairwise (fun a b => a.time ≤ b.time)) :
    (runAux s.initState [] l).2 = s.final ∧
      ((runAux s.initState [] l).1.flatMap (stepDiags s)).Perm (checkEvents s) := by
  have h := runAux_reorder s s.sortedEvents l s.initState [] hp (pairwise_timeLe_sortedEvents s) hl
    (independent_of_noConflict s h₁ h₂)
  exact ⟨h.1.symm, h.2.symm⟩

end MurderMystery
