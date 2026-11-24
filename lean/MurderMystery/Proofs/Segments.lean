import MurderMystery.Proofs.Commute

/-!
# 定理 8: 区間の整合

各キャラクター c の move について、

- 開始時刻以降に出発し(T001)、
- 出発時刻 ≤ 到着時刻であり(R006)、
- 出発時に移動中でない(T006)

なら、

1. 居場所の区間 `segments c` は時刻順に並び、互いに重ならない(各区間は空でない)。
2. 時刻 t(開始時刻 ≤ t < 終了時刻、死亡時刻より前)での `whereAt c t` は、時刻 t までのイベントを
   すべて処理した状態での居場所(移動中なら "transit"、そうでなければ最後の行き先)と一致する。
-/
namespace MurderMystery

/-! ## 移動の列 -/

abbrev Move := Time × Id × Time

/-- 出発 ≤ 到着、前の到着 ≤ 次の出発 が続く(最初の出発は s₀ 以降)。 -/
def ChainOK : Time → List Move → Prop
  | _, [] => True
  | s₀, (d, _, a) :: M => s₀ ≤ d ∧ d ≤ a ∧ ChainOK a M

theorem segsAux_start_ge (endT : Time) :
    ∀ (M : List Move) (p : Id) (s₀ : Time), ChainOK s₀ M → ∀ x ∈ segsAux endT p s₀ M, s₀ ≤ x.2.1
  | [], p, s₀, _, x, hx => by simp [segsAux] at hx; simp [hx]
  | (d, to, a) :: M, p, s₀, ⟨h₁, h₂, h₃⟩, x, hx => by
    simp only [segsAux, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.le_refl _
    · exact Nat.le_trans h₁ (Nat.le_trans h₂ (segsAux_start_ge endT M to a h₃ x hx))

theorem segsAux_pairwise (endT : Time) :
    ∀ (M : List Move) (p : Id) (s₀ : Time), ChainOK s₀ M →
      (segsAux endT p s₀ M).Pairwise (fun x y => x.2.2 ≤ y.2.1)
  | [], _, _, _ => by simp [segsAux]
  | (d, to, a) :: M, p, s₀, ⟨_, h₂, h₃⟩ => by
    simp only [segsAux]
    exact List.Pairwise.cons (fun y hy => Nat.le_trans h₂ (segsAux_start_ge endT M to a h₃ y hy))
      (segsAux_pairwise endT M to a h₃)

/-- 区間が時刻 t を含む。 -/
def covers (t : Time) (x : Id × Time × Time) : Bool := x.2.1 ≤ t && t < x.2.2

/-- 区間の検索結果から居場所を読む。 -/
def locOf : Option (Id × Time × Time) → String
  | some (l, _, _) => l
  | none => "transit"

/-- 位置から、時刻 t での居場所を読む。 -/
def obs (t : Time) (p : Position) : String :=
  if p.via.isSome && t < p.arrive then "transit" else p.dest

/-- 移動の列を順に適用した位置(最後の移動が残る)。 -/
def foldMoves (q : Position) (M : List Move) : Position :=
  M.foldl (fun _ m => ⟨m.2.1, m.2.2, some ""⟩) q

theorem foldMoves_cons_irrel (q q' : Position) (m : Move) (M : List Move) :
    foldMoves q (m :: M) = foldMoves q' (m :: M) := rfl

theorem find?_none_of_lt (endT t : Time) :
    ∀ (M : List Move) (p : Id) (s₀ : Time), ChainOK s₀ M → t < s₀ →
      (segsAux endT p s₀ M).find? (covers t) = none := by
  intro M p s₀ hc ht
  rw [List.find?_eq_none]
  intro x hx
  have := segsAux_start_ge endT M p s₀ hc x hx
  simp only [covers, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_lt]
  intro h; exact absurd (Nat.lt_of_lt_of_le ht this) (Nat.not_lt.mpr h)

theorem filter_nil_of_lt (t : Time) :
    ∀ (M : List Move) (s₀ : Time), ChainOK s₀ M → t < s₀ → M.filter (fun m => decide (m.1 ≤ t)) = []
  | [], _, _, _ => rfl
  | (d, _, a) :: M, s₀, ⟨h₁, h₂, h₃⟩, ht => by
    have hd : ¬ d ≤ t := Nat.not_le.mpr (Nat.lt_of_lt_of_le ht h₁)
    simp only [List.filter_cons, hd, decide_false, Bool.false_eq_true, ite_false]
    exact filter_nil_of_lt t M a h₃ (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ht h₁) h₂)

/-- 区間の検索と、時刻 t までの移動を適用した位置は同じ居場所を与える。 -/
theorem locOf_segsAux (endT t : Time) (ht : t < endT) :
    ∀ (M : List Move) (p : Id) (s₀ : Time), ChainOK s₀ M → s₀ ≤ t →
      locOf ((segsAux endT p s₀ M).find? (covers t)) =
        obs t (foldMoves ⟨p, s₀, none⟩ (M.filter fun m => decide (m.1 ≤ t)))
  | [], p, s₀, _, hs => by
    simp [segsAux, covers, hs, ht, locOf, foldMoves, obs]
  | (d, to, a) :: M, p, s₀, ⟨h₁, h₂, h₃⟩, hs => by
    simp only [segsAux, List.find?_cons]
    by_cases hd : t < d
    · have hcov : covers t (p, s₀, d) = true := by simp [covers, hs, hd]
      have hdt : ¬ d ≤ t := Nat.not_le.mpr hd
      rw [hcov]
      simp only [List.filter_cons, hdt, decide_false, Bool.false_eq_true, ite_false,
        filter_nil_of_lt t M a h₃ (Nat.lt_of_lt_of_le hd h₂)]
      simp [locOf, foldMoves, obs]
    · have hcov : covers t (p, s₀, d) = false := by simp [covers, hd]
      have hdt : d ≤ t := Nat.le_of_not_lt hd
      rw [hcov]
      simp only [List.filter_cons, hdt, decide_true, ite_true]
      by_cases ha : t < a
      · rw [find?_none_of_lt endT t M to a h₃ ha, filter_nil_of_lt t M a h₃ ha]
        simp [locOf, foldMoves, obs, ha]
      · have hat : a ≤ t := Nat.le_of_not_lt ha
        rw [locOf_segsAux endT t ht M to a h₃ hat]
        cases hF : M.filter (fun m => decide (m.1 ≤ t)) with
        | nil => simp [foldMoves, obs, ha]
        | cons m F => rfl

/-! ## 区間 `segments` -/

/-- 死亡時刻で切っても、それより前の時刻の検索結果は変わらない。 -/
theorem locOf_cut (t d : Time) (htd : t < d) (raw : List (Id × Time × Time)) :
    locOf ((raw.map fun (l, a, b) => (l, a, min b d)).find? (covers t)) = locOf (raw.find? (covers t)) := by
  rw [List.find?_map]
  have : (covers t ∘ fun (x : Id × Time × Time) => (x.1, x.2.1, min x.2.2 d)) = covers t := by
    funext x
    simp only [Function.comp, covers]
    by_cases h : t < x.2.2
    · simp [h, Nat.lt_min.mpr ⟨h, htd⟩]
    · have : ¬ t < min x.2.2 d := fun h' => h (Nat.lt_of_lt_of_le h' (Nat.min_le_left _ _))
      simp [h, this]
  simp only [this]
  cases raw.find? (covers t) with
  | none => rfl
  | some x => rfl

theorem find?_filter_of_imp {p q : α → Bool} (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, (l.filter q).find? p = l.find? p
  | [] => rfl
  | x :: xs => by
    simp only [List.filter_cons, List.find?_cons]
    by_cases hq : q x = true
    · simp only [hq, ite_true, List.find?_cons]
      split <;> simp_all [find?_filter_of_imp h xs]
    · have hp : p x = false := by
        cases hpx : p x
        · rfl
        · exact absurd (h x hpx) hq
      simp only [hq, Bool.false_eq_true, ite_false, hp, find?_filter_of_imp h xs]

/-- c の move を (出発, 行き先, 到着) にする(`movesOf` と同じ)。 -/
def mvOf (c : Id) (e : Event) : Option Move :=
  match e.kind with
  | .move c' to arr _ _ => if c' == c then some (e.time, to, arr) else none
  | _ => none

theorem movesOf_eq (s : Scenario) (c : Id) : s.movesOf c = s.sortedEvents.filterMap (mvOf c) := rfl

theorem initState_pos (s : Scenario) (c : Id) :
    (s.initState.pos c).arrive = s.startTime ∧ (s.initState.pos c).via = none := by
  simp only [Scenario.initState]
  split <;> exact ⟨rfl, rfl⟩

/-! ## 状態の位置と移動の列 -/

/-- c の位置への1イベントの効果。 -/
def posUpd (c : Id) (p : Position) (e : Event) : Position :=
  match e.kind with
  | .move c' to arr _ _ => if c' = c then ⟨to, arr, some e.id⟩ else p
  | _ => p

theorem step_pos_eq (S : State) (e : Event) (c : Id) : (step S e).pos c = posUpd c (S.pos c) e := by
  obtain ⟨_, _, k, _⟩ := e
  cases k with
  | move c' to arr m f =>
    simp only [step, posUpd, update]
    by_cases h : c = c' <;> simp [h, eq_comm]
  | die c' => simp only [step, posUpd]; split <;> rfl
  | _ => rfl

theorem runAux_pos (c : Id) : ∀ (L : List Event) (S : State) (P : List Event),
    (runAux S P L).2.pos c = L.foldl (posUpd c) (S.pos c)
  | [], _, _ => rfl
  | e :: L, S, P => by
    simp only [runAux, List.foldl_cons]
    rw [runAux_pos c L, step_pos_eq]

/-- 居場所の読み取りに関係する部分が等しい。 -/
def PosRel (p q : Position) : Prop := p.dest = q.dest ∧ p.arrive = q.arrive ∧ p.via.isSome = q.via.isSome

theorem obs_of_rel {p q : Position} (t : Time) (h : PosRel p q) : obs t p = obs t q := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  simp only [obs, h₁, h₂, h₃]

theorem fold_rel (c : Id) : ∀ (L : List Event) (p q : Position), PosRel p q →
    PosRel (L.foldl (posUpd c) p) (foldMoves q (L.filterMap (mvOf c)))
  | [], _, _, h => h
  | e :: L, p, q, h => by
    obtain ⟨_, _, k, _⟩ := e
    cases k with
    | move c' to arr m f =>
      simp only [List.foldl_cons, List.filterMap_cons, mvOf, posUpd]
      by_cases hc : c' = c
      · simp only [hc, ite_true, beq_self_eq_true]
        exact fold_rel c L _ _ ⟨rfl, rfl, rfl⟩
      · have : (c' == c) = false := by simp [hc]
        simp only [hc, ite_false, this, Bool.false_eq_true]
        exact fold_rel c L _ _ h
    | _ => exact fold_rel c L _ _ h

theorem mvOf_fst {c : Id} {e : Event} {m : Move} (h : mvOf c e = some m) : m.1 = e.time := by
  obtain ⟨_, _, k, _⟩ := e
  cases k <;> simp only [mvOf, reduceCtorEq] at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · cases h

theorem filterMap_filter_mvOf (c : Id) (t : Time) : ∀ L : List Event,
    (L.filter fun e => decide (e.time ≤ t)).filterMap (mvOf c) =
      (L.filterMap (mvOf c)).filter fun m => decide (m.1 ≤ t)
  | [] => rfl
  | e :: L => by
    have ih := filterMap_filter_mvOf c t L
    by_cases ht : e.time ≤ t
    · simp only [List.filter_cons, ht, decide_true, ite_true, List.filterMap_cons]
      cases hm : mvOf c e with
      | none => exact ih
      | some m => simp [List.filter_cons, mvOf_fst hm, ht, ih]
    · simp only [List.filter_cons, ht, decide_false, Bool.false_eq_true, ite_false, List.filterMap_cons]
      cases hm : mvOf c e with
      | none => exact ih
      | some m => simp [List.filter_cons, mvOf_fst hm, ht, ih]

/-! ## 前提と定理 8 -/

/-- c の move についての前提(T001 / R006 / T006)。 -/
def MovesOk (s : Scenario) (c : Id) : Prop :=
  ∀ st ∈ s.trace, ∀ to arr m f, st.ev.kind = .move c to arr m f →
    s.startTime ≤ st.ev.time ∧ st.ev.time ≤ arr ∧ st.pre.inTransit c st.ev.time = false

theorem chain_runAux (c : Id) : ∀ (L : List Event) (S : State) (P : List Event),
    ((S.pos c).via = none → ∀ e ∈ L, ∀ to arr m f, e.kind = .move c to arr m f → (S.pos c).arrive ≤ e.time) →
    (∀ st ∈ (runAux S P L).1, ∀ to arr m f, st.ev.kind = .move c to arr m f →
      st.ev.time ≤ arr ∧ st.pre.inTransit c st.ev.time = false) →
    ChainOK (S.pos c).arrive (L.filterMap (mvOf c))
  | [], _, _, _, _ => trivial
  | e :: L, S, P, h₁, h₂ => by
    have hhead := h₂ ⟨S, e, P⟩ (by simp [runAux])
    have htail : ∀ st ∈ (runAux (step S e) (P ++ [e]) L).1, ∀ to arr m f, st.ev.kind = .move c to arr m f →
        st.ev.time ≤ arr ∧ st.pre.inTransit c st.ev.time = false :=
      fun st hst => h₂ st (by simp [runAux, hst])
    obtain ⟨id, time, k, r⟩ := e
    by_cases hmv : ∃ to arr m f, k = .move c to arr m f
    · obtain ⟨to, arr, m, f, rfl⟩ := hmv
      obtain ⟨hle, htr⟩ := hhead to arr m f rfl
      simp only [List.filterMap_cons, mvOf, beq_self_eq_true, ite_true]
      refine ⟨?_, hle, ?_⟩
      · simp only [State.inTransit, Bool.and_eq_false_iff, Option.isSome_eq_false_iff,
          decide_eq_false_iff_not, Nat.not_lt] at htr
        rcases htr with hv | hv
        · exact h₁ (Option.isNone_iff_eq_none.mp hv) _ (List.mem_cons_self ..) to arr m f rfl
        · exact hv
      · have hpos : (step S ⟨id, time, .move c to arr m f, r⟩).pos c = ⟨to, arr, some id⟩ := by
          rw [step_pos_eq]; simp [posUpd]
        have := chain_runAux c L (step S ⟨id, time, .move c to arr m f, r⟩) (P ++ [_])
          (by rw [hpos]; intro h; cases h) htail
        rwa [hpos] at this
    · have hmv' : mvOf c ⟨id, time, k, r⟩ = none := by
        cases k with
        | move c' to arr m f =>
          have : c' ≠ c := fun h => hmv ⟨to, arr, m, f, by rw [h]⟩
          simp [mvOf, this]
        | _ => rfl
      have hpos : (step S ⟨id, time, k, r⟩).pos c = S.pos c := by
        rw [step_pos_eq]
        cases k with
        | move c' to arr m f =>
          have : c' ≠ c := fun h => hmv ⟨to, arr, m, f, by rw [h]⟩
          simp [posUpd, this]
        | _ => rfl
      simp only [List.filterMap_cons, hmv']
      have := chain_runAux c L (step S ⟨id, time, k, r⟩) (P ++ [_])
        (by rw [hpos]; exact fun hv e he => h₁ hv e (List.mem_cons_of_mem _ he)) htail
      rwa [hpos] at this

theorem exists_step_of_mem (e : Event) (L : List Event) (S : State) (P : List Event) (he : e ∈ L) :
    ∃ st ∈ (runAux S P L).1, st.ev = e := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem he
  obtain ⟨S', h⟩ := mem_runAux_of_eq_append e B A S P
  exact ⟨_, h, rfl⟩

theorem chain_movesOf (s : Scenario) (c : Id) (h : MovesOk s c) : ChainOK s.startTime (s.movesOf c) := by
  have hinit := initState_pos s c
  have := chain_runAux c s.sortedEvents s.initState []
    (fun _ e he to arr m f hk => by
      rw [hinit.1]
      obtain ⟨st, hst, hev⟩ := exists_step_of_mem e s.sortedEvents s.initState [] he
      have := (h st hst to arr m f (by rw [hev]; exact hk)).1
      rwa [hev] at this)
    (fun st hst to arr m f hk => (h st hst to arr m f hk).2)
  rwa [hinit.1] at this

/-- **定理 8 (前半)**: 居場所の区間は時刻順に並び、互いに重ならない。各区間は空でない。 -/
theorem segments_ordered (s : Scenario) (c : Id) (h : MovesOk s c) :
    (s.segments c).Pairwise (fun x y => x.2.2 ≤ y.2.1) ∧ ∀ x ∈ s.segments c, x.2.1 < x.2.2 := by
  have hraw := segsAux_pairwise s.endTime (s.movesOf c) (s.initState.pos c).dest s.startTime
    (chain_movesOf s c h)
  unfold Scenario.segments
  dsimp only
  constructor
  · apply List.Pairwise.filter
    split
    · exact hraw
    · rw [List.pairwise_map]
      exact hraw.imp fun hxy => Nat.le_trans (Nat.min_le_left _ _) hxy
  · intro x hx
    simpa using (List.mem_filter.mp hx).2

/-- 時刻 t までのイベントをすべて(正規順序で)処理した状態。 -/
def Scenario.stateAt (s : Scenario) (t : Time) : State :=
  (runAux s.initState [] (s.sortedEvents.filter fun e => decide (e.time ≤ t))).2

/-- 状態から読む時刻 t での居場所: 移動中なら "transit"、そうでなければ最後の行き先。 -/
def State.locAt (S : State) (c : Id) (t : Time) : String :=
  if S.inTransit c t then "transit" else (S.pos c).dest

theorem whereAlive_eq (s : Scenario) (c : Id) (t : Time) :
    s.whereAlive c t = locOf ((s.segments c).find? (covers t)) := by
  unfold Scenario.whereAlive locOf covers
  rfl

/-- **定理 8 (後半)**: 開始時刻 ≤ t < 終了時刻で死亡時刻より前なら、`whereAt` は
時刻 t までのイベントを処理した状態での居場所と一致する。 -/
theorem whereAt_eq_stateAt (s : Scenario) (c : Id) (t : Time) (h : MovesOk s c)
    (h₁ : s.startTime ≤ t) (h₂ : t < s.endTime) (hd : ∀ d, s.deathTime c = some d → t < d) :
    s.whereAt c t = (s.stateAt t).locAt c t := by
  -- 左辺: 区間の検索
  have hW : s.whereAt c t = s.whereAlive c t := by
    unfold Scenario.whereAt
    split
    · rename_i d hdt
      have := hd d hdt
      rw [ite_of_neg (Nat.not_le.mpr this)]
    · rfl
  have hseg : locOf ((s.segments c).find? (covers t)) =
      locOf ((segsAux s.endTime (s.initState.pos c).dest s.startTime (s.movesOf c)).find? (covers t)) := by
    unfold Scenario.segments
    dsimp only
    rw [find?_filter_of_imp (fun x hx => by
      simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at hx
      simpa using Nat.lt_of_le_of_lt hx.1 hx.2)]
    split
    · rfl
    · rename_i d hdt
      exact locOf_cut t d (hd d hdt) _
  rw [hW, whereAlive_eq, hseg,
    locOf_segsAux s.endTime t h₂ (s.movesOf c) _ s.startTime (chain_movesOf s c h) h₁]
  -- 右辺: 状態の位置
  have hinit := initState_pos s c
  have hrel := fold_rel c (s.sortedEvents.filter fun e => decide (e.time ≤ t)) (s.initState.pos c)
    ⟨(s.initState.pos c).dest, s.startTime, none⟩ ⟨rfl, hinit.1, by simp [hinit.2]⟩
  rw [filterMap_filter_mvOf, ← movesOf_eq] at hrel
  have hpos : (s.stateAt t).pos c = (s.sortedEvents.filter fun e => decide (e.time ≤ t)).foldl (posUpd c)
      (s.initState.pos c) := runAux_pos c _ _ _
  have : (s.stateAt t).locAt c t = obs t ((s.stateAt t).pos c) := by
    unfold State.locAt State.inTransit obs; rfl
  rw [this, hpos, obs_of_rel t hrel]

/-! ## `Valid` から前提を導く -/

theorem mem_of_mem_runAux : ∀ (L : List Event) (S : State) (P : List Event) (st : Step),
    st ∈ (runAux S P L).1 → st.ev ∈ L
  | [], _, _, _, h => by simp [runAux] at h
  | e :: L, S, P, st, h => by
    simp only [runAux, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_mem_runAux L _ _ st h)

theorem arrive_ge_of_checkR (s : Scenario) (hR : checkR s = []) (e : Event) (he : e ∈ s.events)
    (c to : Id) (arr : Time) (m : String) (f : Bool) (hk : e.kind = .move c to arr m f) : e.time ≤ arr := by
  have h6 : checkR006 s = [] := by
    rw [checkR_eq_nil_iff] at hR
    simp only [rIssues, List.append_eq_nil_iff] at hR
    exact hR.1.1.1.1.1.1.1.2
  simp only [checkR006, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h6
  have := h6 e he
  simp only [eventShapeErrors, hk, List.append_eq_nil_iff] at this
  refine Nat.le_of_not_lt fun hlt => ?_
  simp [hlt] at this

theorem movesOk_of_valid (s : Scenario) (h : Valid s) (c : Id) : MovesOk s c := by
  intro st hst to arr m f hk
  have hv := h.2.1 st hst
  have hmem : st.ev ∈ s.events := List.mem_mergeSort.mp (mem_of_mem_runAux _ _ _ st hst)
  refine ⟨hv.1.1, arrive_ge_of_checkR s h.1 st.ev hmem c to arr m f hk, ?_⟩
  exact (hv.2.2.1 c (by rw [hk]; simp [EventKind.participants])).2.1

/-- **定理 8**(`Valid` から): 正しいシナリオでは、どのキャラクターの区間も重ならず、
`whereAt` は時刻 t までの状態と一致する。 -/
theorem segments_consistent (s : Scenario) (h : Valid s) (c : Id) :
    ((s.segments c).Pairwise (fun x y => x.2.2 ≤ y.2.1) ∧ ∀ x ∈ s.segments c, x.2.1 < x.2.2) ∧
    ∀ t, s.startTime ≤ t → t < s.endTime → (∀ d, s.deathTime c = some d → t < d) →
      s.whereAt c t = (s.stateAt t).locAt c t :=
  ⟨segments_ordered s c (movesOk_of_valid s h c),
    fun t h₁ h₂ hd => whereAt_eq_stateAt s c t (movesOk_of_valid s h c) h₁ h₂ hd⟩

end MurderMystery
