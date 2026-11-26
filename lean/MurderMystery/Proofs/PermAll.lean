import MurderMystery.Proofs.Travel
import MurderMystery.Proofs.Rules

/-!
# 定理 3 (後半の一般化): トップレベルのすべての配列の並べ替えに対する不変性

配列を1つずつ並べ替えたときに出力が変わらないことを示し、それをつなげる。
各配列について、

1. R001 の検出結果の集合が変わらない
2. R001 の違反がなければ(ID が重複しないので)、残りの R 群の検出結果の集合が変わらない
3. R 群の違反がなければ、イベント・終了状態・G 群の検出結果の集合が変わらない

を示す。
-/
namespace MurderMystery

/-! ## 共通の枠組み -/

theorem check_eq_of_parts (s s' : Scenario)
    (h1 : ∀ x, x ∈ checkR001 s' ↔ x ∈ checkR001 s)
    (h2 : checkR001 s = [] → ∀ x, x ∈ rIssues s' ↔ x ∈ rIssues s)
    (h3 : rIssues s = [] → ∀ d, d ∈ checkEvents s' ++ checkPost s' ++ checkG s' ↔
      d ∈ checkEvents s ++ checkPost s ++ checkG s) :
    check s' = check s := by
  apply check_eq_of_mem_iff
  have hR1 : (checkR001 s').isEmpty = (checkR001 s).isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem, h1]
  have hR : ∀ d, d ∈ checkR s' ↔ d ∈ checkR s := by
    intro d
    unfold checkR
    rw [hR1]
    split
    · rename_i he
      have : checkR001 s = [] := by simpa using he
      simp only [List.mem_map, h2 this]
    · simp only [List.mem_map, h1]
  have hRe : checkR s' = [] ↔ checkR s = [] := by
    simp only [List.eq_nil_iff_forall_not_mem, hR]
  intro d
  unfold checkRaw
  dsimp only
  by_cases h : checkR s = []
  · have h' := hRe.mpr h
    rw [h, h', List.isEmpty_nil]
    simp only [ite_true]
    exact h3 ((checkR_eq_nil_iff s).mp h) d
  · have h' : ¬ checkR s' = [] := fun e => h (hRe.mp e)
    have e1 : (checkR s).isEmpty = false := by simpa using h
    have e2 : (checkR s').isEmpty = false := by simpa using h'
    rw [e1, e2]
    simp only [Bool.false_eq_true, ite_false]
    exact hR d

/-- R001 の違反がなければ、各種類の ID は重複しない。 -/
theorem nodup_of_R001 (s : Scenario) (h : checkR001 s = []) :
    s.characterIds.Nodup ∧ s.areaIds.Nodup ∧ s.locationIds.Nodup ∧ s.itemIds.Nodup ∧ s.factIds.Nodup ∧
    (s.clues.map (·.id)).Nodup ∧ s.eventIds.Nodup ∧ (s.assertions.map (·.id)).Nodup ∧ s.variableIds.Nodup ∧
    (s.endings.map (·.id)).Nodup ∧ (s.handouts.map (·.character)).Nodup ∧ (s.board.map (·.location)).Nodup := by
  simp only [checkR001, List.flatMap_eq_nil_iff, List.map_eq_nil_iff] at h
  have k : ∀ k ids, (k, ids) ∈ [("character", s.characterIds), ("area", s.areaIds), ("location", s.locationIds),
      ("item", s.itemIds), ("fact", s.factIds), ("clue", s.clues.map (·.id)), ("event", s.eventIds),
      ("assertion", s.assertions.map (·.id)), ("variable", s.variableIds), ("ending", s.endings.map (·.id)),
      ("handout", s.handouts.map (·.character)), ("board", s.board.map (·.location))] → ids.Nodup :=
    fun k ids hm => nodup_of_duplicates_nil _ (h (k, ids) hm)
  exact ⟨k "character" _ (by simp), k "area" _ (by simp), k "location" _ (by simp), k "item" _ (by simp),
    k "fact" _ (by simp), k "clue" _ (by simp), k "event" _ (by simp), k "assertion" _ (by simp),
    k "variable" _ (by simp), k "ending" _ (by simp), k "handout" _ (by simp), k "board" _ (by simp)⟩

theorem rIssues_nil_parts (s : Scenario) (h : rIssues s = []) :
    checkR001 s = [] ∧ checkR002 s = [] ∧ checkR003 s = [] ∧ checkR005 s = [] := by
  simp only [rIssues, List.append_eq_nil_iff] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.2⟩

/-- キーが重複しない列の、キーによる整列は並べ替えで変わらない。 -/
theorem mergeSort_key_perm {f : α → String} {l l' : List α} (hp : l.Perm l') (hn : (l.map f).Nodup) :
    l.mergeSort (fun a b => decide (f a ≤ f b)) = l'.mergeSort (fun a b => decide (f a ≤ f b)) := by
  have trans : ∀ a b c : α, decide (f a ≤ f b) = true → decide (f b ≤ f c) = true → decide (f a ≤ f c) = true := by
    intro a b c h₁ h₂; simp only [decide_eq_true_eq] at *; exact Std.le_trans h₁ h₂
  have total : ∀ a b : α, (decide (f a ≤ f b) || decide (f b ≤ f a)) = true := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Std.le_total
  apply eq_of_perm_of_pairwise _ (List.pairwise_mergeSort trans total l) (List.pairwise_mergeSort trans total l')
  · intro a ha b hb hab hba
    rw [List.mem_mergeSort] at ha hb
    simp only [decide_eq_true_eq] at hab hba
    exact eq_of_mem_of_nodup_map hn ha hb (Std.le_antisymm hab hba)
  · exact (List.mergeSort_perm l _).trans (hp.trans (List.mergeSort_perm l' _).symm)

theorem contains_perm [BEq α] {l l' : List α} (hp : l.Perm l') (x : α) : l.contains x = l'.contains x := by
  simp only [List.contains_eq_any_beq]; exact any_perm hp _

/-- ID が重複しない列での ID による検索は、並べ替えで変わらない。 -/
theorem find?_id_perm {f : α → String} {l l' : List α} (hp : l.Perm l') (hn : (l.map f).Nodup) (x : String) :
    l.find? (fun a => f a == x) = l'.find? (fun a => f a == x) :=
  find?_perm hp fun a ha b hb hpa hpb => by
    simp only [beq_iff_eq] at hpa hpb
    exact eq_of_mem_of_nodup_map hn ha hb (hpa.trans hpb.symm)

theorem coverR_congr {P P' : List (List Clue)} {N N' : List Id}
    (hc : ∀ i c, c ∈ P'.getD i [] ↔ c ∈ P.getD i []) (hn : ∀ f, f ∈ N' ↔ f ∈ N) (caps : List Nat) (k : Nat) :
    coverR P' caps N' k = coverR P caps N k := by
  apply Bool.eq_iff_iff.mpr
  rw [coverR_iff, coverR_iff]
  simp only [hc, hn]

theorem mem_pools_congr (s s' : Scenario) (hc : ∀ c, c ∈ s'.clues ↔ c ∈ s.clues) (rs : List Round) (i : Nat)
    (c : Clue) : c ∈ (s'.pools rs).getD i [] ↔ c ∈ (s.pools rs).getD i [] := by
  simp only [Scenario.pools, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rs[i]? with
  | none => simp
  | some r =>
    simp only [Option.map_some, Option.getD_some, Scenario.pool]
    cases r.clues <;> simp [List.mem_filter, hc]

theorem issuesK010_congr (s s' : Scenario) (he : s'.exploration = s.exploration)
    (hd : s'.playerCount = s.playerCount) (hc : ∀ c, c ∈ s'.clues ↔ c ∈ s.clues)
    (hn : ∀ f, f ∈ s'.clueOnly ↔ f ∈ s.clueOnly) : issuesK010 s' = issuesK010 s := by
  unfold issuesK010
  rw [he]
  cases s.exploration with
  | none => rfl
  | some rs =>
    have hcaps : s'.caps rs = s.caps rs := by simp only [Scenario.caps, hd]
    have hdr : s'.draws rs = s.draws rs := by simp only [Scenario.draws, hcaps]
    simp only [hcaps, hdr, coverR_congr (mem_pools_congr s s' hc rs) hn]

theorem warningsK009_congr (s s' : Scenario) (he : s'.exploration = s.exploration)
    (hd : s'.playerCount = s.playerCount) (hl : s'.clues.length = s.clues.length) :
    warningsK009 s' = warningsK009 s := by
  unfold warningsK009
  rw [he]
  cases s.exploration with
  | none => rfl
  | some rs =>
    have h1 : s'.draws rs = s.draws rs := by simp only [Scenario.draws, Scenario.caps, hd]
    dsimp only
    rw [h1, hl]

theorem warningsK011_congr (s s' : Scenario) (he : s'.exploration = s.exploration)
    (hc : ∀ c, c ∈ s'.clues ↔ c ∈ s.clues) (x : Issue) : x ∈ warningsK011 s' ↔ x ∈ warningsK011 s := by
  unfold warningsK011
  rw [he]
  cases s.exploration with
  | none => exact Iff.rfl
  | some rs => simp only [List.mem_filterMap, hc]

theorem checkR002_of (s s' : Scenario) (h : ∀ r, r ∈ allRefs s' ↔ r ∈ allRefs s)
    (hk : ∀ k i, (s'.idsOfKind k).contains i = (s.idsOfKind k).contains i) :
    ∀ x, x ∈ checkR002 s' ↔ x ∈ checkR002 s := by
  intro x
  simp only [checkR002, List.mem_map, mem_dedup, List.mem_filter, h, hk]

/-! ## solutionFacts -/

theorem check_perm_solutionFacts (s : Scenario) (l : List Id) (hp : s.solutionFacts.Perm l) :
    check { s with solutionFacts := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with solutionFacts := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    simp only [rIssues, List.mem_append, h2]
    exact Iff.rfl
  · intro _ d
    have hK10 : issuesK010 { s with solutionFacts := l } = issuesK010 s :=
      issuesK010_congr s _ rfl rfl (fun _ => Iff.rfl) (fun f => by
        simp only [Scenario.clueOnly, List.mem_filter, hp.mem_iff]; exact Iff.rfl)
    have hP : ∀ x, x ∈ postErrors { s with solutionFacts := l } ↔ x ∈ postErrors s := by
      intro x
      simp only [postErrors, issuesK003, issuesK007, List.mem_append, List.mem_filterMap, hp.mem_iff, hK10]
      exact Iff.rfl
    simp only [checkPost, List.mem_append, List.mem_map, hP]
    exact Iff.rfl

/-! ## assertions -/

theorem check_perm_assertions (s : Scenario) (l : List Assertion) (hp : s.assertions.Perm l) :
    check { s with assertions := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with assertions := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with assertions := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have h13 : x ∈ checkR013 { s with assertions := l } ↔ x ∈ checkR013 s := by
      simp only [checkR013, List.mem_filterMap, hp.mem_iff]
    simp only [rIssues, List.mem_append, h1, h2, h13]
    exact Iff.rfl
  · intro _ d
    have hP : ∀ x, x ∈ postErrors { s with assertions := l } ↔ x ∈ postErrors s := by
      intro x
      simp only [postErrors, issuesA, List.mem_append, List.mem_flatMap, hp.mem_iff]
      exact Iff.rfl
    simp only [checkPost, List.mem_append, List.mem_map, hP]
    exact Iff.rfl

/-! ## board -/

theorem check_perm_board (s : Scenario) (l : List Board) (hp : s.board.Perm l) :
    check { s with board := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with board := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.location))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with board := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    simp only [rIssues, List.mem_append, h1, h2]
    exact Iff.rfl
  · intro _ d
    have hP : ∀ x, x ∈ postErrors { s with board := l } ↔ x ∈ postErrors s := by
      intro x
      simp only [postErrors, issuesH, List.mem_append, List.mem_flatMap, hp.mem_iff]
      exact Iff.rfl
    have hW : ∀ x, x ∈ postWarnings { s with board := l } ↔ x ∈ postWarnings s := by
      intro x
      simp only [postWarnings, warningsH, List.mem_append, List.mem_flatMap, hp.mem_iff]
      exact Iff.rfl
    simp only [checkPost, List.mem_append, List.mem_map, hP, hW]
    exact Iff.rfl

/-! ## clues -/

theorem check_perm_clues (s : Scenario) (l : List Clue) (hp : s.clues.Perm l) :
    check { s with clues := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with clues := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with clues := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, (hp.map (·.id)).mem_iff])
    have h7 : x ∈ checkR007 { s with clues := l } ↔ x ∈ checkR007 s := by
      simp only [checkR007, List.mem_filterMap, hp.mem_iff]
    simp only [rIssues, List.mem_append, h1, h2, h7]
    exact Iff.rfl
  · intro _ d
    have hobt : ∀ f, Scenario.obtainable { s with clues := l } f = s.obtainable f := by
      intro f; simp only [Scenario.obtainable, any_perm hp.symm]; rfl
    have hobtF : Scenario.obtainable { s with clues := l } = s.obtainable := funext hobt
    have hK10 : issuesK010 { s with clues := l } = issuesK010 s :=
      issuesK010_congr s _ rfl rfl (fun _ => hp.mem_iff.symm) (fun f => by
        simp only [Scenario.clueOnly, List.mem_filter, any_perm hp.symm]; exact Iff.rfl)
    have hW9 : warningsK009 { s with clues := l } = warningsK009 s :=
      warningsK009_congr s _ rfl rfl hp.length_eq.symm
    have hP : ∀ x, x ∈ postErrors { s with clues := l } ↔ x ∈ postErrors s := by
      intro x
      simp only [postErrors, issuesK003, issuesK004K005, issuesK006, List.mem_append, List.mem_flatMap,
        List.mem_filterMap, hp.mem_iff, hobt, hobtF, hK10]
      exact Iff.rfl
    have hd : Scenario.derivedConstraints { s with clues := l } = s.derivedConstraints := by
      simp only [Scenario.derivedConstraints, Scenario.itemConstraints, Scenario.knowledgeConstraints, Scenario.conditionConstraints, Scenario.tagConstraints, Scenario.avail,
        Scenario.concealConstraints, Scenario.exposed, hobtF]; try rfl
    have hsat : Scenario.satisfies { s with clues := l } = s.satisfies := by
      funext v; unfold Scenario.satisfies Scenario.effectiveConstraints; rw [hd]; rfl
    have hctx : Scenario.gctx { s with clues := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    have hG : checkG { s with clues := l } = checkG s := by
      unfold checkG; rw [hctx]; rfl
    have hW : ∀ x, x ∈ postWarnings { s with clues := l } ↔ x ∈ postWarnings s := by
      intro x
      unfold postWarnings; rw [hW9]
      simp only [List.mem_append, warningsK011_congr s { s with clues := l } rfl (fun _ => hp.mem_iff.symm) x]
      exact Iff.rfl
    simp only [checkPost, List.mem_append, List.mem_map, hP, hG, hW]
    exact Iff.rfl

/-! ## handouts -/

theorem check_perm_handouts (s : Scenario) (l : List Handout) (hp : s.handouts.Perm l) :
    check { s with handouts := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with handouts := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.character))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with handouts := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    simp only [rIssues, List.mem_append, h1, h2]
    exact Iff.rfl
  · intro _ d
    have hheld : ∀ f, Scenario.held { s with handouts := l } f = s.held f := by
      intro f; simp only [Scenario.held, any_perm hp.symm]; rfl
    have hP : ∀ x, x ∈ postErrors { s with handouts := l } ↔ x ∈ postErrors s := by
      intro x
      simp only [postErrors, issuesK006, issuesH, List.mem_append, List.mem_flatMap, List.mem_filterMap,
        hp.mem_iff, hheld]
      exact Iff.rfl
    have hW : ∀ x, x ∈ postWarnings { s with handouts := l } ↔ x ∈ postWarnings s := by
      intro x
      simp only [postWarnings, warningsH, List.mem_append, List.mem_flatMap, hp.mem_iff]
      exact Iff.rfl
    simp only [checkPost, List.mem_append, List.mem_map, hP, hW]
    exact Iff.rfl

/-! ## characters -/

theorem check_perm_characters (s : Scenario) (l : List Character) (hp : s.characters.Perm l) :
    check { s with characters := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with characters := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with characters := l }
      (fun r => Iff.rfl)
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        simp only [Scenario.characterIds]; exact contains_perm (hp.map _).symm i)
    have h3 : x ∈ checkR003 { s with characters := l } ↔ x ∈ checkR003 s := by
      simp only [checkR003, List.mem_filterMap, hp.mem_iff]
    simp only [rIssues, List.mem_append, h1, h2, h3]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).1
    have hobt : ∀ f, Scenario.obtainable { s with characters := l } f = s.obtainable f := by
      intro f; simp only [Scenario.obtainable, any_perm hp.symm]; rfl
    have hobtF : Scenario.obtainable { s with characters := l } = s.obtainable := funext hobt
    have hheld : ∀ f, Scenario.held { s with characters := l } f = s.held f := by
      intro f; simp only [Scenario.held, any_perm hp.symm]; rfl
    have hsort : sortedIds (Scenario.characterIds { s with characters := l }) = sortedIds s.characterIds := by
      unfold sortedIds Scenario.characterIds
      have hn' : ((s.characters.map (fun c : Character => c.id)).map (fun x => x)).Nodup := by
        rw [List.map_id']; exact hn
      exact (mergeSort_key_perm (f := fun x => x) (hp.map (fun c : Character => c.id)) hn').symm
    have hpc : Scenario.playerCount { s with characters := l } = s.playerCount := by
      unfold Scenario.playerCount; exact (hp.filter _).length_eq.symm
    have hK10 : issuesK010 { s with characters := l } = issuesK010 s :=
      issuesK010_congr s _ rfl hpc (fun _ => Iff.rfl) (fun f => by
        simp only [Scenario.clueOnly, List.mem_filter, any_perm hp.symm]; exact Iff.rfl)
    have hW9 : warningsK009 { s with characters := l } = warningsK009 s :=
      warningsK009_congr s _ rfl hpc rfl
    have hexp : ∀ o f, Scenario.exposed { s with characters := l } o f = s.exposed o f := by
      intro o f; simp only [Scenario.exposed, any_perm hp.symm]; rfl
    have hP : ∀ x, x ∈ postErrors { s with characters := l } ↔ x ∈ postErrors s := by
      intro x
      simp only [postErrors, issuesK003, issuesK006, List.mem_append, List.mem_filterMap, hobt, hobtF, hheld, hK10]
      exact Iff.rfl
    have hW : postWarnings { s with characters := l } = postWarnings s := by
      simp only [postWarnings, warningsT009, hsort, hW9]
      try rfl
    have hG8 : ∀ x, x ∈ checkG008 { s with characters := l } ↔ x ∈ checkG008 s := by
      intro x; simp only [checkG008, List.mem_filterMap, hp.mem_iff]
    have hd : Scenario.derivedConstraints { s with characters := l } = s.derivedConstraints := by
      simp only [Scenario.derivedConstraints, Scenario.itemConstraints, Scenario.knowledgeConstraints, Scenario.conditionConstraints, Scenario.tagConstraints, Scenario.avail,
        Scenario.concealConstraints, hexp, hobtF]; try rfl
    have hsat : Scenario.satisfies { s with characters := l } = s.satisfies := by
      funext v; unfold Scenario.satisfies Scenario.effectiveConstraints; rw [hd]; rfl
    have hctx : Scenario.gctx { s with characters := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    have hG : ∀ x, x ∈ checkG { s with characters := l } ↔ x ∈ checkG s := by
      intro x
      have e : checkG { s with characters := l } =
          (if s.gCount > gLimit then [err "G007" [toString s.gCount]]
            else if s.gctx.pats.isEmpty then [err "G005" []] else checkGPatterns { s with characters := l } s.gctx)
          ++ checkG008 { s with characters := l } := by
        unfold checkG; rw [hctx]; rfl
      rw [e]; simp only [checkG, List.mem_append, hG8]; exact Iff.rfl
    simp only [checkPost, List.mem_append, List.mem_map, hP, hW, hG]
    exact Iff.rfl

/-! ## 移動時間・知覚の表 -/

theorem checkEdges_perm (tbl : String) {es es' : List Edge} (hp : es.Perm es') :
    ∀ x, x ∈ checkEdges tbl es' ↔ x ∈ checkEdges tbl es := by
  intro x
  have hd := mem_duplicates_perm ((hp.filter (fun e => e.src != e.dst)).flatMap_right
    (fun e => if e.bidirectional then [(e.src, e.dst), (e.dst, e.src)] else [(e.src, e.dst)]))
  simp only [checkEdges, List.mem_append, List.mem_map, List.mem_filter, hp.mem_iff, hd]

theorem stepIssues_of (s s' : Scenario) (hs : s'.startTime = s.startTime) (he : s'.endTime = s.endTime)
    (ht : ∀ a b, s'.travelTime a b = s.travelTime a b) (hpc : ∀ a b, s'.perceives a b = s.perceives a b) :
    ∀ st, stepIssues s' st = stepIssues s st := by
  intro st
  simp only [stepIssues, issuesT001, issuesMove, issuesPlace, hs, he, ht, hpc]

theorem checkEvents_of (s s' : Scenario) (htr : s'.trace = s.trace) (hst : ∀ st, stepIssues s' st = stepIssues s st) :
    checkEvents s' = checkEvents s := by
  unfold checkEvents; rw [htr]; simp only [hst]

theorem check_perm_travel (s : Scenario) (l : List Edge) (hp : s.travel.Perm l) :
    check { s with travel := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with travel := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have h5 : x ∈ checkR005 { s with travel := l } ↔ x ∈ checkR005 s := by
      simp only [checkR005, List.mem_append, checkEdges_perm "travel" hp]
    simp only [rIssues, List.mem_append, h2, h5]
    exact Iff.rfl
  · intro hR d
    have h5 := (rIssues_nil_parts s hR).2.2.2
    simp only [checkR005, List.append_eq_nil_iff] at h5
    have hedge : ∀ a b, edgeLookup l a b = edgeLookup s.travel a b :=
      fun a b => (edgeLookup_perm "travel" h5.1.1 hp a b).symm
    have hE := checkEvents_of s { s with travel := l } rfl
      (stepIssues_of s _ rfl rfl (fun a b => by simp only [Scenario.travelTime, hedge]; try rfl) (fun a b => rfl))
    simp only [List.mem_append, hE]
    exact Iff.rfl

theorem check_perm_areaTravel (s : Scenario) (l : List Edge) (hp : s.areaTravel.Perm l) :
    check { s with areaTravel := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with areaTravel := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have h5 : x ∈ checkR005 { s with areaTravel := l } ↔ x ∈ checkR005 s := by
      simp only [checkR005, List.mem_append, checkEdges_perm "area_travel" hp]
    simp only [rIssues, List.mem_append, h2, h5]
    exact Iff.rfl
  · intro hR d
    have h5 := (rIssues_nil_parts s hR).2.2.2
    simp only [checkR005, List.append_eq_nil_iff] at h5
    have hedge : ∀ a b, edgeLookup l a b = edgeLookup s.areaTravel a b :=
      fun a b => (edgeLookup_perm "area_travel" h5.1.2 hp a b).symm
    have hE := checkEvents_of s { s with areaTravel := l } rfl
      (stepIssues_of s _ rfl rfl (fun a b => by simp only [Scenario.travelTime, hedge]; try rfl) (fun a b => rfl))
    simp only [List.mem_append, hE]
    exact Iff.rfl

theorem check_perm_perception (s : Scenario) (l : List Edge) (hp : s.perception.Perm l) :
    check { s with perception := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with perception := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have h5 : x ∈ checkR005 { s with perception := l } ↔ x ∈ checkR005 s := by
      simp only [checkR005, List.mem_append, checkEdges_perm "perception" hp]
    simp only [rIssues, List.mem_append, h2, h5]
    exact Iff.rfl
  · intro hR d
    have h5 := (rIssues_nil_parts s hR).2.2.2
    simp only [checkR005, List.append_eq_nil_iff] at h5
    have hedge : ∀ a b, edgeLookup l a b = edgeLookup s.perception a b :=
      fun a b => (edgeLookup_perm "perception" h5.2 hp a b).symm
    have hE := checkEvents_of s { s with perception := l } rfl
      (stepIssues_of s _ rfl rfl (fun a b => rfl) (fun a b => by simp only [Scenario.perceives, hedge]))
    simp only [List.mem_append, hE]
    exact Iff.rfl

/-! ## areas / locations -/

theorem check_perm_areas (s : Scenario) (l : List Area) (hp : s.areas.Perm l) :
    check { s with areas := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with areas := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with areas := l }
      (fun r => Iff.rfl)
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        simp only [Scenario.areaIds]; exact contains_perm (hp.map _).symm i)
    simp only [rIssues, List.mem_append, h1, h2]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.1
    have hfind : ∀ x, l.find? (fun a => a.id == x) = s.areas.find? (fun a => a.id == x) :=
      fun x => (find?_id_perm (f := fun a : Area => a.id) hp hn x).symm
    have hE := checkEvents_of s { s with areas := l } rfl
      (stepIssues_of s _ rfl rfl (fun a b => by simp only [Scenario.travelTime, hfind]; try rfl) (fun a b => rfl))
    simp only [List.mem_append, hE]
    exact Iff.rfl

theorem check_perm_locations (s : Scenario) (l : List Location) (hp : s.locations.Perm l) :
    check { s with locations := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with locations := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with locations := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        simp only [Scenario.locationIds]; exact contains_perm (hp.map _).symm i)
    simp only [rIssues, List.mem_append, h1, h2]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.2.1
    have hfind : ∀ x, l.find? (fun a => a.id == x) = s.locations.find? (fun a => a.id == x) :=
      fun x => (find?_id_perm (f := fun a : Location => a.id) hp hn x).symm
    have harea : ∀ x, Scenario.areaOf { s with locations := l } x = s.areaOf x := by
      intro x; simp only [Scenario.areaOf, hfind]
    have hpub : ∀ x, Scenario.isPublic { s with locations := l } x = s.isPublic x := by
      intro x; simp only [Scenario.isPublic, hfind]
    have hE := checkEvents_of s { s with locations := l } rfl
      (stepIssues_of s _ rfl rfl (fun a b => by simp only [Scenario.travelTime, harea]; try rfl) (fun a b => rfl))
    have hP : checkPost { s with locations := l } = checkPost s := by
      simp only [checkPost, postWarnings, warningsT009, hpub]; try rfl
    simp only [List.mem_append, hE, hP]
    exact Iff.rfl

/-! ## 初期状態に関わる配列 -/

theorem refs_ok_of_R002 (s : Scenario) (h : checkR002 s = []) :
    ∀ r ∈ allRefs s, (s.idsOfKind r.kind).contains r.id = true := by
  intro r hr
  simp only [checkR002, List.map_eq_nil_iff] at h
  refine Classical.byContradiction fun hc => ?_
  have : r ∈ dedup ((allRefs s).filter fun r => !(s.idsOfKind r.kind).contains r.id) := by
    rw [mem_dedup, List.mem_filter]
    refine ⟨hr, ?_⟩
    cases h' : (s.idsOfKind r.kind).contains r.id
    · rfl
    · exact absurd h' hc
  rw [h] at this; cases this

theorem eq_of_length_one {l : List α} (h : l.length = 1) {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h with
  | [x], _ => simp at ha hb; rw [ha, hb]

/-- R 群の違反がなければ、各キャラクターの初期配置は1つ。 -/
theorem placement_unique (s : Scenario) (hR : rIssues s = []) :
    ∀ p ∈ s.placements, ∀ q ∈ s.placements, p.character = q.character → p = q := by
  obtain ⟨_, h2, h3, _⟩ := rIssues_nil_parts s hR
  intro p hp q hq hpq
  have href : (⟨s!"placement:{p.character}", "character", p.character, none⟩ : Ref) ∈ allRefs s := by
    unfold allRefs baseRefs
    dsimp only
    simp only [List.mem_append]
    iterate 14 apply Or.inl
    apply Or.inr
    exact List.mem_flatMap.mpr ⟨p, hp, by simp⟩
  have hc := refs_ok_of_R002 s h2 _ href
  simp only [Scenario.idsOfKind, Scenario.characterIds, List.contains_iff_mem, List.mem_map] at hc
  obtain ⟨ch, hch, hid⟩ := hc
  simp only [checkR003, List.filterMap_eq_nil_iff] at h3
  have hlen := h3 ch hch
  have h1 : (s.placements.filter (·.character == ch.id)).length = 1 := by
    refine Classical.byContradiction fun hne => ?_
    simp [hne] at hlen
  exact eq_of_length_one h1 (by simp [hp, hid]) (by simp [hq, hid, ← hpq])

theorem check_perm_initialKnowledge (s : Scenario) (l : List (Id × Id)) (hp : s.initialKnowledge.Perm l) :
    check { s with initialKnowledge := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with initialKnowledge := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    simp only [rIssues, List.mem_append, h2]
    exact Iff.rfl
  · intro hR d
    have hinit : Scenario.initState { s with initialKnowledge := l } = s.initState := by
      simp only [Scenario.initState, contains_perm hp.symm]
    have hrun : Scenario.run { s with initialKnowledge := l } = s.run := by
      unfold Scenario.run; rw [hinit]; rfl
    have htrace : Scenario.trace { s with initialKnowledge := l } = s.trace := by unfold Scenario.trace; rw [hrun]
    have hfinal : Scenario.final { s with initialKnowledge := l } = s.final := by unfold Scenario.final; rw [hrun]
    have hdeath : ∀ c, Scenario.deathTime { s with initialKnowledge := l } c = s.deathTime c := by
      intro c; unfold Scenario.deathTime; rw [hfinal]; try rfl
    have hseg : ∀ c, Scenario.segments { s with initialKnowledge := l } c = s.segments c := by
      intro c; unfold Scenario.segments; rw [hinit, hdeath]; try rfl
    have hwhere : ∀ c t, Scenario.whereAt { s with initialKnowledge := l } c t = s.whereAt c t := by
      intro c t; unfold Scenario.whereAt Scenario.whereAlive; rw [hdeath]; simp only [hseg]
    have hobt : ∀ f, Scenario.obtainable { s with initialKnowledge := l } f = s.obtainable f := by
      intro f; unfold Scenario.obtainable; rw [hfinal]
    have hobtF : Scenario.obtainable { s with initialKnowledge := l } = s.obtainable := funext hobt
    have hheld : ∀ f, Scenario.held { s with initialKnowledge := l } f = s.held f := by
      intro f; unfold Scenario.held; rw [hfinal]
    have hE : checkEvents { s with initialKnowledge := l } = checkEvents s := by
      unfold checkEvents; rw [htrace]; rfl
    have hD : Scenario.derivedConstraints { s with initialKnowledge := l } = s.derivedConstraints := by
      simp only [Scenario.derivedConstraints, Scenario.itemConstraints, Scenario.knowledgeConstraints, Scenario.conditionConstraints, Scenario.tagConstraints, Scenario.avail,
        Scenario.concealConstraints, Scenario.exposed, hfinal, hobtF]; try rfl
    have hsat : Scenario.satisfies { s with initialKnowledge := l } = s.satisfies := by
      funext v; unfold Scenario.satisfies Scenario.effectiveConstraints; rw [hD]; rfl
    have hctx : Scenario.gctx { s with initialKnowledge := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    have hG : checkG { s with initialKnowledge := l } = checkG s := by
      unfold checkG; rw [hctx]; rfl
    have hP : ∀ x, x ∈ checkPost { s with initialKnowledge := l } ↔ x ∈ checkPost s := by
      intro x
      simp only [checkPost, postErrors, postWarnings, warningsT009, issuesK003, issuesK004K005, issuesK006,
        issuesK007, issuesK008, issuesH, warningsH, issuesA, checkT012, issuesK010, warningsK009,
      Scenario.clueOnly, Scenario.draws, hfinal, hseg, hwhere, hobt, hobtF, hheld,
        List.mem_append, List.mem_map]
      exact Iff.rfl
    simp only [List.mem_append, hE, hG, hP]

theorem check_perm_placements (s : Scenario) (l : List Placement) (hp : s.placements.Perm l) :
    check { s with placements := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with placements := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have h3 : x ∈ checkR003 { s with placements := l } ↔ x ∈ checkR003 s := by
      simp only [checkR003, List.mem_filterMap, (hp.filter _).length_eq]
    simp only [rIssues, List.mem_append, h2, h3]
    exact Iff.rfl
  · intro hR d
    have huniq := placement_unique s hR
    have hfind : ∀ c, l.find? (fun p => p.character == c) = s.placements.find? (fun p => p.character == c) :=
      fun c => (find?_perm hp fun a ha b hb hpa hpb => huniq a ha b hb (by
        simp only [beq_iff_eq] at hpa hpb; rw [hpa, hpb])).symm
    have hinit : Scenario.initState { s with placements := l } = s.initState := by
      simp only [Scenario.initState, hfind]
    have hrun : Scenario.run { s with placements := l } = s.run := by
      unfold Scenario.run; rw [hinit]; rfl
    have htrace : Scenario.trace { s with placements := l } = s.trace := by unfold Scenario.trace; rw [hrun]
    have hfinal : Scenario.final { s with placements := l } = s.final := by unfold Scenario.final; rw [hrun]
    have hdeath : ∀ c, Scenario.deathTime { s with placements := l } c = s.deathTime c := by
      intro c; unfold Scenario.deathTime; rw [hfinal]; try rfl
    have hseg : ∀ c, Scenario.segments { s with placements := l } c = s.segments c := by
      intro c; unfold Scenario.segments; rw [hinit, hdeath]; try rfl
    have hwhere : ∀ c t, Scenario.whereAt { s with placements := l } c t = s.whereAt c t := by
      intro c t; unfold Scenario.whereAt Scenario.whereAlive; rw [hdeath]; simp only [hseg]
    have hobt : ∀ f, Scenario.obtainable { s with placements := l } f = s.obtainable f := by
      intro f; unfold Scenario.obtainable; rw [hfinal]
    have hobtF : Scenario.obtainable { s with placements := l } = s.obtainable := funext hobt
    have hheld : ∀ f, Scenario.held { s with placements := l } f = s.held f := by
      intro f; unfold Scenario.held; rw [hfinal]
    have hE : checkEvents { s with placements := l } = checkEvents s := by
      unfold checkEvents; rw [htrace]; rfl
    have hD : Scenario.derivedConstraints { s with placements := l } = s.derivedConstraints := by
      simp only [Scenario.derivedConstraints, Scenario.itemConstraints, Scenario.knowledgeConstraints, Scenario.conditionConstraints, Scenario.tagConstraints, Scenario.avail,
        Scenario.concealConstraints, Scenario.exposed, hfinal, hobtF]; try rfl
    have hsat : Scenario.satisfies { s with placements := l } = s.satisfies := by
      funext v; unfold Scenario.satisfies Scenario.effectiveConstraints; rw [hD]; rfl
    have hctx : Scenario.gctx { s with placements := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    have hG : checkG { s with placements := l } = checkG s := by
      unfold checkG; rw [hctx]; rfl
    have hP : ∀ x, x ∈ checkPost { s with placements := l } ↔ x ∈ checkPost s := by
      intro x
      simp only [checkPost, postErrors, postWarnings, warningsT009, issuesK003, issuesK004K005, issuesK006,
        issuesK007, issuesK008, issuesH, warningsH, issuesA, checkT012, issuesK010, warningsK009,
      Scenario.clueOnly, Scenario.draws, hfinal, hseg, hwhere, hobt, hobtF, hheld,
        List.mem_append, List.mem_map]
      exact Iff.rfl
    simp only [List.mem_append, hE, hG, hP]

/-- 記載漏れの警告は、終了状態・ハンドアウト・盤面が同じで、アイテムと知識の ID の集合が同じなら同じ。 -/
theorem mem_warningsH_of (s s' : Scenario) (hfin : s'.final = s.final) (hho : s'.handouts = s.handouts)
    (hbo : s'.board = s.board) (hi : ∀ i, i ∈ s'.itemIds ↔ i ∈ s.itemIds)
    (hf : ∀ f, f ∈ s'.factIds ↔ f ∈ s.factIds) : ∀ x, x ∈ warningsH s' ↔ x ∈ warningsH s := by
  intro x
  unfold warningsH
  simp only [hfin, hho, hbo, List.mem_append, List.mem_flatMap]
  apply or_congr
  · apply exists_congr; intro h; apply and_congr_right; intro _
    apply or_congr
    · cases h.items <;> simp [List.mem_filterMap, hi]
    · cases h.knows <;> simp [List.mem_filterMap, hf]
  · apply exists_congr; intro b; apply and_congr_right; intro _
    simp [List.mem_filterMap, hi]

/-! ## items / facts -/

theorem check_perm_items (s : Scenario) (l : List Item) (hp : s.items.Perm l) :
    check { s with items := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with items := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with items := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        simp only [Scenario.itemIds]; exact contains_perm (hp.map _).symm i)
    simp only [rIssues, List.mem_append, h1, h2]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.2.2.1
    have hfind : ∀ x, l.find? (fun a => a.id == x) = s.items.find? (fun a => a.id == x) :=
      fun x => (find?_id_perm (f := fun a : Item => a.id) hp hn x).symm
    have hinit : Scenario.initState { s with items := l } = s.initState := by
      simp only [Scenario.initState, hfind]
    have hrun : Scenario.run { s with items := l } = s.run := by
      unfold Scenario.run; rw [hinit]; rfl
    have htrace : Scenario.trace { s with items := l } = s.trace := by unfold Scenario.trace; rw [hrun]
    have hfinal : Scenario.final { s with items := l } = s.final := by unfold Scenario.final; rw [hrun]
    have hdeath : ∀ c, Scenario.deathTime { s with items := l } c = s.deathTime c := by
      intro c; unfold Scenario.deathTime; rw [hfinal]; try rfl
    have hseg : ∀ c, Scenario.segments { s with items := l } c = s.segments c := by
      intro c; unfold Scenario.segments; rw [hinit, hdeath]; try rfl
    have hwhere : ∀ c t, Scenario.whereAt { s with items := l } c t = s.whereAt c t := by
      intro c t; unfold Scenario.whereAt Scenario.whereAlive; rw [hdeath]; simp only [hseg]
    have hobt : ∀ f, Scenario.obtainable { s with items := l } f = s.obtainable f := by
      intro f; unfold Scenario.obtainable; rw [hfinal]
    have hobtF : Scenario.obtainable { s with items := l } = s.obtainable := funext hobt
    have hheld : ∀ f, Scenario.held { s with items := l } f = s.held f := by
      intro f; unfold Scenario.held; rw [hfinal]
    have hE : checkEvents { s with items := l } = checkEvents s := by
      unfold checkEvents; rw [htrace]; rfl
    have hav : ∀ p, Scenario.avail { s with items := l } p = s.avail p := by
      intro p; unfold Scenario.avail; rw [hfinal]; exact (hp.filter _).length_eq.symm
    have hD : Scenario.derivedConstraints { s with items := l } = s.derivedConstraints := by
      simp only [Scenario.derivedConstraints, Scenario.itemConstraints, Scenario.knowledgeConstraints, Scenario.conditionConstraints, Scenario.tagConstraints, hav,
        Scenario.concealConstraints, Scenario.exposed, hfinal, hobtF]; try rfl
    have hsat : Scenario.satisfies { s with items := l } = s.satisfies := by
      funext v; unfold Scenario.satisfies Scenario.effectiveConstraints; rw [hD]; rfl
    have hctx : Scenario.gctx { s with items := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    have hG : checkG { s with items := l } = checkG s := by
      unfold checkG; rw [hctx]; rfl
    have hW := mem_warningsH_of s { s with items := l } hfinal rfl rfl
      (fun i => by simp only [Scenario.itemIds, (hp.map (·.id)).mem_iff]) (fun f => Iff.rfl)
    have hP : ∀ x, x ∈ checkPost { s with items := l } ↔ x ∈ checkPost s := by
      intro x
      simp only [checkPost, postErrors, postWarnings, warningsT009, issuesK003, issuesK004K005, issuesK006,
        issuesK007, issuesK008, issuesH, issuesA, checkT012, issuesK010, warningsK009,
        Scenario.clueOnly, Scenario.draws, hfinal, hseg, hwhere, hobt, hobtF, hheld,
        List.mem_append, List.mem_map, hW]
      exact Iff.rfl
    simp only [List.mem_append, hE, hG, hP]

theorem check_perm_facts (s : Scenario) (l : List Fact) (hp : s.facts.Perm l) :
    check { s with facts := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with facts := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro h0 x
    have hn := (nodup_of_R001 s h0).2.2.2.2.1
    have hff : ∀ f, Scenario.findFact? { s with facts := l } f = s.findFact? f :=
      fun f => (find?_id_perm (f := fun a : Fact => a.id) hp hn f).symm
    have h2 := checkR002_of s { s with facts := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        simp only [Scenario.factIds]; exact contains_perm (hp.map _).symm i)
    have h10 : x ∈ checkR010 { s with facts := l } ↔ x ∈ checkR010 s := by
      simp only [checkR010, List.mem_flatMap, hp.mem_iff, hff]
    have h11 : x ∈ checkR011 { s with facts := l } ↔ x ∈ checkR011 s := by
      simp only [checkR011, List.mem_flatMap, hp.mem_iff]
    simp only [rIssues, List.mem_append, h1, h2, h10, h11]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.2.2.2.1
    have hff : ∀ f, Scenario.findFact? { s with facts := l } f = s.findFact? f :=
      fun f => (find?_id_perm (f := fun a : Fact => a.id) hp hn f).symm
    have hW := mem_warningsH_of s { s with facts := l } rfl rfl rfl (fun i => Iff.rfl)
      (fun f => by simp only [Scenario.factIds, (hp.map (·.id)).mem_iff])
    have hP : ∀ x, x ∈ checkPost { s with facts := l } ↔ x ∈ checkPost s := by
      intro x
      simp only [checkPost, postErrors, postWarnings, issuesK006, issuesK007, issuesK008,
        List.mem_append, List.mem_map, List.mem_filterMap, hp.mem_iff, hff, hW]
      exact Iff.rfl
    simp only [List.mem_append, hP]
    exact Iff.rfl

/-! ## endings / constraints -/

theorem all_perm {l l' : List α} (hp : l.Perm l') (p : α → Bool) : l.all p = l'.all p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, hp.mem_iff]

theorem check_perm_endings (s : Scenario) (l : List Ending) (hp : s.endings.Perm l) :
    check { s with endings := l } = check s := by
  have h1 : ∀ x, x ∈ checkR001 { s with endings := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm (hp.map (·.id))
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have h2 := checkR002_of s { s with endings := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have hform : ∀ y, y ∈ formulas { s with endings := l } ↔ y ∈ formulas s := by
      intro y; simp only [formulas, List.mem_append, List.mem_map, hp.mem_iff]
    have h9 : x ∈ checkR009 { s with endings := l } ↔ x ∈ checkR009 s := by
      simp only [checkR009, List.mem_flatMap, hform]; exact Iff.rfl
    have h12 : x ∈ checkR012 { s with endings := l } ↔ x ∈ checkR012 s := by
      simp only [checkR012, List.mem_flatMap, hform]; exact Iff.rfl
    simp only [rIssues, List.mem_append, h1, h2, h9, h12]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.2.2.2.2.2.2.2.2.1
    have hsortE : Scenario.sortedEndings { s with endings := l } = s.sortedEndings :=
      (mergeSort_key_perm (f := fun e : Ending => e.id) hp hn).symm
    have hG : checkG { s with endings := l } = checkG s := by
      simp only [checkG, checkGPatterns, checkG001, checkG002, checkGRest, hsortE]
      try rfl
    simp only [List.mem_append, hG]
    exact Iff.rfl

theorem check_perm_constraints (s : Scenario) (l : List Formula) (hp : s.constraints.Perm l) :
    check { s with constraints := l } = check s := by
  apply check_eq_of_parts
  · intro x; exact Iff.rfl
  · intro _ x
    have h2 := checkR002_of s { s with constraints := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => rfl)
    have hform : ∀ y, y ∈ formulas { s with constraints := l } ↔ y ∈ formulas s := by
      intro y; simp only [formulas, List.mem_append, List.mem_map, hp.mem_iff]
    have h9 : x ∈ checkR009 { s with constraints := l } ↔ x ∈ checkR009 s := by
      simp only [checkR009, List.mem_flatMap, hform]; exact Iff.rfl
    have h12 : x ∈ checkR012 { s with constraints := l } ↔ x ∈ checkR012 s := by
      simp only [checkR012, List.mem_flatMap, hform]; exact Iff.rfl
    simp only [rIssues, List.mem_append, h2, h9, h12]
    exact Iff.rfl
  · intro _ d
    have hsat : Scenario.satisfies { s with constraints := l } = s.satisfies := by
      funext v
      unfold Scenario.satisfies Scenario.effectiveConstraints
      exact all_perm (hp.append_right _).symm _
    have hctx : Scenario.gctx { s with constraints := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hsat]; rfl
    have hG : checkG { s with constraints := l } = checkG s := by
      unfold checkG; rw [hctx]; rfl
    simp only [List.mem_append, hG]
    exact Iff.rfl

/-! ## goals / choices -/

def goalDom (g : Goal) : Id × List Val := (g.id, [Val.bool false, .bool true])

def choiceDom (c : Choice) : Id × List Val :=
  match c.values with
  | none => (c.id, [Val.bool false, .bool true])
  | some vs => (c.id, (vs.mergeSort (fun a b => decide (a ≤ b))).map Val.str)

theorem domains_def (s : Scenario) :
    s.domains = (s.goals.map goalDom ++ s.choices.map choiceDom).mergeSort (fun a b => decide (a.1 ≤ b.1)) := rfl

theorem domains_keys (s : Scenario) : (s.goals.map goalDom ++ s.choices.map choiceDom).map (·.1) = s.variableIds := by
  have hc : (fun a : Id × List Val => a.1) ∘ choiceDom = (·.id) := by
    funext c; simp only [Function.comp, choiceDom]; split <;> rfl
  have hg : (fun a : Id × List Val => a.1) ∘ goalDom = (·.id) := rfl
  rw [List.map_append, List.map_map, List.map_map, hc, hg]; rfl

theorem domains_perm (s s' : Scenario) (hp : (s.goals.map goalDom ++ s.choices.map choiceDom).Perm
    (s'.goals.map goalDom ++ s'.choices.map choiceDom)) (hn : s.variableIds.Nodup) : s'.domains = s.domains := by
  rw [domains_def, domains_def]
  exact (mergeSort_key_perm (f := fun a : Id × List Val => a.1) hp (by rw [domains_keys]; exact hn)).symm

/-- 定義域が同じなら、変数・定義域・割り当て数も同じ。 -/
theorem g_of_domains {s s' : Scenario} (h : s'.domains = s.domains) :
    s'.gVars = s.gVars ∧ s'.gDoms = s.gDoms ∧ s'.gCount = s.gCount := by
  simp only [Scenario.gVars, Scenario.gDoms, Scenario.gCount, h, and_self]

theorem variableIds_nodup_split (s : Scenario) (h : s.variableIds.Nodup) :
    (s.goals.map (·.id)).Nodup ∧ (s.choices.map (·.id)).Nodup := by
  unfold Scenario.variableIds at h
  rw [List.nodup_append] at h
  exact ⟨h.1, h.2.1⟩

theorem checkG_mem_of (s s' : Scenario) (hc : s'.gCount = s.gCount) (hctx : s'.gctx = s.gctx)
    (h8 : checkG008 s' = checkG008 s) (hR : ∀ g x, x ∈ checkGRest s' g ↔ x ∈ checkGRest s g)
    (h1 : ∀ g, checkG001 s' g = checkG001 s g) (h2 : ∀ g, checkG002 s' g = checkG002 s g) :
    ∀ x, x ∈ checkG s' ↔ x ∈ checkG s := by
  intro x
  unfold checkG
  dsimp only
  rw [hc, hctx, h8]
  simp only [List.mem_append]
  apply or_congr_left
  split
  · exact Iff.rfl
  · split
    · exact Iff.rfl
    · simp only [checkGPatterns, List.mem_append, hR, h1, h2]

theorem check_perm_goals (s : Scenario) (l : List Goal) (hp : s.goals.Perm l) :
    check { s with goals := l } = check s := by
  have hvp : s.variableIds.Perm (Scenario.variableIds { s with goals := l }) :=
    (hp.map (·.id)).append_right _
  have h1 : ∀ x, x ∈ checkR001 { s with goals := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm hvp
    simp only [Scenario.variableIds] at hd
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro _ x
    have hvc : ∀ v, (Scenario.variableIds { s with goals := l }).contains v = s.variableIds.contains v :=
      fun v => (contains_perm hvp v).symm
    have hvcF : (Scenario.variableIds { s with goals := l }).contains = s.variableIds.contains := funext hvc
    have h2 := checkR002_of s { s with goals := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        exact hvc i)
    have hFT : ∀ r f, formulaTypeErrors { s with goals := l } r f = formulaTypeErrors s r f := by
      intro r f; simp only [formulaTypeErrors, hvc]; try rfl
    have hTE : ∀ r f, tallyErrors { s with goals := l } r f = tallyErrors s r f := by
      intro r f; simp only [tallyErrors, hvcF]; try rfl
    have h9 : ∀ x, x ∈ checkR009 { s with goals := l } ↔ x ∈ checkR009 s := by
      intro x
      simp only [checkR009, formulas, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_filterMap,
        hp.mem_iff, hFT]
    have h12 : ∀ x, x ∈ checkR012 { s with goals := l } ↔ x ∈ checkR012 s := by
      intro x
      simp only [checkR012, formulas, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_filterMap,
        hp.mem_iff, hTE]
    simp only [rIssues, List.mem_append, h1, h2, h9, h12]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.2.2.2.2.2.2.2.1
    have hdom : Scenario.domains { s with goals := l } = s.domains :=
      domains_perm s _ ((hp.map goalDom).append_right _) hn
    obtain ⟨hV, hD, hC⟩ := g_of_domains hdom
    have hgs : l.mergeSort (fun a b => decide (a.id ≤ b.id)) = s.goals.mergeSort (fun a b => decide (a.id ≤ b.id)) :=
      (mergeSort_key_perm (f := fun g : Goal => g.id) hp (variableIds_nodup_split s hn).1).symm
    have hder : (Scenario.derivedConstraints { s with goals := l }).Perm s.derivedConstraints := by
      unfold Scenario.derivedConstraints Scenario.itemConstraints Scenario.knowledgeConstraints
        Scenario.conditionConstraints Scenario.tagConstraints Scenario.concealConstraints
      dsimp only
      rw [hgs]
      exact (((((List.Perm.filterMap _ hp.symm).append_right _).append (List.Perm.filterMap _ hp.symm)).append
        (List.Perm.filterMap _ hp.symm)).append ((List.Perm.filterMap _ hp.symm).append_right _)).append
        (List.Perm.filterMap _ hp.symm)
    have hsat : Scenario.satisfies { s with goals := l } = s.satisfies := by
      funext v
      unfold Scenario.satisfies Scenario.effectiveConstraints
      rw [hV]
      exact all_perm (hder.append_left _) _
    have hctx : Scenario.gctx { s with goals := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hV, hD, hsat]
    have hG := checkG_mem_of s { s with goals := l } hC hctx
      (by simp only [checkG008, any_perm hp.symm]; try rfl)
      (fun g x => by
        simp only [checkGRest, List.mem_append, List.mem_filterMap, List.mem_flatMap, hp.mem_iff]
        exact Iff.rfl)
      (fun g => rfl) (fun g => rfl)
    simp only [List.mem_append, hG]
    exact Iff.rfl

theorem check_perm_choices (s : Scenario) (l : List Choice) (hp : s.choices.Perm l) :
    check { s with choices := l } = check s := by
  have hvp : s.variableIds.Perm (Scenario.variableIds { s with choices := l }) :=
    List.Perm.append_left _ (hp.map (·.id))
  have h1 : ∀ x, x ∈ checkR001 { s with choices := l } ↔ x ∈ checkR001 s := by
    intro x
    have hd := mem_duplicates_perm hvp
    simp only [Scenario.variableIds] at hd
    simp only [checkR001, Scenario.eventIds, Scenario.characterIds, Scenario.areaIds, Scenario.locationIds,
      Scenario.itemIds, Scenario.factIds, Scenario.variableIds, List.flatMap_cons, List.flatMap_nil, List.mem_append,
      List.mem_map, hd]
  apply check_eq_of_parts _ _ h1
  · intro h0 x
    have hn := (nodup_of_R001 s h0).2.2.2.2.2.2.2.2.1
    have hfc : ∀ v, Scenario.findChoice? { s with choices := l } v = s.findChoice? v :=
      fun v => (find?_id_perm (f := fun c : Choice => c.id) hp (variableIds_nodup_split s hn).2 v).symm
    have hen : ∀ v, Scenario.enumValues? { s with choices := l } v = s.enumValues? v := by
      intro v; simp only [Scenario.enumValues?, hfc]
    have henF : Scenario.enumValues? { s with choices := l } = s.enumValues? := funext hen
    have hvc : ∀ v, (Scenario.variableIds { s with choices := l }).contains v = s.variableIds.contains v :=
      fun v => (contains_perm hvp v).symm
    have hvcF : (Scenario.variableIds { s with choices := l }).contains = s.variableIds.contains := funext hvc
    have h2 := checkR002_of s { s with choices := l }
      (fun r => by simp only [allRefs, baseRefs, List.mem_append, List.mem_flatMap, List.mem_map, hp.mem_iff])
      (fun k i => by
        unfold Scenario.idsOfKind
        split <;> try rfl
        exact hvc i)
    have h8 : x ∈ checkR008 { s with choices := l } ↔ x ∈ checkR008 s := by
      simp only [checkR008, List.mem_filterMap, hp.mem_iff]
    have hFT : ∀ r f, formulaTypeErrors { s with choices := l } r f = formulaTypeErrors s r f := by
      intro r f; simp only [formulaTypeErrors, hvc, hen]
    have hTE : ∀ r f, tallyErrors { s with choices := l } r f = tallyErrors s r f := by
      intro r f; simp only [tallyErrors, hvcF, hen, henF]
    have h9 : checkR009 { s with choices := l } = checkR009 s := by simp only [checkR009, hFT]; try rfl
    have h12 : checkR012 { s with choices := l } = checkR012 s := by simp only [checkR012, hTE]; try rfl
    simp only [rIssues, List.mem_append, h1, h2, h8, h9, h12]
    exact Iff.rfl
  · intro hR d
    have hn := (nodup_of_R001 s (rIssues_nil_parts s hR).1).2.2.2.2.2.2.2.2.1
    have hdom : Scenario.domains { s with choices := l } = s.domains :=
      domains_perm s _ (List.Perm.append_left _ (hp.map choiceDom)) hn
    obtain ⟨hV, hD, hC⟩ := g_of_domains hdom
    have hsat : Scenario.satisfies { s with choices := l } = s.satisfies := by
      funext v
      unfold Scenario.satisfies
      rw [hV]; rfl
    have hctx : Scenario.gctx { s with choices := l } = s.gctx := by
      rw [Scenario.gctx_eq, Scenario.gctx_eq, hV, hD, hsat]
    have hG := checkG_mem_of s { s with choices := l } hC hctx rfl
      (fun g x => by
        simp only [checkGRest, List.mem_append, List.mem_filterMap, List.mem_flatMap, hp.mem_iff]
        exact Iff.rfl)
      (fun g => rfl) (fun g => rfl)
    simp only [List.mem_append, hG]
    exact Iff.rfl

/-! ## 定理 3: トップレベルのすべての配列の並べ替え -/

/-- s' は s のトップレベルの配列をそれぞれ並べ替えたもの(時刻などのスカラー値は同じ)。 -/
structure ScenarioPerm (s s' : Scenario) : Prop where
  startTime : s'.startTime = s.startTime
  endTime : s'.endTime = s.endTime
  claimTolerance : s'.claimTolerance = s.claimTolerance
  exploration : s'.exploration = s.exploration
  characters : s.characters.Perm s'.characters
  areas : s.areas.Perm s'.areas
  locations : s.locations.Perm s'.locations
  travel : s.travel.Perm s'.travel
  areaTravel : s.areaTravel.Perm s'.areaTravel
  perception : s.perception.Perm s'.perception
  placements : s.placements.Perm s'.placements
  items : s.items.Perm s'.items
  facts : s.facts.Perm s'.facts
  initialKnowledge : s.initialKnowledge.Perm s'.initialKnowledge
  events : s.events.Perm s'.events
  clues : s.clues.Perm s'.clues
  solutionFacts : s.solutionFacts.Perm s'.solutionFacts
  assertions : s.assertions.Perm s'.assertions
  handouts : s.handouts.Perm s'.handouts
  board : s.board.Perm s'.board
  goals : s.goals.Perm s'.goals
  choices : s.choices.Perm s'.choices
  constraints : s.constraints.Perm s'.constraints
  endings : s.endings.Perm s'.endings

/-- **定理 3 (並べ替え不変)**: トップレベルのどの配列を並べ替えても、判定器の出力は変わらない
(R 群の違反がある場合も含む)。 -/
theorem check_perm (s s' : Scenario) (h : ScenarioPerm s s') : check s' = check s := by
  have e0 : s' = { s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices, constraints := s'.constraints, endings := s'.endings } := by
    have h1 := h.startTime; have h2 := h.endTime; have h3 := h.claimTolerance; have h4 := h.exploration
    cases s'
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    rfl
  rw [e0]
  have e20 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices, constraints := s'.constraints, endings := s'.endings }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices, constraints := s'.constraints }) :=
    check_perm_endings ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices, constraints := s'.constraints }) s'.endings h.endings
  have e19 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices, constraints := s'.constraints }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices }) :=
    check_perm_constraints ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices }) s'.constraints h.constraints
  have e18 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals, choices := s'.choices }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals }) :=
    check_perm_choices ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals }) s'.choices h.choices
  have e17 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board, goals := s'.goals }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board }) :=
    check_perm_goals ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board }) s'.goals h.goals
  have e16 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts, board := s'.board }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts }) :=
    check_perm_board ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts }) s'.board h.board
  have e15 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions, handouts := s'.handouts }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions }) :=
    check_perm_handouts ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions }) s'.handouts h.handouts
  have e14 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts, assertions := s'.assertions }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts }) :=
    check_perm_assertions ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts }) s'.assertions h.assertions
  have e13 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues, solutionFacts := s'.solutionFacts }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues }) :=
    check_perm_solutionFacts ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues }) s'.solutionFacts h.solutionFacts
  have e12 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events, clues := s'.clues }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events }) :=
    check_perm_clues ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events }) s'.clues h.clues
  have e11 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge, events := s'.events }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge }) :=
    check_perm_events ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge }) s'.events h.events
  have e10 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts, initialKnowledge := s'.initialKnowledge }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts }) :=
    check_perm_initialKnowledge ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts }) s'.initialKnowledge h.initialKnowledge
  have e9 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items, facts := s'.facts }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items }) :=
    check_perm_facts ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items }) s'.facts h.facts
  have e8 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements, items := s'.items }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements }) :=
    check_perm_items ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements }) s'.items h.items
  have e7 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception, placements := s'.placements }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception }) :=
    check_perm_placements ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception }) s'.placements h.placements
  have e6 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel, perception := s'.perception }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel }) :=
    check_perm_perception ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel }) s'.perception h.perception
  have e5 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel, areaTravel := s'.areaTravel }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel }) :=
    check_perm_areaTravel ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel }) s'.areaTravel h.areaTravel
  have e4 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations, travel := s'.travel }) = check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations }) :=
    check_perm_travel ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations }) s'.travel h.travel
  have e3 : check ({ s with characters := s'.characters, areas := s'.areas, locations := s'.locations }) = check ({ s with characters := s'.characters, areas := s'.areas }) :=
    check_perm_locations ({ s with characters := s'.characters, areas := s'.areas }) s'.locations h.locations
  have e2 : check ({ s with characters := s'.characters, areas := s'.areas }) = check ({ s with characters := s'.characters }) :=
    check_perm_areas ({ s with characters := s'.characters }) s'.areas h.areas
  have e1 : check ({ s with characters := s'.characters }) = check (s) :=
    check_perm_characters (s) s'.characters h.characters
  exact (e20.trans (e19.trans (e18.trans (e17.trans (e16.trans (e15.trans (e14.trans (e13.trans (e12.trans (e11.trans (e10.trans (e9.trans (e8.trans (e7.trans (e6.trans (e5.trans (e4.trans (e3.trans (e2.trans e1)))))))))))))))))))

end MurderMystery
