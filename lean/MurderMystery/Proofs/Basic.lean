import MurderMystery.Checker.Check

/-!
# 基本性質の証明

- 定理 5: 知識の単調性(イベントを処理しても知識は減らない)
- 定理 11: 死亡の一意性(一度死亡したキャラクターの死亡イベントは変わらない)
- 重複除去・正規化は要素の集合を変えない(定理 1 の前提)
-/
namespace MurderMystery

/-! ## 定理 5: 知識の単調性 -/

theorem step_knows_mono (S : State) (e : Event) (c f : Id) (h : S.knows c f = true) :
    (step S e).knows c f = true := by
  unfold step
  split <;> (try split) <;> simp_all [addKnows]

theorem runAux_knows_mono (c f : Id) :
    ∀ (evs prev : List Event) (S : State), S.knows c f = true → (runAux S prev evs).2.knows c f = true
  | [], _, _, h => h
  | e :: es, prev, S, h => runAux_knows_mono c f es (prev ++ [e]) (step S e) (step_knows_mono S e c f h)

/-- 初期状態で知っていることは、終了状態でも知っている。 -/
theorem final_knows_of_initial (s : Scenario) (c f : Id) (h : s.initState.knows c f = true) :
    s.final.knows c f = true :=
  runAux_knows_mono c f _ _ _ h

/-- トレースの各ステップの処理前に知っていることは、終了状態でも知っている。 -/
theorem runAux_trace_knows (c f : Id) :
    ∀ (evs prev : List Event) (S : State), ∀ st ∈ (runAux S prev evs).1,
      st.pre.knows c f = true → (runAux S prev evs).2.knows c f = true
  | [], _, _, st, hst, _ => by simp [runAux] at hst
  | e :: es, prev, S, st, hst, h => by
    simp only [runAux, List.mem_cons] at hst ⊢
    rcases hst with rfl | hst
    · exact runAux_knows_mono c f es _ _ (step_knows_mono _ e c f h)
    · exact runAux_trace_knows c f es _ _ st hst h

theorem trace_knows_final (s : Scenario) (st : Step) (hst : st ∈ s.trace) (c f : Id)
    (h : st.pre.knows c f = true) : s.final.knows c f = true :=
  runAux_trace_knows c f _ _ _ st hst h

/-! ## 定理 11: 死亡の一意性 -/

theorem step_dead_stable (S : State) (e : Event) (c d : Id) (h : S.dead c = some d) :
    (step S e).dead c = some d := by
  cases hk : e.kind with
  | move c' to arr mode fatal =>
    simp only [step, hk]
    split
    · simp only [update]
      split
      · rename_i hf hc; subst hc; simp_all
      · exact h
    · exact h
  | die c' =>
    simp only [step, hk]
    split
    · simp only [update]
      split
      · rename_i hn hc; subst hc; simp_all
      · exact h
    · exact h
  | _ => simp [step, hk, h]

theorem runAux_dead_stable (c d : Id) :
    ∀ (evs prev : List Event) (S : State), S.dead c = some d → (runAux S prev evs).2.dead c = some d
  | [], _, _, h => h
  | e :: es, prev, S, h => runAux_dead_stable c d es (prev ++ [e]) (step S e) (step_dead_stable S e c d h)

/-! ## 重複除去と正規化 -/

theorem mem_dedup_foldl [DecidableEq α] (x : α) :
    ∀ (l acc : List α), x ∈ l.foldl (fun acc y => if y ∈ acc then acc else acc ++ [y]) acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc => by simp
  | y :: ys, acc => by
    simp only [List.foldl_cons]
    rw [mem_dedup_foldl x ys]
    split <;> simp_all <;> grind

theorem mem_dedup [DecidableEq α] (x : α) (l : List α) : x ∈ dedup l ↔ x ∈ l := by
  simp [dedup, mem_dedup_foldl]

theorem nodup_dedup_foldl [DecidableEq α] :
    ∀ (l acc : List α), acc.Nodup → (l.foldl (fun acc y => if y ∈ acc then acc else acc ++ [y]) acc).Nodup
  | [], _, h => h
  | y :: ys, acc, h => by
    simp only [List.foldl_cons]
    apply nodup_dedup_foldl ys
    split
    · exact h
    · rename_i hy
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb hab
      simp at hb
      subst hb hab
      exact hy ha

theorem nodup_dedup [DecidableEq α] (l : List α) : (dedup l).Nodup :=
  nodup_dedup_foldl l [] List.nodup_nil

theorem mem_dedupSorted [DecidableEq α] (x : α) : ∀ l : List α, x ∈ dedupSorted l ↔ x ∈ l
  | [] => by simp [dedupSorted]
  | [_] => by simp [dedupSorted]
  | a :: b :: rest => by
    have ih := mem_dedupSorted x (b :: rest)
    unfold dedupSorted
    split
    · rename_i hab
      subst hab
      simp_all
    · simp_all

/-- 正規化は検出結果の集合を変えない。 -/
theorem mem_normalize (d : Diag) (ds : List Diag) : d ∈ normalize ds ↔ d ∈ ds := by
  simp [normalize, mem_dedupSorted, List.mem_mergeSort]

/-- 判定器が error を出すかどうかは、正規化の前後で変わらない。 -/
theorem check_noError_iff (s : Scenario) :
    (∀ d ∈ check s, d.sev = .warning) ↔ (∀ d ∈ checkRaw s, d.sev = .warning) := by
  simp [check, mem_normalize]

end MurderMystery
