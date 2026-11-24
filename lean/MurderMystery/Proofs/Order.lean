import MurderMystery.Proofs.Basic

/-!
# 定理 3 (前半): 出力の正規順序

`Diag.lt` は狭義全順序であり、`normalize` の結果は `Diag.lt` について狭義に整列している
(したがって重複がない)。さらに、要素の集合が同じ列は正規化すると等しくなる。
-/
namespace MurderMystery

theorem ite_of_pos {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a := by simp [h]
theorem ite_of_neg {c : Prop} [Decidable c] (h : ¬c) {a b : α} : (if c then a else b) = b := by simp [h]

/-- Bool 値の比較関数が狭義全順序である。 -/
structure StrictTotal (lt : α → α → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

namespace StrictTotal

theorem asymm {lt : α → α → Bool} (h : StrictTotal lt) (a b : α) (hab : lt a b = true) :
    lt b a = false := by
  cases hba : lt b a
  · rfl
  · have := h.irrefl a; rw [h.trans a b a hab hba] at this; cases this

/-- 単射で引き戻した比較も狭義全順序。 -/
theorem comap {lt : β → β → Bool} (h : StrictTotal lt) (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    StrictTotal (fun a b => lt (f a) (f b)) where
  irrefl a := h.irrefl (f a)
  trans a b c := h.trans (f a) (f b) (f c)
  total a b hne := h.total (f a) (f b) (fun he => hne (hf a b he))

end StrictTotal

theorem strLt_total : StrictTotal strLt where
  irrefl a := by simp only [strLt, decide_eq_false_iff_not]; exact Std.lt_irrefl
  trans a b c h1 h2 := by
    simp only [strLt, decide_eq_true_eq] at *
    exact Std.lt_trans h1 h2
  total a b hne := by
    simp only [strLt, decide_eq_true_eq]
    rcases Std.lt_trichotomy a b with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h

theorem natLt_total : StrictTotal natLt where
  irrefl a := by simp [natLt]
  trans a b c h1 h2 := by simp only [natLt, decide_eq_true_eq] at *; omega
  total a b hne := by simp only [natLt, decide_eq_true_eq]; omega

theorem sevLt_total : StrictTotal sevLt where
  irrefl a := by cases a <;> rfl
  trans a b c h1 h2 := by cases a <;> cases b <;> cases c <;> simp_all [sevLt]
  total a b hne := by cases a <;> cases b <;> simp_all [sevLt]

theorem valLt_total : StrictTotal valLt where
  irrefl a := by
    rcases a with (_ | _) | a
    · rfl
    · rfl
    · exact strLt_total.irrefl a
  trans a b c h1 h2 := by
    rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;> rcases c with (_ | _) | c <;>
      simp_all [valLt]
    exact strLt_total.trans a b c h1 h2
  total a b hne := by
    rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;> simp_all [valLt]
    exact strLt_total.total a b hne

theorem optLt_total {lt : α → α → Bool} (h : StrictTotal lt) : StrictTotal (optLt lt) where
  irrefl a := by cases a <;> simp [optLt, h.irrefl]
  trans a b c h1 h2 := by
    cases a <;> cases b <;> cases c <;> simp_all [optLt]
    exact h.trans _ _ _ h1 h2
  total a b hne := by
    cases a <;> cases b <;> simp_all [optLt]
    exact h.total _ _ hne

theorem pairLt_total [DecidableEq α] {lt₁ : α → α → Bool} {lt₂ : β → β → Bool}
    (h₁ : StrictTotal lt₁) (h₂ : StrictTotal lt₂) : StrictTotal (pairLt lt₁ lt₂) where
  irrefl a := by simp [pairLt, h₂.irrefl]
  trans a b c hab hbc := by
    unfold pairLt at *
    by_cases e1 : a.1 = b.1
    · rw [ite_of_pos e1] at hab
      by_cases e2 : b.1 = c.1
      · rw [ite_of_pos e2] at hbc; rw [ite_of_pos (e1.trans e2)]; exact h₂.trans _ _ _ hab hbc
      · rw [ite_of_neg e2] at hbc; rw [ite_of_neg (by rw [e1]; exact e2), e1]; exact hbc
    · rw [ite_of_neg e1] at hab
      by_cases e2 : b.1 = c.1
      · rw [ite_of_pos e2] at hbc; rw [ite_of_neg (by rw [← e2]; exact e1), ← e2]; exact hab
      · rw [ite_of_neg e2] at hbc
        by_cases e3 : a.1 = c.1
        · rw [e3] at hab; rw [h₁.asymm _ _ hab] at hbc; cases hbc
        · rw [ite_of_neg e3]; exact h₁.trans _ _ _ hab hbc
  total a b hne := by
    unfold pairLt
    by_cases e : a.1 = b.1
    · have : a.2 ≠ b.2 := fun h2 => hne (Prod.ext e h2)
      simp only [e, ite_true]
      exact h₂.total _ _ this
    · simp only [e, Ne.symm e, ite_false]
      exact h₁.total _ _ e

theorem lexLt_total [DecidableEq α] {lt : α → α → Bool} (h : StrictTotal lt) : StrictTotal (lexLt lt) where
  irrefl := by
    intro a; induction a with
    | nil => rfl
    | cons x xs ih => simp [lexLt, ih]
  trans := by
    intro a
    induction a with
    | nil => intro b c h1 h2; cases b <;> cases c <;> simp_all [lexLt]
    | cons x xs ih =>
      intro b c h1 h2
      cases b with
      | nil => simp [lexLt] at h1
      | cons y ys =>
        cases c with
        | nil => simp [lexLt] at h2
        | cons z zs =>
          simp only [lexLt] at *
          by_cases e1 : x = y
          · rw [ite_of_pos e1] at h1
            by_cases e2 : y = z
            · rw [ite_of_pos e2] at h2; rw [ite_of_pos (e1.trans e2)]; exact ih _ _ h1 h2
            · rw [ite_of_neg e2] at h2; rw [ite_of_neg (by rw [e1]; exact e2), e1]; exact h2
          · rw [ite_of_neg e1] at h1
            by_cases e2 : y = z
            · rw [ite_of_pos e2] at h2; rw [ite_of_neg (by rw [← e2]; exact e1), ← e2]; exact h1
            · rw [ite_of_neg e2] at h2
              by_cases e3 : x = z
              · rw [e3] at h1; rw [h.asymm _ _ h1] at h2; cases h2
              · rw [ite_of_neg e3]; exact h.trans _ _ _ h1 h2
  total := by
    intro a
    induction a with
    | nil => intro b hne; cases b <;> simp_all [lexLt]
    | cons x xs ih =>
      intro b hne
      cases b with
      | nil => simp [lexLt]
      | cons y ys =>
        simp only [lexLt]
        by_cases e : x = y
        · subst e
          have : xs ≠ ys := fun h' => hne (by rw [h'])
          simp only [ite_true]; exact ih _ this
        · simp only [e, Ne.symm e, ite_false]; exact h.total _ _ e

theorem keyLt_total : StrictTotal keyLt :=
  pairLt_total strLt_total <| pairLt_total (optLt_total strLt_total) <|
    pairLt_total (lexLt_total strLt_total) <| pairLt_total (lexLt_total natLt_total) <|
      pairLt_total sevLt_total (optLt_total (lexLt_total (pairLt_total strLt_total valLt_total)))

theorem Diag.key_inj (a b : Diag) (h : a.key = b.key) : a = b := by
  cases a; cases b
  simp only [Diag.key, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6; rfl

/-- `Diag.lt` は検出結果全体の上の狭義全順序。 -/
theorem diagLt_total : StrictTotal Diag.lt := keyLt_total.comap Diag.key Diag.key_inj

/-! ## 整列と重複除去 -/

section
variable {lt : α → α → Bool} (h : StrictTotal lt)
include h

theorem le_trans_of_strictTotal (a b c : α) (hab : (!lt b a) = true) (hbc : (!lt c b) = true) :
    (!lt c a) = true := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at *
  cases hca : lt c a
  · rfl
  · exfalso
    by_cases e : a = b
    · subst e; rw [hca] at hbc; cases hbc
    · rcases h.total a b e with h' | h'
      · rw [h.trans _ _ _ hca h'] at hbc; cases hbc
      · rw [h'] at hab; cases hab

theorem le_total_of_strictTotal (a b : α) : ((!lt b a) || (!lt a b)) = true := by
  cases hba : lt b a
  · rfl
  · simp [h.asymm _ _ hba]

theorem lt_of_le_of_ne (a b : α) (hle : (!lt b a) = true) (hne : a ≠ b) : lt a b = true := by
  rcases h.total a b hne with h' | h'
  · exact h'
  · simp [h'] at hle

theorem eq_of_le_le (a b : α) (h1 : (!lt b a) = true) (h2 : (!lt a b) = true) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  rw [lt_of_le_of_ne h a b h1 hne] at h2; cases h2

/-- 整列済みの列から隣り合う重複を除くと、狭義に整列する。 -/
theorem pairwise_lt_dedupSorted [DecidableEq α] :
    ∀ l : List α, l.Pairwise (fun a b => (!lt b a) = true) →
      (dedupSorted l).Pairwise (fun a b => lt a b = true)
  | [], _ => by simp [dedupSorted]
  | [_], _ => by simp [dedupSorted]
  | x :: y :: rest, hp => by
    have ih := pairwise_lt_dedupSorted (y :: rest) (List.Pairwise.of_cons hp)
    unfold dedupSorted
    split
    · exact ih
    · rename_i hxy
      refine List.Pairwise.cons (fun z hz => ?_) ih
      rw [mem_dedupSorted] at hz
      have hxz : (!lt z x) = true := List.rel_of_pairwise_cons hp hz
      apply lt_of_le_of_ne h x z hxz
      rintro rfl
      have hxy' : (!lt y x) = true := List.rel_of_pairwise_cons hp (List.mem_cons_self ..)
      rcases List.mem_cons.mp hz with hz | hz
      · exact hxy hz
      · have hyx : (!lt x y) = true :=
          List.rel_of_pairwise_cons (List.Pairwise.of_cons hp) hz
        exact hxy (eq_of_le_le h x y hxy' hyx)

/-- 狭義に整列した列は、要素の集合で決まる。 -/
theorem eq_of_pairwise_lt_of_mem_iff :
    ∀ l₁ l₂ : List α, l₁.Pairwise (fun a b => lt a b = true) → l₂.Pairwise (fun a b => lt a b = true) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, hm => by simpa using (hm y).mpr (List.mem_cons_self ..)
  | x :: _, [], _, _, hm => by simpa using (hm x).mp (List.mem_cons_self ..)
  | x :: xs, y :: ys, h1, h2, hm => by
    have hxy : x = y := by
      refine Classical.byContradiction fun hne => ?_
      have hx : x ∈ ys := by
        rcases List.mem_cons.mp ((hm x).mp (List.mem_cons_self ..)) with e | e
        · exact absurd e hne
        · exact e
      have hy : y ∈ xs := by
        rcases List.mem_cons.mp ((hm y).mpr (List.mem_cons_self ..)) with e | e
        · exact absurd e.symm hne
        · exact e
      have := h.trans _ _ _ (List.rel_of_pairwise_cons h1 hy) (List.rel_of_pairwise_cons h2 hx)
      rw [h.irrefl] at this; cases this
    subst hxy
    congr 1
    refine eq_of_pairwise_lt_of_mem_iff xs ys (List.Pairwise.of_cons h1) (List.Pairwise.of_cons h2) fun z => ?_
    have hz := hm z
    constructor
    · intro hzx
      have hne : z ≠ x := by
        rintro rfl; have := List.rel_of_pairwise_cons h1 hzx; rw [h.irrefl] at this; cases this
      rcases List.mem_cons.mp (hz.mp (List.mem_cons_of_mem _ hzx)) with e | e
      · exact absurd e hne
      · exact e
    · intro hzy
      have hne : z ≠ x := by
        rintro rfl; have := List.rel_of_pairwise_cons h2 hzy; rw [h.irrefl] at this; cases this
      rcases List.mem_cons.mp (hz.mpr (List.mem_cons_of_mem _ hzy)) with e | e
      · exact absurd e hne
      · exact e

end

/-! ## 定理 3: 出力の決定性 -/

/-- 正規化の結果は正規順序で狭義に整列している。 -/
theorem normalize_sorted (ds : List Diag) : (normalize ds).Pairwise (fun a b => Diag.lt a b = true) := by
  unfold normalize
  apply pairwise_lt_dedupSorted diagLt_total
  exact List.pairwise_mergeSort (le_trans_of_strictTotal diagLt_total)
    (le_total_of_strictTotal diagLt_total) ds

theorem normalize_nodup (ds : List Diag) : (normalize ds).Nodup :=
  (normalize_sorted ds).imp fun {a b} hab he => by
    subst he; rw [diagLt_total.irrefl] at hab; cases hab

/-- 要素の集合が同じなら、正規化の結果は等しい。 -/
theorem normalize_eq_of_mem_iff (ds ds' : List Diag) (h : ∀ d, d ∈ ds ↔ d ∈ ds') :
    normalize ds = normalize ds' :=
  eq_of_pairwise_lt_of_mem_iff diagLt_total _ _ (normalize_sorted ds) (normalize_sorted ds')
    fun d => by rw [mem_normalize, mem_normalize, h]

/-- **定理 3 (整列・重複なし)**: 判定器の出力は正規順序で狭義に整列し、重複がない。 -/
theorem check_sorted (s : Scenario) : (check s).Pairwise (fun a b => Diag.lt a b = true) :=
  normalize_sorted _

theorem check_nodup (s : Scenario) : (check s).Nodup := normalize_nodup _

/-- 正規化前の検出結果の集合が同じなら、出力は等しい。 -/
theorem check_eq_of_mem_iff (s s' : Scenario) (h : ∀ d, d ∈ checkRaw s ↔ d ∈ checkRaw s') :
    check s = check s' :=
  normalize_eq_of_mem_iff _ _ h

end MurderMystery
