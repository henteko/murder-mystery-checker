import MurderMystery.Proofs.Perm

/-!
# 定理 9: 移動時間の決定性

R005 の違反がない表では、どの (from, to) についても一致する辺は高々1つ。
したがって `edgeLookup` の値は一致する唯一の辺の分数で、表の並び順によらない。
`travelTime` / `perceives` は `travel` / `area_travel` / `perception` の並び順によらない。
-/
namespace MurderMystery

/-- 辺 e が (a, b) に一致する(`edgeLookup` の検索条件)。 -/
def edgeMatches (a b : Id) (e : Edge) : Bool :=
  (e.src == a && e.dst == b) || (e.bidirectional && e.src == b && e.dst == a)

/-- 双方向を展開した (from, to) の組(`checkEdges` と同じ)。 -/
def expandEdge (e : Edge) : List (Id × Id) :=
  if e.bidirectional then [(e.src, e.dst), (e.dst, e.src)] else [(e.src, e.dst)]

theorem mem_expandEdge_of_matches {a b : Id} {e : Edge} (h : edgeMatches a b e = true) :
    (a, b) ∈ expandEdge e := by
  unfold edgeMatches at h
  unfold expandEdge
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨⟨hb, h₁⟩, h₂⟩
  · subst h₁ h₂; split <;> simp
  · subst h₁ h₂; simp [hb]

/-- 重複のない flatMap では、同じ要素を生む元の要素は1つ。 -/
theorem eq_of_nodup_flatMap {f : α → List β} :
    ∀ {l : List α}, (l.flatMap f).Nodup → ∀ x ∈ l, ∀ y ∈ l, ∀ z, z ∈ f x → z ∈ f y → x = y
  | [], _, _, hx, _, _, _, _, _ => by cases hx
  | w :: ws, h, x, hx, y, hy, z, hzx, hzy => by
    simp only [List.flatMap_cons] at h
    rw [List.nodup_append] at h
    obtain ⟨_, hws, hdis⟩ := h
    have hin : ∀ v ∈ ws, z ∈ f v → z ∈ ws.flatMap f := fun v hv hz => List.mem_flatMap.mpr ⟨v, hv, hz⟩
    rcases List.mem_cons.mp hx with ex | ex <;> rcases List.mem_cons.mp hy with ey | ey
    · rw [ex, ey]
    · subst ex; exact absurd rfl (hdis z hzx z (hin y ey hzy))
    · subst ey; exact absurd rfl (hdis z hzy z (hin x ex hzx))
    · exact eq_of_nodup_flatMap hws x ex y ey z hzx hzy

theorem edgeLookup_eq (es : List Edge) (a b : Id) :
    edgeLookup es a b = (es.find? (edgeMatches a b)).map (·.minutes) := rfl

/-- **定理 9 (一意性)**: R005 の違反がない表では、(a, b) に一致する辺は高々1つ。 -/
theorem edge_unique (tbl : String) (es : List Edge) (h : checkEdges tbl es = []) (a b : Id) :
    ∀ e₁ ∈ es, ∀ e₂ ∈ es, edgeMatches a b e₁ = true → edgeMatches a b e₂ = true → e₁ = e₂ := by
  unfold checkEdges at h
  simp only [List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq] at h
  obtain ⟨hself, hdup⟩ := h
  have hnd := nodup_of_duplicates_nil _ hdup
  intro e₁ h₁ e₂ h₂ hm₁ hm₂
  have hf : ∀ e ∈ es, e ∈ es.filter (fun e => e.src != e.dst) := fun e he => by
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    exact ⟨he, hself e he⟩
  exact eq_of_nodup_flatMap (f := expandEdge) hnd e₁ (hf e₁ h₁) e₂ (hf e₂ h₂) (a, b)
    (mem_expandEdge_of_matches hm₁) (mem_expandEdge_of_matches hm₂)

/-- **定理 9 (値)**: R005 の違反がなければ、`edgeLookup` の値は一致する唯一の辺の分数。 -/
theorem edgeLookup_eq_some_iff (tbl : String) (es : List Edge) (h : checkEdges tbl es = []) (a b : Id)
    (m : Nat) : edgeLookup es a b = some m ↔ ∃ e ∈ es, edgeMatches a b e = true ∧ e.minutes = m := by
  rw [edgeLookup_eq]
  constructor
  · intro hl
    simp only [Option.map_eq_some_iff] at hl
    obtain ⟨e, he, rfl⟩ := hl
    exact ⟨e, List.mem_of_find?_eq_some he, List.find?_some he, rfl⟩
  · rintro ⟨e, he, hm, rfl⟩
    cases hf : es.find? (edgeMatches a b) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd hm (hf e he)
    | some e' =>
      have := edge_unique tbl es h a b e' (List.mem_of_find?_eq_some hf) e he (List.find?_some hf) hm
      simp [hf, this]

/-- **定理 9 (並べ替え不変)**: R005 の違反がなければ、表を並べ替えても `edgeLookup` は変わらない。 -/
theorem edgeLookup_perm (tbl : String) {es es' : List Edge} (h : checkEdges tbl es = []) (hp : es.Perm es')
    (a b : Id) : edgeLookup es a b = edgeLookup es' a b := by
  rw [edgeLookup_eq, edgeLookup_eq]
  rw [find?_perm hp (edge_unique tbl es h a b)]

end MurderMystery
