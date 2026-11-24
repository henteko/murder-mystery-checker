import MurderMystery.Checker.Events

/-!
# 終了状態・区間に対する検査: T009 / K003〜K008 / H / A (docs/spec.md §4.2, §4.4〜§4.6)
-/
namespace MurderMystery

/-! ## T009 -/

/-- c₁ と c₂ の遭遇が、時刻 [lo, hi] のイベントで認知されているか。 -/
def acknowledged (s : Scenario) (c₁ c₂ l : Id) (lo hi : Time) : Bool :=
  s.events.any fun e =>
    lo ≤ e.time && e.time ≤ hi &&
    match e.kind with
    | .scene .. | .transfer .. | .tell .. => e.kind.participants.contains c₁ && e.kind.participants.contains c₂
    | .observe c loc tl ts _ =>
      loc == l && tl == l && ((c == c₁ && ts.contains c₂) || (c == c₂ && ts.contains c₁))
    | _ => false

def sortedIds (ids : List Id) : List Id := ids.mergeSort (fun a b => decide (a ≤ b))

/-- 相異なる組 (x, y) で x が y より前にあるもの。 -/
def pairs : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ pairs xs

def checkT009 (s : Scenario) : List Diag :=
  (pairs (sortedIds s.characterIds)).flatMap fun (c₁, c₂) =>
    (s.segments c₁).flatMap fun (l₁, a₁, b₁) =>
      (s.segments c₂).filterMap fun (l₂, a₂, b₂) =>
        let lo := max a₁ a₂
        let hi := min b₁ b₂
        if l₁ == l₂ && !s.isPublic l₁ && lo < hi && !acknowledged s c₁ c₂ l₁ lo hi then
          some (warn "T009" [c₁, c₂, l₁, toString lo, toString hi])
        else none

/-! ## K003〜K008 -/

def checkK003 (s : Scenario) : List Diag :=
  s.solutionFacts.filterMap fun f => if s.obtainable f then none else some (err "K003" [f])

def checkK004K005 (s : Scenario) : List Diag :=
  s.clues.flatMap fun c => match c.item with
    | none => []
    | some i =>
      let h := s.final.holder i
      if h == .consumed then [err "K004" [c.id, i]]
      else match c.location with
        | some l => if h != .place l then [err "K005" [c.id, i, l, h.render]] else []
        | none => []

/-- 終了状態で NPC 以外が知っているか、いずれかのハンドアウトの knows にある。 -/
def Scenario.held (s : Scenario) (f : Id) : Bool :=
  s.characters.any (fun c => !c.npc && s.final.knows c.id f) || s.handouts.any (fun h => (h.knows.getD []).contains f)

def checkK006 (s : Scenario) : List Diag :=
  s.facts.filterMap fun f =>
    if !f.truth && s.held f.id && !f.contradictedBy.any s.obtainable then some (err "K006" [f.id]) else none

def checkK007 (s : Scenario) : List Diag :=
  s.solutionFacts.filterMap fun f => match s.findFact? f with
    | some fact => if fact.truth then none else some (err "K007" [f])
    | none => none

def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

def checkK008 (s : Scenario) : List Diag :=
  s.facts.filterMap fun f =>
    if !f.truth then none else
    match f.aboutEvent, f.claimedAt with
    | some eid, some claimed =>
      match s.findEvent? eid with
      | some e =>
        let actual := match e.kind, f.aboutPoint with
          | .move _ _ arr _ _, "arrive" => arr
          | _, _ => e.time
        if absDiff claimed actual > f.tolerance.getD s.claimTolerance then
          some (err "K008" [f.id, toString claimed, toString actual])
        else none
      | none => none
    | _, _ => none

/-! ## H -/

def checkH (s : Scenario) : List Diag :=
  let E := s.final
  let hs := s.handouts.flatMap fun h =>
    let c := h.character
    (match h.location with
      | some l => if (E.pos c).dest != l then [err "H001" [c, l, (E.pos c).dest]] else []
      | none => [])
    ++ (match h.items with
      | some is =>
        is.filterMap (fun i => if E.holder i != .char c then some (err "H002" [c, i, (E.holder i).render]) else none)
        ++ s.itemIds.filterMap (fun i => if E.holder i == .char c && !is.contains i then some (warn "H003" [c, i]) else none)
      | none => [])
    ++ (match h.knows with
      | some ks =>
        ks.filterMap (fun f => if E.knows c f then none else some (err "H004" [c, f]))
        ++ s.factIds.filterMap (fun f => if E.knows c f && !ks.contains f then some (warn "H005" [c, f]) else none)
      | none => [])
  let bs := s.board.flatMap fun b =>
    let l := b.location
    b.items.filterMap (fun i => if E.holder i != .place l then some (err "H006" [l, i, (E.holder i).render]) else none)
    ++ s.itemIds.filterMap (fun i => if E.holder i == .place l && !b.items.contains i then some (warn "H007" [l, i]) else none)
  hs ++ bs

/-! ## A -/

def checkA (s : Scenario) : List Diag :=
  s.assertions.flatMap fun a =>
    a.characters.filterMap fun c =>
      let w := s.whereAt c a.time
      let bad := match a.kind with
        | .present => w != a.location
        | .absent => w == a.location
      if bad then some (err "A001" [a.id, c, a.kind.render, w]) else none

def checkPost (s : Scenario) : List Diag :=
  checkT009 s ++ checkK003 s ++ checkK004K005 s ++ checkK006 s ++ checkK007 s ++ checkK008 s ++ checkH s ++ checkA s

end MurderMystery
