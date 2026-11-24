import MurderMystery.Checker.Events

/-!
# 終了状態・区間に対する検査: T009 / K003〜K008 / H / A (docs/spec.md §4.2, §4.4〜§4.6)

error と warning を分けて返し、`checkPost` でまとめて `Diag` にする。
-/
namespace MurderMystery

/-! ## T009 (warning) -/

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

def warningsT009 (s : Scenario) : List Issue :=
  (pairs (sortedIds s.characterIds)).flatMap fun (c₁, c₂) =>
    (s.segments c₁).flatMap fun (l₁, a₁, b₁) =>
      (s.segments c₂).filterMap fun (l₂, a₂, b₂) =>
        let lo := max a₁ a₂
        let hi := min b₁ b₂
        if l₁ == l₂ && !s.isPublic l₁ && lo < hi && !acknowledged s c₁ c₂ l₁ lo hi then
          some ("T009", [c₁, c₂, l₁, toString lo, toString hi])
        else none

/-! ## K003〜K008 (error) -/

def issuesK003 (s : Scenario) : List Issue :=
  s.solutionFacts.filterMap fun f => if s.obtainable f then none else some ("K003", [f])

def issuesK004K005 (s : Scenario) : List Issue :=
  s.clues.flatMap fun c => match c.item with
    | none => []
    | some i =>
      let h := s.final.holder i
      if h == .consumed then [("K004", [c.id, i])]
      else match c.location with
        | some l => if h != .place l then [("K005", [c.id, i, l, h.render])] else []
        | none => []

/-- 終了状態で NPC 以外が知っているか、いずれかのハンドアウトの knows にある。 -/
def Scenario.held (s : Scenario) (f : Id) : Bool :=
  s.characters.any (fun c => !c.npc && s.final.knows c.id f) || s.handouts.any (fun h => (h.knows.getD []).contains f)

def issuesK006 (s : Scenario) : List Issue :=
  s.facts.filterMap fun f =>
    if !f.truth && s.held f.id && !f.contradictedBy.any s.obtainable then some ("K006", [f.id]) else none

def issuesK007 (s : Scenario) : List Issue :=
  s.solutionFacts.filterMap fun f => match s.findFact? f with
    | some fact => if fact.truth then none else some ("K007", [f])
    | none => none

def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- 証言が指す実際の時刻。 -/
def Fact.actualTime (f : Fact) (e : Event) : Time :=
  match e.kind, f.aboutPoint with
  | .move _ _ arr _ _, "arrive" => arr
  | _, _ => e.time

def issuesK008 (s : Scenario) : List Issue :=
  s.facts.filterMap fun f =>
    if !f.truth then none else
    match f.aboutEvent, f.claimedAt with
    | some eid, some claimed =>
      match s.findEvent? eid with
      | some e =>
        if absDiff claimed (f.actualTime e) > f.tolerance.getD s.claimTolerance then
          some ("K008", [f.id, toString claimed, toString (f.actualTime e)])
        else none
      | none => none
    | _, _ => none

/-! ## H -/

def issuesH (s : Scenario) : List Issue :=
  let E := s.final
  let hs := s.handouts.flatMap fun h =>
    let c := h.character
    (match h.location with
      | some l => if (E.pos c).dest != l then [("H001", [c, l, (E.pos c).dest])] else []
      | none => [])
    ++ (match h.items with
      | some is => is.filterMap (fun i => if E.holder i != .char c then some ("H002", [c, i, (E.holder i).render]) else none)
      | none => [])
    ++ (match h.knows with
      | some ks => ks.filterMap (fun f => if E.knows c f then none else some ("H004", [c, f]))
      | none => [])
  let bs := s.board.flatMap fun b =>
    b.items.filterMap (fun i => if E.holder i != .place b.location then some ("H006", [b.location, i, (E.holder i).render]) else none)
  hs ++ bs

def warningsH (s : Scenario) : List Issue :=
  let E := s.final
  let hs := s.handouts.flatMap fun h =>
    let c := h.character
    (match h.items with
      | some is => s.itemIds.filterMap (fun i => if E.holder i == .char c && !is.contains i then some ("H003", [c, i]) else none)
      | none => [])
    ++ (match h.knows with
      | some ks => s.factIds.filterMap (fun f => if E.knows c f && !ks.contains f then some ("H005", [c, f]) else none)
      | none => [])
  let bs := s.board.flatMap fun b =>
    s.itemIds.filterMap (fun i => if E.holder i == .place b.location && !b.items.contains i then some ("H007", [b.location, i]) else none)
  hs ++ bs

/-! ## A -/

def AssertKind.violated (k : AssertKind) (w l : String) : Bool :=
  match k with
  | .present => w != l
  | .absent => w == l

def issuesA (s : Scenario) : List Issue :=
  s.assertions.flatMap fun a =>
    a.characters.filterMap fun c =>
      let w := s.whereAt c a.time
      if a.kind.violated w a.location then some ("A001", [a.id, c, a.kind.render, w]) else none

/-! ## T012 (warning) -/

/-- observe の対象 x が、同じ時刻に始まる move で移動している。 -/
def checkT012 (s : Scenario) : List Diag :=
  s.sortedEvents.flatMap fun o =>
    o.kind.observed.flatMap fun x =>
      (s.sortedEvents.filter fun m => m.time == o.time && m.kind.moved.contains x).map fun m =>
        warn "T012" [x, m.id] (some o.id)

def postErrors (s : Scenario) : List Issue :=
  issuesK003 s ++ issuesK004K005 s ++ issuesK006 s ++ issuesK007 s ++ issuesK008 s ++ issuesH s ++ issuesA s

def postWarnings (s : Scenario) : List Issue := warningsT009 s ++ warningsH s

def checkPost (s : Scenario) : List Diag :=
  (postErrors s).map (fun (c, a) => err c a) ++ (postWarnings s).map (fun (c, a) => warn c a) ++ checkT012 s

end MurderMystery
