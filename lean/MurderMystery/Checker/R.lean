import MurderMystery.Checker.Diag

/-!
# R 群: 構造・参照整合 (docs/spec.md §4.1)
-/
namespace MurderMystery

/-- 2回以上現れる値(最初の出現順、重複なし)。 -/
def duplicates [DecidableEq α] (l : List α) : List α :=
  dedup (l.filter fun x => (l.filter (· == x)).length ≥ 2)

namespace Scenario
variable (s : Scenario)

def characterIds := s.characters.map (·.id)
def areaIds := s.areas.map (·.id)
def locationIds := s.locations.map (·.id)
def itemIds := s.items.map (·.id)
def factIds := s.facts.map (·.id)
def eventIds := s.events.map (·.id)
def variableIds := s.goals.map (·.id) ++ s.choices.map (·.id)

def findFact? (f : Id) : Option Fact := s.facts.find? (·.id == f)
def findChoice? (c : Id) : Option Choice := s.choices.find? (·.id == c)
def isGoal (v : Id) : Bool := s.goals.any (·.id == v)

/-- 選択 v が列挙型ならその値の集合。 -/
def enumValues? (v : Id) : Option (List String) := (s.findChoice? v).bind (·.values)

end Scenario

/-- R 群のコード。 -/
inductive RCode where
  | R001 | R002 | R003 | R004 | R005 | R006 | R007 | R008 | R009 | R010 | R011 | R012 | R013
  deriving DecidableEq, Repr

def RCode.str : RCode → String
  | .R001 => "R001" | .R002 => "R002" | .R003 => "R003" | .R004 => "R004" | .R005 => "R005"
  | .R006 => "R006" | .R007 => "R007" | .R008 => "R008" | .R009 => "R009" | .R010 => "R010"
  | .R011 => "R011" | .R012 => "R012" | .R013 => "R013"

/-- R 群の検出結果: (コード, args, event)。すべて error。 -/
abbrev RIssue := RCode × List String × Option Id

def rerr (code : RCode) (args : List String) (event : Option Id := none) : RIssue := (code, args, event)

/-! ## R001 -/
def checkR001 (s : Scenario) : List RIssue :=
  let kinds : List (String × List Id) := [
    ("character", s.characterIds), ("area", s.areaIds), ("location", s.locationIds),
    ("item", s.itemIds), ("fact", s.factIds), ("clue", s.clues.map (·.id)),
    ("event", s.eventIds), ("assertion", s.assertions.map (·.id)), ("variable", s.variableIds),
    ("ending", s.endings.map (·.id)), ("handout", s.handouts.map (·.character)),
    ("board", s.board.map (·.location))]
  kinds.flatMap fun (k, ids) => (duplicates ids).map fun id => rerr .R001 [k, id]

/-! ## R002 -/

/-- 参照: (referrer, kind, id, 参照元イベント) -/
structure Ref where
  referrer : String
  kind : String
  id : Id
  event : Option Id := none
  deriving DecidableEq

def eventRefs (e : Event) : List Ref :=
  let r := s!"event:{e.id}"
  let mk (k : String) (id : Id) : Ref := ⟨r, k, id, some e.id⟩
  let chars := e.kind.participants ++ (match e.kind with | .observe _ _ _ ts _ => ts | _ => [])
  let locs := match e.kind with
    | .move _ to .. => [to]
    | .scene l .. => [l]
    | .observe _ l tl .. => [l, tl]
    | _ => []
  let facts := e.requires ++ (match e.kind with
    | .scene _ _ rv => rv
    | .observe _ _ _ _ fs | .learn _ fs | .tell _ _ fs => fs
    | _ => [])
  chars.map (mk "character") ++ locs.map (mk "location") ++ (e.kind.item?.toList.map (mk "item"))
    ++ facts.map (mk "fact")

def formulaRefs (referrer : String) (f : Formula) : List Ref :=
  f.refs.flatMap fun
    | .asBool v => [⟨referrer, "variable", v, none⟩]
    | .asEq v _ => [⟨referrer, "variable", v, none⟩]
    | .inTally vs _ => vs.map fun v => ⟨referrer, "variable", v, none⟩
    | .asFact f => [⟨referrer, "fact", f, none⟩]

/-- 探索の回の `clues` からの参照(referrer は `round:<1 から数えた番号>`)。 -/
def roundRefs (ex : Option (List Round)) : List Ref :=
  (ex.getD []).zipIdx.flatMap fun (r, i) =>
    (r.clues.getD []).map fun c => ⟨s!"round:{i + 1}", "clue", c, none⟩

/-- 探索の回以外からの参照。 -/
def baseRefs (s : Scenario) : List Ref :=
  let edgeRefs (tbl kind : String) (es : List Edge) : List Ref :=
    es.flatMap fun e => [⟨tbl, kind, e.src, none⟩, ⟨tbl, kind, e.dst, none⟩]
  s.locations.flatMap (fun l => l.area.toList.map fun a => ⟨s!"location:{l.id}", "area", a, none⟩)
  ++ edgeRefs "travel" "location" s.travel
  ++ edgeRefs "area_travel" "area" s.areaTravel
  ++ edgeRefs "perception" "location" s.perception
  ++ s.placements.flatMap (fun p =>
      [⟨s!"placement:{p.character}", "character", p.character, none⟩,
       ⟨s!"placement:{p.character}", "location", p.location, none⟩])
  ++ s.items.flatMap (fun i => match i.initial with
      | .char c => [⟨s!"item:{i.id}", "character", c, none⟩]
      | .place l => [⟨s!"item:{i.id}", "location", l, none⟩]
      | .consumed => [])
  ++ s.initialKnowledge.flatMap (fun (c, f) =>
      [⟨s!"initial_knowledge:{c}", "character", c, none⟩, ⟨s!"initial_knowledge:{c}", "fact", f, none⟩])
  ++ s.facts.flatMap (fun f =>
      f.contradictedBy.map (fun r => ⟨s!"fact:{f.id}", "fact", r, none⟩)
      ++ f.aboutEvent.toList.map (fun e => ⟨s!"fact:{f.id}", "event", e, none⟩))
  ++ s.events.flatMap eventRefs
  ++ s.clues.flatMap (fun c =>
      c.location.toList.map (fun l => ⟨s!"clue:{c.id}", "location", l, none⟩)
      ++ c.item.toList.map (fun i => ⟨s!"clue:{c.id}", "item", i, none⟩)
      ++ c.reveals.map (fun f => ⟨s!"clue:{c.id}", "fact", f, none⟩))
  ++ s.solutionFacts.map (fun f => ⟨"solution", "fact", f, none⟩)
  ++ s.assertions.flatMap (fun a =>
      ⟨s!"assertion:{a.id}", "location", a.location, none⟩
      :: a.characters.map (fun c => ⟨s!"assertion:{a.id}", "character", c, none⟩))
  ++ s.handouts.flatMap (fun h =>
      let r := s!"handout:{h.character}"
      ⟨r, "character", h.character, none⟩
      :: (h.location.toList.map (fun l => ⟨r, "location", l, none⟩)
      ++ (h.items.getD []).map (fun i => ⟨r, "item", i, none⟩)
      ++ (h.knows.getD []).map (fun f => ⟨r, "fact", f, none⟩)))
  ++ s.board.flatMap (fun b =>
      ⟨s!"board:{b.location}", "location", b.location, none⟩
      :: b.items.map (fun i => ⟨s!"board:{b.location}", "item", i, none⟩))
  ++ s.goals.flatMap (fun g =>
      ⟨s!"goal:{g.id}", "character", g.owner, none⟩
      :: (g.requiresItems.map (fun i => ⟨s!"goal:{g.id}", "item", i, none⟩)
      ++ g.requiresKnowledge.map (fun f => ⟨s!"goal:{g.id}", "fact", f, none⟩)
      ++ g.conceals.map (fun f => ⟨s!"goal:{g.id}", "fact", f, none⟩)
      ++ (g.condition.map (formulaRefs s!"goal:{g.id}")).getD []))
  ++ s.choices.map (fun c => ⟨s!"choice:{c.id}", "character", c.owner, none⟩)
  ++ s.constraints.flatMap (formulaRefs "constraint")
  ++ s.endings.flatMap (fun e => formulaRefs s!"ending:{e.id}" e.condition)

/-- すべての参照(R002 の対象)。 -/
def allRefs (s : Scenario) : List Ref := baseRefs s ++ roundRefs s.exploration

def Scenario.idsOfKind (s : Scenario) : String → List Id
  | "character" => s.characterIds
  | "area" => s.areaIds
  | "location" => s.locationIds
  | "item" => s.itemIds
  | "fact" => s.factIds
  | "event" => s.eventIds
  | "variable" => s.variableIds
  | "clue" => s.clues.map (·.id)
  | _ => []

def checkR002 (s : Scenario) : List RIssue :=
  (dedup ((allRefs s).filter fun r => !(s.idsOfKind r.kind).contains r.id)).map fun r =>
    rerr .R002 [r.referrer, r.kind, r.id] r.event

/-! ## R003〜R005 -/
def checkR003 (s : Scenario) : List RIssue :=
  s.characters.filterMap fun c =>
    if (s.placements.filter (·.character == c.id)).length == 1 then none else some (rerr .R003 [c.id])

def checkR004 (s : Scenario) : List RIssue :=
  if s.startTime > s.endTime then [rerr .R004 []] else []

def checkEdges (tbl : String) (es : List Edge) : List RIssue :=
  let self := es.filter (fun e => e.src == e.dst)
  let pairs := (es.filter (fun e => e.src != e.dst)).flatMap fun e =>
    if e.bidirectional then [(e.src, e.dst), (e.dst, e.src)] else [(e.src, e.dst)]
  self.map (fun e => rerr .R005 [tbl, e.src, e.dst])
    ++ (duplicates pairs).map (fun (a, b) => rerr .R005 [tbl, a, b])

def checkR005 (s : Scenario) : List RIssue :=
  checkEdges "travel" s.travel ++ checkEdges "area_travel" s.areaTravel ++ checkEdges "perception" s.perception

/-! ## R006 -/
def eventShapeErrors (e : Event) : List String :=
  match e.kind with
  | .move _ _ arr mode _ =>
    (if arr < e.time then ["arrive_before_depart"] else [])
    ++ (if ["walk", "fall", "carried"].contains mode then [] else ["unknown_mode"])
  | .transfer a b _ => if a == b then ["self_transfer"] else []
  | .tell a b fs => (if a == b then ["self_tell"] else []) ++ (if fs.isEmpty then ["empty_facts"] else [])
  | .observe c _ _ ts fs =>
    (if ts.contains c then ["self_observe"] else [])
    ++ (if (duplicates ts).isEmpty then [] else ["duplicate_participant"])
    ++ (if fs.isEmpty then ["empty_facts"] else [])
  | .scene _ ps _ =>
    (if ps.isEmpty then ["empty_participants"] else [])
    ++ (if (duplicates ps).isEmpty then [] else ["duplicate_participant"])
  | .learn _ fs => if fs.isEmpty then ["empty_facts"] else []
  | _ => []

def checkR006 (s : Scenario) : List RIssue :=
  s.events.flatMap fun e => (eventShapeErrors e).map fun r => rerr .R006 [r] (some e.id)

/-! ## R007〜R013 -/
def EventKind.isMove : EventKind → Bool
  | .move .. => true
  | _ => false

def checkR007 (s : Scenario) : List RIssue :=
  s.clues.filterMap fun c =>
    if c.location.isNone && c.item.isNone && c.deck.isNone then some (rerr .R007 [c.id]) else none

def checkR008 (s : Scenario) : List RIssue :=
  s.choices.filterMap fun c => match c.values with
    | some vs => if vs.isEmpty || !(duplicates vs).isEmpty then some (rerr .R008 [c.id]) else none
    | none => none

def formulaTypeErrors (s : Scenario) (referrer : String) (f : Formula) : List RIssue :=
  f.refs.flatMap fun
    | .asBool v => if (s.enumValues? v).isSome then [rerr .R009 [referrer, v, ""]] else []
    | .asEq v x =>
      if !s.variableIds.contains v then []
      else match s.enumValues? v with
        | none => [rerr .R009 [referrer, v, x]]
        | some vs => if vs.contains x then [] else [rerr .R009 [referrer, v, x]]
    | .inTally _ _ => []
    | .asFact _ => []

def tallyErrors (s : Scenario) (referrer : String) (f : Formula) : List RIssue :=
  f.refs.flatMap fun
    | .inTally vs x =>
      let known := vs.filter s.variableIds.contains
      let enums := known.filterMap s.enumValues?
      let sets := enums.map fun vals => vals.mergeSort (fun a b => decide (a ≤ b))
      (if vs.isEmpty then [rerr .R012 [referrer, "empty_votes"]] else [])
      ++ (if known.any (fun v => (s.enumValues? v).isNone) then [rerr .R012 [referrer, "not_enum"]] else [])
      ++ (if (dedup sets).length ≥ 2 then [rerr .R012 [referrer, "different_values"]] else [])
      ++ (match x with
          | some v => if enums.any (fun vals => !vals.contains v) then [rerr .R012 [referrer, "unknown_value"]] else []
          | none => [])
    | _ => []

def formulas (s : Scenario) : List (String × Formula) :=
  s.constraints.map (fun f => ("constraint", f)) ++ s.endings.map (fun e => (s!"ending:{e.id}", e.condition))
    ++ s.goals.filterMap (fun g => g.condition.map fun c => (s!"goal:{g.id}", c))

def checkR009 (s : Scenario) : List RIssue := (formulas s).flatMap fun (r, f) => formulaTypeErrors s r f
def checkR012 (s : Scenario) : List RIssue := (formulas s).flatMap fun (r, f) => tallyErrors s r f

def checkR010 (s : Scenario) : List RIssue :=
  s.facts.flatMap fun f =>
    if f.truth then (if f.contradictedBy.isEmpty then [] else [rerr .R010 [f.id, ""]])
    else f.contradictedBy.filterMap fun r => match s.findFact? r with
      | some rf => if rf.truth then none else some (rerr .R010 [f.id, r])
      | none => none

def checkR011 (s : Scenario) : List RIssue :=
  s.facts.flatMap fun f =>
    (match f.aboutEvent, f.claimedAt with
      | some _, none => [rerr .R011 [f.id, "about_without_claimed_at"]]
      | none, some _ => [rerr .R011 [f.id, "claimed_at_without_about"]]
      | _, _ => [])
    ++ (if f.aboutPoint == "at" || f.aboutPoint == "arrive" then [] else [rerr .R011 [f.id, "unknown_point"]])
    ++ (match f.aboutEvent with
      | some eid =>
        if f.aboutPoint == "arrive" then
          if s.events.any (fun e => e.id == eid && !e.kind.isMove) then
            [rerr .R011 [f.id, "arrive_on_non_move"]]
          else []
        else []
      | none => [])

def checkR013 (s : Scenario) : List RIssue :=
  s.assertions.filterMap fun a =>
    if s.startTime ≤ a.time && a.time < s.endTime then none else some (rerr .R013 [a.id])

def rIssues (s : Scenario) : List RIssue :=
  checkR001 s ++ checkR002 s ++ checkR003 s ++ checkR004 s ++ checkR005 s ++ checkR006 s ++ checkR007 s
    ++ checkR008 s ++ checkR009 s ++ checkR010 s ++ checkR011 s ++ checkR012 s ++ checkR013 s

/-- R 群の検出結果。ID の重複 (R001) があれば参照先が決まらないので、R001 だけを出す。 -/
def checkR (s : Scenario) : List Diag :=
  (if (checkR001 s).isEmpty then rIssues s else checkR001 s).map fun (c, a, e) => err c.str a e

end MurderMystery
