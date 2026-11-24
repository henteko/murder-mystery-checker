import MurderMystery.Spec.Types

/-!
# 操作的意味論 (docs/spec.md §1.2, §2)
-/
namespace MurderMystery

/-! ## 汎用 -/

/-- 重複を除く(最初の出現を残す)。 -/
def dedup [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) []

def update [DecidableEq α] (f : α → β) (k : α) (v : β) : α → β :=
  fun x => if x = k then v else f x

/-! ## イベントの属性 (§1.3) -/

def EventKind.participants : EventKind → List Id
  | .move c .. => [c]
  | .scene _ ps _ => ps
  | .observe c .. => [c]
  | .transfer a b _ => [a, b]
  | .pickup c _ | .drop c _ | .use c _ | .consume c _ => [c]
  | .learn c _ => [c]
  | .tell a b _ => [a, b]
  | .die c => [c]

def EventKind.actors : EventKind → List Id
  | .scene _ ps _ => ps
  | .transfer a .. | .tell a .. => [a]
  | k => k.participants

def EventKind.item? : EventKind → Option Id
  | .transfer _ _ i | .pickup _ i | .drop _ i | .use _ i | .consume _ i => some i
  | _ => none

/-- 正規順序 (at 昇順, id 昇順) の ≤。 -/
def evLe (a b : Event) : Bool :=
  a.time < b.time || (a.time == b.time && decide (a.id ≤ b.id))

def Scenario.sortedEvents (s : Scenario) : List Event := s.events.mergeSort evLe

def Scenario.findEvent? (s : Scenario) (id : Id) : Option Event := s.events.find? (·.id == id)

/-! ## 移動時間と知覚 (§1.2) -/

def edgeLookup (es : List Edge) (a b : Id) : Option Nat :=
  (es.find? fun e => (e.src == a && e.dst == b) || (e.bidirectional && e.src == b && e.dst == a)).map (·.minutes)

def Scenario.areaOf (s : Scenario) (l : Id) : Option Id := (s.locations.find? (·.id == l)).bind (·.area)

def Scenario.isPublic (s : Scenario) (l : Id) : Bool := (s.locations.find? (·.id == l)).any (·.isPublic)

def Scenario.isNpc (s : Scenario) (c : Id) : Bool := (s.characters.find? (·.id == c)).any (·.npc)

def Scenario.travelTime (s : Scenario) (a b : Id) : Option Nat :=
  match edgeLookup s.travel a b with
  | some m => some m
  | none =>
    match s.areaOf a, s.areaOf b with
    | some x, some y =>
      if x == y then (s.areas.find? (·.id == x)).bind (·.internalMinutes)
      else edgeLookup s.areaTravel x y
    | _, _ => none

def Scenario.perceives (s : Scenario) (a b : Id) : Bool :=
  a == b || (edgeLookup s.perception a b).isSome

/-! ## 状態 (§2.1) -/

structure Position where
  dest : Id
  arrive : Time
  via : Option Id
  deriving Repr, DecidableEq, Inhabited

structure State where
  pos : Id → Position
  holder : Id → Holder
  knows : Id → Id → Bool
  dead : Id → Option Id

def State.inTransit (S : State) (c : Id) (t : Time) : Bool :=
  (S.pos c).via.isSome && t < (S.pos c).arrive

def Scenario.initState (s : Scenario) : State where
  pos c := match s.placements.find? (·.character == c) with
    | some p => ⟨p.location, s.startTime, none⟩
    | none => ⟨"", s.startTime, none⟩
  holder i := match s.items.find? (·.id == i) with
    | some it => it.initial
    | none => .consumed
  knows c f := s.initialKnowledge.contains (c, f)
  dead _ := none

def addKnows (k : Id → Id → Bool) (cs fs : List Id) : Id → Id → Bool :=
  fun c f => k c f || (cs.contains c && fs.contains f)

/-- 1イベントの効果 (§2.2)。事前条件の違反の有無に関係なく適用する。 -/
def step (S : State) (e : Event) : State :=
  match e.kind with
  | .move c to arr _ fatal =>
    { S with
      pos := update S.pos c ⟨to, arr, some e.id⟩
      dead := if fatal && (S.dead c).isNone then update S.dead c (some e.id) else S.dead }
  | .scene _ ps rv => { S with knows := addKnows S.knows ps rv }
  | .observe c _ _ _ fs => { S with knows := addKnows S.knows [c] fs }
  | .learn c fs => { S with knows := addKnows S.knows [c] fs }
  | .tell _ b fs => { S with knows := addKnows S.knows [b] fs }
  | .transfer _ b i => { S with holder := update S.holder i (.char b) }
  | .pickup c i => { S with holder := update S.holder i (.char c) }
  | .drop c i => { S with holder := update S.holder i (.place (S.pos c).dest) }
  | .consume _ i => { S with holder := update S.holder i .consumed }
  | .use .. => S
  | .die c => if (S.dead c).isNone then { S with dead := update S.dead c (some e.id) } else S

/-- 処理の1ステップ: 処理前の状態、イベント、正規順序でそれより前のイベント。 -/
structure Step where
  pre : State
  ev : Event
  earlier : List Event

def runAux : State → List Event → List Event → List Step × State
  | S, _, [] => ([], S)
  | S, prev, e :: es =>
    let r := runAux (step S e) (prev ++ [e]) es
    (⟨S, e, prev⟩ :: r.1, r.2)

def Scenario.run (s : Scenario) : List Step × State := runAux s.initState [] s.sortedEvents

def Scenario.trace (s : Scenario) : List Step := s.run.1

/-- 終了状態 E。 -/
def Scenario.final (s : Scenario) : State := s.run.2

/-! ## 死亡時刻・居場所の区間・時刻での居場所 (§2.1, §2.3, §2.4) -/

def Scenario.deathTime (s : Scenario) (c : Id) : Option Time :=
  match s.final.dead c with
  | none => none
  | some d =>
    match s.findEvent? d with
    | some ⟨_, _, .move _ _ arr _ _, _⟩ => some arr
    | some e => some e.time
    | none => none

/-- moves: (出発時刻, 行き先, 到着時刻) の列。 -/
def segsAux (endT : Time) : Id → Time → List (Time × Id × Time) → List (Id × Time × Time)
  | cur, start, [] => [(cur, start, endT)]
  | cur, start, (dep, to, arr) :: ms => (cur, start, dep) :: segsAux endT to arr ms

def Scenario.movesOf (s : Scenario) (c : Id) : List (Time × Id × Time) :=
  s.sortedEvents.filterMap fun e =>
    match e.kind with
    | .move c' to arr _ _ => if c' == c then some (e.time, to, arr) else none
    | _ => none

def Scenario.segments (s : Scenario) (c : Id) : List (Id × Time × Time) :=
  let place := (s.initState.pos c).dest
  let raw := segsAux s.endTime place s.startTime (s.movesOf c)
  let cut := match s.deathTime c with
    | none => raw
    | some d => raw.map fun (l, a, b) => (l, a, min b d)
  cut.filter fun (_, a, b) => a < b

def Scenario.whereAlive (s : Scenario) (c : Id) (t : Time) : String :=
  match (s.segments c).find? (fun (_, a, b) => a ≤ t && t < b) with
  | some (l, _, _) => l
  | none => "transit"

def Scenario.whereAt (s : Scenario) (c : Id) (t : Time) : String :=
  match s.deathTime c with
  | some d => if d ≤ t then "dead" else s.whereAlive c t
  | none => s.whereAlive c t

/-! ## 入手可能 (§2.5) -/

def Scenario.obtainable (s : Scenario) (f : Id) : Bool :=
  s.characters.any (fun c => !c.npc && s.final.knows c.id f) || s.clues.any (·.reveals.contains f)

end MurderMystery
