/-!
# 入力モデル (docs/spec.md §1)

正規化 JSON に一対一で対応するデータ型。省略可能なフィールドはパース時に既定値で埋める。
ただし R 群の検査に「指定されていたか」が必要なもの(about / claimed_at など)は `Option` のまま持つ。
-/
namespace MurderMystery

abbrev Id := String
abbrev Time := Nat

structure Character where
  id : Id
  npc : Bool := false
  deriving Repr, DecidableEq, Inhabited

structure Area where
  id : Id
  internalMinutes : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

structure Location where
  id : Id
  area : Option Id := none
  isPublic : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- travel / area_travel / perception の1エントリ。perception では minutes を使わない。 -/
structure Edge where
  src : Id
  dst : Id
  minutes : Nat := 0
  bidirectional : Bool := false
  deriving Repr, DecidableEq, Inhabited

structure Placement where
  character : Id
  location : Id
  deriving Repr, DecidableEq, Inhabited

/-- アイテムの保持者 (§2.1)。 -/
inductive Holder where
  | char (c : Id)
  | place (l : Id)
  | consumed
  deriving Repr, DecidableEq, Inhabited

def Holder.render : Holder → String
  | .char c => s!"character:{c}"
  | .place l => s!"location:{l}"
  | .consumed => "consumed"

structure Item where
  id : Id
  initial : Holder
  deriving Repr, DecidableEq, Inhabited

structure Fact where
  id : Id
  truth : Bool := true
  contradictedBy : List Id := []
  /-- `about.event` -/
  aboutEvent : Option Id := none
  /-- `about.point`(文字列のまま。R011 で検査) -/
  aboutPoint : String := "at"
  claimedAt : Option Time := none
  tolerance : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- イベントの種類ごとのフィールド (§1.3)。 -/
inductive EventKind where
  | move (character to : Id) (arrive : Time) (mode : String) (fatal : Bool)
  | scene (location : Id) (participants : List Id) (reveals : List Id)
  | observe (character location targetLocation : Id) (targets facts : List Id)
  | transfer (src dst item : Id)
  | pickup (character item : Id)
  | drop (character item : Id)
  | use (character item : Id)
  | consume (character item : Id)
  | learn (character : Id) (facts : List Id)
  | tell (src dst : Id) (facts : List Id)
  | die (character : Id)
  deriving Repr, DecidableEq, Inhabited

structure Event where
  id : Id
  time : Time
  kind : EventKind
  requires : List Id := []
  deriving Repr, DecidableEq, Inhabited

structure Clue where
  id : Id
  location : Option Id := none
  item : Option Id := none
  deck : Option String := none
  reveals : List Id := []
  deriving Repr, DecidableEq, Inhabited

inductive AssertKind where
  | present
  | absent
  deriving Repr, DecidableEq, Inhabited

def AssertKind.render : AssertKind → String
  | .present => "present"
  | .absent => "absent"

structure Assertion where
  id : Id
  kind : AssertKind
  location : Id
  time : Time
  characters : List Id
  deriving Repr, DecidableEq, Inhabited

structure Handout where
  character : Id
  location : Option Id := none
  items : Option (List Id) := none
  knows : Option (List Id) := none
  deriving Repr, DecidableEq, Inhabited

structure Board where
  location : Id
  items : List Id
  deriving Repr, DecidableEq, Inhabited

structure Goal where
  id : Id
  owner : Id
  requiresItems : List Id := []
  deriving Repr, DecidableEq, Inhabited

structure Choice where
  id : Id
  owner : Id
  /-- `none` なら真偽値の選択 -/
  values : Option (List String) := none
  deriving Repr, DecidableEq, Inhabited

/-- 論理式 (§1.9)。 -/
inductive Formula where
  | const (b : Bool)
  | var (v : Id)
  | eq (v : Id) (value : String)
  | plurality (votes : List Id) (value : String)
  | tie (votes : List Id)
  | not (f : Formula)
  | and (fs : List Formula)
  | or (fs : List Formula)
  deriving Repr, Inhabited

structure Ending where
  id : Id
  condition : Formula
  deriving Repr, Inhabited

structure Scenario where
  startTime : Time
  endTime : Time
  claimTolerance : Nat := 0
  characters : List Character
  areas : List Area := []
  locations : List Location
  travel : List Edge := []
  areaTravel : List Edge := []
  perception : List Edge := []
  placements : List Placement
  items : List Item := []
  facts : List Fact := []
  initialKnowledge : List (Id × Id) := []
  events : List Event := []
  clues : List Clue := []
  solutionFacts : List Id := []
  assertions : List Assertion := []
  handouts : List Handout := []
  board : List Board := []
  goals : List Goal := []
  choices : List Choice := []
  constraints : List Formula := []
  endings : List Ending := []
  deriving Repr, Inhabited

end MurderMystery
