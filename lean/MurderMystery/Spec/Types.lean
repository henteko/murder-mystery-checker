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
  /-- 静的なタグ(イベントで変わらない) -/
  tags : List String := []
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

/-- 論理式 (§1.9)。 -/
inductive Formula where
  | const (b : Bool)
  | var (v : Id)
  | eq (v : Id) (value : String)
  | plurality (votes : List Id) (value : String)
  | tie (votes : List Id)
  /-- 知識 f が真か。値 b は入力の読み込み時に facts から決める(§1.9) -/
  | truth (f : Id) (b : Bool)
  | not (f : Formula)
  | and (fs : List Formula)
  | or (fs : List Formula)
  deriving Repr, Inhabited

mutual
/-- Formula の決定可能な等号(入れ子の帰納型なので手で書く)。 -/
def Formula.decEq : (a b : Formula) → Decidable (a = b)
  | .const x, .const y => if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .var x, .var y => if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .eq x v, .eq y w =>
    if h : x = y ∧ v = w then isTrue (by rw [h.1, h.2]) else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
  | .plurality x v, .plurality y w =>
    if h : x = y ∧ v = w then isTrue (by rw [h.1, h.2]) else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
  | .tie x, .tie y => if h : x = y then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .truth x v, .truth y w =>
    if h : x = y ∧ v = w then isTrue (by rw [h.1, h.2]) else isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)
  | .not f, .not g => match Formula.decEq f g with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .and fs, .and gs => match Formula.decEqList fs gs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .or fs, .or gs => match Formula.decEqList fs gs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .const _, .var _ | .const _, .eq _ _ | .const _, .plurality _ _
  | .const _, .tie _ | .const _, .truth _ _ | .const _, .not _
  | .const _, .and _ | .const _, .or _ | .var _, .const _
  | .var _, .eq _ _ | .var _, .plurality _ _ | .var _, .tie _
  | .var _, .truth _ _ | .var _, .not _ | .var _, .and _
  | .var _, .or _ | .eq _ _, .const _ | .eq _ _, .var _
  | .eq _ _, .plurality _ _ | .eq _ _, .tie _ | .eq _ _, .truth _ _
  | .eq _ _, .not _ | .eq _ _, .and _ | .eq _ _, .or _
  | .plurality _ _, .const _ | .plurality _ _, .var _ | .plurality _ _, .eq _ _
  | .plurality _ _, .tie _ | .plurality _ _, .truth _ _ | .plurality _ _, .not _
  | .plurality _ _, .and _ | .plurality _ _, .or _ | .tie _, .const _
  | .tie _, .var _ | .tie _, .eq _ _ | .tie _, .plurality _ _
  | .tie _, .truth _ _ | .tie _, .not _ | .tie _, .and _
  | .tie _, .or _ | .truth _ _, .const _ | .truth _ _, .var _
  | .truth _ _, .eq _ _ | .truth _ _, .plurality _ _ | .truth _ _, .tie _
  | .truth _ _, .not _ | .truth _ _, .and _ | .truth _ _, .or _
  | .not _, .const _ | .not _, .var _ | .not _, .eq _ _
  | .not _, .plurality _ _ | .not _, .tie _ | .not _, .truth _ _
  | .not _, .and _ | .not _, .or _ | .and _, .const _
  | .and _, .var _ | .and _, .eq _ _ | .and _, .plurality _ _
  | .and _, .tie _ | .and _, .truth _ _ | .and _, .not _
  | .and _, .or _ | .or _, .const _ | .or _, .var _
  | .or _, .eq _ _ | .or _, .plurality _ _ | .or _, .tie _
  | .or _, .truth _ _ | .or _, .not _ | .or _, .and _ => isFalse (by intro e; cases e)

def Formula.decEqList : (a b : List Formula) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | f :: fs, g :: gs => match Formula.decEq f g, Formula.decEqList fs gs with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
end

instance : DecidableEq Formula := Formula.decEq

structure Goal where
  id : Id
  owner : Id
  requiresItems : List Id := []
  /-- 終了時に入手可能でなければならない知識 -/
  requiresKnowledge : List Id := []
  /-- タグ t のアイテムを k 個以上、終了時に owner が持つ(必要条件) -/
  requiresTagged : List (String × Nat) := []
  /-- ほかのプレイヤーに知られてはいけない知識 -/
  conceals : List Id := []
  /-- 達成条件(ゴールが真 ⇔ この式が真) -/
  condition : Option Formula := none
  deriving Repr, DecidableEq, Inhabited

structure Choice where
  id : Id
  owner : Id
  /-- `none` なら真偽値の選択 -/
  values : Option (List String) := none
  deriving Repr, DecidableEq, Inhabited

structure Ending where
  id : Id
  condition : Formula
  deriving Repr, Inhabited

/-- 探索フェイズの 1 回(§1.10)。 -/
structure Round where
  /-- この回に1人が引く探索カードの枚数 -/
  draws : Nat
  /-- この回に引ける探索カードの ID。`none` ならすべて -/
  clues : Option (List Id) := none
  deriving Repr, DecidableEq, Inhabited

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
  /-- 探索フェイズの回(§1.10)。`draws_per_player: n` は `[{draws := n}]` -/
  exploration : Option (List Round) := none
  deriving Repr, Inhabited

end MurderMystery
