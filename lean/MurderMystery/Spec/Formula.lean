import MurderMystery.Spec.Semantics

/-!
# 論理式と割り当て (docs/spec.md §1.9, §4.7)
-/
namespace MurderMystery

/-- 変数の値: 真偽値、または列挙型の値。 -/
inductive Val where
  | bool (b : Bool)
  | str (s : String)
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev Assignment := Id → Val

/-- 得票数。 -/
def count (vals : List Val) (w : Val) : Nat := (vals.filter (· == w)).length

/-- 最多得票の値(重複なし)。 -/
def winners (vals : List Val) : List Val :=
  let ds := dedup vals
  let m := (ds.map (count vals)).foldl max 0
  ds.filter (fun w => count vals w == m)

def Formula.eval (σ : Assignment) : Formula → Bool
  | .const b => b
  | .var v => match σ v with
    | .bool b => b
    | .str _ => false
  | .eq v x => σ v == .str x
  | .plurality votes x => winners (votes.map σ) == [.str x]
  | .tie votes => (winners (votes.map σ)).length ≥ 2
  | .not f => !f.eval σ
  | .and fs => (fs.attach.map fun ⟨f, _⟩ => f.eval σ).all id
  | .or fs => (fs.attach.map fun ⟨f, _⟩ => f.eval σ).any id

/-- 論理式が参照する変数(R002 / R009 / R012 用)。 -/
inductive VarRef where
  | asBool (v : Id)
  | asEq (v : Id) (value : String)
  | inTally (votes : List Id) (value : Option String)

def Formula.refs : Formula → List VarRef
  | .const _ => []
  | .var v => [.asBool v]
  | .eq v x => [.asEq v x]
  | .plurality vs x => [.inTally vs (some x)]
  | .tie vs => [.inTally vs none]
  | .not f => f.refs
  | .and fs => (fs.attach.map fun ⟨f, _⟩ => f.refs).flatten
  | .or fs => (fs.attach.map fun ⟨f, _⟩ => f.refs).flatten

/-! ## 変数・定義域・数え上げ -/

/-- 変数 ID と定義域(定義域内の順序つき)。V は ID 昇順。 -/
def Scenario.domains (s : Scenario) : List (Id × List Val) :=
  let gs := s.goals.map fun g => (g.id, [Val.bool false, .bool true])
  let cs := s.choices.map fun c => match c.values with
    | none => (c.id, [Val.bool false, .bool true])
    | some vs => (c.id, (vs.mergeSort (fun a b => decide (a ≤ b))).map Val.str)
  (gs ++ cs).mergeSort (fun a b => decide (a.1 ≤ b.1))

/-- 定義域の直積を、割り当ての順序(定義域内の位置の辞書式順序)で列挙する。 -/
def enumerate : List (List Val) → List (List Val)
  | [] => [[]]
  | d :: ds => d.flatMap fun x => (enumerate ds).map (x :: ·)

def toAssignment (vars : List Id) (vals : List Val) : Assignment :=
  fun v => match (vars.zip vals).find? (·.1 == v) with
    | some (_, x) => x
    | none => .bool false

end MurderMystery
