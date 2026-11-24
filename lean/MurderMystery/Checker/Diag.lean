import MurderMystery.Spec.Formula

/-!
# 検出結果 (docs/spec.md §6)
-/
namespace MurderMystery

inductive Sev where
  | error
  | warning
  deriving Repr, DecidableEq, Inhabited

structure Diag where
  code : String
  sev : Sev
  event : Option Id := none
  args : List String := []
  /-- G001 / G002 の witness(V の ID 昇順) -/
  witness : Option (List (Id × Val)) := none
  /-- witness の並べ替えキー(定義域内の位置)。出力には含めない -/
  wkey : List Nat := []
  deriving Repr, DecidableEq, Inhabited

def err (code : String) (args : List String) (event : Option Id := none) : Diag :=
  { code, sev := .error, event, args }

def warn (code : String) (args : List String) (event : Option Id := none) : Diag :=
  { code, sev := .warning, event, args }

/-! ## 比較関数

すべて Bool 値の狭義の < 。`Proofs/Order.lean` で狭義全順序であることを示す。 -/

def strLt (a b : String) : Bool := decide (a < b)

def natLt (a b : Nat) : Bool := decide (a < b)

/-- 辞書式の < (短い方が接頭辞なら短い方が先)。 -/
def lexLt [DecidableEq α] (lt : α → α → Bool) : List α → List α → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then lexLt lt as bs else lt a b

/-- none が最小。 -/
def optLt (lt : α → α → Bool) : Option α → Option α → Bool
  | none, none => false
  | none, some _ => true
  | some _, none => false
  | some a, some b => lt a b

/-- 組の辞書式の < 。 -/
def pairLt [DecidableEq α] (lt₁ : α → α → Bool) (lt₂ : β → β → Bool) (a b : α × β) : Bool :=
  if a.1 = b.1 then lt₂ a.2 b.2 else lt₁ a.1 b.1

/-- error が先。 -/
def sevLt : Sev → Sev → Bool
  | .error, .warning => true
  | _, _ => false

/-- 真偽値が先(false, true の順)、次に文字列。 -/
def valLt : Val → Val → Bool
  | .bool false, .bool true => true
  | .bool _, .str _ => true
  | .str a, .str b => strLt a b
  | _, _ => false

/-- §6.3 の正規順序のキー: (code, event, args, witness の位置, severity, witness)。
後ろの2つは全順序にするためのもので、通常は前の4つで決まる。 -/
abbrev DiagKey := String × Option Id × List String × List Nat × Sev × Option (List (Id × Val))

def Diag.key (d : Diag) : DiagKey := (d.code, d.event, d.args, d.wkey, d.sev, d.witness)

def keyLt : DiagKey → DiagKey → Bool :=
  pairLt strLt <| pairLt (optLt strLt) <| pairLt (lexLt strLt) <| pairLt (lexLt natLt) <|
    pairLt sevLt (optLt (lexLt (pairLt strLt valLt)))

/-- §6.3 の正規順序の < 。 -/
def Diag.lt (a b : Diag) : Bool := keyLt a.key b.key

def Diag.le (a b : Diag) : Bool := !b.lt a

/-- 整列済みの列から、隣り合う重複を除く。 -/
def dedupSorted [DecidableEq α] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedupSorted (y :: rest) else x :: dedupSorted (y :: rest)

def normalize (ds : List Diag) : List Diag := dedupSorted (ds.mergeSort Diag.le)

end MurderMystery
