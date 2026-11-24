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

/-- 辞書式の < (短い方が接頭辞なら短い方が先)。 -/
def lexLt [LT α] [DecidableRel (α := α) (· < ·)] [DecidableEq α] : List α → List α → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then lexLt as bs else decide (a < b)

/-- §6.3 の正規順序の < 。 -/
def Diag.lt (a b : Diag) : Bool :=
  if a.code ≠ b.code then decide (a.code < b.code)
  else if a.event.getD "" ≠ b.event.getD "" then decide (a.event.getD "" < b.event.getD "")
  else if a.args ≠ b.args then lexLt a.args b.args
  else lexLt a.wkey b.wkey

def Diag.le (a b : Diag) : Bool := !b.lt a

/-- 整列済みの列から、隣り合う重複を除く。 -/
def dedupSorted [DecidableEq α] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: rest => if x = y then dedupSorted (y :: rest) else x :: dedupSorted (y :: rest)

def normalize (ds : List Diag) : List Diag := dedupSorted (ds.mergeSort Diag.le)

end MurderMystery
