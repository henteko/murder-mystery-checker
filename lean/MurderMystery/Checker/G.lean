import MurderMystery.Checker.Post

/-!
# G 群: ゴール・選択・エンディング (docs/spec.md §4.7)
-/
namespace MurderMystery

/-- 導出制約 (§4.7)。 -/
def Scenario.derivedConstraints (s : Scenario) : List Formula :=
  let E := s.final
  let lost := s.goals.filterMap fun g =>
    if g.requiresItems.any (fun i => E.holder i == .consumed) then some (Formula.not (.var g.id)) else none
  let gs := s.goals.mergeSort (fun a b => decide (a.id ≤ b.id))
  let clash := (pairs gs).filterMap fun (g₁, g₂) =>
    if g₁.owner != g₂.owner && g₁.requiresItems.any g₂.requiresItems.contains then
      some (Formula.not (.and [.var g₁.id, .var g₂.id]))
    else none
  lost ++ clash

def Scenario.effectiveConstraints (s : Scenario) : List Formula := s.constraints ++ s.derivedConstraints

def gLimit : Nat := 1048576

/-- 定義域内の位置(witness の並べ替えキー)。 -/
def indexIn (d : List Val) (x : Val) : Nat := (d.idxOf x)

structure GCtx where
  vars : List Id
  doms : List (List Val)
  /-- パターン(割り当ての順序どおり) -/
  pats : List (List Val)

def GCtx.σ (g : GCtx) (vals : List Val) : Assignment := toAssignment g.vars vals

def GCtx.witness (g : GCtx) (vals : List Val) (d : Diag) : Diag :=
  { d with witness := some (g.vars.zip vals), wkey := (g.doms.zip vals).map fun (dm, x) => indexIn dm x }

def checkG008 (s : Scenario) : List Diag :=
  s.characters.filterMap fun c =>
    if !c.npc && !s.goals.any (·.owner == c.id) then some (warn "G008" [c.id]) else none

def checkGPatterns (s : Scenario) (g : GCtx) : List Diag :=
  let ends := s.endings.mergeSort (fun a b => decide (a.id ≤ b.id))
  let matched (vals : List Val) : List Id := (ends.filter fun e => e.condition.eval (g.σ vals)).map (·.id)
  let g001 := match g.pats.find? (fun p => (matched p).isEmpty) with
    | some p => [g.witness p (err "G001" [])]
    | none => []
  let g002 := (pairs (ends.map (·.id))).filterMap fun (e₁, e₂) =>
    match g.pats.find? (fun p => let m := matched p; m.contains e₁ && m.contains e₂) with
    | some p => some (g.witness p (err "G002" [e₁, e₂]))
    | none => none
  let g003 := ends.filterMap fun e =>
    if g.pats.any (fun p => e.condition.eval (g.σ p)) then none else some (err "G003" [e.id])
  let valsOf (v : Id) : List Val := g.pats.map fun p => g.σ p v
  let g46 := s.goals.filterMap fun gl =>
    let vs := valsOf gl.id
    if !vs.contains (.bool true) then some (err "G004" [gl.id])
    else if vs.all (· == .bool true) then some (warn "G006" [gl.id]) else none
  let gc := s.choices.flatMap fun c =>
    let vs := dedup (valsOf c.id)
    (if vs.length == 1 then [warn "G006" [c.id]] else [])
    ++ (match c.values with
      | some vals => vals.filterMap fun v => if vs.contains (.str v) then none else some (warn "G009" [c.id, v])
      | none => [])
  g001 ++ g002 ++ g003 ++ g46 ++ gc

def checkG (s : Scenario) : List Diag :=
  let ds := s.domains
  let vars := ds.map (·.1)
  let doms := ds.map (·.2)
  let n := (doms.map List.length).foldl (· * ·) 1
  let body :=
    if n > gLimit then [err "G007" [toString n]]
    else
      let cons := s.effectiveConstraints
      let pats := (enumerate doms).filter fun p => cons.all fun c => c.eval (toAssignment vars p)
      if pats.isEmpty then [err "G005" []]
      else checkGPatterns s ⟨vars, doms, pats⟩
  body ++ checkG008 s

end MurderMystery
