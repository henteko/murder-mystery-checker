import MurderMystery.Checker.Post

/-!
# G 群: ゴール・選択・エンディング (docs/spec.md §4.7)
-/
namespace MurderMystery

/-- a ⇔ b。 -/
def Formula.iff (a b : Formula) : Formula := .or [.and [a, b], .and [.not a, .not b]]

/-- 導出制約 1, 2: requires_items から (§4.7)。 -/
def Scenario.itemConstraints (s : Scenario) : List Formula :=
  let E := s.final
  let lost := s.goals.filterMap fun g =>
    if g.requiresItems.any (fun i => E.holder i == .consumed) then some (Formula.not (.var g.id)) else none
  let gs := s.goals.mergeSort (fun a b => decide (a.id ≤ b.id))
  let clash := (pairs gs).filterMap fun (g₁, g₂) =>
    if g₁.owner != g₂.owner && g₁.requiresItems.any g₂.requiresItems.contains then
      some (Formula.not (.and [.var g₁.id, .var g₂.id]))
    else none
  lost ++ clash

/-- 導出制約 3: requires_knowledge に入手可能でない知識があるゴールは達成できない (§4.7)。 -/
def Scenario.knowledgeConstraints (s : Scenario) : List Formula :=
  s.goals.filterMap fun g =>
    if g.requiresKnowledge.any (fun f => !s.obtainable f) then some (Formula.not (.var g.id)) else none

/-- 導出制約 4: ゴールが真 ⇔ condition (§4.7)。 -/
def Scenario.conditionConstraints (s : Scenario) : List Formula :=
  s.goals.filterMap fun g => g.condition.map (Formula.iff (.var g.id))

/-- ゴールの要求: アイテムの条件と個数。requires_items の i は (id = i, 1)、requires_tagged は (タグ t, k)。 -/
def Goal.demands (g : Goal) : List ((Item → Bool) × Nat) :=
  g.requiresItems.map (fun i => (fun it => it.id == i, 1)) ++
  g.requiresTagged.map (fun (t, k) => (fun it => it.tags.contains t, k))

/-- 条件 p を満たし、終了時に使い切られていないアイテムの数。 -/
def Scenario.avail (s : Scenario) (p : Item → Bool) : Nat :=
  (s.items.filter fun it => p it && s.final.holder it.id != .consumed).length

/-- 導出制約 5, 6: requires_tagged から(必要条件)(§4.7)。 -/
def Scenario.tagConstraints (s : Scenario) : List Formula :=
  let single := s.goals.filterMap fun g =>
    if g.requiresTagged.any (fun (t, k) => s.avail (fun it => it.tags.contains t) < k) then
      some (Formula.not (.var g.id)) else none
  let gs := s.goals.mergeSort (fun a b => decide (a.id ≤ b.id))
  let pair := (pairs gs).filterMap fun (g₁, g₂) =>
    if g₁.owner != g₂.owner && (!g₁.requiresTagged.isEmpty || !g₂.requiresTagged.isEmpty) &&
        g₁.demands.any (fun (p₁, k₁) => g₂.demands.any fun (p₂, k₂) =>
          s.avail (fun it => p₁ it || p₂ it) < k₁ + k₂) then
      some (Formula.not (.and [.var g₁.id, .var g₂.id]))
    else none
  single ++ pair

/-- ほかのプレイヤー(NPC と owner 以外)が終了時に知っている。 -/
def Scenario.exposed (s : Scenario) (owner f : Id) : Bool :=
  s.characters.any fun c => !c.npc && c.id != owner && s.final.knows c.id f

/-- 導出制約 7: conceals の知識がすでにほかのプレイヤーに知られているゴールは達成できない (§4.7)。 -/
def Scenario.concealConstraints (s : Scenario) : List Formula :=
  s.goals.filterMap fun g =>
    if g.conceals.any (fun f => s.exposed g.owner f) then some (Formula.not (.var g.id)) else none

/-- 導出制約 (§4.7)。 -/
def Scenario.derivedConstraints (s : Scenario) : List Formula :=
  s.itemConstraints ++ s.knowledgeConstraints ++ s.conditionConstraints ++ s.tagConstraints
    ++ s.concealConstraints

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

def Scenario.sortedEndings (s : Scenario) : List Ending :=
  s.endings.mergeSort (fun a b => decide (a.id ≤ b.id))

/-- エンディング e がパターン p で成り立つか。 -/
def GCtx.holds (g : GCtx) (e : Ending) (p : List Val) : Bool := e.condition.eval (g.σ p)

/-- G001: 網羅性の違反(最小の反例1件)。 -/
def checkG001 (s : Scenario) (g : GCtx) : List Diag :=
  match g.pats.find? (fun p => s.sortedEndings.all fun e => !g.holds e p) with
  | some p => [g.witness p (err "G001" [])]
  | none => []

/-- G002: 排他性の違反(エンディングの組ごとに最小の反例)。 -/
def checkG002 (s : Scenario) (g : GCtx) : List Diag :=
  (pairs s.sortedEndings).filterMap fun (e₁, e₂) =>
    match g.pats.find? (fun p => g.holds e₁ p && g.holds e₂ p) with
    | some p => some (g.witness p (err "G002" [e₁.id, e₂.id]))
    | none => none

/-- G003 / G004 / G006 / G009。 -/
def checkGRest (s : Scenario) (g : GCtx) : List Diag :=
  let ends := s.sortedEndings
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
  g003 ++ g46 ++ gc

def checkGPatterns (s : Scenario) (g : GCtx) : List Diag :=
  checkG001 s g ++ checkG002 s g ++ checkGRest s g

def Scenario.gVars (s : Scenario) : List Id := s.domains.map (·.1)
def Scenario.gDoms (s : Scenario) : List (List Val) := s.domains.map (·.2)
/-- 割り当ての総数 N。 -/
def Scenario.gCount (s : Scenario) : Nat := (s.gDoms.map List.length).foldl (· * ·) 1
/-- 割り当て vals が実効制約を満たすか。 -/
def Scenario.satisfies (s : Scenario) (vals : List Val) : Bool :=
  s.effectiveConstraints.all fun c => c.eval (toAssignment s.gVars vals)
/-- 実効制約 cs を満たす割り当てだけを残す。cs は引数として一度だけ評価される(実行時間のため)。 -/
@[noinline] def filterPats (cs : List Formula) (vars : List Id) (pats : List (List Val)) : List (List Val) :=
  pats.filter fun vals => cs.all fun c => c.eval (toAssignment vars vals)
def Scenario.gctx (s : Scenario) : GCtx :=
  ⟨s.gVars, s.gDoms, filterPats s.effectiveConstraints s.gVars (enumerate s.gDoms)⟩

theorem Scenario.gctx_eq (s : Scenario) : s.gctx = ⟨s.gVars, s.gDoms, (enumerate s.gDoms).filter s.satisfies⟩ := rfl

def checkG (s : Scenario) : List Diag :=
  let body :=
    if s.gCount > gLimit then [err "G007" [toString s.gCount]]
    else if s.gctx.pats.isEmpty then [err "G005" []]
    else checkGPatterns s s.gctx
  body ++ checkG008 s

end MurderMystery
