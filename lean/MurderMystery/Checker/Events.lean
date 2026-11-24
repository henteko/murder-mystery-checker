import MurderMystery.Checker.R

/-!
# イベントごとの検査: T / I / K 群 (docs/spec.md §4.2〜§4.4)

各ステップ(処理前の状態 S、イベント e、それより前のイベント)に対して評価する。
ここでの検査はすべて error で、検出結果の event はそのイベントの ID になる。
そのため各検査は (コード, args) の組を返し、`checkEvents` でまとめて `Diag` にする。
-/
namespace MurderMystery

abbrev Issue := String × List String

/-- 正規順序で e より前にある同時刻のイベントのうち、条件を満たす最後のもの。 -/
def lastSameTime (st : Step) (p : Event → Bool) : Option Event :=
  (st.earlier.filter fun e' => e'.time == st.ev.time && p e').getLast?

def issuesT001 (s : Scenario) (st : Step) : List Issue :=
  let e := st.ev
  let late := match e.kind with
    | .move _ _ arr _ _ => decide (arr > s.endTime)
    | _ => false
  if e.time < s.startTime || e.time > s.endTime || late then [("T001", [])] else []

def issuesMove (s : Scenario) (st : Step) : List Issue :=
  let S := st.pre
  let e := st.ev
  match e.kind with
  | .move c to arr mode _ =>
    let frm := (S.pos c).dest
    if frm == to then [("T004", [c, frm])]
    else if mode != "walk" then []
    else match s.travelTime frm to with
      | none => [("T002", [c, frm, to])]
      | some m => if arr - e.time < m then [("T003", [c, frm, to, toString m])] else []
  | _ => []

def issuesT005 (st : Step) (c : Id) : List Issue :=
  match lastSameTime st (fun e' => e'.kind.participants.contains c) with
  | some e' => [("T005", [c, e'.id])]
  | none => []

def issuesT006 (st : Step) (c : Id) : List Issue :=
  if st.pre.inTransit c st.ev.time then [("T006", [c, (st.pre.pos c).via.getD ""])] else []

def issuesT010 (st : Step) (c : Id) : List Issue :=
  match st.pre.dead c with
  | some d => [("T010", [c, d])]
  | none => []

def issuesParticipant (st : Step) (c : Id) : List Issue :=
  issuesT005 st c ++ issuesT006 st c ++ issuesT010 st c

def issuesParticipants (st : Step) : List Issue := st.ev.kind.participants.flatMap (issuesParticipant st)

/-- 場所の条件。参加者は移動中なら抑制、参加者でない (targets) は移動中なら "transit"。 -/
def atLoc (S : State) (t : Time) (c loc : Id) (participant : Bool) : List Issue :=
  if S.inTransit c t then (if participant then [] else [("T007", [c, loc, "transit"])])
  else if (S.pos c).dest != loc then [("T007", [c, loc, (S.pos c).dest])]
  else []

def issuesPlace (s : Scenario) (st : Step) : List Issue :=
  let S := st.pre
  let t := st.ev.time
  match st.ev.kind with
  | .scene l ps _ => ps.flatMap fun c => atLoc S t c l true
  | .observe c l tl ts _ =>
    (if s.perceives l tl then [] else [("T011", [c, l, tl])])
    ++ atLoc S t c l true ++ ts.flatMap fun x => atLoc S t x tl false
  | .transfer a b _ | .tell a b _ =>
    if !S.inTransit a t && !S.inTransit b t && (S.pos a).dest != (S.pos b).dest then
      [("T008", [a, b, (S.pos a).dest, (S.pos b).dest])]
    else []
  | _ => []

/-- アイテムを扱うイベントの所持者(transfer は from)。 -/
def EventKind.holderRole : EventKind → Id
  | .transfer a .. => a
  | .pickup c _ | .drop c _ | .use c _ | .consume c _ => c
  | _ => ""

def EventKind.isPickup : EventKind → Bool
  | .pickup .. => true
  | _ => false

def issuesI004 (st : Step) (i : Id) : List Issue :=
  match lastSameTime st (fun e' => e'.kind.item? == some i) with
  | some e' => [("I004", [i, e'.id])]
  | none => []

def issuesItem (st : Step) : List Issue :=
  let S := st.pre
  let e := st.ev
  match e.kind.item? with
  | none => []
  | some i =>
    let i004 := issuesI004 st i
    let who := e.kind.holderRole
    let h := S.holder i
    let rest :=
      if h == .consumed then [("I002", [who, i])]
      else if e.kind.isPickup then
        if !S.inTransit who e.time && h != .place (S.pos who).dest then [("I003", [who, i, h.render])] else []
      else if h != .char who then [("I001", [who, i, h.render])] else []
    i004 ++ rest

def issuesKnowledge (st : Step) : List Issue :=
  let S := st.pre
  let e := st.ev
  let k001 := match e.kind with
    | .tell a _ fs => fs.filterMap fun f => if S.knows a f then none else some ("K001", [a, f])
    | _ => []
  let k002 := e.kind.actors.flatMap fun a =>
    e.requires.filterMap fun f => if S.knows a f then none else some ("K002", [a, f])
  k001 ++ k002

def stepIssues (s : Scenario) (st : Step) : List Issue :=
  issuesT001 s st ++ issuesMove s st ++ issuesParticipants st ++ issuesPlace s st ++ issuesItem st
    ++ issuesKnowledge st

def checkEvents (s : Scenario) : List Diag :=
  s.trace.flatMap fun st => (stepIssues s st).map fun (c, a) => err c a (some st.ev.id)

end MurderMystery
