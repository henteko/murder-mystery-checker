import MurderMystery.Checker.R

/-!
# イベントごとの検査: T / I / K 群 (docs/spec.md §4.2〜§4.4)

各ステップ(処理前の状態 S、イベント e、それより前のイベント)に対して評価する。
-/
namespace MurderMystery

/-- 正規順序で e より前にある同時刻のイベントのうち、条件を満たす最後のもの。 -/
def lastSameTime (st : Step) (p : Event → Bool) : Option Event :=
  (st.earlier.filter fun e' => e'.time == st.ev.time && p e').getLast?

def renderWhere (S : State) (c : Id) (t : Time) : String :=
  if S.inTransit c t then "transit" else (S.pos c).dest

def checkT001 (s : Scenario) (st : Step) : List Diag :=
  let e := st.ev
  let late := match e.kind with
    | .move _ _ arr _ _ => decide (arr > s.endTime)
    | _ => false
  if e.time < s.startTime || e.time > s.endTime || late then [err "T001" [] (some e.id)] else []

def checkMove (s : Scenario) (st : Step) : List Diag :=
  let S := st.pre
  let e := st.ev
  match e.kind with
  | .move c to arr mode _ =>
    let frm := (S.pos c).dest
    if frm == to then [err "T004" [c, frm] (some e.id)]
    else if mode != "walk" then []
    else match s.travelTime frm to with
      | none => [err "T002" [c, frm, to] (some e.id)]
      | some m => if arr - e.time < m then [err "T003" [c, frm, to, toString m] (some e.id)] else []
  | _ => []

def checkParticipants (st : Step) : List Diag :=
  let S := st.pre
  let e := st.ev
  e.kind.participants.flatMap fun c =>
    (match lastSameTime st (fun e' => e'.kind.participants.contains c) with
      | some e' => [err "T005" [c, e'.id] (some e.id)]
      | none => [])
    ++ (if S.inTransit c e.time then [err "T006" [c, (S.pos c).via.getD ""] (some e.id)] else [])
    ++ (match S.dead c with
      | some d => [err "T010" [c, d] (some e.id)]
      | none => [])

def checkPlace (s : Scenario) (st : Step) : List Diag :=
  let S := st.pre
  let e := st.ev
  let t := e.time
  -- 参加者: 移動中なら抑制。参加者でない (targets): 移動中なら "transit"。
  let atLoc (c loc : Id) (participant : Bool) : List Diag :=
    if S.inTransit c t then (if participant then [] else [err "T007" [c, loc, "transit"] (some e.id)])
    else if (S.pos c).dest != loc then [err "T007" [c, loc, (S.pos c).dest] (some e.id)]
    else []
  match e.kind with
  | .scene l ps _ => ps.flatMap fun c => atLoc c l true
  | .observe c l tl ts _ =>
    (if s.perceives l tl then [] else [err "T011" [c, l, tl] (some e.id)])
    ++ atLoc c l true ++ ts.flatMap fun x => atLoc x tl false
  | .transfer a b _ | .tell a b _ =>
    if !S.inTransit a t && !S.inTransit b t && (S.pos a).dest != (S.pos b).dest then
      [err "T008" [a, b, (S.pos a).dest, (S.pos b).dest] (some e.id)]
    else []
  | _ => []

def checkItem (st : Step) : List Diag :=
  let S := st.pre
  let e := st.ev
  let t := e.time
  match e.kind.item? with
  | none => []
  | some i =>
    let i004 := match lastSameTime st (fun e' => e'.kind.item? == some i) with
      | some e' => [err "I004" [i, e'.id] (some e.id)]
      | none => []
    let who := match e.kind with
      | .transfer a .. => a
      | .pickup c _ | .drop c _ | .use c _ | .consume c _ => c
      | _ => ""
    let h := S.holder i
    let rest :=
      if h == .consumed then [err "I002" [who, i] (some e.id)]
      else match e.kind with
        | .pickup c _ =>
          if !S.inTransit c t && h != .place (S.pos c).dest then [err "I003" [c, i, h.render] (some e.id)] else []
        | _ => if h != .char who then [err "I001" [who, i, h.render] (some e.id)] else []
    i004 ++ rest

def checkKnowledge (st : Step) : List Diag :=
  let S := st.pre
  let e := st.ev
  let k001 := match e.kind with
    | .tell a _ fs => fs.filterMap fun f => if S.knows a f then none else some (err "K001" [a, f] (some e.id))
    | _ => []
  let k002 := e.kind.actors.flatMap fun a =>
    e.requires.filterMap fun f => if S.knows a f then none else some (err "K002" [a, f] (some e.id))
  k001 ++ k002

def checkStep (s : Scenario) (st : Step) : List Diag :=
  checkT001 s st ++ checkMove s st ++ checkParticipants st ++ checkPlace s st ++ checkItem st ++ checkKnowledge st

def checkEvents (s : Scenario) : List Diag := s.trace.flatMap (checkStep s)

end MurderMystery
