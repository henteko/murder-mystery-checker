import MurderMystery.Checker.Check
import MurderMystery.Proofs.G

/-!
# 正しさの宣言的な定義 (docs/spec.md §5)

各 error 規則の「違反がない」ことを、判定関数とは独立に命題として書く。
判定器が error を1件も出さないこと ⇔ `Valid s` は `Proofs/Main.lean` で証明する。
-/
namespace MurderMystery

/-! ## イベントごとの規則 (§4.2〜§4.4) -/

/-- move の到着時刻。 -/
def EventKind.arrive? : EventKind → Option Time
  | .move _ _ arr _ _ => some arr
  | _ => none

/-- T001: 時刻が範囲内。 -/
def T001Ok (s : Scenario) (st : Step) : Prop :=
  s.startTime ≤ st.ev.time ∧ st.ev.time ≤ s.endTime ∧
  ∀ arr, st.ev.kind.arrive? = some arr → arr ≤ s.endTime

/-- T002〜T004: 移動元と行き先が異なり、徒歩なら経路があり移動時間が足りている。 -/
def MoveOk (s : Scenario) (st : Step) : Prop :=
  ∀ c to arr m f, st.ev.kind = .move c to arr m f →
    (st.pre.pos c).dest ≠ to ∧
    (m = "walk" → ∃ t, s.travelTime (st.pre.pos c).dest to = some t ∧ t ≤ arr - st.ev.time)

/-- T005 / T006 / T010: 参加者は同時刻に他のイベントに参加せず、移動中でもなく、生きている。 -/
def ParticipantsOk (st : Step) : Prop :=
  ∀ c ∈ st.ev.kind.participants,
    (∀ e' ∈ st.earlier, e'.time = st.ev.time → c ∉ e'.kind.participants) ∧
    st.pre.inTransit c st.ev.time = false ∧
    st.pre.dead c = none

/-- T007 / T008 / T011: 場所の条件と知覚。 -/
def PlaceOk (s : Scenario) (st : Step) : Prop :=
  let S := st.pre
  let t := st.ev.time
  (∀ l ps rv, st.ev.kind = .scene l ps rv →
    ∀ c ∈ ps, S.inTransit c t = false → (S.pos c).dest = l) ∧
  (∀ c l tl ts fs, st.ev.kind = .observe c l tl ts fs →
    s.perceives l tl = true ∧
    (S.inTransit c t = false → (S.pos c).dest = l) ∧
    ∀ x ∈ ts, S.inTransit x t = false ∧ (S.pos x).dest = tl) ∧
  (∀ a b i, st.ev.kind = .transfer a b i →
    S.inTransit a t = false → S.inTransit b t = false → (S.pos a).dest = (S.pos b).dest) ∧
  (∀ a b fs, st.ev.kind = .tell a b fs →
    S.inTransit a t = false → S.inTransit b t = false → (S.pos a).dest = (S.pos b).dest)

/-- I001〜I004: アイテムを扱うイベント。 -/
def ItemOk (st : Step) : Prop :=
  let S := st.pre
  let who := st.ev.kind.holderRole
  ∀ i, st.ev.kind.item? = some i →
    (∀ e' ∈ st.earlier, e'.time = st.ev.time → e'.kind.item? ≠ some i) ∧
    S.holder i ≠ .consumed ∧
    (st.ev.kind.isPickup = true → S.inTransit who st.ev.time = false → S.holder i = .place (S.pos who).dest) ∧
    (st.ev.kind.isPickup = false → S.holder i = .char who)

/-- K001 / K002: 伝える知識・行動に必要な知識を知っている。 -/
def KnowledgeOk (st : Step) : Prop :=
  (∀ a b fs, st.ev.kind = .tell a b fs → ∀ f ∈ fs, st.pre.knows a f = true) ∧
  ∀ a ∈ st.ev.kind.actors, ∀ f ∈ st.ev.requires, st.pre.knows a f = true

def StepValid (s : Scenario) (st : Step) : Prop :=
  T001Ok s st ∧ MoveOk s st ∧ ParticipantsOk st ∧ PlaceOk s st ∧ ItemOk st ∧ KnowledgeOk st

/-! ## 終了状態・区間に対する規則 (§4.4〜§4.6) -/

/-- 探索の回 rs で、手がかりからしか手に入らない真相の知識をすべて明かす手がかりを引ける:
    (回の番号, カード) の組の列 ps で、各カードはその回で引けるもの、回 i で引くのは caps[i] 枚以内、
    合計は D 枚以内、真相の知識はどれも ps のどれかのカードが明かす。 -/
def Scenario.CanDraw (s : Scenario) (rs : List Round) : Prop :=
  ∃ ps : List (Nat × Clue), (∀ p ∈ ps, p.2 ∈ (s.pools rs).getD p.1 []) ∧ ps.length ≤ s.draws rs ∧
    (∀ i, ps.countP (·.1 == i) ≤ (s.caps rs).getD i 0) ∧ ∀ f ∈ s.clueOnly, ∃ p ∈ ps, f ∈ p.2.reveals

def PostValid (s : Scenario) : Prop :=
  let E := s.final
  -- K003: 真相に必要な知識は入手可能
  (∀ f ∈ s.solutionFacts, s.obtainable f = true) ∧
  -- K004 / K005: 手がかりのアイテムは失われておらず、宣言した場所にある
  (∀ c ∈ s.clues, ∀ i, c.item = some i →
    E.holder i ≠ .consumed ∧ ∀ l, c.location = some l → E.holder i = .place l) ∧
  -- K006: 誰かが持つ偽の知識は、否定する知識が入手可能
  (∀ f ∈ s.facts, f.truth = false → s.held f.id = true → ∃ r ∈ f.contradictedBy, s.obtainable r = true) ∧
  -- K007: 真相は真の知識だけに依存する
  (∀ f ∈ s.solutionFacts, ∀ fact, s.findFact? f = some fact → fact.truth = true) ∧
  -- K008: 真の証言の時刻は許容誤差内
  (∀ f ∈ s.facts, f.truth = true → ∀ eid claimed e,
    f.aboutEvent = some eid → f.claimedAt = some claimed → s.findEvent? eid = some e →
    absDiff claimed (f.actualTime e) ≤ f.tolerance.getD s.claimTolerance) ∧
  -- H001 / H002 / H004: ハンドアウトの宣言は終了状態と一致する
  (∀ h ∈ s.handouts,
    (∀ l, h.location = some l → (E.pos h.character).dest = l) ∧
    (∀ is, h.items = some is → ∀ i ∈ is, E.holder i = .char h.character) ∧
    (∀ ks, h.knows = some ks → ∀ f ∈ ks, E.knows h.character f = true)) ∧
  -- H006: 盤面の宣言は終了状態と一致する
  (∀ b ∈ s.board, ∀ i ∈ b.items, E.holder i = .place b.location) ∧
  -- A001: 真相の断言はタイムラインと一致する
  (∀ a ∈ s.assertions, ∀ c ∈ a.characters, a.kind.violated (s.whereAt c a.time) a.location = false) ∧
  -- K010: 探索で引ける枚数の手がかりで、手がかりからしか手に入らない真相の知識をすべて明かせる
  (∀ rs, s.exploration = some rs → s.CanDraw rs)

/-! ## G 群 (§4.7) -/

/-- パターン: 定義域に従い実効制約を満たす割り当て。 -/
def Scenario.IsPattern (s : Scenario) (p : List Val) : Prop := WellTyped s.gDoms p ∧ s.satisfies p = true

def GValid (s : Scenario) : Prop :=
  -- G007: 数え上げの上限内
  s.gCount ≤ gLimit ∧
  -- G005: パターンが存在する
  (∃ p, s.IsPattern p) ∧
  -- G001 / G002: すべてのパターンでエンディングがちょうど1つ
  (∀ p, s.IsPattern p →
    (s.sortedEndings.filter fun e => e.condition.eval (toAssignment s.gVars p)).length = 1) ∧
  -- G003: どのエンディングにも到達できる
  (∀ e ∈ s.sortedEndings, ∃ p, s.IsPattern p ∧ e.condition.eval (toAssignment s.gVars p) = true) ∧
  -- G004: どのゴールも達成できる
  (∀ g ∈ s.goals, ∃ p, s.IsPattern p ∧ toAssignment s.gVars p g.id = .bool true)

/-! ## 全体 -/

/-- シナリオが正しい: 構造が正しく(R 群)、全イベント・終了状態・G 群の error 規則に違反しない。 -/
def Valid (s : Scenario) : Prop :=
  checkR s = [] ∧ (∀ st ∈ s.trace, StepValid s st) ∧ PostValid s ∧ GValid s

end MurderMystery
