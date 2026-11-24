import MurderMystery.Spec.Valid

/-!
# 規則ごとの違反条件 (docs/spec.md §4.2〜§4.7)

R 群以外の error 規則それぞれについて、「その規則の検出結果が出る」条件を判定関数とは独立に命題で書く。
`Proofs/Rules.lean` で、判定器がその規則のコードを出す ⇔ R 群の違反がなく、この条件が成り立つ、を示す。
-/
namespace MurderMystery

/-! ## イベントごとの規則 (§4.2〜§4.4)。st は処理前の状態・イベント・前のイベント -/

section
variable (s : Scenario) (st : Step)

def T001V : Prop :=
  st.ev.time < s.startTime ∨ s.endTime < st.ev.time ∨ ∃ arr, st.ev.kind.arrive? = some arr ∧ s.endTime < arr
def T002V : Prop :=
  ∃ c to arr f, st.ev.kind = .move c to arr "walk" f ∧ (st.pre.pos c).dest ≠ to ∧
    s.travelTime (st.pre.pos c).dest to = none
def T003V : Prop :=
  ∃ c to arr f m, st.ev.kind = .move c to arr "walk" f ∧ (st.pre.pos c).dest ≠ to ∧
    s.travelTime (st.pre.pos c).dest to = some m ∧ arr - st.ev.time < m
def T004V : Prop :=
  ∃ c to arr md f, st.ev.kind = .move c to arr md f ∧ (st.pre.pos c).dest = to
def T005V : Prop :=
  ∃ c ∈ st.ev.kind.participants, ∃ e' ∈ st.earlier, e'.time = st.ev.time ∧ c ∈ e'.kind.participants
def T006V : Prop := ∃ c ∈ st.ev.kind.participants, st.pre.inTransit c st.ev.time = true
def T007V : Prop :=
  (∃ l ps rv, st.ev.kind = .scene l ps rv ∧
    ∃ c ∈ ps, st.pre.inTransit c st.ev.time = false ∧ (st.pre.pos c).dest ≠ l) ∨
  (∃ c l tl ts fs, st.ev.kind = .observe c l tl ts fs ∧
    ((st.pre.inTransit c st.ev.time = false ∧ (st.pre.pos c).dest ≠ l) ∨
      ∃ x ∈ ts, st.pre.inTransit x st.ev.time = true ∨ (st.pre.pos x).dest ≠ tl))
/-- transfer / tell の2人がどちらも移動中でなく、居場所が異なる。 -/
def apart (st : Step) (a b : Id) : Prop :=
  st.pre.inTransit a st.ev.time = false ∧ st.pre.inTransit b st.ev.time = false ∧
    (st.pre.pos a).dest ≠ (st.pre.pos b).dest
def T008V : Prop :=
  (∃ a b i, st.ev.kind = .transfer a b i ∧ apart st a b) ∨ (∃ a b fs, st.ev.kind = .tell a b fs ∧ apart st a b)
def T010V : Prop := ∃ c ∈ st.ev.kind.participants, st.pre.dead c ≠ none
def T011V : Prop := ∃ c l tl ts fs, st.ev.kind = .observe c l tl ts fs ∧ s.perceives l tl = false
def I001V : Prop :=
  ∃ i, st.ev.kind.item? = some i ∧ st.ev.kind.isPickup = false ∧ st.pre.holder i ≠ .consumed ∧
    st.pre.holder i ≠ .char st.ev.kind.holderRole
def I002V : Prop := ∃ i, st.ev.kind.item? = some i ∧ st.pre.holder i = .consumed
def I003V : Prop :=
  ∃ i, st.ev.kind.item? = some i ∧ st.ev.kind.isPickup = true ∧ st.pre.holder i ≠ .consumed ∧
    st.pre.inTransit st.ev.kind.holderRole st.ev.time = false ∧
    st.pre.holder i ≠ .place (st.pre.pos st.ev.kind.holderRole).dest
def I004V : Prop :=
  ∃ i, st.ev.kind.item? = some i ∧ ∃ e' ∈ st.earlier, e'.time = st.ev.time ∧ e'.kind.item? = some i
def K001V : Prop := ∃ a b fs, st.ev.kind = .tell a b fs ∧ ∃ f ∈ fs, st.pre.knows a f = false
def K002V : Prop := ∃ a ∈ st.ev.kind.actors, ∃ f ∈ st.ev.requires, st.pre.knows a f = false

/-- イベントごとの規則 c の違反。 -/
def StepViolates (c : String) : Prop :=
  match c with
  | "T001" => T001V s st | "T002" => T002V s st | "T003" => T003V s st | "T004" => T004V st
  | "T005" => T005V st | "T006" => T006V st | "T007" => T007V st | "T008" => T008V st
  | "T010" => T010V st | "T011" => T011V s st
  | "I001" => I001V st | "I002" => I002V st | "I003" => I003V st | "I004" => I004V st
  | "K001" => K001V st | "K002" => K002V st
  | _ => False

end

/-! ## 終了状態・区間に対する規則 (§4.4〜§4.6) -/

section
variable (s : Scenario)

def PostViolates (c : String) : Prop :=
  let E := s.final
  match c with
  | "K003" => ∃ f ∈ s.solutionFacts, s.obtainable f = false
  | "K004" => ∃ cl ∈ s.clues, ∃ i, cl.item = some i ∧ E.holder i = .consumed
  | "K005" => ∃ cl ∈ s.clues, ∃ i l, cl.item = some i ∧ cl.location = some l ∧
      E.holder i ≠ .consumed ∧ E.holder i ≠ .place l
  | "K006" => ∃ f ∈ s.facts, f.truth = false ∧ s.held f.id = true ∧ ∀ r ∈ f.contradictedBy, s.obtainable r = false
  | "K007" => ∃ f ∈ s.solutionFacts, ∃ fact, s.findFact? f = some fact ∧ fact.truth = false
  | "K008" => ∃ f ∈ s.facts, f.truth = true ∧ ∃ eid claimed e, f.aboutEvent = some eid ∧
      f.claimedAt = some claimed ∧ s.findEvent? eid = some e ∧
      f.tolerance.getD s.claimTolerance < absDiff claimed (f.actualTime e)
  | "H001" => ∃ h ∈ s.handouts, ∃ l, h.location = some l ∧ (E.pos h.character).dest ≠ l
  | "H002" => ∃ h ∈ s.handouts, ∃ is, h.items = some is ∧ ∃ i ∈ is, E.holder i ≠ .char h.character
  | "H004" => ∃ h ∈ s.handouts, ∃ ks, h.knows = some ks ∧ ∃ f ∈ ks, E.knows h.character f = false
  | "H006" => ∃ b ∈ s.board, ∃ i ∈ b.items, E.holder i ≠ .place b.location
  | "A001" => ∃ a ∈ s.assertions, ∃ c ∈ a.characters, a.kind.violated (s.whereAt c a.time) a.location = true
  | "K010" => ∃ n, s.exploration = some n ∧ ¬ s.CanDraw n
  | _ => False

/-! ## G 群 (§4.7) -/

def Scenario.holdsAt (s : Scenario) (e : Ending) (p : List Val) : Bool := e.condition.eval (toAssignment s.gVars p)

def GViolates (c : String) : Prop :=
  match c with
  | "G007" => gLimit < s.gCount
  | "G005" => s.gCount ≤ gLimit ∧ ¬ ∃ p, s.IsPattern p
  | "G001" => s.gCount ≤ gLimit ∧ ∃ p, s.IsPattern p ∧ ∀ e ∈ s.endings, s.holdsAt e p = false
  | "G002" => s.gCount ≤ gLimit ∧ ∃ p, s.IsPattern p ∧
      ∃ e₁ ∈ s.endings, ∃ e₂ ∈ s.endings, e₁.id ≠ e₂.id ∧ s.holdsAt e₁ p = true ∧ s.holdsAt e₂ p = true
  | "G003" => s.gCount ≤ gLimit ∧ (∃ p, s.IsPattern p) ∧
      ∃ e ∈ s.endings, ∀ p, s.IsPattern p → s.holdsAt e p = false
  | "G004" => s.gCount ≤ gLimit ∧ (∃ p, s.IsPattern p) ∧
      ∃ g ∈ s.goals, ∀ p, s.IsPattern p → toAssignment s.gVars p g.id ≠ .bool true
  | _ => False

/-- 規則 c の違反: イベントごと、終了状態、G 群のいずれか。 -/
def Violates (c : String) : Prop :=
  (∃ st ∈ s.trace, StepViolates s st c) ∨ PostViolates s c ∨ GViolates s c

end

/-- R 群以外の error 規則。 -/
def errorCodes : List String :=
  ["T001", "T002", "T003", "T004", "T005", "T006", "T007", "T008", "T010", "T011",
   "I001", "I002", "I003", "I004", "K001", "K002",
   "K003", "K004", "K005", "K006", "K007", "K008", "K010", "H001", "H002", "H004", "H006", "A001",
   "G001", "G002", "G003", "G004", "G005", "G007"]

end MurderMystery
