import Lean.Data.Json
import MurderMystery.Checker.Check
import MurderMystery.Spec.Basic

/-!
# 正規化 JSON の入出力 (docs/spec.md §1, §6)

形式の誤り(§6.4 のスキーマエラー)は `Except.error` で返す。
-/
namespace MurderMystery.Json
open Lean (Json)

abbrev P := Except String

def maxTime : Nat := 10000000

def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def req (j : Json) (k : String) : P Json :=
  match field? j k with
  | some v => pure v
  | none => throw s!"missing field '{k}'"

def asStr (k : String) : Json → P String
  | .str s => if s.isEmpty then throw s!"'{k}' must be non-empty" else pure s
  | _ => throw s!"'{k}' must be a string"

/-- 仮数 × 10^(−指数) の末尾の 0 を指数から取り除く(1260.0 → 1260)。 -/
def normNum (m : Int) : Nat → Int × Nat
  | 0 => (m, 0)
  | e + 1 => if m == 0 then (0, 0) else if m % 10 == 0 then normNum (m / 10) e else (m, e + 1)

/-- 値が整数で 0 以上 `maxTime` 以下の数(1260、1260.0、1.26e3 はどれも 1260)。 -/
def asNat (k : String) (j : Json) : P Nat := do
  match j with
  | .num ⟨m, e⟩ =>
    let (m', e') := normNum m e
    if e' != 0 || m' < 0 then throw s!"'{k}' must be a non-negative integer"
    else if m'.toNat ≤ maxTime then pure m'.toNat else throw s!"'{k}' out of range"
  | _ => throw s!"'{k}' must be a non-negative integer"

def asBool (k : String) : Json → P Bool
  | .bool b => pure b
  | _ => throw s!"'{k}' must be a boolean"

def asArr (k : String) : Json → P (List Json)
  | .arr a => pure a.toList
  | _ => throw s!"'{k}' must be an array"

/-- どこにでも置けるキー(メモと説明。検査に使わない)。 -/
def freeKeys : List String := ["note", "name", "text"]

/-- 知らないキーを入力エラーにする(§6.4)。`note`・`name`・`text` と `_` で始まるキーはどこにでも置ける。 -/
def only (j : Json) (ks : List String) : P Unit :=
  match j with
  | .obj kvs =>
    let bad := (kvs.toList.map (fun (p : String × Json) => p.1)).find? fun k =>
      !(ks.contains k || freeKeys.contains k || k.startsWith "_")
    match bad with
    | some k => throw s!"unknown field '{k}'"
    | none => pure ()
  | _ => pure ()


def str (j : Json) (k : String) : P String := do asStr k (← req j k)
def nat (j : Json) (k : String) : P Nat := do asNat k (← req j k)
def strOpt (j : Json) (k : String) : P (Option String) := (field? j k).mapM (asStr k)
def natOpt (j : Json) (k : String) : P (Option Nat) := (field? j k).mapM (asNat k)
def boolD (j : Json) (k : String) (d : Bool) : P Bool := do
  match field? j k with
  | some v => asBool k v
  | none => pure d
def arrD (j : Json) (k : String) : P (List Json) := do
  match field? j k with
  | some v => asArr k v
  | none => pure []
def strs (j : Json) (k : String) : P (List String) := do (← arrD j k).mapM (asStr k)
def strsReq (j : Json) (k : String) : P (List String) := do (← asArr k (← req j k)).mapM (asStr k)
def strsOpt (j : Json) (k : String) : P (Option (List String)) := do
  match field? j k with
  | some v => some <$> (← asArr k v).mapM (asStr k)
  | none => pure none

def parseEdge (withMinutes : Bool) (j : Json) : P Edge := do
  only j (["from", "to", "bidirectional"] ++ if withMinutes then ["minutes"] else [])
  pure { src := ← str j "from", dst := ← str j "to",
         minutes := ← (if withMinutes then nat j "minutes" else pure 0),
         bidirectional := ← boolD j "bidirectional" false }

def parseHolder (j : Json) : P Holder := do
  only j ["character", "location"]
  match field? j "character", field? j "location" with
  | some c, none => .char <$> asStr "character" c
  | none, some l => .place <$> asStr "location" l
  | _, _ => throw "'initial' must have exactly one of 'character' or 'location'"

def parseFact (j : Json) : P Fact := do
  only j (["id", "truth", "contradicted_by", "about", "claimed_at", "tolerance"])
  let (ev, pt) ← match field? j "about" with
    | some a => do only a ["event", "point"]; pure (some (← str a "event"), (← strOpt a "point").getD "at")
    | none => pure (none, "at")
  pure { id := ← str j "id", truth := ← boolD j "truth" true, contradictedBy := ← strs j "contradicted_by",
         aboutEvent := ev, aboutPoint := pt, claimedAt := ← natOpt j "claimed_at",
         tolerance := ← natOpt j "tolerance" }

def parseEvent (j : Json) : P Event := do
  let id ← str j "id"
  let time ← nat j "at"
  let requires ← strs j "requires"
  let only' (ks : List String) := only j (["id", "at", "kind", "requires"] ++ ks)
  let kind ← match ← str j "kind" with
    | "move" => do
      only' ["character", "to", "arrive", "mode", "fatal"]
      pure (EventKind.move (← str j "character") (← str j "to") (← nat j "arrive")
        ((← strOpt j "mode").getD "walk") (← boolD j "fatal" false))
    | "scene" => do only' ["location", "participants", "reveals"]; pure (.scene (← str j "location") (← strsReq j "participants") (← strs j "reveals"))
    | "observe" => do
      only' ["character", "location", "target_location", "targets", "facts"]
      let l ← str j "location"
      pure (.observe (← str j "character") l ((← strOpt j "target_location").getD l)
        (← strs j "targets") (← strsReq j "facts"))
    | "transfer" => do only' ["from", "to", "item"]; pure (.transfer (← str j "from") (← str j "to") (← str j "item"))
    | "pickup" => do only' ["character", "item"]; pure (.pickup (← str j "character") (← str j "item"))
    | "drop" => do only' ["character", "item"]; pure (.drop (← str j "character") (← str j "item"))
    | "use" => do only' ["character", "item"]; pure (.use (← str j "character") (← str j "item"))
    | "consume" => do only' ["character", "item"]; pure (.consume (← str j "character") (← str j "item"))
    | "learn" => do only' ["character", "facts"]; pure (.learn (← str j "character") (← strsReq j "facts"))
    | "tell" => do only' ["from", "to", "facts"]; pure (.tell (← str j "from") (← str j "to") (← strsReq j "facts"))
    | "die" => do only' ["character"]; pure (.die (← str j "character"))
    | k => throw s!"unknown event kind '{k}'"
  pure { id, time, kind, requires }

partial def parseFormula (tr : Id → Bool) (j : Json) : P Formula := do
  let obj ← match j with
    | .obj o => pure o
    | _ => throw "formula must be an object"
  if obj.size != 1 then throw "formula must have exactly one key"
  if let some v := field? j "const" then return .const (← asBool "const" v)
  if let some v := field? j "var" then return .var (← asStr "var" v)
  if let some v := field? j "eq" then only v ["var", "value"]; return .eq (← str v "var") (← str v "value")
  if let some v := field? j "plurality" then only v ["votes", "value"]; return .plurality (← strsReq v "votes") (← str v "value")
  if let some v := field? j "tie" then only v ["votes"]; return .tie (← strsReq v "votes")
  if let some v := field? j "truth" then let f ← asStr "truth" v; return .truth f (tr f)
  if let some v := field? j "not" then return .not (← parseFormula tr v)
  if let some v := field? j "and" then return .and (← (← asArr "and" v).mapM (parseFormula tr))
  if let some v := field? j "or" then return .or (← (← asArr "or" v).mapM (parseFormula tr))
  throw "unknown formula"

/-- 探索フェイズ(§1.10): `draws_per_player` か `rounds` のどちらか一方。 -/
def parseExploration (x : Json) : P (List Round) := do
  only x ["draws_per_player", "rounds"]
  match field? x "draws_per_player", field? x "rounds" with
  | some n, none => pure [{ draws := ← asNat "draws_per_player" n }]
  | none, some rs =>
    let rs ← asArr "rounds" rs
    if rs.isEmpty then throw "'rounds' must be non-empty"
    rs.mapM fun r => do
      only r (["draws_per_player", "clues"])
      pure { draws := ← nat r "draws_per_player", clues := ← strsOpt r "clues" }
  | _, _ => throw "'exploration' must have exactly one of 'draws_per_player' or 'rounds'"

def topKeys : List String :=
  ["spec_version", "start_time", "end_time", "claim_tolerance", "characters", "areas", "locations", "travel",
   "area_travel", "perception", "placements", "items", "facts", "initial_knowledge", "events", "clues",
   "solution_facts", "assertions", "handouts", "board", "goals", "choices", "constraints", "endings", "exploration"]

def parseScenario (j : Json) : P Scenario := do
  only j topKeys
  let list {α} (k : String) (f : Json → P α) : P (List α) := do (← arrD j k).mapM f
  let facts ← list "facts" parseFact
  -- {"truth": f} の値: f の truth(最初に見つかったもの)。f がなければ false(R002 になる)
  let tr (f : Id) : Bool := match facts.find? (·.id == f) with
    | some x => x.truth
    | none => false
  let parseFormula := parseFormula tr
  pure {
    startTime := ← nat j "start_time"
    endTime := ← nat j "end_time"
    claimTolerance := (← natOpt j "claim_tolerance").getD 0
    characters := ← (← asArr "characters" (← req j "characters")).mapM fun c => do
      only c ["id", "npc"]; pure { id := ← str c "id", npc := ← boolD c "npc" false }
    areas := ← list "areas" fun a => do only a (["id", "internal_minutes"]); pure { id := ← str a "id", internalMinutes := ← natOpt a "internal_minutes" }
    locations := ← (← asArr "locations" (← req j "locations")).mapM fun l => do
      only l (["id", "area", "public"])
      pure { id := ← str l "id", area := ← strOpt l "area", isPublic := ← boolD l "public" false }
    travel := ← list "travel" (parseEdge true)
    areaTravel := ← list "area_travel" (parseEdge true)
    perception := ← list "perception" (parseEdge false)
    placements := ← (← asArr "placements" (← req j "placements")).mapM fun p => do
      only p ["character", "location"]
      pure { character := ← str p "character", location := ← str p "location" }
    items := ← list "items" fun i => do
      only i (["id", "initial", "tags"])
      pure { id := ← str i "id", initial := ← parseHolder (← req i "initial"), tags := ← strs i "tags" }
    facts := facts
    initialKnowledge := ← list "initial_knowledge" fun k => do only k ["character", "fact"]; pure (← str k "character", ← str k "fact")
    events := ← list "events" parseEvent
    clues := ← list "clues" fun c => do
      only c (["id", "location", "item", "deck", "reveals"])
      pure { id := ← str c "id", location := ← strOpt c "location", item := ← strOpt c "item",
             deck := ← strOpt c "deck", reveals := ← strs c "reveals" }
    solutionFacts := ← strs j "solution_facts"
    assertions := ← list "assertions" fun a => do
      only a (["id", "kind", "location", "at", "characters"])
      let kind ← match ← str a "kind" with
        | "present" => pure AssertKind.present
        | "absent" => pure .absent
        | k => throw s!"unknown assertion kind '{k}'"
      pure { id := ← str a "id", kind, location := ← str a "location", time := ← nat a "at",
             characters := ← strsReq a "characters" }
    handouts := ← list "handouts" fun h => do
      only h ["character", "location", "items", "knows"]
      pure { character := ← str h "character", location := ← strOpt h "location",
             items := ← strsOpt h "items", knows := ← strsOpt h "knows" }
    board := ← list "board" fun b => do only b ["location", "items"]; pure { location := ← str b "location", items := ← strsReq b "items" }
    goals := ← list "goals" fun g => do
      only g (["id", "owner", "requires_items", "requires_knowledge", "requires_tagged", "conceals", "condition"])
      pure { id := ← str g "id", owner := ← str g "owner", requiresItems := ← strs g "requires_items",
             requiresKnowledge := ← strs g "requires_knowledge",
             requiresTagged := ← (← arrD g "requires_tagged").mapM (fun t => do only t ["tag", "count"]; pure (← str t "tag", ← nat t "count")),
             conceals := ← strs g "conceals",
             condition := ← (field? g "condition").mapM parseFormula }
    choices := ← list "choices" fun c => do
      only c (["id", "owner", "values"])
      pure { id := ← str c "id", owner := ← str c "owner", values := ← strsOpt c "values" }
    constraints := ← list "constraints" parseFormula
    endings := ← list "endings" fun e => do only e (["id", "condition"]); pure { id := ← str e "id", condition := ← parseFormula (← req e "condition") }
    exploration := ← (field? j "exploration").mapM parseExploration
  }

def valToJson : Val → Json
  | .bool b => .bool b
  | .str s => .str s

def diagToJson (d : Diag) : Json :=
  let base : List (String × Json) := [
    ("code", .str d.code),
    ("severity", .str (match d.sev with | .error => "error" | .warning => "warning"))]
  let ev := match d.event with
    | some e => [("event", Lean.Json.str e)]
    | none => []
  let args := [("args", Json.arr (d.args.map Lean.Json.str).toArray)]
  let wit := match d.witness with
    | some w => [("witness", Json.mkObj (w.map fun (k, v) => (k, valToJson v)))]
    | none => []
  Json.mkObj (base ++ ev ++ args ++ wit)

def output (ds : List Diag) : Json :=
  Json.mkObj [("spec_version", .str specVersion), ("diagnostics", .arr (ds.map diagToJson).toArray)]

end MurderMystery.Json
