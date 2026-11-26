import Lean.Data.Json
import Tazuna.Trace.Wire

/-! The lines of a trace. Snapshots, generate's output and verify's input share one format: a header line
`{"trace":1,"service":...}`, then one line per input (`"in"`) or output (`"out"`) of the service, each with the
service's time in ms. Inputs: a clock line, which fires the timers due; a request to a command or query, with an `id`
the trace chooses; an answer to a request the service sent, naming it in `to`; an event the service subscribes to.
Outputs: the answer to a request, naming it in `to`; each event the service applied; each request the service sends,
with its wire `id`. Payloads are values on the wire (`Tazuna.Trace.Wire`); `Line.ofWire_toWire` reads back every line
written. -/

namespace Tazuna.Trace

/-- How the service answered a request. -/
inductive Answer where
  | accepted
  | answered (output : Wire)
  | rejected (rejection : Wire)
  | invalid (rules : List String)
deriving Inhabited, DecidableEq

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .ok _, .error _ | .error _, .ok _ => isFalse nofun

inductive Line where
  | clock (time : Int)
  | request (time : Int) (id name : String) (caller input : Wire)
  | answer (time : Int) (to : String) (result : Except Wire Wire)
  | event (time : Int) (source name : String) (value : Wire)
  | answered (time : Int) (to : String) (answer : Answer)
  | applied (time : Int) (value : Wire)
  | sent (time : Int) (id external name : String) (input : Wire)
deriving Inhabited, DecidableEq

/-- Whether the line is an input, which opens the window of outputs that follow it. -/
def Line.isIn : Line → Bool
  | .clock .. | .request .. | .answer .. | .event .. => true
  | .answered .. | .applied .. | .sent .. => false

def Line.time : Line → Int
  | .clock t | .request t .. | .answer t .. | .event t .. | .answered t .. | .applied t .. | .sent t .. => t

def Line.toWire : Line → Wire
  | .clock t => .obj [("time", .num t), ("in", .str "clock")]
  | .request t id n c i => .obj [("time", .num t), ("in", .str "request"), ("id", .str id), ("name", .str n),
      ("caller", c), ("input", i)]
  | .answer t to (.ok v) => .obj [("time", .num t), ("in", .str "answer"), ("to", .str to), ("ok", v)]
  | .answer t to (.error v) => .obj [("time", .num t), ("in", .str "answer"), ("to", .str to), ("error", v)]
  | .event t s n v => .obj [("time", .num t), ("in", .str "event"), ("source", .str s), ("name", .str n), ("value", v)]
  | .answered t to .accepted => .obj [("time", .num t), ("out", .str "answer"), ("to", .str to),
      ("outcome", .str "accepted")]
  | .answered t to (.answered v) => .obj [("time", .num t), ("out", .str "answer"), ("to", .str to),
      ("outcome", .str "answered"), ("output", v)]
  | .answered t to (.rejected v) => .obj [("time", .num t), ("out", .str "answer"), ("to", .str to),
      ("outcome", .str "rejected"), ("rejection", v)]
  | .answered t to (.invalid rs) => .obj [("time", .num t), ("out", .str "answer"), ("to", .str to),
      ("outcome", .str "invalid"), ("rules", .arr (rs.map .str))]
  | .applied t v => .obj [("time", .num t), ("out", .str "event"), ("value", v)]
  | .sent t id x n i => .obj [("time", .num t), ("out", .str "request"), ("id", .str id), ("external", .str x),
      ("name", .str n), ("input", i)]

def Wire.str? : Wire → Option String
  | .str s => some s
  | _ => none

def Wire.num? : Wire → Option Int
  | .num n => some n
  | _ => none

def Wire.strs? : Wire → Option (List String)
  | .arr ws => ws.mapM Wire.str?
  | _ => none

def Line.ofWire : Wire → Option Line
  | .obj kvs => do
    let field (k : String) : Option Wire := kvs.lookup k
    let str (k : String) : Option String := (field k).bind Wire.str?
    let t ← (field "time").bind Wire.num?
    match str "in", str "out" with
    | some "clock", none => pure (.clock t)
    | some "request", none => pure (.request t (← str "id") (← str "name") (← field "caller") (← field "input"))
    | some "answer", none => match field "ok", field "error" with
      | some v, none => pure (.answer t (← str "to") (.ok v))
      | none, some v => pure (.answer t (← str "to") (.error v))
      | _, _ => none
    | some "event", none => pure (.event t (← str "source") (← str "name") (← field "value"))
    | none, some "answer" => do
      let to ← str "to"
      match str "outcome" with
      | some "accepted" => pure (.answered t to .accepted)
      | some "answered" => pure (.answered t to (.answered (← field "output")))
      | some "rejected" => pure (.answered t to (.rejected (← field "rejection")))
      | some "invalid" => pure (.answered t to (.invalid (← (field "rules").bind Wire.strs?)))
      | _ => none
    | none, some "event" => pure (.applied t (← field "value"))
    | none, some "request" => pure (.sent t (← str "id") (← str "external") (← str "name") (← field "input"))
    | _, _ => none
  | _ => none

theorem strs?_map (rs : List String) : Wire.strs? (.arr (rs.map .str)) = some rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp_all [Wire.strs?, Wire.str?, List.mapM_cons]

/-- Every line written reads back as itself. -/
theorem Line.ofWire_toWire (l : Line) : Line.ofWire l.toWire = some l := by
  cases l with
  | answer t to r => cases r <;> simp [Line.toWire, Line.ofWire, List.lookup, Wire.str?, Wire.num?]
  | answered t to a => cases a <;> simp [Line.toWire, Line.ofWire, List.lookup, Wire.str?, Wire.num?, strs?_map]
  | _ => simp [Line.toWire, Line.ofWire, List.lookup, Wire.str?, Wire.num?]

/-! Text. A line of text is JSON, which Lean's JSON library reads and writes; numbers must be integers. -/

open Lean (Json JsonNumber)

partial def Wire.ofJson : Json → Option Wire
  | .null => some .null
  | .bool b => some (.bool b)
  | .num n =>
    let d := (10 : Int) ^ n.exponent
    if n.mantissa % d == 0 then some (.num (n.mantissa / d)) else none
  | .str s => some (.str s)
  | .arr xs => xs.toList.mapM Wire.ofJson |>.map .arr
  | .obj kvs =>
    let pairs : List (String × Json) := kvs.foldl (fun acc k v => acc ++ [(k, v)]) []
    (pairs.mapM fun (kv : String × Json) => (Wire.ofJson kv.2).map (kv.1, ·)).map Wire.obj

partial def Wire.toJson : Wire → Json
  | .null => .null
  | .bool b => .bool b
  | .num n => .num (JsonNumber.fromInt n)
  | .str s => .str s
  | .arr ws => .arr (ws.map Wire.toJson).toArray
  | .obj kvs => Json.mkObj (kvs.map fun (k, w) => (k, w.toJson))

def Wire.text (w : Wire) : String := w.toJson.compress

def Wire.parse (text : String) : Except String Wire :=
  match Json.parse text with
  | .ok j => match Wire.ofJson j with
    | some w => .ok w
    | none => .error "a number is not an integer"
  | .error e => .error e

end Tazuna.Trace
