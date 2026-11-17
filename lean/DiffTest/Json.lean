import Lean.Data.Json.Parser
import Lean.Data.Json.Printer
import Tazuna.Explore.Enabled
import Tazuna.Explore.Instrument
import Tazuna.Validation.Check
import Tazuna.Verify.External
import Tazuna.Verify.Pairing
import Tazuna.Verify.Snapshot

/-!
Lean.Json objects sort fields by name (Std.TreeMap), so this module parses and renders `Data.Value`, which keeps the
field order that TS writes.
-/

namespace Tazuna.Json

open Tazuna.Data Tazuna.Service Tazuna.Explore
open Std.Internal.Parsec Std.Internal.Parsec.String

mutual

partial def arrayCore (acc : Array Value) : Parser (Array Value) := do
  let acc := acc.push (← anyCore)
  let c ← any
  if c == ']' then ws; pure acc
  else if c == ',' then ws; arrayCore acc
  else fail "unexpected character in array"

partial def objectCore (acc : Array (String × Value)) : Parser (Array (String × Value)) := do
  skipChar '"'
  let k ← Lean.Json.Parser.str
  ws; skipChar ':'; ws
  let acc := acc.push (k, ← anyCore)
  let c ← any
  if c == '}' then ws; pure acc
  else if c == ',' then ws; objectCore acc
  else fail "unexpected character in object"

partial def anyCore : Parser Value := do
  let c ← peek!
  if c == '[' then
    skip; ws
    if (← peek!) == ']' then skip; ws; pure (.arr [])
    else pure (.arr (← arrayCore #[]).toList)
  else if c == '{' then
    skip; ws
    if (← peek!) == '}' then skip; ws; pure (.obj [])
    else pure (.obj (← objectCore #[]).toList)
  else if c == '"' then
    skip
    let s ← Lean.Json.Parser.str
    ws; pure (.str s)
  else if c == 'f' then skipString "false"; ws; pure (.bool false)
  else if c == 't' then skipString "true"; ws; pure (.bool true)
  else if c == 'n' then skipString "null"; ws; pure .null
  else if c == '-' || ('0' ≤ c && c ≤ '9') then
    let n ← Lean.Json.Parser.num
    ws; pure (.num n)
  else fail "unexpected input"

end

def parse (text : String) : Except String Value :=
  Parser.run (do ws; let v ← anyCore; eof; pure v) text

partial def render : Value → String
  | .null => "null"
  | .bool b => toString b
  | .num n => toString n
  | .str s => Lean.Json.renderString s
  | .arr vs => "[" ++ ",".intercalate (vs.map render) ++ "]"
  | .obj fs => "{" ++ ",".intercalate (fs.map fun (k, v) => Lean.Json.renderString k ++ ":" ++ render v) ++ "}"

def field (v : Value) (key : String) : Except String Value :=
  match v.field? key with
  | some x => pure x
  | none => throw s!"missing field {key}"

def asList : Value → Except String (List Value)
  | .arr vs => pure vs
  | v => throw s!"expected an array, got {render v}"

def stringField (v : Value) (key : String) : Except String String := do FromValue.fromValue (← field v key)

/-- The field `key` of `v`, or `none` when it is missing or null. -/
def optional (v : Value) (key : String) : Option Value :=
  match v.field? key with
  | none | some .null => none
  | some x => some x

def optionalString (v : Value) (key : String) : Except String (Option String) :=
  (optional v key).mapM FromValue.fromValue

def obj (fields : List (String × Option Value)) : Value :=
  .obj (fields.filterMap fun (k, v) => v.map (k, ·))

def lineValue (line : Line) (after created : List String) : Value := ToValue.toValue (Sim.traceLineOf line after created)

def Enabled.toValue (e : Enabled) : Value :=
  obj [("operations", some (.arr (e.operations.map fun o => .obj [("screen", .str o.screen),
          ("control", .str o.control), ("payloads", (o.payloads.map .arr).getD (.str "any"))]))),
       ("awaiting", some (.arr (e.awaiting.map fun a => .obj [("id", .str a.id), ("name", .str a.name),
          ("target", .str a.target), ("sender", .str a.sender)]))),
       ("nextDeadline", e.nextDeadline.map (.str ∘ renderTime))]

def Schema.toValue : Schema → Value
  | .input d => .obj [("kind", .str "input"), ("definition", .str d)]
  | .payload e => .obj [("kind", .str "payload"), ("event", .str e)]
  | .output d => .obj [("kind", .str "output"), ("definition", .str d)]
  | .control screen control => .obj [("kind", .str "control"), ("screen", .str screen), ("control", .str control)]
  | .held chart state name =>
    .obj [("kind", .str "held"), ("chart", .str chart), ("state", .str state), ("name", .str name)]
  | .context chart => .obj [("kind", .str "context"), ("chart", .str chart)]
  | .mapContext chart map => .obj [("kind", .str "mapContext"), ("chart", .str chart), ("map", .str map)]
  | .mapKey chart map => .obj [("kind", .str "mapKey"), ("chart", .str chart), ("map", .str map)]
  | .record entity => .obj [("kind", .str "record"), ("entity", .str entity)]

def Schema.decode (v : Value) : Except String Schema := do
  match ← stringField v "kind" with
  | "input" => pure (.input (← stringField v "definition"))
  | "payload" => pure (.payload (← stringField v "event"))
  | "output" => pure (.output (← stringField v "definition"))
  | "control" => pure (.control (← stringField v "screen") (← stringField v "control"))
  | "held" => pure (.held (← stringField v "chart") (← stringField v "state") (← stringField v "name"))
  | "context" => pure (.context (← stringField v "chart"))
  | "mapContext" => pure (.mapContext (← stringField v "chart") (← stringField v "map"))
  | "mapKey" => pure (.mapKey (← stringField v "chart") (← stringField v "map"))
  | "record" => pure (.record (← stringField v "entity"))
  | other => throw s!"unknown schema kind {other}"

def Issue.decode (v : Value) : Except String Issue := do
  match ← stringField v "kind" with
  | "thrown" => pure (.thrown (← (optional v "schema").mapM Schema.decode))
  | "schema" => pure (.schema (← Schema.decode (← field v "schema")))
  | "unheld" => pure (.unheld (← stringField v "held"))
  | "notOnly" => pure .notOnly
  | other => throw s!"unknown issue kind {other}"

def Transition.toValue (t : Transition) : Value :=
  .obj [("source", (t.source.map .str).getD .null), ("trigger", ToValue.toValue t.trigger), ("index", .num t.index)]

def Scope.toValue (s : Scope) : Value :=
  .obj [("machine", .str s.machine), ("state", (s.state.map .str).getD .null), ("context", s.context),
        ("copy", (s.copy.map fun c => .obj [("map", .str c.map), ("key", c.key), ("context", c.context)]).getD .null),
        ("active", .arr (s.active.map .str)), ("shown", .obj s.shown), ("input", s.input),
        ("now", .str (renderTime s.now))]

def Assignment.toValue : Assignment → Value
  | .transition t => .obj [("kind", .str "transition"), ("transition", Transition.toValue t)]
  | .entry state => .obj [("kind", .str "entry"), ("state", .str state)]
  | .exit state => .obj [("kind", .str "exit"), ("state", .str state)]

def Extra.toValue : Extra → Value
  | .none => .obj []
  | .payload v => .obj [("payload", v)]
  | .output v => .obj [("output", v)]
  | .rejection r => .obj [("rejection", .obj [("kind", ToValue.toValue r.kind)])]

def Activity.toValue (a : Activity) : Value :=
  let keyword := match a with
    | .calls .. => "calls"
    | .sends .. => "sends"
    | .shows .. => "shows"
    | .opens .. => "opens"
  .obj [("keyword", .str keyword), ("key", .str a.key)]

def Emit.decode (v : Value) : Except String Emit := do
  pure { event := ← stringField v "event", payload := ← field v "payload" }

def Access.decode (v : Value) : Except String Access := do
  let holder (p : Value) : Except String Holder := do
    match ← stringField p "holder" with
    | "owner" => pure .owner
    | "copy" => pure .copy
    | other => throw s!"unknown holder {other}"
  let pairs (key : String) : Except String (List (Holder × String)) := do
    match v.field? key with
    | none => pure []
    | some l => (← asList l).mapM fun p => do pure (← holder p, ← stringField p "name")
  let shown ← match v.field? "shown" with
    | none => pure []
    | some l => (← asList l).mapM FromValue.fromValue
  pure { context := ← pairs "context", active := ← pairs "active", assigned := ← pairs "assigned", shown }

def FileLine.decode (v : Value) : Except String (FileLine TraceLine) :=
  match v with
  | .null => pure .blank
  | .str "malformed" => pure .malformed
  | v => .line <$> FromValue.fromValue v

/--
The compared value that `v` encodes as an object with one field, whose name tells the variant (leaf, arr, obj, bag,
runs).
-/
partial def CValue.decode (v : Value) : Except String CValue := do
  match v with
  | .obj [("leaf", x)] => pure (.leaf x)
  | .obj [("ref", .arr [.str e, .str x])] => pure (.ref e x)
  | .obj [("arr", xs)] => pure (.arr (← (← asList xs).mapM CValue.decode))
  | .obj [("bag", xs)] => pure (.bag (← (← asList xs).mapM CValue.decode))
  | .obj [("runs", xs)] => pure (.runs (← (← asList xs).mapM CValue.decode))
  | .obj [("obj", fs)] => pure (.obj (← (← asList fs).mapM fun f => do
      match ← asList f with
      | [k, x] => pure (← FromValue.fromValue k, ← CValue.decode x)
      | _ => throw s!"expected a field pair, got {render f}"))
  | other => throw s!"expected a compared value, got {render other}"

def _root_.Tazuna.Verify.Part.toValue : Verify.Part → List (String × Value)
  | .input => [("part", .str "input")]
  | .output => [("part", .str "output")]
  | .payload => [("part", .str "payload")]
  | .control c => [("part", .str "control"), ("control", .str c)]

def _root_.Tazuna.Verify.Finding.toValue : Verify.Finding → Value
  | .mismatch m => m.toValue
  | .uncomparable u => u.toValue

def _root_.Tazuna.Verify.At.toValue : Verify.At → Value
  | .entry service name => obj [("service", service.map (.str ·)), ("entry", some (.str name))]
  | .snapshotEntry service name => obj [("service", some (.str service)), ("snapshotEntry", some (.str name))]
  | .scenario service name => .obj [("scenario", .obj [("service", .str service), ("name", .str name)])]

def Scenario.decode (s : Value) : Except String Verify.Scenario := do
  pure { service := ← stringField s "service", name := ← stringField s "name",
         compared := ← FromValue.fromValue (← field s "compared") }

def Folder.decode (f : Value) : Except String Verify.Folder := do
  let entries ← (← asList (← field f "entries")).mapM fun e => do
    let kind ← match ← stringField e "kind" with
      | "file" => pure Data.EntryKind.file
      | "folder" => pure .folder
      | "other" => pure .other
      | k => throw s!"unknown entry kind {k}"
    pure { name := ← stringField e "name", kind : Data.Entry }
  pure { service := ← stringField f "service", entries }

def refValues (l : List (String × String)) : Value :=
  .arr (l.map fun (service, name) => .obj [("service", .str service), ("name", .str name)])

def pairingFindings (violations : List (Verify.At × Verify.Uncomparable)) : Value :=
  .arr (violations.map fun (place, u) => .obj [("at", place.toValue), ("violation", u.toValue)])

/--
The reply to request `pair`, which takes the services, the scenarios, and the trace folders, and returns the compared
traces, the traces checked against contracts, and the pairing violations.
-/
def pair (request : Value) : Except String Value := do
  let services : List (String × Bool) ← (← asList (← field request "services")).mapM fun s => do
    pure (← stringField s "name", ← FromValue.fromValue (← field s "external"))
  let scenarios ← (← asList (← field request "scenarios")).mapM Scenario.decode
  let others : List String ← (← asList (← field request "others")).mapM FromValue.fromValue
  let folders ← (← asList (← field request "folders")).mapM Folder.decode
  let found := Verify.pairTraces services scenarios others folders
  pure (.obj [("type", .str "paired"), ("compare", refValues found.compare), ("contract", refValues found.contract),
    ("findings", pairingFindings found.violations)])

/--
The reply to request `pairSnapshots`, which takes the services, the scenarios, and the snapshot folder of each service,
and returns the compared scenarios and the pairing violations.
-/
def pairSnapshots (request : Value) : Except String Value := do
  let services : List String ← (← asList (← field request "services")).mapM FromValue.fromValue
  let scenarios ← (← asList (← field request "scenarios")).mapM Scenario.decode
  let folders ← (← asList (← field request "folders")).mapM Folder.decode
  let found := Verify.pairSnapshots services scenarios folders
  pure (.obj [("type", .str "pairedSnapshots"), ("compare", refValues found.compare),
    ("findings", pairingFindings found.violations)])

/--
The reply to request `compareSnapshot`, which takes the snapshot lines (null for a blank line) and the run lines, and
returns the mismatch or null.
-/
def compareSnapshot (request : Value) : Except String Value := do
  let snapshot := (← asList (← field request "snapshot")).map fun l => if l == .null then none else some l
  let run ← asList (← field request "run")
  pure (.obj [("type", .str "comparedSnapshot"),
    ("mismatch", ((Verify.compareSnapshot snapshot run).map Verify.Mismatch.toValue).getD .null)])

/--
The reply to request `decodeLines`, which takes JSON values and returns, for each value, the line as the decoder of
`TraceLine` reads it and its encoder writes it, or null when the decoder does not read it.
-/
def decodeLines (request : Value) : Except String Value := do
  let values ← asList (← field request "values")
  pure (.obj [("type", .str "decodedLines"), ("lines", .arr (values.map fun v =>
    match (FromValue.fromValue v : Except String TraceLine) with
    | .ok line => ToValue.toValue line
    | .error _ => .null))])

/--
The reply to request `checkExternal`, which takes a structure, a service, and trace lines, and returns the violations
that `checkExternal` finds.
-/
def checkExternal (request : Value) : Except String Value := do
  let s : Spec.Structure ← FromValue.fromValue (← field request "structure")
  let service ← stringField request "service"
  let trace ← (← asList (← field request "trace")).mapM FileLine.decode
  pure (.obj [("type", .str "checkedExternal"),
    ("findings", .arr ((Verify.checkExternal s service trace).map Verify.Finding.toValue))])

end Tazuna.Json
