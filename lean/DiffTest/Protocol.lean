import Tazuna.Explore.StepOrders
import Tazuna.Explore.Enabled
import Tazuna.Explore.Instrument
import Tazuna.Scenario.Given
import Tazuna.Sim.InvalidScenario
import Tazuna.Validation.Illegal
import Tazuna.Verify.Compare
import Tazuna.Verify.Pairing

/-!
The messages that tazuna-lean exchanges with TS over stdio, one JSON value per line. TS sends a Request; while Lean
answers it, Lean sends Questions about spec functions and TS sends Replies, until Lean sends the Response.
-/

namespace Tazuna.DiffTest

open Tazuna.Data Tazuna.Service

local instance : ToValue Time := ⟨Time.toValue⟩
local instance : FromValue Time := ⟨Time.fromValue⟩

/-- A service of a `pair` request, and whether it is external. -/
structure PairedService where
  name : String
  external : Bool

derive_wire PairedService

/-- The step order that a simulation takes for the processing of `service` while `origin` is processed. -/
structure StepOrder where
  origin : Scenario.Origin
  service : String
  order : List StepName

derive_wire StepOrder

/-- What TS asks Lean to compute. A snapshot line is null for a blank line. -/
inductive Request where
  | check («structure» : Spec.Structure)
  | verify («structure» : Spec.Structure) (service : String) (snapshot : List (Option TraceLine))
      (trace : List (FileLine TraceLine))
  | checkExternal («structure» : Spec.Structure) (service : String) (trace : List (FileLine TraceLine))
  | pair (services : List PairedService) (expected : List Verify.Expected) (others : List String)
      (folders : List Verify.Folder)
  | pairSnapshots (services : List String) (expected : List Verify.Expected) (folders : List Verify.Folder)
  | compareSnapshot (snapshot : List (Option Value)) (run : List Value)
  | afters (snapshot : List (Option TraceLine))
  | decodeLines (values : List Value)
  /-- With `execute`, the lines take place as explore runs them, and each service also returns what it enables. -/
  | simulate («structure» : Spec.Structure) (scenario : Scenario) (execute : Option Bool)
      (stepOrders : Option (List StepOrder))
  | stepOrderChanges («structure» : Spec.Structure) (scenario : Scenario)
  /-- sortCollections of an encoded value by its JSON Schema. -/
  | sort (schema value : Value)
  /-- keyOrdered of an encoded value by its JSON Schema. -/
  | keyOrdered (schema value : Value)
  /-- scenarioTime? of a text, as renderTime writes the time. -/
  | scenarioTime (text : String)
  /-- Service.schemaOf of the service `service` of the structure. -/
  | schemaOf («structure» : Spec.Structure) (service : String) (schema : Service.Schema)

derive_wire Request tag "type" skip_serializing_none

/--
A question that Lean asks TS: one per field of Functions, comparableValue for verify, and `served`, the value of a
record that TS read while it answers.
-/
inductive Question where
  | parse (schema : Schema) (value : Value)
  | unordered (schema : Schema) (value : Value)
  | binding (command binding : String) (input : Value) (now : Time)
  | requirement (command condition : String) (input : Value) (now : Time)
  | inputRequirement (target : Spec.Ref) (condition : String) (input : Value)
  | decide (command : String) (input : Value) (now : Time)
  | ensures (command : String) (input : Value) (now : Time)
  | queryEnsures (query : String) (input output : Value)
  | resultEnsures (target : Spec.Ref) (condition : String) (input : Value) (output : Option Value) (events : List Emit)
  | invariant (entity : String) (record : Value)
  | serviceInvariant
  | chartInvariant (scope : Scope)
  | resolve (query : String) (input : Value) (now : Time)
  | automationBinding (automation binding : String) (payload : Value) (now : Time)
  | automationGuard (automation condition : String) (payload : Value) (now : Time)
  | react (automation : String) (payload : Value) (now : Time) (keys : Keys)
  | comparable (query : String) (answer : Answer)
  | initialContext (machine : String) (input : Value)
  | guard (scope : Scope) (transition : Transition) (condition : String) (extra : Extra)
  | assign (scope : Scope) (assignment : Assignment) (extra : Extra) (keys : Keys)
  | input (scope : Scope) (activity : Activity) (keys : Keys)
  | held (scope : Scope) (state : String) (edge : Edge) (extra : Extra)
  | deadlineAt (scope : Scope) (name : String)
  | offers (scope : Scope) (control : String)
  | showInput (scope : Scope) (activity : Activity)
  | items (scope : Scope)
  | defaults (schema : Schema)
  | close (scope : Scope)
  | closeEnsures (screen : String) (input output : Value)
  /-- The comparable value of `value`, read by the schema `part` of the definition `kind` `definition`. -/
  | comparableValue (kind : String) (definition : Spec.Ref) (part : Verify.Part) (value : Value)
  | served (value : Option Value)

/-- A question with the service it is about, which TS answers with every Bag in reverse order when `reversed`. -/
structure Asked where
  service : Option String := none
  reversed : Option Bool := none
  question : Question

derive_wire Question tag "type" skip_serializing_none
derive_wire Asked flatten question skip_serializing_none

/-- A key of a map state's items, encoded and as a canonical value. -/
structure ItemKey where
  key : Value
  canonical : Value

derive_wire ItemKey

/--
A message that TS sends while it answers a question: a read of a record, an issue that stops the answer, or the answer
to the question of the same name.
-/
inductive Reply where
  | read (entity : String) (key field : Option String) (beforeEventWrite : Option Bool)
  | issue (issue : Issue)
  | parse (value : Option Value)
  | unordered (value : Value)
  | binding (bound : Bool)
  | requirement (holds : Bool)
  | inputRequirement (holds : Bool)
  | decide (groups : List (List Emit))
  | ensures (failed : Option String)
  | queryEnsures (failed : Option String)
  | resultEnsures (ensured : Ensured)
  | invariant (failed : Option String)
  | serviceInvariant (failed : Option String)
  | chartInvariant (failed : Option String)
  | resolve (output : Value)
  | automationBinding (bound : Bool)
  | automationGuard (holds : Bool)
  | react (input : Value) (created : List String)
  | comparable (value : Value)
  | initialContext (context : Value)
  | guard (holds : Bool)
  | assign (context : Value) (copy : Option Value) (created : List String)
  | input (input : Value) (created : List String)
  | held (held : Value)
  | deadlineAt (time : Option String)
  | offers (payloads : List Value)
  | showInput (input : Value)
  | items (keys : List ItemKey)
  | defaults (defaults : Value)
  | close (output : Value)
  | closeEnsures (failed : Option String)
  | comparableValue (value : Value)

/-- A reply, with what the chart expressions read and assigned, and whether a Bag of two or more ran a callback. -/
structure Replied where
  reply : Reply
  access : Option Explore.Access
  enumerated : Option Bool

derive_wire Reply tag "type" skip_serializing_none
derive_wire Replied flatten reply skip_serializing_none

instance : ToValue Verify.Finding := ⟨fun
  | .mismatch m => ToValue.toValue m
  | .uncomparable u => ToValue.toValue u
  | .after line subject snapshot trace =>
    .obj [("after", .obj [("line", ToValue.toValue line), ("subject", ToValue.toValue subject),
      ("snapshot", ToValue.toValue snapshot), ("trace", ToValue.toValue trace)])]⟩

/-- A pairing violation and where it is. -/
structure Unpaired where
  «at» : Verify.At
  violation : Verify.Uncomparable

derive_wire Unpaired serialize_only

/--
What a simulation shows of one running service: its trace lines, its violations, and its candidates, and when it runs
as explore does and did not halt, what it enables next or the fault that computing it raised.
-/
structure SimulatedService where
  service : String
  lines : List TraceLine
  violations : List Violation
  candidates : List (Nat × Nat)
  enabled : Option Explore.Enabled
  fault : Option Violation
  /-- The state that ChoiceDependent compares (Explore.stateValue), given with `enabled`. -/
  state : Option Value

derive_wire SimulatedService serialize_only skip_serializing_none

/-- A step order that a search ran, refused or with the violation found, if any. -/
structure TriedOrder where
  order : List StepName
  refused : Option Bool
  found : Option (Option Violation)

derive_wire TriedOrder serialize_only skip_serializing_none

/-- What the search of the processing of `service` while `origin` was processed ran and found. -/
structure SearchedProcessing where
  origin : Scenario.Origin
  service : String
  tried : List TriedOrder
  found : Option Violation

derive_wire SearchedProcessing serialize_only

/-- What Lean answers a Request with, the constructor named after the request's. -/
inductive Response where
  | checked (findings : List Validation.Illegal)
  /-- The pairs of each binding that the comparison ends with. -/
  | verified (findings : List Verify.Finding) (bindings : List (List (String × String)))
  | checkedExternal (findings : List Verify.Finding)
  | paired (compare : List Verify.Run) (contract : List Spec.Ref) (findings : List Unpaired)
  | pairedSnapshots (compare : List Verify.Run) (findings : List Unpaired)
  | comparedSnapshot (mismatch : Option Verify.Mismatch)
  | afters (findings : List Verify.Uncomparable)
  /-- Each value as a trace line, or null when it is none. -/
  | decodedLines (lines : List (Option TraceLine))
  | simulated (services : List SimulatedService) (violations : List Sim.InvalidScenario)
      (halted : Option Sim.InvalidScenario)
  | stepOrderChanges (searched : List SearchedProcessing)
  | sorted (value : Value)
  | keyOrdered (ordered : Bool)
  | scenarioTime (time : Option String)
  | schemaOf (schema : Option Value)
  | error (message : String)

derive_wire Response tag "type" serialize_only

end Tazuna.DiffTest
