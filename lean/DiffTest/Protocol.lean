import Tazuna.Explore.Instrument
import Tazuna.Scenario.Given
import Tazuna.Verify.Compare
import Tazuna.Verify.Pairing

/-!
The messages that tazuna-lean exchanges with TS over stdio, one JSON value per line. TS sends a Request; while Lean
answers it, Lean sends Questions about spec functions and TS sends Replies, until Lean sends the response.
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

/-- The step order that a simulation takes for the processing of `origin` in `service`. -/
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
  | pair (services : List PairedService) (scenarios : List Verify.Scenario) (others : List String)
      (folders : List Verify.Folder)
  | pairSnapshots (services : List String) (scenarios : List Verify.Scenario) (folders : List Verify.Folder)
  | compareSnapshot (snapshot : List (Option Value)) (run : List Value)
  | afters (snapshot : List (Option TraceLine))
  | decodeLines (values : List Value)
  /-- With `execute`, the lines take place as explore runs them, and each service also returns what it enables. -/
  | simulate («structure» : Spec.Structure) (scenario : Scenario) (execute : Option Bool)
      (stepOrders : Option (List StepOrder))
  | stepOrderChanges («structure» : Spec.Structure) (scenario : Scenario)
  | assignmentChanges («structure» : Spec.Structure) (scenario : Scenario)

derive_wire Request tag "type" skip_serializing_none

/--
A question that Lean asks TS: one per field of Functions, comparableValue for verify, and `served`, the value of a
record that TS read while it answers.
-/
inductive Question where
  | parse (schema : Schema) (value : Value)
  | unordered (schema : Schema) (value : Value)
  | normalize (schema : Schema) (value : Value)
  | binding (command binding : String) (input : Value) (now : Time)
  | requirement (command condition : String) (input : Value) (now : Time)
  | inputRequirement (target condition : String) (input : Value)
  | decide (command : String) (input : Value) (now : Time)
  | ensures (command : String) (input : Value) (now : Time)
  | queryEnsures (query : String) (input output : Value)
  | resultEnsures (target : String) (input : Value) (output : Option Value) (events : List Emit)
  | invariant (entity : String) (record : Value)
  | serviceInvariant
  | chartInvariant (scope : Scope)
  | resolve (query : String) (input : Value) (now : Time)
  | react (automation : String) (payload : Value) (now : Time) (keys : Keys)
  | comparable (query : String) (answer : Answer)
  | initialContext (machine : String) (input : Value)
  | guard (scope : Scope) (transition : Transition) (extra : Extra)
  | assign (scope : Scope) (assignment : Assignment) (extra : Extra) (keys : Keys)
  | input (scope : Scope) (activity : Activity) (keys : Keys)
  | holds (scope : Scope)
  | deadlines (machine state : String)
  | deadlineAt (scope : Scope) (name : String)
  | offers (scope : Scope) (control : String)
  | showInput (scope : Scope) (activity : Activity)
  | items (scope : Scope)
  | copyContext (machine map : String)
  | singleRecord (entity : String)
  | copyKey (machine map : String) (payload : Value)
  | close (scope : Scope)
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

/-- A key of a map state's items, encoded and as canonicalJson. -/
structure ItemKey where
  key : Value
  encodedKey : String

derive_wire ItemKey

/-- An `after` deadline of a state: its delay in milliseconds, or none when an expression sets its time. -/
structure Deadline where
  name : String
  delay : Option Nat

derive_wire Deadline skip_serializing_none

/--
A message that TS sends while it answers a question: a read of a record, an issue that stops the answer, or the answer
to the question of the same name.
-/
inductive Reply where
  | read (entity : String) (key field : Option String) (beforeEventWrite : Option Bool)
  | issue (issue : Issue)
  | parse (value : Option Value)
  | unordered (value : Value)
  | normalize (value : Option Value)
  | binding (bound : Bool)
  | requirement (holds : Bool)
  | inputRequirement (holds : Bool)
  | decide (groups : List (List Emit))
  | ensures (failed : Option String)
  | queryEnsures (failed : Option String)
  | resultEnsures (failed : Option String)
  | invariant (failed : Option String)
  | serviceInvariant (failed : Option String)
  | chartInvariant (failed : Option String)
  | resolve (output : Value)
  | react (input : Option Value) (created : List String)
  | comparable (value : Value)
  | initialContext (context : Value)
  | guard (passes : Bool)
  | assign (context : Value) (copy : Option Value) (created : List String)
  | input (input : Value) (created : List String)
  | holds
  | deadlines (deadlines : List Deadline)
  | deadlineAt (time : Time)
  | offers (payloads : List Value)
  | showInput (input : Value)
  | items (keys : List ItemKey)
  | copyContext (context : Value)
  | singleRecord (record : Value)
  /-- The key, null when the payload's key fields fail the schema, or none without them. -/
  | copyKey (key : Option (Option String))
  | close (output : Value) (failed : Option String)
  | comparableValue (value : Value)

/-- A reply, with what the chart expressions read and assigned, and whether a Bag of two or more ran a callback. -/
structure Replied where
  reply : Reply
  access : Option Explore.Access
  enumerated : Option Bool

derive_wire Reply tag "type" skip_serializing_none
derive_wire Replied flatten reply skip_serializing_none

end Tazuna.DiffTest
