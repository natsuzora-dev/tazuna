import Engine.Drive
import Engine.Prove
import Engine.Generate
import Tazuna.Ir.Expr
import Tazuna.Semantics.Explore.Coverage
import Tazuna.Semantics.Explore.Instrument
import Tazuna.Semantics.Scenario.Given
import Tazuna.Semantics.Sim.InvalidScenario
import Tazuna.Semantics.Validation.Illegal
import Tazuna.Semantics.Validation.NonCanonical
import Tazuna.Semantics.Verify.Compare
import Tazuna.Semantics.Verify.Pairing

/-!
The messages that the engine exchanges with TS over stdio, one JSON value per line: TS sends Requests, and the engine
answers each with a Response.
-/

namespace Tazuna.Engine

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service


/-- A record that an `evaluate` request gives: the key is absent for a single entity's. -/
structure Stored where
  entity : String
  key : Option Value
  value : Value

derive_wire Stored skip_serializing_none

def Stored.row (s : Stored) : Service.Row := { entity := s.entity, key := s.key, value := s.value }

/-- What TS asks Lean to compute. A snapshot line is null for a blank line. -/
inductive Request where
  | check («structure» : Ir.Structure)
  | checkCanonical («structure» : Ir.Structure)
  | pairSnapshots (services : List String) (expected : List Verify.Expected) (folders : List Verify.Folder)
  | compareSnapshot (snapshot : List (Option Value)) (run : List Value)
  | afters (snapshot : List (Option TraceLine))
  | decodeLines (values : List Value)
  /-- The simulation of the scenario: what each running service shows, and the simulation's violations. -/
  | simulate («structure» : Ir.Structure) (scenario : Scenario)
  /-- What test finds of each scenario (Engine.test). -/
  | test («structure» : Ir.Structure) (scenarios : List Scenario)
  /-- What verify finds of each log, and the parts of the spec that no log reached (Engine.verify). -/
  | verify («structure» : Ir.Structure) (logs : List Log)
  /-- The comparison of drive's log so far with the snapshot so far, for its bindings (Engine.bindingsOf). -/
  | bindings («structure» : Ir.Structure) (service : String) (snapshot : List (Option TraceLine))
      (trace : List (FileLine TraceLine))
  /-- The violations of an external service's trace against its contract (Engine.verifyExternal). -/
  | verifyExternal («structure» : Ir.Structure) (service : String) (trace : List (FileLine TraceLine))
  /-- The Given records of the running service `service` of the scenario, as its records hold them. -/
  | givenRecords («structure» : Ir.Structure) (scenario : Scenario) (service : String)
  /-- Each line of a snapshot of `service` as verify reads it (readSnapshotLines), by which drive substitutes keys. -/
  | readLines («structure» : Ir.Structure) (service : String) (lines : List (Option TraceLine))
  /-- sortCollections of an encoded value by its JSON Schema. -/
  | sort (schema value : Value)
  /-- keyOrdered of an encoded value by its JSON Schema. -/
  | keyOrdered (schema value : Value)
  /--
  The value of an IR expression whose only argument is `input`, over `records` whose entities have `fields` in their
  schemas' order, with createKey over `keys`.
  -/
  | evaluate (body : Ir.Expr) (input : Value) (records : List Stored) (keys : Keys)
      (fields : List (String × List String))
  /-- `value` parsed by the JSON Schema `schema` as Lean's Semantics.parse does. -/
  | parse (schema : Value) (value : Value)
  /-- The SMT-LIB scripts of prove's queries, each once, in order (Engine.proveQueriesOf). -/
  | proveQueries («structure» : Ir.Structure)
  /-- prove's result of each property, from Z3's output on each script of proveQueries, in order (Engine.proveOf). -/
  | prove («structure» : Ir.Structure) (answers : List String)
  /--
  generate's result (Engine.generateOf). Before it the engine sends `solve` responses, each answered by `solved`.
  `depth` is the most requests of a sequence, by default one more than the creations that the service's bounds allow.
  -/
  | generate («structure» : Ir.Structure) (depth : Option Nat)
  /-- Z3's output on each script of the engine's last `solve`, in order. -/
  | solved (outputs : List String)

derive_wire Request tag "type" skip_serializing_none

/-- A pairing violation and where it is. -/
structure Unpaired where
  «at» : Verify.At
  violation : Verify.Uncomparable

derive_wire Unpaired serialize_only

/-- A part of the records that an evaluation read, as a `read` reply names it. -/
structure ReadPart where
  entity : String
  key : Option Value
  field : Option String

derive_wire ReadPart serialize_only skip_serializing_none

def ReadPart.of : RecordPart → ReadPart
  | .keys entity => { entity, key := none, field := none }
  | .record entity key => { entity, key := some key, field := none }
  | .field entity key field => { entity, key, field := some field }

/--
The value of an IR expression, absent for `undefined`, or the Issue that stopped it, the parts it read, and the
entities that createKey made a key of.
-/
structure Evaluated where
  value : Option Value
  issue : Option Issue
  reads : List ReadPart
  created : List String

derive_wire Evaluated serialize_only skip_serializing_none

/-- What Lean answers a Request with, the constructor named after the request's. -/
inductive Response where
  | checked (findings : List Validation.Illegal)
  | checkedCanonical (findings : List Validation.NonCanonical)
  | pairedSnapshots (compare : List Verify.Run) (findings : List Unpaired)
  | comparedSnapshot (mismatch : Option Verify.Mismatch)
  | afters (findings : List Verify.Uncomparable)
  /-- Each value as a trace line, or null when it is none. -/
  | decodedLines (lines : List (Option TraceLine))
  | simulated (services : List SimulatedService) (violations : List Sim.InvalidScenario)
      (halted : Option Sim.InvalidScenario)
  | sorted (value : Value)
  | keyOrdered (ordered : Bool)
  | evaluated (result : Evaluated)
  | tested (runs : List Engine.ScenarioRun)
  | verified (logs : List Replayed) (uncovered : List Violation)
  | bound (findings : List Verify.Finding) (bindings : List (List (String × String)))
  | verifiedExternal (findings : List Verify.Finding)
  | given (records : List Scenario.GivenRecord)
  | read (lines : List (Option ReadLine))
  /--
  Whether Lean parses by the schema, and then the value, Zod's issues, or whether a codec threw; and whether prove's
  record facts hold of the parsed record, or of the value when parse rejects it, with their fit (Smt.recordHolds).
  -/
  | parsed (supported : Bool) (value : Option Value) (issues : Option (List Value)) (thrown : Bool)
    (facts : Option (Bool × Smt.Fit))
  | queried (scripts : List String)
  | proved (results : List ProveResult)
  | generated (result : Generation)
  /-- The SMT-LIB scripts whose Z3 outputs a running request needs next; TS answers with `solved`. -/
  | solve (scripts : List String)
  | error (message : String)

derive_wire Response tag "type" serialize_only

end Tazuna.Engine
