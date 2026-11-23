import Tazuna.Semantics.Verify.Entries
import Tazuna.Semantics.Verify.Uncomparable

namespace Tazuna.Semantics.Verify

open Tazuna.Ir

/-- A run that a snapshot records: a scenario of `service`, made by the implementation of `runner`. -/
structure Run where
  service : String
  scenario : String
  runner : String
deriving DecidableEq, Repr

derive_wire Run

/-- The name of a run's snapshot: the scenario's, or `<scenario>.<runner>` for a peer's run. -/
def Run.stem (r : Run) : String := if r.runner == r.service then r.scenario else r.scenario ++ "." ++ r.runner

def Run.ref (r : Run) : Ir.Ref := { service := r.service, name := r.scenario }

structure Expected where
  run : Run
  /-- Whether the run is compared. A compared run's file is compared when present and reported when missing. The file
  of a run that is not compared is ignored. -/
  compared : Bool
deriving DecidableEq, Repr

derive_wire Expected

/-- The snapshot folder of `service`. -/
structure Folder where
  service : String
  entries : List Entry
deriving DecidableEq, Repr

derive_wire Folder

/-- An entry of the snapshot folder of `service`, or a scenario. -/
inductive At where
  | snapshotEntry (service entry : String)
  | scenario (scenario : Ir.Ref)
deriving DecidableEq, Repr

derive_wire At tag "kind" skip_serializing_none

def runsOf (expected : List Expected) (service : String) : List Run :=
  (expected.filter (·.run.service == service)).map (·.run)

def comparedRuns (expected : List Expected) (service : String) : List Run :=
  (expected.filter fun e => e.run.service == service && e.compared).map (·.run)

def entriesIn (folders : List Folder) (service : String) : List Entry :=
  ((folders.find? (·.service == service)).map (·.entries)).getD []

end Tazuna.Semantics.Verify
