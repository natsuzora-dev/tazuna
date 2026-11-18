import Tazuna.Data.Pairing
import Tazuna.Verify.Uncomparable

namespace Tazuna.Verify

open Tazuna.Data

/-- A run that a snapshot records: a scenario of `service`, made by the implementation of `runner`. -/
structure Run where
  service : String
  scenario : String
  runner : String
deriving DecidableEq, Repr

derive_wire Run

/-- The name of a run's snapshot and trace file: the scenario's, or `<scenario>.<runner>` for a peer's run. -/
def Run.stem (r : Run) : String := if r.runner == r.service then r.scenario else r.scenario ++ "." ++ r.runner

def Run.ref (r : Run) : Spec.Ref := { service := r.service, name := r.scenario }

structure Expected where
  service : String
  scenario : String
  runner : String
  /-- Whether the run is compared. A compared run's file is compared when present and reported when missing. The file
  of a run that is not compared is ignored. -/
  compared : Bool
deriving DecidableEq, Repr

derive_wire Expected

def Expected.toRun (e : Expected) : Run := { service := e.service, scenario := e.scenario, runner := e.runner }

/-- The subfolder `service` of the trace folder, or the snapshot folder of `service`. -/
structure Folder where
  service : String
  entries : List Entry
deriving DecidableEq, Repr

derive_wire Folder

/-- An entry of the trace folder or of its subfolder `service`, an entry of the snapshot folder of `service`, or a
scenario. -/
inductive At where
  | traceEntry (service : Option String) (entry : String)
  | snapshotEntry (service entry : String)
  | scenario (scenario : Spec.Ref)
deriving DecidableEq, Repr

derive_wire At tag "kind" skip_serializing_none

def unknownTraceEntry (place : At) : At × Uncomparable := (place, .unknownTraceEntry)

def runsOf (expected : List Expected) (service : String) : List Run :=
  (expected.filter (·.service == service)).map (·.toRun)

def comparedRuns (expected : List Expected) (service : String) : List Run :=
  (expected.filter fun e => e.service == service && e.compared).map (·.toRun)

def entriesIn (folders : List Folder) (service : String) : List Entry :=
  ((folders.find? (·.service == service)).map (·.entries)).getD []

/-- The violations of the subfolder of a service that is not a service of the spec. -/
def unknownServiceViolations (f : Folder) : List (At × Uncomparable) :=
  let p := pair id [] f.entries
  p.extra.map (fun n => (.traceEntry (some f.service) (n ++ ".jsonl"), .unknownService f.service)) ++
    p.unknown.map fun e => unknownTraceEntry (.traceEntry (some f.service) e)

structure TracePairing where
  /-- The traces that verify compares with their snapshots. -/
  compare : List Run
  /-- The traces of external services, which verify checks against their contracts. -/
  contract : List Spec.Ref
  violations : List (At × Uncomparable)

/-- The pairing of one service's traces. An external service pairs every trace name with its contract. -/
def servicePairing (expected : List Expected) (folders : List Folder) : String × Bool → TracePairing
  | (service, external) =>
    let p := pair Run.stem (if external then [] else comparedRuns expected service) (entriesIn folders service)
    let unknownEntries := p.unknown.map fun e => unknownTraceEntry (.traceEntry (some service) e)
    if external then
      { compare := [], contract := p.extra.map fun name => { service, name }, violations := unknownEntries }
    else
      { compare := p.paired, contract := []
        violations := unknownEntries ++
          (pair Run.stem (runsOf expected service) (entriesIn folders service)).extra.map (fun n =>
            (.traceEntry (some service) (n ++ ".jsonl"), .unknownScenario { service, name := n })) ++
            p.missing.map fun r =>
              (.snapshotEntry service (r.stem ++ ".jsonl"), .missingTrace r.ref r.runner) }

/-- The pairing of the compared scenarios of each service that is not external with the traces in the subfolder of
the service. `services` holds each service name and whether it is external. `others` holds the entries of the trace
folder that are not folders. -/
def pairTraces (services : List (String × Bool)) (expected : List Expected) (others : List String)
    (folders : List Folder) : TracePairing :=
  { compare := services.flatMap fun s => (servicePairing expected folders s).compare
    contract := services.flatMap fun s => (servicePairing expected folders s).contract
    violations := others.map (fun e => unknownTraceEntry (.traceEntry none e)) ++
      (folders.filter fun f => (services.lookup f.service).isNone).flatMap unknownServiceViolations ++
      services.flatMap fun s => (servicePairing expected folders s).violations }

end Tazuna.Verify
