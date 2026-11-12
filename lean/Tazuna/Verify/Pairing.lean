import Tazuna.Data.Pairing
import Tazuna.Verify.Uncomparable

namespace Tazuna.Verify

open Tazuna.Data

structure Scenario where
  service : String
  name : String
  /-- Whether the scenario is compared. A compared scenario's file is compared when present and reported when missing.
  The file of a scenario that is not compared is ignored. -/
  compared : Bool
deriving DecidableEq, Repr

/-- The subfolder `service` of the trace folder, or the snapshot folder of `service`. -/
structure Folder where
  service : String
  entries : List Entry
deriving DecidableEq, Repr

/-- An entry of the trace folder or of its subfolder `service`, an entry of the snapshot folder of `service`, or a
scenario. -/
inductive At where
  | entry (service : Option String) (name : String)
  | snapshotEntry (service name : String)
  | scenario (service name : String)
deriving DecidableEq, Repr

def unknownTraceEntry (place : At) : At × Uncomparable := (place, .unknownTraceEntry)

def entriesIn (folders : List Folder) (service : String) : List Entry :=
  ((folders.find? (·.service == service)).map (·.entries)).getD []

def scenarioNames (scenarios : List Scenario) (service : String) : List String :=
  (scenarios.filter (·.service == service)).map (·.name)

def comparedNames (scenarios : List Scenario) (service : String) : List String :=
  (scenarios.filter fun s => s.service == service && s.compared).map (·.name)

/-- The violations of the subfolder of a service that is not a service of the spec. -/
def unknownServiceViolations (f : Folder) : List (At × Uncomparable) :=
  let p := pair [] f.entries
  p.extra.map (fun n => (.entry (some f.service) (n ++ ".jsonl"), .unknownService f.service)) ++
    p.unknown.map fun e => unknownTraceEntry (.entry (some f.service) e)

structure TracePairing where
  /-- The traces that verify compares with their snapshots. -/
  compare : List (String × String)
  /-- The traces of external services, which verify checks against their contracts. -/
  contract : List (String × String)
  problems : List (At × Uncomparable)

/-- The pairing of one service's traces. An external service pairs every trace name with its contract. -/
def servicePairing (scenarios : List Scenario) (folders : List Folder) : String × Bool → TracePairing
  | (service, external) =>
    let p := pair (if external then [] else comparedNames scenarios service) (entriesIn folders service)
    let unknownEntries := p.unknown.map fun e => unknownTraceEntry (.entry (some service) e)
    if external then { compare := [], contract := p.extra.map ((service, ·)), problems := unknownEntries }
    else
      { compare := p.paired.map ((service, ·)), contract := []
        problems := unknownEntries ++
          (pair (scenarioNames scenarios service) (entriesIn folders service)).extra.map (fun n =>
            (.entry (some service) (n ++ ".jsonl"), .unknownScenario { service, name := n })) ++
            p.missing.map fun n => (.snapshotEntry service (n ++ ".jsonl"), .missingTrace { service, name := n }) }

/-- The pairing of the compared scenarios of each service that is not external with the traces in the subfolder of
the service. `services` holds each service name and whether it is external. `others` holds the entries of the trace
folder that are not folders. -/
def pairTraces (services : List (String × Bool)) (scenarios : List Scenario) (others : List String)
    (folders : List Folder) : TracePairing :=
  { compare := services.flatMap fun s => (servicePairing scenarios folders s).compare
    contract := services.flatMap fun s => (servicePairing scenarios folders s).contract
    problems := others.map (fun e => unknownTraceEntry (.entry none e)) ++
      (folders.filter fun f => (services.lookup f.service).isNone).flatMap unknownServiceViolations ++
      services.flatMap fun s => (servicePairing scenarios folders s).problems }

end Tazuna.Verify
