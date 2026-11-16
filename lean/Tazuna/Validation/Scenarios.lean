import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Scenarios

open Tazuna.Data
open Tazuna.Syntax

def requests (d : Definition) (target : Ref) : Bool :=
  match d.body with
  | .automation _ command _ _ => command == some target
  | .machine c | .screen c => c.commands.any (·.2 == some target) || c.queries.any (·.2 == some target)
  | _ => false

def unrequestedAnswers (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (l, i) =>
      match l.input with
      | .answer (some sender) (some target) =>
        if s.definitions.any fun d => d.ref == sender && requests d target then none
        else some (.unrequestedAnswer sc.ref (i + 1))
      | _ => none

/-- The runs of the scenario: the run of its service, then the runs of the peers that its elsewhere lines go to. -/
def runsOf (sc : Scenario) : List (Option String) := (none :: sc.inputs.map (·.run)).eraseDups

/--
The lines that the run `run` of the scenario takes, each with its index in the scenario, or none for a line of the
state that the scenario gives the run's peer, which comes first.
-/
def runLines (s : Structure) (sc : Scenario) (run : Option String) : List (ScenarioLine × Option Nat) :=
  let state := match run with
    | some p =>
      match sc.given.find? fun (g : Ref) => g.service == p with
      | some g => ((s.scenarios.find? fun (t : Scenario) => t.ref == g).map fun (t : Scenario) => t.inputs).getD []
      | none => []
    | none => []
  state.map (·, none) ++ (sc.inputs.zipIdx.filter (·.1.run == run)).map fun (l, i) => (l, some i)

/--
Each line of the scenario, by its run (runsOf), with its index, the lines that its run takes before it, and all
lines that its run takes.
-/
def scopedLines (s : Structure) (sc : Scenario) : List (Nat × ScenarioLine × List ScenarioLine × List ScenarioLine) :=
  (runsOf sc).flatMap fun r =>
    let lines := runLines s sc r
    lines.zipIdx.filterMap fun ((l, o), k) => o.map fun i => (i, l, (lines.take k).map (·.1), lines.map (·.1))

def namedInputsPlacedTwice (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    (scopedLines s sc).filterMap fun (i, l, _, all) =>
      l.names.bind fun h =>
        if 1 < (all.filter (·.handle == some h)).length then some (.namedInputPlacedTwice sc.ref (i + 1)) else none

def namedInputsUnplaced (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    (scopedLines s sc).filterMap fun (i, l, before, _) =>
      l.names.bind fun h =>
        if before.any fun b => b.handle == some h && b.sentBy == l.sentBy then none
        else some (.namedInputUnplaced sc.ref (i + 1))

def keysNamedTwice (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    (scopedLines s sc).filterMap fun (i, l, before, _) =>
      (l.keyNames.zipIdx.find? fun (p, j) => before.any (p ∈ ·.keyNames) || p ∈ l.keyNames.take j).map
        fun ((e, n), _) => .keyNamedTwice sc.ref (i + 1) e n

def keysUsedBeforeNamed (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (l, i) =>
      (l.strings.find? fun v => (sc.inputs.drop (i + 1)).any fun m => m.keyNames.any (·.2 == v)).map
        (.keyUsedBeforeNamed sc.ref (i + 1))

def scenariosOfExternalServices (s : Structure) : List Illegal :=
  s.scenarios.filterMap fun sc =>
    if s.services.any fun sv => sv.name == sc.service && sv.external then some (.scenarioOfExternalService sc.ref)
    else none

def keyedEntities (s : Structure) : List Ref :=
  s.definitions.filterMap fun d =>
    match d.body with
    | .entity (some _) .. => some d.ref
    | _ => none

/-- The values of the line that countedKey checks: its strings, then its `keys` names. -/
def checkedValues (l : ScenarioLine) : List String := (l.strings ++ l.keyNames.map (·.2)).eraseDups

def countedKeys (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    let entities := (keyedEntities s).filter fun e => e.service == sc.service || sc.peers.contains e.service
    sc.inputs.zipIdx.flatMap fun (l, i) =>
      (checkedValues l).filterMap fun v =>
        (entities.find? (isKeyOf ·.name v)).map (.countedKey sc.ref (i + 1) v ·)

def check (s : Structure) : List Illegal :=
  unrequestedAnswers s ++ namedInputsPlacedTwice s ++ namedInputsUnplaced s ++ scenariosOfExternalServices s ++
    countedKeys s ++ keysNamedTwice s ++ keysUsedBeforeNamed s

end Tazuna.Validation.Scenarios
