import Tazuna.Validation.Illegal

namespace Tazuna.Validation.Scenarios

open Tazuna.Data
open Tazuna.Syntax

def requests (d : Definition) (target : Ref) : Bool :=
  match d.body with
  | .automation _ command _ _ => command == some target
  | .machine c | .screen c => c.commands.any (·.2 == some target) || c.queries.any (·.2 == some target)
  | _ => false

def notRequestedAnswers (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input with
      | .answer (some sender) (some target) =>
        if s.definitions.any fun d => d.ref == sender && requests d target then none
        else some (.notRequested sc.ref i)
      | _ => none

def resultsOfPlacedTwice (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input with
      | .event (some positions) => if 1 < positions.length then some (.resultOfPlacedTwice sc.ref i) else none
      | _ => none

def resultsOfUnplaced (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input with
      | .event (some positions) => if positions.any (· < i) then none else some (.resultOfUnplaced sc.ref i)
      | _ => none

def scenariosOfExternalServices (s : Structure) : List Illegal :=
  s.scenarios.filterMap fun sc =>
    if s.services.any fun sv => sv.name == sc.service && sv.external then some (.scenarioOfExternalService sc.ref)
    else none

def check (s : Structure) : List Illegal :=
  notRequestedAnswers s ++ resultsOfPlacedTwice s ++ resultsOfUnplaced s ++ scenariosOfExternalServices s

end Tazuna.Validation.Scenarios
