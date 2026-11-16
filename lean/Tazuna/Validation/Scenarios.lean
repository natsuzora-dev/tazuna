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
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input with
      | .answer (some sender) (some target) _ =>
        if s.definitions.any fun d => d.ref == sender && requests d target then none
        else some (.unrequestedAnswer sc.ref (i + 1))
      | _ => none

def resultsOfPlacedTwice (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input with
      | .event (some positions) _ => if 1 < positions.length then some (.resultOfPlacedTwice sc.ref (i + 1)) else none
      | _ => none

def resultsOfUnplaced (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input with
      | .event (some positions) _ => if positions.any (· < i) then none else some (.resultOfUnplaced sc.ref (i + 1))
      | _ => none

def scenariosOfExternalServices (s : Structure) : List Illegal :=
  s.scenarios.filterMap fun sc =>
    if s.services.any fun sv => sv.name == sc.service && sv.external then some (.scenarioOfExternalService sc.ref)
    else none

def keyedEntities (s : Structure) : List Ref :=
  s.definitions.filterMap fun d =>
    match d.body with
    | .entity (some _) .. => some d.ref
    | _ => none

def countedKeys (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.flatMap fun (input, i) =>
      input.strings.eraseDups.filterMap fun v =>
        ((keyedEntities s).find? (isKeyOf ·.name v)).map (.countedKey sc.ref (i + 1) v ·)

def check (s : Structure) : List Illegal :=
  unrequestedAnswers s ++ resultsOfPlacedTwice s ++ resultsOfUnplaced s ++ scenariosOfExternalServices s ++
    countedKeys s

end Tazuna.Validation.Scenarios
