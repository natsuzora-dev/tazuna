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

def namedInputsPlacedTwice (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input.named with
      | some positions => if 1 < positions.length then some (.namedInputPlacedTwice sc.ref (i + 1)) else none
      | none => none

def namedInputsUnplaced (s : Structure) : List Illegal :=
  s.scenarios.flatMap fun sc =>
    sc.inputs.zipIdx.filterMap fun (input, i) =>
      match input.named with
      | some positions => if positions.any (· < i) then none else some (.namedInputUnplaced sc.ref (i + 1))
      | none => none

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
  unrequestedAnswers s ++ namedInputsPlacedTwice s ++ namedInputsUnplaced s ++ scenariosOfExternalServices s ++
    countedKeys s

end Tazuna.Validation.Scenarios
