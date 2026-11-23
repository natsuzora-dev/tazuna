import Tazuna.Semantics.Validation.Automations
import Tazuna.Semantics.Validation.Charts
import Tazuna.Semantics.Validation.Commands
import Tazuna.Semantics.Validation.Contracts
import Tazuna.Semantics.Validation.Schemas

namespace Tazuna.Semantics.Validation

open Tazuna.Ir

def inexactWithins (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    match d.body with
    | .entity e => (e.responses.filter (!·.isDuration)).map fun r => .inexactWithin d.ref r.name
    | _ => []

def check (s : Structure) : List Illegal :=
  Automations.check s ++ Charts.check s ++ Commands.check s ++ Contracts.check s ++ Schemas.check s ++
    inexactWithins s

end Tazuna.Semantics.Validation
