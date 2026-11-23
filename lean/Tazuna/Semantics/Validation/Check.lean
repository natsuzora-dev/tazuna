import Tazuna.Semantics.Validation.Automations
import Tazuna.Semantics.Validation.Charts
import Tazuna.Semantics.Validation.Commands
import Tazuna.Semantics.Validation.Contracts
import Tazuna.Semantics.Validation.Schemas

namespace Tazuna.Semantics.Validation

open Tazuna.Ir

def check (s : Structure) : List Illegal :=
  Automations.check s ++ Charts.check s ++ Commands.check s ++ Contracts.check s ++ Schemas.check s

end Tazuna.Semantics.Validation
