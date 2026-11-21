import Tazuna.Validation.Automations
import Tazuna.Validation.Charts
import Tazuna.Validation.Commands
import Tazuna.Validation.Contracts
import Tazuna.Validation.Explores
import Tazuna.Validation.Schemas

namespace Tazuna.Validation

open Tazuna.Spec

def check (s : Structure) : List Illegal :=
  Automations.check s ++ Charts.check s ++ Commands.check s ++ Contracts.check s ++ Schemas.check s ++ Explores.check s

end Tazuna.Validation
