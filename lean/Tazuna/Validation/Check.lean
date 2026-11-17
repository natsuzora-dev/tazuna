import Tazuna.Validation.Automations
import Tazuna.Validation.Charts
import Tazuna.Validation.Commands
import Tazuna.Validation.Contracts

namespace Tazuna.Validation

open Tazuna.Spec

def check (s : Structure) : List Illegal :=
  Automations.check s ++ Charts.check s ++ Commands.check s ++ Contracts.check s

end Tazuna.Validation
