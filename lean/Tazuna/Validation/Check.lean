import Tazuna.Validation.Automations
import Tazuna.Validation.Charts
import Tazuna.Validation.Commands
import Tazuna.Validation.Contracts
import Tazuna.Validation.Scenarios

namespace Tazuna.Validation

open Tazuna.Syntax

def check (s : Structure) : List Illegal :=
  Automations.check s ++ Charts.check s ++ Commands.check s ++ Contracts.check s ++ Scenarios.check s

end Tazuna.Validation
