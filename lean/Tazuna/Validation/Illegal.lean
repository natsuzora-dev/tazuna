import Tazuna.Data.Group
import Tazuna.Syntax.Structure

namespace Tazuna.Validation

open Tazuna.Data

/--
A form that the spec must not have, which `check` finds from the structure without running the spec.

For `notRequested`, `resultOfPlacedTwice`, `resultOfUnplaced`, and `scenarioOfExternalService`, `definition` names
the scenario. `input` is the position of a scenario input as written, counting from 0 with `at` included.
`resultOfUnplaced` means that the scenario places the event's resultOf mock only after the event, or not at all.

The `chain` of `automationCycle` lists the automations after `definition` in the cycle, and is empty when
`definition` receives an event of its own command. The `keys` of `keysWithoutParent` lists which of input, requires,
output, and ensures, in this order, a screen that no screen opens has; only a screen that opens it gives the input
and reads the output. The `path` of `alwaysCycle` leads from the state of an unguarded always transition back to
that state.
-/
inductive Illegal where
  | automationCycle (definition : Syntax.Ref) (chain : List Syntax.Ref)
  | keysWithoutParent (definition : Syntax.Ref) (keys : List String)
  | ownQuery (definition : Syntax.Ref) (key : String)
  | alwaysCycle (definition : Syntax.Ref) (path : List String)
  | foreignEvent (definition : Syntax.Ref) (event : Syntax.Ref)
  | foreignMember (contract key : String)
  | notRequested (definition : Syntax.Ref) (input : Nat)
  | resultOfPlacedTwice (definition : Syntax.Ref) (input : Nat)
  | resultOfUnplaced (definition : Syntax.Ref) (input : Nat)
  | scenarioOfExternalService (definition : Syntax.Ref)

derive_group Illegal

end Tazuna.Validation
