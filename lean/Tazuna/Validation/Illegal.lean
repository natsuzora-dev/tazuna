import Tazuna.Data.Group
import Tazuna.Syntax.Structure

namespace Tazuna.Validation

open Tazuna.Data

/-- A form that the spec must not have, which `check` finds from the structure without running the spec. -/
inductive Illegal where
  /--
  The automations after `definition` in the cycle, empty when `definition` receives an event of its own command.
  -/
  | automationCycle (definition : Syntax.Ref) (chain : List Syntax.Ref)
  /--
  A screen that no screen opens has the `keys` of input, requires, output, and ensures, in this order; only a screen
  that opens it gives the input and reads the output.
  -/
  | missingParent (definition : Syntax.Ref) (keys : List String)
  /-- The chart reads under `key` a query of its own service. -/
  | ownQuery (definition : Syntax.Ref) (key : String)
  /-- `statePath` leads from the state of an unguarded always transition back to that state. -/
  | alwaysCycle (definition : Syntax.Ref) (statePath : List String)
  | foreignEvent (definition : Syntax.Ref) (event : Syntax.Ref)
  /-- The contract of service `contract` lists under `key` a definition of another service. -/
  | foreignMember (contract key : String)
  /-- The sender of the answer input does not request its target. -/
  | unrequestedAnswer (scenario : Syntax.Ref) (input : Nat)
  /-- The resultOf of the event input names an answer input that the scenario places more than once. -/
  | resultOfPlacedTwice (scenario : Syntax.Ref) (input : Nat)
  /-- The scenario places the resultOf answer of the event input only after the event, or not at all. -/
  | resultOfUnplaced (scenario : Syntax.Ref) (input : Nat)
  | scenarioOfExternalService (scenario : Syntax.Ref)
  /--
  The input has `value`, of the form of a createKey value of the keyed entity `entity` that counts the entity's keys. A
  scenario names a createKey value on the line that creates it (Step.keys), as no caller knows how many keys an
  implementation has made.
  -/
  | countedKey (scenario : Syntax.Ref) (input : Nat) (value : String) (entity : Syntax.Ref)

derive_group Illegal

end Tazuna.Validation
