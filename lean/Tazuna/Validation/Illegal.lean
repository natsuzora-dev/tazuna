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
  /--
  The sender of the answer input does not request its target. The `scenario` of this and the following kinds is a
  scenario, or a contract's start state named `states.<state>`.
  -/
  | unrequestedAnswer (scenario : Syntax.Ref) (input : Nat)
  /--
  The input names an input that its run takes more than once: the mock of an event's resultOf, or the subscribe input of
  an unsubscribe. A run takes the scenario's inputs to its service, or a state with the scenario's elsewhere inputs to
  the state's service.
  -/
  | namedInputPlacedTwice (scenario : Syntax.Ref) (input : Nat)
  /--
  The run of the input takes the input that it names (ScenarioLine.names) only after it, from another sender, or not at
  all: a subscription that a from line opens is ended by a from line of the same peer, and any other by a plain line.
  -/
  | namedInputUnplaced (scenario : Syntax.Ref) (input : Nat)
  | scenarioOfExternalService (scenario : Syntax.Ref)
  /--
  The input has `value`, among its values or `keys` names, of the form of a createKey value of the keyed entity
  `entity` of the scenario's service or of a peer that counts the entity's keys. A scenario names a createKey value on
  the line that creates it (Step.keys), as no caller knows how many keys an implementation has made. Any string field
  counts, such as a title.
  -/
  | countedKey (scenario : Syntax.Ref) (input : Nat) (value : String) (entity : Syntax.Ref)
  /-- The input's `keys` gives `name` to a createKey value of `entity` that an earlier line of its run, or the input, named. -/
  | keyNamedTwice (scenario : Syntax.Ref) (input : Nat) (entity : String) (name : String)
  /-- The input has the value `name`, which a later line's `keys` gives a createKey value. -/
  | keyUsedBeforeNamed (scenario : Syntax.Ref) (input : Nat) (name : String)

derive_group Illegal

end Tazuna.Validation
