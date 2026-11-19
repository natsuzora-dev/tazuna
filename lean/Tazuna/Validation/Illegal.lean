import Tazuna.Data.Group
import Tazuna.Spec.Structure

namespace Tazuna.Validation

open Tazuna.Data

/-- A form that the spec must not have, which `check` finds from the structure without running the spec. -/
inductive Illegal where
  /--
  The automations after `definition` in the cycle, empty when `definition` receives an event of its own command.
  `check` reports none exactly when no automation that commands its own service leads back to itself
  (`no_automation_returns`).
  -/
  | automationCycle (definition : Spec.Ref) (chain : List Spec.Ref)
  /--
  A screen that no screen opens has the `keys` of input, requires, output, and ensures, in this order. Only a screen
  that opens it gives the input and reads the output.
  -/
  | missingParent (definition : Spec.Ref) (keys : List String)
  /--
  The chart reads under `key` a query of its own service. `check` reports none exactly when every chart reads only
  queries of other services (`queries_of_other_services`).
  -/
  | ownQuery (definition : Spec.Ref) (key : String)
  /--
  The chart's own offers have no entry for `control`. They list every control, `any` for every payload, so that what a
  state does not offer is written, not left out.
  -/
  | unlistedControl (definition : Spec.Ref) (control : String)
  /--
  `statePath` leads from the state of an unguarded always transition back to that state. `check` reports none exactly
  when no unguarded always transition can reach its source again (`unguarded_always_does_not_return`).
  -/
  | alwaysCycle (definition : Spec.Ref) (statePath : List String)
  /--
  The command lists in its emits `event`, an event of another service. `check` reports none exactly when every command
  lists only events of its own service (`commands_emit_own_events`), and then an accepted command emits only those
  (`accepted_command_emits_own_events`).
  -/
  | foreignEvent (definition : Spec.Ref) (event : Spec.Ref)
  /--
  A binds or requires key of the command or query, which a requires rejection may name as its reason, is an array index
  such as `"1"`. JavaScript lists such keys before the others (ECMA-262 OrdinaryOwnPropertyKeys), so the written order
  would not decide which failing condition gives the reason.
  -/
  | indexReason (definition : Spec.Ref) (reason : String)
  /--
  The contract of service `contract` lists under `key` a definition of another service. `check` reports none exactly
  when every contract lists only definitions of its own service (`members_of_own_service`).
  -/
  | foreignMember (contract key : String)

derive_group Illegal

end Tazuna.Validation
