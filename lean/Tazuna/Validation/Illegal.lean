import Tazuna.Data.Group
import Tazuna.Spec.Structure

namespace Tazuna.Validation

open Tazuna.Data

/-- A form that the spec must not have, which `check` finds from the structure without running the spec. -/
inductive Illegal where
  /--
  The automation `definition` commands its own service and leads back to itself through the automations `chain`, empty
  when `definition` receives an event of its own command. `check` reports none exactly when no automation that commands its own service leads back to itself
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
  The automation or chart sends `target`, whose callers list neither the sender's service nor, when the sender is a
  screen, which sends as the user that operates it, an entity. `check` reports none exactly when every sent request
  lists its sender (`Checked.callersListed`), so no spec sender's request is rejected with `permission-denied` by kind.
  -/
  | unlistedCaller (definition : Spec.Ref) (target : Spec.Ref)
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
  /--
  The chart's history state `history` may restore `state`, which has parameters (`held`). A restore enters `state`
  without an edge whose `with` fills them. `check` reports none exactly when no history state restores a state with
  parameters (`Checked.heldNotRestored`).
  -/
  | restoredHeld (definition : Spec.Ref) (state history : String)
  /--
  The delay of the deadline `deadline` of `state` is no safe integer, so the run cannot add it to an instant in
  milliseconds. `check` reports none exactly when every delay is a safe integer (`Checked.delaysExact`).
  -/
  | inexactDelay (definition : Spec.Ref) (state deadline : String)
  /--
  The delay of the deadline `deadline` of `state` is below zero, so it would be due before `state` was entered.
  `check` reports none exactly when no delay is below zero (`Checked.delaysNonNegative`).
  -/
  | negativeDelay (definition : Spec.Ref) (state deadline : String)
  /--
  The sortedBy array at `path` of the definition's schemas sorts by `key`, which is optional or has a default, so an
  element from outside may leave it out and have no place in the order, or whose value is no number or date label, so
  tazuna has no order to sort by. `check` reports none exactly when every sort key is required with no default and is
  one of these (`Checked.sortKeysOrdered`).
  -/
  | unorderedSortKey (definition : Spec.Ref) (path : List String) (key : String)
  /--
  The schema at `path` of a map state's key declares a default, which never fills: items is typed by the key's output
  type, in which that field is required. `check` reports none exactly when no map state's key declares a default at any
  depth (`Checked.mapKeysUndefaulted`).
  -/
  | defaultedMapKey (definition : Spec.Ref) (path : List String)
  /--
  The union at `path` of the definition's schemas holds a collection, and one value can fit two of its options by type,
  const or enum, closed fields, and required fields, so the option whose order sorts the value would be a guess. `check`
  reports none exactly when every such union tells its options apart (`Checked.unionsApart`).
  -/
  | ambiguousUnion (definition : Spec.Ref) (path : List String)

derive_group Illegal

end Tazuna.Validation
