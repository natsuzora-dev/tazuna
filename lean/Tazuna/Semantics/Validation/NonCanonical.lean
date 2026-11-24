import Tazuna.Ir.Group
import Tazuna.Ir.Structure

namespace Tazuna.Semantics.Validation

open Tazuna.Ir

/-- Where an `onRejected` is written or left out. -/
inductive OnRejectedAt where
  /-- The automation's own, whose command may be rejected only with `unavailable`. -/
  | automation
  /-- The `onRejected` with `trigger` of a request of `state`. -/
  | request (state : String) (trigger : Ir.Trigger)
deriving Repr, Inhabited

derive_wire OnRejectedAt tag "kind"

/--
A form that changes no meaning but is not the one canonical way to write that meaning, which `Canonical.check` finds
from the structure and its program. TS finds the kinds that only the source shows.
-/
inductive NonCanonical where
  /-- A transition to its source state or a descendant of it has no `reenter`. -/
  | missingReenter (definition : Ir.Ref) (transition : Ir.TransitionRef)
  /-- A transition of the chart's own `on` has a `reenter`. -/
  | reenterOnRoot (definition : Ir.Ref) (transition : Ir.TransitionRef)
  /-- A transition to a state outside its source state has a `reenter`. -/
  | reenterOutsideSource (definition : Ir.Ref) (transition : Ir.TransitionRef)
  /-- A machine with one state, no context, and nothing to wait for, which turns one event into one command. -/
  | statelessMachine (definition : Ir.Ref)
  /-- An answer may be rejected, but the automation or the request `at` has no `onRejected`. -/
  | missingOnRejected (definition : Ir.Ref) («at» : OnRejectedAt)
  /-- The automation or the request `at` has an `onRejected`, but no answer can be rejected. -/
  | unreachableOnRejected (definition : Ir.Ref) («at» : OnRejectedAt)
  /-- No function of the command or automation reads the binding `binding` of its `binds`. -/
  | unreadBinding (definition : Ir.Ref) (binding : String)

derive_group NonCanonical

end Tazuna.Semantics.Validation
