import Tazuna.Data.Group
import Tazuna.Spec.Structure

namespace Tazuna.Service

open Tazuna.Data

/--
A part that no trace's replay reached, which verify --coverage reports. A run notes each part
of a command, query, automation, or chart that it reaches (Note.reached). A run evaluates bindings and conditions in
order and stops at the first null binding or false condition, so `bindsRejection`, `requiresRejection`,
`automationBindingNull`, `automationGuard` with `met` false, and `guardFalse` name only that first one.
-/
inductive Uncovered where
  /-- A request to the command or query. -/
  | request (definition : Spec.Ref)
  /-- An answer that accepts or fulfills a request to the command or query. -/
  | successAnswer (definition : Spec.Ref)
  /-- A rejection of the request because its binding `binding` is null. -/
  | bindsRejection (definition : Spec.Ref) (binding : String)
  /-- A rejection of the request because its requires `condition` is false. -/
  | requiresRejection (definition : Spec.Ref) (condition : String)
  /-- A run of the automation. -/
  | automation (definition : Spec.Ref)
  /-- A run of the automation in which its binding `binding` has a value. -/
  | automationBindingValue (definition : Spec.Ref) (binding : String)
  /-- A run of the automation in which its binding `binding` is null. -/
  | automationBindingNull (definition : Spec.Ref) (binding : String)
  /-- A run of the automation in which its guard `condition` has the value `met`. -/
  | automationGuard (definition : Spec.Ref) (condition : String) (met : Bool)
  /-- A firing of the chart's transition `transition`. -/
  | transition (definition : Spec.Ref) (transition : Spec.TransitionRef)
  /-- An evaluation of the guard `condition` of the chart's transition `transition` that is false. -/
  | guardFalse (definition : Spec.Ref) (transition : Spec.TransitionRef) (condition : String)
  /-- An entry into the chart's state `state`. -/
  | state (definition : Spec.Ref) (state : String)
deriving DecidableEq, Repr, Inhabited

derive_group Uncovered

end Tazuna.Service
