import Tazuna.Ir.Group
import Tazuna.Ir.Structure

namespace Tazuna.Semantics.Service

open Tazuna.Ir

/--
A part that no trace's replay reached, which verify --coverage reports. A run notes each part
of a command, query, automation, or chart that it reaches (Note.reached). A run evaluates bindings and conditions in
order and stops at the first null binding or false condition, so `bindsRejection`, `requiresRejection`,
`automationBindingNull`, `automationGuard` with `met` false, and `guardFalse` name only that first one.
-/
inductive Uncovered where
  /-- A request to the command or query. -/
  | request (definition : Ir.Ref)
  /-- An answer that accepts or fulfills a request to the command or query. -/
  | successAnswer (definition : Ir.Ref)
  /-- A rejection of the request because its binding `binding` is null. -/
  | bindsRejection (definition : Ir.Ref) (binding : String)
  /-- A rejection of the request because its requires `condition` is false. -/
  | requiresRejection (definition : Ir.Ref) (condition : String)
  /-- A run of the automation. -/
  | automation (definition : Ir.Ref)
  /-- A run of the automation in which its binding `binding` has a value. -/
  | automationBindingValue (definition : Ir.Ref) (binding : String)
  /-- A run of the automation in which its binding `binding` is null. -/
  | automationBindingNull (definition : Ir.Ref) (binding : String)
  /-- A run of the automation in which its guard `condition` has the value `met`. -/
  | automationGuard (definition : Ir.Ref) (condition : String) (met : Bool)
  /-- A firing of the chart's transition `transition`. -/
  | transition (definition : Ir.Ref) (transition : Ir.TransitionRef)
  /-- An evaluation of the guard `condition` of the chart's transition `transition` that is false. -/
  | guardFalse (definition : Ir.Ref) (transition : Ir.TransitionRef) (condition : String)
  /-- An entry into the chart's state `state`. -/
  | state (definition : Ir.Ref) (state : String)
deriving DecidableEq, Repr, Inhabited

derive_group Uncovered

end Tazuna.Semantics.Service
