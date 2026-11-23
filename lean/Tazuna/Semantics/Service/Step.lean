import Tazuna.Semantics.Service.Chart.Basic
import Tazuna.Semantics.Service.Instance

/-! This module defines the senders of requests and the names of the steps whose order prove compares. -/

namespace Tazuna.Semantics.Service

open Tazuna.Ir

/-- The sender of a request. -/
inductive Requester where
  /-- The machine `machine`, which sent the request on entering `state`. -/
  | state (machine : InstanceId) (state : String)
  /-- The screen `machine`, which subscribed the query of shows slot `slot`; answers keep coming until it ends. -/
  | slot (machine : InstanceId) (slot : String)
  | automation (automation : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Requester tag "kind"

def Requester.machine? : Requester → Option InstanceId
  | .state m _ | .slot m _ => some m
  | .automation _ => none

/-- The state that sent the request, none for a shows slot or an automation. -/
def Requester.slot? : Requester → Option String
  | .slot _ k => some k
  | _ => none

/-- The definition that sent the request: the chart of the sending instance, or the automation. -/
def Requester.sender : Requester → String
  | .state m _ | .slot m _ => m.chart
  | .automation a => a

/-- An event that a machine receives: the key of its `receives` and the event's payload. -/
structure Received where
  key : String
  payload : Value
deriving DecidableEq, Repr, Inhabited

derive_wire Received

/--
A step whose order prove compares (ChoiceDependent): an own command that an automation sends, a deadline of a state
that fires, or the arrival of a message from another service, by the id that the receiver's trace writes for it.
-/
inductive StepName where
  | command (activity : Activity) (sender : Requester) (input : Value)
  | deadline (id : InstanceId) (state name : String)
  | arrival (definition : Ir.Ref) (message : String)
deriving DecidableEq, Repr, Inhabited

derive_wire StepName tag "kind"

end Tazuna.Semantics.Service
