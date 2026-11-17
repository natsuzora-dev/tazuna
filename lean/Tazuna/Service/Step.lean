import Tazuna.Spec.Structure
import Tazuna.Service.Instance

/-! This module defines how the internal queue and the search name a step. -/

namespace Tazuna.Service

open Tazuna.Data

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
A step as the internal queue and the search name it: by its definition and what tells it apart from another step of
that definition. The search treats two steps with equal names as one, so equal names must run equal work. `input` of a
command or answer is the request's input. A receive step takes one event.
-/
inductive StepName where
  | start (id : InstanceId)
  | receive (id : InstanceId) (received : Received)
  | always (id : InstanceId)
  | onDone (id : InstanceId)
  | opensDone (id : InstanceId) (state key : String)
  | activities (id : InstanceId) (state : String)
  | deadline (id : InstanceId) (state name : String)
  | reaction (automation : String) (event : Spec.Ref) (payload : Value)
  | command (command : Spec.Ref) (sender : Requester) (input : Value)
  | answer (command : Spec.Ref) (sender : Requester) (input : Value)
deriving DecidableEq, Repr, Inhabited

derive_wire StepName tag "kind"

def StepName.isDeadline : StepName → Bool
  | .deadline .. => true
  | _ => false

/-- The definition of the step, in service `service`. -/
def StepName.definition (service : String) : StepName → Spec.Ref
  | .start i | .receive i _ | .always i | .onDone i | .opensDone i _ _ | .activities i _ | .deadline i _ _ =>
    { service, name := i.chart }
  | .reaction a _ _ => { service, name := a }
  | .command _ sender _ | .answer _ sender _ => { service, name := sender.sender }

end Tazuna.Service
