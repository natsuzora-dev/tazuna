import Tazuna.Semantics.Service.Chart.Basic
import Tazuna.Semantics.Service.Instance

/-! This module defines how the internal queue and the search name a step. -/

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
A step as the internal queue and the search name it. The search treats two steps with equal names as one, so a name
holds what the step runs and what its work came with, but not the step that caused it or the Queued it answers. A
receive or reaction step takes one event, of the groups `delivered` that its work received; a name must not depend on
which events of those groups other steps took, since the search reorders them. `answer` is the answer as written.
-/
inductive StepName where
  | start (id : InstanceId)
  | receive (id : InstanceId) (received : Received) (delivered : List (List Received))
  | always (id : InstanceId)
  | onDone (id : InstanceId)
  | opensDone (id : InstanceId) (state key : String)
  | activities (id : InstanceId) (state : String)
  | deadline (id : InstanceId) (state name : String)
  | reaction (automation : String) (event : Ir.Ref) (payload : Value) (delivered : List (List Value))
  | command (activity : Activity) (sender : Requester) (input : Value)
  | answer (activity : Activity) (sender : Requester) (input : Value) (answer : Value)
  /--
  The arrival of the message `message` of a tie (Tie.arrivals), its id as the receiver's trace writes it, which carries
  `definition`'s request or event, or answers or ends one.
  -/
  | arrival (definition : Ir.Ref) (message : String)
deriving DecidableEq, Repr, Inhabited

derive_wire StepName tag "kind"

def StepName.isDeadline : StepName → Bool
  | .deadline .. => true
  | _ => false

def StepName.isArrival : StepName → Bool
  | .arrival .. => true
  | _ => false

/-- The definition of the step, in service `service`. -/
def StepName.definition (service : String) : StepName → Ir.Ref
  | .start i | .receive i .. | .always i | .onDone i | .opensDone i _ _ | .activities i _ | .deadline i _ _ =>
    { service, name := i.chart }
  | .reaction a .. => { service, name := a }
  | .command _ sender _ | .answer _ sender _ _ => { service, name := sender.sender }
  | .arrival definition _ => definition

end Tazuna.Semantics.Service
