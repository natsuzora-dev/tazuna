import Tazuna.Semantics.Service.Restart

/-!
Each running service of a simulation takes each message it receives by the one-service semantics (Service).
The simulation names a message by the sender's id of it; its receiver writes it with the id `<sender>/<id>`, unique
among the messages it receives, and answers it with that id.
-/

namespace Tazuna.Semantics.Sim

open Tazuna.Ir Tazuna.Semantics.Service

/--
The id by which the receiver of a message from `sender` names the sender's id `id` of it. Only another service's
message has a received id, and a service sends on only its own lines, so a received `id` stays as it is.
-/
def receivedId (sender : String) : LineId → LineId
  | .own id => .received sender id
  | id => id

/-- The sender's id of a message that `service` received with the id `id`, when `service` sent it. -/
def sentId? (service : String) : LineId → Option LineId
  | .received sender id => if sender == service then some (.own id) else none
  | .own _ => none

variable {m : Type → Type} [Monad m] [MonadNote m]

/--
The state after the message with body `body`, which `sender` sent with id `id`, arrives at the service. An event names
its resultOf by the id of the request, which is the service's own request when `sender` received it from the service.
-/
def arriveFrom (st : Service) (fs : Functions m) (s : Service.State) (sender : String) (id : LineId) (body : LineBody) :
    m Service.State :=
  let given := some (receivedId sender id)
  match body with
  | .command n input caller => send st fs s n given input caller
  | .query n input caller => call st fs s n given input caller
  | .subscribe n input caller => subscribe st fs s n given input caller
  | .unsubscribe to => endSubscription st fs s (receivedId sender to)
  | .answer to a => match sentId? st.service to with
    | some own => answerIn st fs s (receivedId sender id) own a
    | none => pure s
  | .event n payload resultOf =>
    receive st fs s n (receivedId sender id) payload (resultOf.bind (sentId? st.service))
  | _ => pure s

/--
A message that one line delivers with others: what `sender` sent with id `id` and body `body`, a request or an
event, or what answers or ends one. One line delivers at most one message per channel (Sim's
messagesOf), so its messages arrive in any order.
-/
structure Arrival where
  sender : String
  id : LineId
  body : LineBody

/--
The state after the messages `arrivals` that one line delivers arrive, each as its own message, in sending order. Nothing
outside tells which arrives first; prove checks that their order changes no outcome.
-/
def arriveAll (st : Service) (fs : Functions m) (arrivals : List Arrival) (s : Service.State) : m Service.State :=
  go arrivals s
where
  go : List Arrival → Service.State → m Service.State
    | [], s => pure s
    | a :: more, s => do
      if s.halted.isSome then return s
      go more (← arriveFrom st fs s a.sender a.id a.body)

end Tazuna.Semantics.Sim
