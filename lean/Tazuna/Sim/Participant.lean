import Tazuna.Service.Restart

/-!
A running service of a simulation is a participant: the one-service semantics (Service) take each message it receives.
The simulation names a message by the sender's id of it; its receiver writes it with the id `<sender>/<id>`, unique
among the messages it receives, and answers it with that id.
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Semantics

/-- The id by which the receiver of a message from `sender` names it. -/
def receivedId (sender id : String) : String := s!"{sender}/{id}"

/-- The sender's id of a message that `service` received with the id `id`, when `service` sent it. -/
def sentId? (service id : String) : Option String :=
  if id.startsWith (service ++ "/") then some (id.drop (service.length + 1)).toString else none

/-- The service whose message `id` names, when another service sent it. -/
def senderOf? (id : String) : Option String :=
  match id.splitOn "/" with
  | [sender, _] => some sender
  | _ => none

/-- The name by which `receiver` names the definition that `sender` names `name`. -/
def renamed (sender receiver name : String) : String :=
  (Syntax.Ref.ofTraceName sender name).traceName receiver

variable {m : Type → Type} [Monad m] [MonadNote m]

/--
The state after the answer `a` to the request `to` arrives. A later event's resultOf names the request by its id, so the
answer is kept under it. A request that no longer waits, as after a restart, takes the answer as a message with no
effect.
-/
def answerIn (st : Service) (fs : Functions m) (s : State) (to : String) (a : Answer) : m State :=
  match s.pending.find? (·.id == to) with
  | some p => answerRequest st fs { s with mocks := (to, p, a) :: s.mocks } p a
  | none => message st fs (s.write .in none (.answer to a)).1.newMessage {}

/--
The state after the message with body `body`, which `sender` sent with id `id`, arrives at the service. An event names
its resultOf by the id of the request, which is the service's own request when `sender` received it from the service.
-/
def arriveFrom (st : Service) (fs : Functions m) (s : State) (sender id : String) (body : LineBody) : m State :=
  let name := renamed sender st.service
  let given := some (receivedId sender id)
  match body with
  | .command n input => send st fs s (name n) given input
  | .query n input => call st fs s (name n) given input
  | .subscribe n input => subscribe st fs s (name n) given input
  | .unsubscribe to => endSubscription st fs s (receivedId sender to)
  | .answer to a => match sentId? st.service to with
    | some own => answerIn st fs s own a
    | none => pure s
  | .event n payload resultOf =>
    receive st fs s (name n) given payload (resultOf.bind (sentId? st.service))
  | _ => pure s

end Tazuna.Sim
