import Tazuna.Service.Restart

/-!
Each running service of a simulation takes each message it receives by the one-service semantics (Service).
The simulation names a message by the sender's id of it; its receiver writes it with the id `<sender>/<id>`, unique
among the messages it receives, and answers it with that id.
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Service

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
def arriveFrom (st : Service) (fs : Functions m) (s : State) (sender : String) (id : LineId) (body : LineBody) :
    m State :=
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
A message of a tie: what `sender` sent with id `id` and body `body`, which carries `definition`'s request or event, or
answers or ends one. A tie has at most one message per channel (Sim's messagesOf), so its messages arrive in any order.
-/
structure Arrival where
  sender : String
  id : LineId
  body : LineBody
  definition : Spec.Ref

/-- The name of the step in which `a` arrives: each message has its own, so equal messages are ordered like any others. -/
def Arrival.name (a : Arrival) : StepName :=
  .arrival a.definition (receivedId a.sender a.id).text

/--
The state after the messages `arrivals` that one line delivers arrive, each as its own message in a step of the tie
`first`, the step number of the first: nothing outside tells which arrives first, so the next entry of the input's
`stepOrder` that names an arrival chooses it, as chooseDeadline chooses a deadline of a tie, and without one it is the
first left in sending order. The step belongs to the message that the arrival opens, whatever messages the processing
opens after it, and what the processing does outside any step belongs to the step.
-/
def arriveAll (st : Service) (fs : Functions m) (arrivals : List Arrival) (s : State) : m State :=
  go s.steps.size arrivals s
where
  go (first : Nat) : List Arrival → State → m State
    | [], s => pure s
    | next :: more, s => do
      if s.halted.isSome then return s
      let remaining := next :: more
      let chosen : Except InvalidInput (Fin remaining.length × List StepName) := match s.stepOrder with
        | named :: rest =>
          if !named.isArrival then .ok (⟨0, by simp [remaining]⟩, s.stepOrder) else
          match remaining.findFinIdx? (·.name == named) with
          | some i => .ok (i, rest)
          | none => .error (.unreadyStep named (remaining.map (·.name)))
        | [] => .ok (⟨0, by simp [remaining]⟩, [])
      match chosen with
      | .error e => return s.report (.invalidInput e)
      | .ok (i, stepOrder) =>
        let a := remaining[i]
        let (s, step) := { s with stepOrder }.newStep (.arrival (.arrivals first))
          (message := some (s.messageCount + 1))
        MonadNote.note (.arrivalBegins step a.name)
        let t ← arriveFrom st fs s a.sender a.id a.body
        MonadNote.note .arrivalEnds
        go first (remaining.eraseIdx i) t
  termination_by arrivals => arrivals.length
  decreasing_by simp only [remaining, List.length_eraseIdx_of_lt i.isLt]; simp

end Tazuna.Sim
