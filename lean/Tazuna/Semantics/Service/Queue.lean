import Tazuna.Semantics.Service.Clock
import Tazuna.Semantics.Service.Screen.Subscription
import Tazuna.Semantics.Service.Query
import Tazuna.Semantics.Service.Response

/-!
Each message runs to completion: the service processes external messages one at a time, and each due deadline is its
own message.
-/

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

def afterMessage [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  if s.halted.isSome then pure s else
  publish st fs s

/--
afterMessage, noted as the end of the current message, whose state the next message may observe in another order, and
then the responses' observation of that visible state.
-/
def endMessage [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  let s ← afterMessage st fs s
  observeResponses st fs s

/--
The state after the deadlines due by `to` fire, each as its own message. An overdue deadline fires at the current time.
Deadlines due at one time fire in the order they were armed (earliestDeadline); prove checks that their order changes
no outcome.
-/
def fireDue [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (to : Time) : Nat → State → m State
  | 0, s =>
    pure (if s.halted.isNone && (earliestDeadline s.deadlines to).isSome then
      s.report (.fault (.exceededDueDeadlines Limit.dueDeadlines.max)) else s)
  | fuel + 1, s =>
    if s.halted.isSome then pure s else
    match earliestDeadline s.deadlines to with
    | none => pure s
    | some t => do
      let s := s.passTime st t.time
      let s := s.newMessage
      let (s, step) := s.newStep (.deadline t.armedBy)
      let r ← settled fs st step (some t.machine) (fire fs st step t) ⟨s, {}⟩
      let s ← drain st fs Limit.messageWork.max r.state r.queue
      let s ← endMessage st fs s
      fireDue st fs to fuel s

def finish [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  let s ← endMessage st fs s
  fireDue st fs s.now Limit.dueDeadlines.max s

def message [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (q : Queue) : m State := do
  let s ← drain st fs Limit.messageWork.max s q
  finish st fs s

end Tazuna.Semantics.Service
