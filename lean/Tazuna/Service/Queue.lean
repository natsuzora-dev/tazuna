import Tazuna.Service.Clock
import Tazuna.Service.Screen.Subscription
import Tazuna.Service.Query
import Tazuna.Service.Response

/-!
Each message runs to completion: the service processes external messages one at a time, and each due deadline is its
own message.
-/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def afterMessage [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  if s.halted.isSome then pure s else
  publish st fs s

/--
afterMessage, noted as the end of the current message, whose state the next message may observe in another order, and
then the responses' observation of that visible state.
-/
def endMessage [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  MonadNote.note (.afterMessageBegins s.messageCount)
  let s ← afterMessage st fs s
  MonadNote.note .afterMessageEnds
  observeResponses st fs s

/--
The state after the deadlines due by `to` fire, each as its own message. An overdue deadline fires at the current time.
A tie starts when two or more deadlines are due at the earliest time and lasts until no deadline is due at that time;
chooseDeadline chooses each deadline that fires in it. `tie` is the time of the tie that the previous deadline fired in.
-/
def fireDue [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (to : Time) :
    Nat → Option Time → State → m State
  | 0, _, s =>
    pure (if s.halted.isNone && (earliestDeadline s.deadlines to).isSome then
      s.report (.fault (.exceededDueDeadlines Limit.dueDeadlines.max)) else s)
  | fuel + 1, tie, s =>
    if s.halted.isSome then pure s else
    match earliestDeadline s.deadlines to with
    | none => pure s
    | some e =>
    let due := s.deadlines.filter (·.time == e.time)
    let tied := 1 < due.length || tie == e.time
    match chooseDeadline s e due tied with
    | .error invalid => pure (s.report (.invalidInput invalid))
    | .ok (t, s) => do
      let s := s.passTime st t.time
      let s := s.newMessage
      let (s, step) := s.newStep (.deadline t.armedBy (if tied then some (.deadlines e.time) else none))
      MonadNote.note (.stepBegins step t.step none)
      let r ← settled fs st step (some t.machine) (fire fs st step t) ⟨s, {}⟩
      MonadNote.note .stepEnds
      let s ← drain st fs Limit.messageWork.max r.state r.queue
      let s ← endMessage st fs s
      fireDue st fs to fuel (if tied then e.time else none) s

def finish [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  let s ← endMessage st fs s
  fireDue st fs s.now Limit.dueDeadlines.max none s

def message [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (q : Queue) : m State := do
  let s ← drain st fs Limit.messageWork.max s q
  finish st fs s

end Tazuna.Service
