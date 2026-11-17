import Tazuna.Service.Clock
import Tazuna.Service.Screen.Subscription
import Tazuna.Service.Query

/-!
Each message runs to completion: the service processes external messages one at a time, and each due deadline is its
own message.
-/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def checkHolds [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  s.running.foldlM (fun s i =>
    if s.halted.isSome || i.closed then pure s else
    i.entered.foldlM (fun s (n, _) => do
      if s.halted.isSome then pure s else
      match ← fs.holds (s.scopeOf i (some n)) s.records with
      | .error e =>
        pure (s.report (.fault (issueViolation st (st.ref i.chart.name) e)))
      | .ok () => pure s) s) s

def invariantViolations [Monad m] (st : Service) (fs : Functions m) (s : State) :
    m (List Fault) := do
  let found ← (s.machines.filter (!·.closed)).mapM fun i => do
    match ← fs.chartInvariant (s.scopeOf i none) s.records with
    | .error e => pure (some (issueViolation st (st.ref i.chart.name) e))
    | .ok failed => pure (failed.map (.failedChartInvariant (st.ref i.chart.name)))
  pure (found.filterMap id)

/--
The state with the chart invariant violations reported. As in JML visible-state semantics, the invariants are checked
when a message finishes, not between microsteps.
-/
def checkInvariants [Monad m] (st : Service) (fs : Functions m) (s : State) : m State := do
  pure (s.reportAll (← invariantViolations st fs s))

def afterMessage [Monad m] (st : Service) (fs : Functions m) (s : State) : m State := do
  let s ← checkHolds st fs s
  if s.halted.isSome then pure s else
  let s ← checkInvariants st fs s
  let s ← rearm st fs s
  if s.halted.isSome then pure s else
  publish st fs s

/-- afterMessage, noted as the end of the current message, whose state the next message may observe in another order. -/
def endMessage [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  MonadNote.note (.afterMessageBegins s.messageCount)
  let s ← afterMessage st fs s
  MonadNote.note .afterMessageEnds
  pure s

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
    match chooseDeadline st s e due tied with
    | .error invalid => pure (s.report (.invalidInput invalid))
    | .ok (t, s) => do
      let time := t.time.getD s.now
      let s := { s with now := max s.now time }
      let s := s.newMessage
      let (s, step) := s.newStep none (tie := if tied then e.time else none)
      MonadNote.note (.stepBegins step (s.deadlineStep st t) none)
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
