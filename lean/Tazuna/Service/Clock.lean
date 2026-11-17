import Tazuna.Service.Chart.Macrostep

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def fire (st : Service) (step : Nat) (t : Deadline) (r : Processing) : m Processing := do
  let (s, waiting) := r.state.takeDeadline t
  MonadNote.note (.readStates [(t.machine, t.state)])
  if !waiting then pure ⟨s, r.queue⟩ else
  withMachine t.machine (fun i r =>
    if i.closed || !i.isIn t.state then pure r
    else applyCompletion fs st step t.machine (i.chart.transitionsAt (some t.state) ["after", t.name, "onFired"]) .none r)
    ⟨s, r.queue⟩

end

def earliestDeadline (deadlines : List Deadline) (to : Time) : Option Deadline :=
  deadlines.foldl (fun best t =>
    match t.time with
    | none => best
    | some time =>
      if time > to then best else
      match best with
      | none => some t
      | some b => if time < b.time.getD time then some t else some b) none

/-- The name of the step in which deadline `t` fires. -/
def State.deadlineStep (s : State) (st : Service) (t : Deadline) : StepName := .deadline (s.who st t.machine) t.name

/--
The deadline that fires among `due`, the deadlines due at the earliest time in entry order, whose first is `first`, and
the state with the order entry that chose it used. Without a tie it is `first`. A tie is internal to the service, as the
order of its steps is, whichever line advanced the time: the next entry of the input's `stepOrder`, which test's search
writes, chooses it, and without entries it is `first`, one of the orders that the search compares.
-/
def chooseDeadline (st : Service) (s : State) (first : Deadline) (due : List Deadline) (tied : Bool) :
    Except InvalidInput (Deadline × State) :=
  if !tied then .ok (first, s) else
  match s.stepOrder with
  | named :: rest =>
    match due.find? (s.deadlineStep st · == named) with
    | some t => .ok (t, { s with stepOrder := rest })
    | none => .error (.unreadyStep named (due.map (s.deadlineStep st)))
  | [] => .ok (first, s)

end Tazuna.Service
