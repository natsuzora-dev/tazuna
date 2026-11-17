import Tazuna.Service.Chart.Macrostep

namespace Tazuna.Semantics

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
the state with the order entry that chose it used. Without a tie it is `first`. In a tie during a clock line (`clock`),
the next entry of the line's `deadlineOrder` chooses it, and a tie with no entry left is reported. A tie of any other
processing is internal to the service, as the order of its steps is: the next entry of the input's `stepOrder`, which
test's search writes, chooses it, and without entries it is `first`, one of the orders that the search compares.
-/
def chooseDeadline (st : Service) (s : State) (clock : Bool) (first : Deadline) (due : List Deadline) (tied : Bool) :
    Except InvalidInput (Deadline × State) :=
  if !tied then .ok (first, s) else
  if clock then
    match s.deadlineOrder with
    | c :: rest =>
      match due.find? (·.id == c) with
      | some t => .ok (t, { s with deadlineOrder := rest })
      | none => .error (.unreadyDeadline c (due.map Deadline.id))
    | [] => .error (.unorderedDeadlines (due.map Deadline.id))
  else
    match s.stepOrder with
    | named :: rest =>
      match due.find? (s.deadlineStep st · == named) with
      | some t => .ok (t, { s with stepOrder := rest })
      | none => .error (.unreadyStep named (due.map (s.deadlineStep st)))
    | [] => .ok (first, s)

end Tazuna.Semantics
