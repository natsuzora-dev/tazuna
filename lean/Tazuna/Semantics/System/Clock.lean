import Tazuna.Semantics.Chart.Macrostep

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

/--
The deadline that fires among `due`, the deadlines due at the earliest time in entry order, whose first is `first`, with
the entries of `order` left: in a tie, the one that the next entry names, or `first` when no entry is left; otherwise
`first`, the only one. Test's search sets `order` to try the other orders of a tie (ChoiceDependent.deadlineOrder).
-/
def chooseDeadline (first : Deadline) (due : List Deadline) (tied : Bool) (order : List DeadlineId) :
    Except InvalidInput (Deadline × List DeadlineId) :=
  match tied, order with
  | true, c :: rest =>
    match due.find? (·.id == c) with
    | some t => .ok (t, rest)
    | none => .error (.unreadyDeadline c (due.map Deadline.id))
  | _, _ => .ok (first, order)

end Tazuna.Semantics
