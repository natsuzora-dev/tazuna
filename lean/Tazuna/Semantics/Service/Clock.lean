import Tazuna.Semantics.Service.Chart.Macrostep

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def fire (st : Service) (step : Nat) (t : Deadline) (r : Processing) : m Processing := do
  let (s, waiting) := r.state.takeDeadline t
  if !waiting then pure ⟨s, r.queue⟩ else
  withMachine t.machine (fun i r =>
    if i.closed || !i.isIn t.state then pure r
    else applyCompletion fs st step t.machine (i.chart.transitionsAt (some t.state) (.after t.name)) .none r)
    ⟨s, r.queue⟩

end

def earliestDeadline (deadlines : List Deadline) (to : Time) : Option Deadline :=
  deadlines.foldl (fun best t =>
    if t.time > to then best else
    match best with
    | none => some t
    | some b => if t.time < b.time then some t else some b) none

end Tazuna.Semantics.Service
