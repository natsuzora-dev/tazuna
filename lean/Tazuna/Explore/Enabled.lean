import Tazuna.Service.Restart

/-! This module computes what can happen next right after an input, for the explorer. -/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

variable {m : Type → Type}

/--
A request that awaits its answer. `id` is the request line's id, `target` is the receiving service, and `sender` is the
sending definition.
-/
structure Awaiting where
  id : String
  name : String
  target : String
  sender : String
deriving DecidableEq, Repr, Inhabited

structure Enabled where
  operations : List Operation
  awaiting : List Awaiting
  nextDeadline : Option Time
deriving DecidableEq, Repr, Inhabited

/-- The requests that await their answers, including stale requests. -/
def awaiting (s : State) : List Awaiting :=
  s.pending.map fun p => { id := p.id, name := p.activity.ref.name, target := p.activity.ref.service, sender := s.senderOf p.requester }

def nextDeadline (s : State) : Option Time :=
  s.deadlines.foldl (fun best t => match t.time, best with
    | none, _ => best
    | some time, none => some time
    | some time, some b => some (min b time)) none

/-- What can happen next in a state. Operations are grouped by open screen definition, in first-opened order. -/
def enabled [Monad m] (st : Service) (fs : Functions m) (s : State) :
    m (Except Fault Enabled) := do
  let operations ← (dedupe ((s.stack.filterMap s.machine?).map (·.chart.name))).foldlM
      (init := (.ok [] : Except Fault (List Operation))) fun acc screen => do
    match acc with
    | .error v => pure (.error v)
    | .ok done =>
      match ← operationsOf fs st s screen with
      | .error v => pure (.error v)
      | .ok ops => pure (.ok (done ++ ops))
  pure (operations.map fun operations => { operations, awaiting := awaiting s, nextDeadline := nextDeadline s })

end Tazuna.Explore
