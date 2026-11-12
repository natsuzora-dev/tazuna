import Tazuna.Semantics.System.Run

/-! This module computes what can happen next right after an input, for the explorer. -/

namespace Tazuna.Observe

open Tazuna.Data Tazuna.Semantics

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
  s.pending.map fun p => { id := p.id, name := p.activity.name, target := p.activity.service, sender := s.senderOf p.requester }

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

/-- What can happen next after each input of a run. `stopped` is a violation from evaluating enabled. Later inputs are
not processed, and `stopped` is reported as the violation that halted the run. -/
structure EnabledLog where
  enabled : List Enabled := []
  stopped : Option Violation := none
deriving Repr, Inhabited

/-- The stepper that logs what can happen next after each input. It leaves the semantic state unchanged. -/
def enabledStep [Monad m] (st : Service) (stepper : Stepper m) (fs : Functions m) : Stepper (StateT EnabledLog m) :=
  fun s input => do
    if (← get).stopped.isSome then return s
    let s ← liftM (stepper s input)
    if s.halted.isSome then return s
    match ← liftM (enabled st fs s) with
    | .error fault => modify fun l => { l with stopped := some (Finding.fault fault).toViolation }
    | .ok e => modify fun l => { l with enabled := l.enabled ++ [e] }
    return s

end Tazuna.Observe
