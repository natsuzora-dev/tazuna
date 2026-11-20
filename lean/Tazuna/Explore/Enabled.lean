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
  id : LineId
  name : String
  target : String
  sender : String
deriving DecidableEq, Repr, Inhabited

derive_wire Awaiting

local instance : ToValue Time := ⟨Time.toValue⟩
local instance : FromValue Time := ⟨Time.fromValue⟩

structure Enabled where
  operations : List Operation
  awaiting : List Awaiting
  nextDeadline : Option Time
deriving DecidableEq, Repr, Inhabited

derive_wire Enabled skip_serializing_none

/-- The requests that await their answers, including stale requests. -/
def awaiting (s : State) : List Awaiting :=
  s.pending.map fun p => { id := p.id, name := p.activity.ref.name, target := p.activity.ref.service, sender := p.requester.sender }

def nextDeadline (s : State) : Option Time :=
  s.deadlines.foldl (fun best t => some (match best with | none => t.time | some b => min b t.time)) none

/-- What can happen next in a state. Operations are grouped by open screen instance, in opening order. -/
def enabled [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) :
    m (Except Fault Enabled) := do
  let operations ← (dedupe s.stack).foldlM
      (init := (.ok [] : Except Fault (List Operation))) fun acc resource => do
    match acc with
    | .error v => pure (.error v)
    | .ok done =>
      match ← operationsOf fs st s resource with
      | .error v => pure (.error v)
      | .ok ops => pure (.ok (done ++ ops))
  pure (operations.map fun operations => { operations, awaiting := awaiting s, nextDeadline := nextDeadline s })

end Tazuna.Explore
