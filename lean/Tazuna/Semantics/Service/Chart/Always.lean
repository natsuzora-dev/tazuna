import Tazuna.Semantics.Service.Chart.Map
import Tazuna.Semantics.Service.Chart.Select

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def alwaysRound (st : Service) (step : Nat) (owner : InstanceId)
    (next : Instance → List (InstanceId × Transition) → Processing → m Processing) (r : Processing) : m Processing :=
  if r.halted then pure r else
  match r.state.machine? owner with
  | none => pure r
  | some o =>
    if o.closed then pure r else do
    let (r, changed) ← syncCopies fs st step owner r
    if r.halted then pure r else
    match r.state.machine? owner with
    | none => pure r
    | some o =>
      match ← select fs st r.state o .always .none (leavesOf r.state o o.copyIds) with
      | .error fault => pure (r.report (.fault fault))
      | .ok chosen => if chosen.isEmpty && !changed then pure r else next o chosen r

def settleFrom (st : Service) (step : Nat) (owner : InstanceId) : (roundsLeft : Nat) → Processing → m Processing
  | 0 => alwaysRound fs st step owner fun o _ r =>
    pure (r.report (.fault (.exceededAlwaysRounds (st.ref o.chart.name) Limit.alwaysRounds.max)))
  | roundsLeft + 1 => alwaysRound fs st step owner fun _ chosen r => do
    settleFrom st step owner roundsLeft (← if chosen.isEmpty then pure r else microstep fs st step owner chosen .none r)

def settle (st : Service) (step : Nat) (name : InstanceId) (r : Processing) : m Processing :=
  settleFrom fs st step (name.owner) Limit.alwaysRounds.max r

def settleAround (st : Service) (step : Nat) (owner : InstanceId) (f : Processing → m Processing) (r : Processing) :
    m Processing := do
  let r ← settleFrom fs st step owner Limit.alwaysRounds.max r
  settleFrom fs st step owner Limit.alwaysRounds.max (← unlessHalted f r)

/--
The processing `f` with the always transitions settled before and after it, for the owner of `name` as of the start of
the step (for a copy, the copy's owner).
-/
def settled (st : Service) (step : Nat) : Option InstanceId → (Processing → m Processing) → Processing → m Processing
  | none, f, r => f r
  | some name, f, r => do
    MonadNote.note (.settlesAround (name.owner))
    settleAround fs st step (name.owner) f r

end

end Tazuna.Semantics.Service
