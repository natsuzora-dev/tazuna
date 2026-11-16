import Tazuna.Semantics.System.Restart

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

/-- The state after `input` arrives, in the state that `advance` makes for it. -/
def arrive [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (input : Step) : m State :=
  match input.body with
  | .time => pure (s.writeInput none .time).1
  | .restart => restart st fs s
  | .command id name raw => send st fs s name id raw
  | .query id name raw => call st fs s name id raw
  | .subscribe id name raw => subscribe st fs s name id raw
  | .unsubscribe to => endSubscription st fs s to
  | .event id name raw resultOf => receive st fs s name id raw resultOf
  | .operation screen control payload => operate st fs s screen control payload true
  | .unacceptedOperation screen control payload => operate st fs s screen control payload false
  | .answer sender target answer choice handle => mock st fs s sender target answer choice handle

/-- The state after `input`, which arrives unless the advance halts or a value of it is an uncreated key. -/
def step [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (input : Step) : m State :=
  if s.halted.isSome then pure s else do
  let deadlineOrder := input.deadlineOrder.getD []
  let t ← advance st fs
    { s with deadlineOrder, inputDeadlineOrder := deadlineOrder, stepOrder := input.stepOrder.getD [] } input
  let t ← if t.halted.isSome then pure t else
    match t.uncreatedKey st input.body with
    | some (key, entity) => pure (t.report (.invalidInput (.uncreatedKey key (st.ref entity))))
    | none => arrive st fs t input
  pure t.checkOrderUsed

abbrev Stepper (m : Type → Type) := State → Step → m State

def runFrom [Monad m] (stepper : Stepper m) : State → List Step → m State
  | s, [] => pure s
  | s, input :: rest => do
    let s ← stepper s input
    if s.halted.isSome then pure s else runFrom stepper s rest

def run [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (inputs : List Step) : m State :=
  runFrom (step st fs) {} inputs

end Tazuna.Semantics
