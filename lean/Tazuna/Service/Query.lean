import Tazuna.Service.Contract

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def normalizeOutput [Monad m] (st : Service) (fs : Functions m) (name : String) (output : Value) :
    m (Except Issue (Option Value)) :=
  fs.normalize (.output name) (st.sorted (.output name) output)

inductive Resolution where
  | answered (answer : Answer) (violations : List Fault)
  | halted (violation : Fault)
deriving Repr, Inhabited

def resolveChecked [Monad m] (st : Service) (fs : Functions m) (s : State) (name : String) (raw : Value) :
    m Resolution := do
  let definition := st.ref name
  match ← fs.parse (.input name) raw with
  | .error e => pure (.halted (issueViolation st definition e))
  | .ok none => pure (.answered (.rejected { kind := .invalidInput }) [])
  | .ok (some input) =>
    match ← firstFalse (fs.inputRequirement name · input) (st.requirementsOf name).requires with
    | .error e => pure (.halted (issueViolation st definition e))
    | .ok (some reason) => pure (.answered (.rejected { kind := .requires, reason := some reason }) [])
    | .ok none =>
      match ← fs.resolve name input s.records s.now with
      | .error e => pure (.halted (issueViolation st definition e))
      | .ok output =>
        match ← normalizeOutput st fs name output with
        | .error e => pure (.halted (issueViolation st definition e))
        | .ok none => pure (.halted (.outputSchema definition))
        | .ok (some output) =>
          match ← fs.queryEnsures name input output s.records with
          | .error e => pure (.halted (issueViolation st definition e))
          | .ok (some c) => pure (.answered (.fulfilled output) [st.failedEnsures name c])
          | .ok none => pure (.answered (.fulfilled output) [])

def publishOne [Monad m] (st : Service) (fs : Functions m) (s : State) (sub : Subscription) :
    m State := do
  if s.halted.isSome then pure s else
  match ← resolveChecked st fs s sub.query sub.input with
  | .halted fault => pure (s.report (.fault fault))
  | .answered answer violations =>
    let s := s.reportAll violations
    match ← fs.comparable sub.query answer with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref sub.query) e)))
    | .ok c =>
    if sub.last == some c then pure s else
    let s := { s with subscriptions := s.subscriptions.map fun (u : Subscription) =>
      if u.id == sub.id then { u with last := some c } else u }
    pure (s.write .out none (.answer sub.id answer)).1

/--
The state after each subscription receives its new answer. It runs after the message, outside any step: an answer
depends only on the values at the end of the message, so its reads are not reads of a step.
-/
def publish [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  s.subscriptions.foldlM (publishOne st fs) s

end Tazuna.Service
