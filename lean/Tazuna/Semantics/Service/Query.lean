import Tazuna.Semantics.Service.Contract

namespace Tazuna.Semantics.Service

open Tazuna.Ir

variable {m : Type → Type}

inductive Resolution where
  | answered (answer : Answer) (violations : List Fault)
  | halted (violation : Fault)
deriving Repr, Inhabited

def resolveChecked [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (raw : Value)
    (caller : Caller) : m Resolution := do
  let definition := st.ref name
  MonadNote.note (.reached (.request definition))
  match ← fs.parseOutside st (.input definition) raw with
  | .error e => pure (.halted (issueViolation definition e))
  | .ok none => pure (.answered (.rejected { kind := .invalidInput }) [])
  | .ok (some input) =>
    let rq ← expectFound s!"requirements of {name}" (st.requirements.lookup name)
    if let some r ← callerRejection st s.records definition rq.callers caller then return .answered (.rejected r) []
    match ← firstFalse (fs.inputRequirement definition · input) rq.requires with
    | .error e => pure (.halted (issueViolation definition e))
    | .ok (some reason) =>
      MonadNote.note (.reached (.requiresRejection definition reason))
      pure (.answered (.rejected { kind := .requires, reason := some reason }) [])
    | .ok none =>
      match ← fs.resolve name input caller s.records s.now with
      | .error e => pure (.halted (issueViolation definition e fun _ => .outputSchema definition))
      | .ok output =>
        match ← fs.queryEnsures name input caller output s.records with
        | .error e => pure (.halted (issueViolation definition e))
        | .ok (some c) =>
          MonadNote.note (.reached (.successAnswer definition))
          pure (.answered (.fulfilled output) [st.failedEnsures name c])
        | .ok none =>
          MonadNote.note (.reached (.successAnswer definition))
          pure (.answered (.fulfilled output) [])

def publishOne [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (sub : Subscription) :
    m State := do
  if s.halted.isSome then pure s else
  match ← resolveChecked st fs s sub.query sub.input sub.caller with
  | .halted fault => pure (s.report (.fault fault))
  | .answered answer violations =>
    let s := s.reportAll violations
    match ← fs.comparable sub.query answer with
    | .error e =>
      pure (s.report (.fault (issueViolation (st.ref sub.query) e)))
    | .ok c =>
    if sub.last == some c then pure s else
    let s := { s with subscriptions := s.subscriptions.map fun (u : Subscription) =>
      if u.id == sub.id then { u with last := some c } else u }
    pure (s.write .out none (.answer sub.id answer) () () (st.ref sub.query)).1

/--
The state after each subscription receives its new answer. It runs after the message, outside any step: an answer
depends only on the values at the end of the message, so its reads are not reads of a step. They are reads of the
message (endMessage), which a later message may observe in another order.
-/
def publish [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State :=
  s.subscriptions.foldlM (publishOne st fs) s

end Tazuna.Semantics.Service
