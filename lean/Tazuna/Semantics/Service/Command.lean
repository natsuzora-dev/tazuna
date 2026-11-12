import Tazuna.Semantics.Service.Contract
import Tazuna.Semantics.Service.Integrity

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

def normalizeEmits [Monad m] (st : Service) (fs : Functions m) (command : String) (emits : List Emit) :
    m (Except Fault (List Emit)) :=
  emits.foldlM (init := .ok []) fun acc e => do
    match acc with
    | .error r => pure (.error r)
    | .ok done =>
      match ← fs.normalize (.payload e.event) (st.sorted (.payload e.event) e.payload) with
      | .error issue => pure (.error (issueViolation st (st.ref command) issue))
      | .ok (some payload) => pure (.ok (done ++ [{ e with payload }]))
      | .ok none => pure (.error (.emittedPayloadSchema (st.ref command) (st.refOf e.event)))

/-- Whether the command `command` lists the event of `e` in its emits. -/
def Service.lists (st : Service) (command : String) (e : Emit) : Bool :=
  (st.«structure».emitsOf (some (st.ref command))).any (·.any (·.traceName st.service == e.event))

inductive Outcome where
  | rejected (rejection : Rejection)
  | accepted (records : Records) (emits : List Emit) (violations : List Fault)
  /-- A halt, with the violations in report order up to the first one that halts. -/
  | halted (violations : List Fault)
deriving Repr, Inhabited

/-- The answer of an outcome. A halted run answers `unavailable`, since nobody uses its answer. -/
def Outcome.answer : Outcome → Answer
  | .rejected r => .rejected r
  | .accepted .. => .accepted none
  | .halted .. => .rejected { kind := .unavailable }

def evaluate [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (records : Records) (now : Time) (name : String)
    (raw : Value) : m Outcome := do
  match ← fs.parse (.input name) raw with
  | .error e => pure (.halted [issueViolation st (st.ref name) e])
  | .ok none => pure (.rejected { kind := .invalidInput })
  | .ok (some input) =>
    match ← requirementsRejection st fs records now name input with
    | .error v => pure (.halted [v])
    | .ok (some r) => pure (.rejected r)
    | .ok none =>
      match ← fs.decide name input records now with
      | .error e => pure (.halted [issueViolation st (st.ref name) e])
      | .ok decided =>
      match decided.find? (!st.lists name ·) with
      | some e =>
        let event := (st.«structure».named st.service (some e.event) ["event"]).map (·.ref)
        pure (.halted [.unlistedEmittedEvent (st.ref name) event])
      | none =>
      match ← normalizeEmits st fs name decided with
      | .error v => pure (.halted [v])
      | .ok emits =>
        let written := applyAll st records emits
        if duplicated st written then pure (.rejected { kind := .alreadyExists })
        else
          let ensures ← commandEnsures st fs name input records written now
          let violations := ensures ++ (← integrityViolations st fs written name)
          pure (if violations.any (·.halts) then .halted violations else .accepted written emits violations)

/--
The state, answer, and events after a command. As in CQRS, an own-service command answers without output and the
sender reads records with a query. An external service's command may return output such as a created id, as external
APIs like Stripe do.
-/
def processCommand [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (raw : Value)
    (id : Option String) (step : Nat) : m (State × Answer × List Emit) := do
  let outcome ← evaluate st fs s.records s.now name raw
  match outcome with
  | .rejected r => pure (s.answer id (.rejected r), .rejected r, [])
  | .accepted records emits violations =>
    let s := ({ s with records }.reportAll violations).answer id (.accepted none)
    MonadNote.note (.events step s.lines.size emits.length)
    pure (s.emitAll emits, .accepted none, emits)
  | .halted violations => pure (s.reportAll violations, outcome.answer, [])

end Tazuna.Semantics
