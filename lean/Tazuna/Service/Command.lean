import Tazuna.Service.Contract
import Tazuna.Service.Integrity

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/-- `xs` cut into consecutive lists of the lengths `lengths`. -/
def chunks {α : Type} : List Nat → List α → List (List α)
  | [], _ => []
  | n :: ns, xs => xs.take n :: chunks ns (xs.drop n)

/-- The text that orders the events of one group. -/
def Emit.text (e : Emit) : String := (ToValue.toValue e).canonical

/--
The groups of `decided` with the events of `sorted`, the sorted flattening of `decided`, each group in the
order of its texts. A group has no order, so the run writes its events in this order; `sameRecordInBag` keeps the
records from depending on it.
-/
def orderedGroups (decided : List (List Emit)) (sorted : List Emit) : List (List Emit) :=
  (chunks (decided.map (·.length)) sorted).map (·.mergeSort fun a b => decide (a.text ≤ b.text))

/-- A record that two events of one group write, as its entity and key. -/
def twiceWritten (st : Service) (records : Records) (groups : List (List Emit)) :
    Option (String × Option String) :=
  groups.findSome? fun g =>
    let rows := g.filterMap fun e => (evolve st records e).map fun ev => (ev.entity, ev.key)
    firstDuplicate id rows

inductive Outcome where
  | rejected (rejection : Rejection)
  | accepted (records : Records) (groups : List (List Emit)) (violations : List Fault)
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
  match ← fs.parseOutside st (.input (st.ref name)) raw with
  | .error e => pure (.halted [issueViolation (st.ref name) e])
  | .ok none => pure (.rejected { kind := .invalidInput })
  | .ok (some input) =>
    match ← requirementsRejection st fs records now name input with
    | .error v => pure (.halted [v])
    | .ok (some r) => pure (.rejected r)
    | .ok none =>
      match ← fs.decide name input records now with
      | .error e =>
        pure (.halted [issueViolation (st.ref name) e fun
          | .payload event => .emittedPayloadSchema (st.ref name) event
          | _ => .exception (some (st.ref name))])
      | .ok decided =>
      match decided.flatten.find? (!st.lists name ·) with
      | some e =>
        let event := (st.«structure».definitions.find? fun d => d.kind == "event" && d.ref == e.event).map (·.ref)
        pure (.halted [.unlistedEmittedEvent (st.ref name) event])
      | none =>
      let groups := orderedGroups decided decided.flatten
      match twiceWritten st records groups with
      | some (entity, key) => pure (.halted [.sameRecordInBag (st.ref name) (st.ref entity) key])
      | none =>
        let written := applyAll st records groups.flatten
        if duplicated st written then pure (.rejected { kind := .alreadyExists })
        else
          let ensures ← commandEnsures st fs name input records written now
          let violations := ensures ++ (← integrityViolations st fs written now name)
          pure (if violations.any (·.halts) then .halted violations else .accepted written groups violations)

/--
The state, answer, and groups of events after a command. As in CQRS, an own-service command answers without output and the
sender reads records with a query. An external service's command may return output such as a created id, as external
APIs like Stripe do.
-/
def processCommand [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (raw : Value)
    (id : Option LineId) (step : Nat) : m (State × Answer × List (List Emit)) := do
  MonadNote.note (.reached (.request (st.ref name)))
  let outcome ← evaluate st fs s.records s.now name raw
  match outcome with
  | .rejected r => pure (s.answer id (st.ref name) (.rejected r), .rejected r, [])
  | .accepted records groups violations =>
    MonadNote.note (.reached (.successAnswer (st.ref name)))
    let s := ({ s with records }.reportAll violations).answer id (st.ref name) (.accepted none)
    pure (s.emitAll id (emittedBy step groups), .accepted none, groups)
  | .halted violations => pure (s.reportAll violations, outcome.answer, [])

end Tazuna.Service
