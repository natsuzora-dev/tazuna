import Tazuna.Service.Note
import Tazuna.Service.State

/-!
A failed `requires` of a command or query (a caller that it does not list or whose record is missing, a missing ref
target, a false bind, or a false requires condition) is the caller's error: the service checks it before processing and
rejects the request. A failed `ensures` is the service's error: the service checks it before answering.
-/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

structure RefCheck where
  reads : List RecordPart
  missing : Bool

def missingRef (st : Service) (records : Records) (input : Value) : List (String × Spec.Ref) → RefCheck
  | [] => { reads := [], missing := false }
  | (field, r) :: rest =>
    match input.field? field with
    | none | some .null => missingRef st records input rest
    | some v =>
      if r.service == st.service && r.name ∈ st.entities then
        let key := canonicalKey (st.keyFieldsOf r.name) v
        if records.any (fun row => row.entity == r.name && row.key == some key) then
          let found := missingRef st records input rest
          { found with reads := .record r.name key :: found.reads }
        else { reads := [.record r.name key], missing := true }
      else missingRef st records input rest

/--
The rejection of a request from `caller` to a command or query that takes the callers `callers`: `permissionDenied`
when it lists no kind of `caller`, and `notFound` when the caller is a record that does not exist, as for a ref input. The
check reads the caller's record, which a deletion may race with.
-/
def callerRejection [Monad m] [MonadNote m] (st : Service) (records : Records) (definition : Spec.Ref)
    (callers : List Spec.CallerType) (caller : Caller) : m (Option Rejection) := do
  if !callers.any (·.admits caller) then return some { kind := .permissionDenied }
  match caller with
  | .entity entity key =>
    let key := canonicalKey (st.keyFieldsOf entity) key
    MonadNote.note (.read definition [.record entity key])
    pure (if records.any fun row => row.entity == entity && row.key == some key then none else some { kind := .notFound })
  | .service _ => pure none

def requirementsRejection [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (records : Records) (now : Time)
    (name : String) (input : Value) (caller : Caller) : m (Except Fault (Option Rejection)) := do
  let rq ← expectFound s!"requirements of {name}" (st.requirements.lookup name)
  if let some r ← callerRejection st records (st.ref name) rq.callers caller then return .ok (some r)
  let refs := missingRef st records input rq.refs
  MonadNote.note (.read (st.ref name) refs.reads)
  if refs.missing then return .ok (some { kind := .notFound })
  match ← firstFalse (fun b => fs.binding name b input caller records now) rq.binds with
  | .error e => return .error (issueViolation (st.ref name) e)
  | .ok (some b) =>
    MonadNote.note (.reached (.bindsRejection (st.ref name) b))
    return .ok (some { kind := .requires, reason := some b })
  | .ok none =>
    match ← firstFalse (fun c => fs.requirement name c input caller records now) rq.requires with
    | .error e => return .error (issueViolation (st.ref name) e)
    | .ok (some c) =>
      MonadNote.note (.reached (.requiresRejection (st.ref name) c))
      return .ok (some { kind := .requires, reason := some c })
    | .ok none => return .ok none

def commandEnsures [Monad m] (st : Service) (fs : Functions m) (name : String) (input : Value) (caller : Caller)
    (before after : Records) (now : Time) : m (List Fault) := do
  match ← fs.ensures name input caller before after now with
  | .error e => pure [issueViolation (st.ref name) e]
  | .ok (some c) => pure [st.failedEnsures name c]
  | .ok none => pure []

end Tazuna.Service
