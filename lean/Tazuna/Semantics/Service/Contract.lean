import Tazuna.Semantics.Note
import Tazuna.Semantics.State

/-!
A failed `requires` of a command or query (a missing ref target, a false bind, or a false requires condition) is the
caller's error: the service checks it before processing and rejects the request. A failed `ensures` is the service's
error: the service checks it before answering.
-/

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

def firstFalse [Monad m] (test : String → m (Except Issue Bool)) : List String → m (Except Issue (Option String))
  | [] => pure (.ok none)
  | n :: ns => do
    match ← test n with
    | .error e => pure (.error e)
    | .ok true => firstFalse test ns
    | .ok false => pure (.ok (some n))

structure RefCheck where
  reads : List RecordPart
  missing : Bool

def missingRef (st : Service) (records : Records) (input : Value) : List (String × Syntax.Ref) → RefCheck
  | [] => { reads := [], missing := false }
  | (field, r) :: rest =>
    match input.field? field with
    | none | some .null => missingRef st records input rest
    | some v =>
      if r.service == st.service && r.name ∈ st.entities then
        if records.any (fun row => row.entity == r.name && row.key == some v.keyString) then
          let found := missingRef st records input rest
          { found with reads := .record r.name v.keyString :: found.reads }
        else { reads := [.record r.name v.keyString], missing := true }
      else missingRef st records input rest

def requirementsRejection [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (records : Records) (now : Time)
    (name : String) (input : Value) : m (Except Fault (Option Rejection)) := do
  let rq := st.requirementsOf name
  let refs := missingRef st records input rq.refs
  MonadNote.note (.read (st.ref name) refs.reads)
  if refs.missing then return .ok (some { kind := .notFound })
  match ← firstFalse (fun b => fs.binding name b input records now) rq.binds with
  | .error e => return .error (issueViolation st (st.ref name) e)
  | .ok (some b) => return .ok (some { kind := .requires, reason := some b })
  | .ok none =>
    match ← firstFalse (fun c => fs.requirement name c input records now) rq.requires with
    | .error e => return .error (issueViolation st (st.ref name) e)
    | .ok (some c) => return .ok (some { kind := .requires, reason := some c })
    | .ok none => return .ok none

def commandEnsures [Monad m] (st : Service) (fs : Functions m) (name : String) (input : Value) (before after : Records)
    (now : Time) : m (List Fault) := do
  match ← fs.ensures name input before after now with
  | .error e => pure [issueViolation st (st.ref name) e]
  | .ok (some c) => pure [st.failedEnsures name c]
  | .ok none => pure []

end Tazuna.Semantics
