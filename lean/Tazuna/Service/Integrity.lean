import Tazuna.Service.Functions

/-!
This module checks records at the end of a command: duplicate keys and unique values, which are not checked between
events (like SQL DEFERRABLE INITIALLY DEFERRED constraints); entity and service invariants, which are not checked inside
a command (like JML visible-state semantics and Event-B invariants); and ref targets.
-/

namespace Tazuna.Service

open Tazuna.Data

def uniqueValues (unique : List String) (v : Value) : List (Option Value) := unique.map v.field?

/--
Whether the unique fields of `row` are checked. A row with a null unique field is not, as SQL UNIQUE treats NULLs as
distinct.
-/
def uniqueChecked (unique : List String) (row : Value) : Bool :=
  !unique.isEmpty && unique.all fun f => row.field? f != some .null

def clash (st : Service) (a b : Row) : Bool :=
  a.entity == b.entity &&
    (a.key == b.key ||
      (uniqueChecked (st.uniqueOf a.entity) a.value &&
        uniqueValues (st.uniqueOf a.entity) a.value == uniqueValues (st.uniqueOf a.entity) b.value))

def duplicated (st : Service) : Records → Bool
  | [] => false
  | r :: rs => rs.any (clash st r) || duplicated st rs

def applyEmit (st : Service) (records : Records) (e : Emit) : Records :=
  match evolve st records e with
  | none => records
  | some ev => ev.records

def applyAll (st : Service) (records : Records) (emits : List Emit) : Records := emits.foldl (applyEmit st) records

variable {m : Type → Type}

def Row.failedInvariant (st : Service) (row : Row) (condition : String) (command : Spec.Ref) : Fault :=
  match row.key with
  | some key => .failedEntityInvariant (st.ref row.entity) key condition command
  | none => .failedSingleInvariant (st.ref row.entity) condition command

def danglingRefs (st : Service) (records : Records) (name : String) (row : Row) : List Fault :=
  (st.references.filter (·.1 == row.entity)).filterMap fun (_, field, targetEntity) =>
    match row.value.field? field with
    | none | some .null => none
    | some v =>
      if targetEntity ∈ st.entities && !records.any (fun r => r.entity == targetEntity && r.key == some v.keyString) then
        some (match row.key with
          | some key => .danglingRef (st.ref row.entity) key field v.keyString (st.ref name)
          | none => .danglingSingleRef (st.ref row.entity) field v.keyString (st.ref name))
      else none

def rowViolations [Monad m] (st : Service) (fs : Functions m) (records : Records) (name : String) (row : Row) :
    m (List Fault) := do
  let invariant := match ← fs.invariant row.entity row.value with
    | .error e => [issueViolation (st.ref row.entity) e]
    | .ok (some c) => [row.failedInvariant st c (st.ref name)]
    | .ok none => []
  pure (invariant ++ danglingRefs st records name row)

def integrityViolations [Monad m] (st : Service) (fs : Functions m) (records : Records) (name : String) :
    m (List Fault) := do
  let rows ← (st.entities.flatMap fun e => records.filter (·.entity == e)).mapM (rowViolations st fs records name)
  match ← fs.serviceInvariant records with
  | .error schema => pure (rows.flatten ++ [.exception (schema.map Schema.owner)])
  | .ok (some c) => pure (rows.flatten ++ [.failedServiceInvariant c (st.ref name)])
  | .ok none => pure rows.flatten

end Tazuna.Service
