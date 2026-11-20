import Tazuna.Data.Collections
import Tazuna.Service.Basic
import Tazuna.Service.Message
import Tazuna.Service.Limits

namespace Tazuna.Service

open Tazuna.Data

structure Row where
  entity : String
  key : Option String
  value : Value
deriving DecidableEq, Repr, Inhabited

/-- The records of a service, in write order. -/
abbrev Records := List Row

/--
The keys of `entity` in code-point order, as String's `≤`. Spec functions receive `records.<entity>` without order; TS
calls them on the records in this order, so that a run is deterministic.
-/
def Records.keys (records : Records) (entity : String) : List String :=
  ((records.filter (·.entity == entity)).filterMap (·.key)).mergeSort fun a b => decide (a ≤ b)

def updatedRow (records : Records) (entity : String) (key : Option String) (payload : Value) : Value :=
  match records.find? (fun r => r.entity == entity && r.key == key) with
  | some r => r.value.merge payload
  | none => payload

inductive RowChange where
  | create
  | update
  | delete
deriving DecidableEq, Repr, Inhabited

structure Evolved where
  records : Records
  change : RowChange
  entity : String
  key : Option String
deriving Repr, Inhabited

/--
The records after event `e`, or `none` for an event that writes no record. Duplicate keys and unique values are not
checked here: a create event adds another record even if one has its key, and Integrity checks at the end of the
command.
-/
def evolve (st : Service) (records : Records) (e : Emit) : Option Evolved :=
  let keyOf (field : String) := some ((e.payload.field? field).getD .null).keyString
  let isRow (entity : String) (key : Option String) (r : Row) := r.entity == entity && r.key == key
  let update (entity : String) (key : Option String) : Evolved :=
    let row := updatedRow records entity key e.payload
    { records := if records.any (isRow entity key) then records.map fun r => if isRow entity key r then { r with value := row } else r
                 else records ++ [{ entity, key, value := e.payload }],
      change := .update, entity, key }
  match st.changeOf e.event with
  | some (.create entity keyField _) =>
    let key := keyOf keyField
    some { records := records ++ [{ entity, key, value := e.payload }], change := .create, entity, key }
  | some (.update entity keyField _) => some (update entity (keyOf keyField))
  | some (.set entity _) => some (update entity none)
  | some (.delete entity keyField _) =>
    let key := keyOf keyField
    some { records := records.filter fun r => !isRow entity key r, change := .delete, entity, key }
  | _ => none

/-- The value with its collections sorted by `schema`, which the structure holds for each own event and query. -/
def sorted {m : Type → Type} [Monad m] [MonadNote m] (st : Service) (schema : Schema) (v : Value) : m Value := do
  pure (sortCollections (← expectFound s!"schema {repr schema}" (st.schemaOf schema)) v)

end Tazuna.Service
