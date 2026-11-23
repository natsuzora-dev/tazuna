import Tazuna.Semantics.Value.Collections
import Tazuna.Semantics.Service.Basic
import Tazuna.Semantics.Service.Message
import Tazuna.Semantics.Service.Limits

namespace Tazuna.Semantics.Service

open Tazuna.Ir

/--
A record. `key` is none for a single entity's record; for a keyed entity's, it is the value of its key field, or, for an
entity with several key fields, the object of those fields in key order.
-/
structure Row where
  entity : String
  key : Option Value
  value : Value
deriving DecidableEq, Repr, Inhabited

/-- The records of a service, in write order. -/
abbrev Records := List Row

/-- The key that `v`, a record or an event payload, holds in the key fields `fields`. -/
def keyAt (fields : List String) (v : Value) : Value :=
  match fields with
  | [f] => (v.field? f).getD .null
  | fs => .obj (fs.map fun f => (f, (v.field? f).getD .null))

/--
The key `k` of an entity with the key fields `fields`, as Row.key holds it: an object of several key fields with its
fields in key order, which a spec may write in any order.
-/
def canonicalKey (fields : List String) (k : Value) : Value :=
  match fields, k with
  | [_], k => k
  | fs, .obj _ => keyAt fs k
  | _, k => k

/-- The text by which records sort by key: the key's canonical JSON, empty for a single entity's record. -/
def Row.keyText (r : Row) : String := (r.key.map (·.canonical)).getD ""

/-- The key fields of the own keyed entity `entity`. -/
def keyFieldsOf (st : Service) (entity : String) : List String := (st.keyFields.lookup entity).getD []

/-- The keys of `entity`, in the order that the records hold them. -/
def Records.keys (records : Records) (entity : String) : List Value :=
  (records.filter (·.entity == entity)).filterMap (·.key)

def updatedRow (records : Records) (entity : String) (key : Option Value) (payload : Value) : Value :=
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
  key : Option Value
deriving Repr, Inhabited

/--
The records after event `e`, or `none` for an event that writes no record. Duplicate keys and unique values are not
checked here: a create event adds another record even if one has its key, and Integrity checks at the end of the
command.
-/
def evolve (st : Service) (records : Records) (e : Emit) : Option Evolved :=
  let keyOf (fields : List String) := some (keyAt fields e.payload)
  let isRow (entity : String) (key : Option Value) (r : Row) := r.entity == entity && r.key == key
  let update (entity : String) (key : Option Value) : Evolved :=
    let row := updatedRow records entity key e.payload
    { records := if records.any (isRow entity key) then records.map fun r => if isRow entity key r then { r with value := row } else r
                 else records ++ [{ entity, key, value := e.payload }],
      change := .update, entity, key }
  match st.changeOf e.event with
  | some (.create entity keyFields _) =>
    let key := keyOf keyFields
    some { records := records ++ [{ entity, key, value := e.payload }], change := .create, entity, key }
  | some (.update entity keyFields _) => some (update entity (keyOf keyFields))
  | some (.set entity _) => some (update entity none)
  | some (.delete entity keyFields _) =>
    let key := keyOf keyFields
    some { records := records.filter fun r => !isRow entity key r, change := .delete, entity, key }
  | _ => none

end Tazuna.Semantics.Service
