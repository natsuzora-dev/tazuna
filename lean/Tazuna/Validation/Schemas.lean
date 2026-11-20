import Tazuna.Data.Collections
import Tazuna.Validation.Illegal

/-!
The schema rules that keep each collection's order defined by its encoded value, which sortCollections orders.
-/

namespace Tazuna.Validation.Schemas

open Tazuna.Data
open Tazuna.Spec

/-- Whether the field `key` of `item` is a number, or a string that holds an instant or a date, which SortKey orders. -/
def orderedKey (item : Value) (key : String) : Bool :=
  match (item.field? "properties").bind (·.field? key) with
  | some p =>
    match p.field? "type", p.field? "format" with
    | some (.str "number"), _ | some (.str "integer"), _ => true
    | some (.str "string"), some (.str "date-time") | some (.str "string"), some (.str "date") => true
    | _, _ => false
  | none => false

def requiredOf (option : Value) : List String :=
  match option.field? "required" with
  | some (.arr required) => required.filterMap fun | .str k => some k | _ => none
  | _ => []

def propertyConst (option : Value) (k : String) : Option Value :=
  (option.field? "properties").bind (·.field? k) |>.bind (·.field? "const")

/-- Whether `a` lacks a field that `b` requires, while `a` takes no field outside its properties. -/
def missesRequired (a b : Value) : Bool :=
  a.field? "additionalProperties" == some (.bool false) &&
    (requiredOf b).any fun k => ((a.field? "properties").bind (·.field? k)).isNone

/--
Whether no value fits both options as `fits` reads them: their types differ (an integer is a number), their own consts
differ, a property has a different const in each, or one requires a field that the other cannot have.
-/
def apart (a b : Value) : Bool :=
  (match a.field? "type", b.field? "type" with
    | some (.str x), some (.str y) =>
      x != y && !([x, y] == ["integer", "number"] || [x, y] == ["number", "integer"])
    | _, _ => false) ||
  (match a.field? "const", b.field? "const" with
    | some x, some y => x != y
    | _, _ => false) ||
  (requiredOf a ++ requiredOf b).any (fun k =>
    match propertyConst a k, propertyConst b k with
    | some x, some y => x != y
    | _, _ => false) ||
  missesRequired a b || missesRequired b a

/-- Whether every two options are `apart`. -/
def allApart : List Value → Bool
  | [] => true
  | o :: os => os.all (apart o) && allApart os

/-- What a schema breaks at a path: a sortedBy key that its encoded value does not order, or an ambiguous union. -/
inductive Issue where
  | unorderedSortKey (key : String)
  | ambiguousUnion
deriving DecidableEq, Repr

/--
Whether the schema has a bag, set, or sortedBy array at any depth that sortCollections reaches (union options, items,
properties, additionalProperties).
-/
def holdsCollection (schema : Value) : Bool :=
  (schema.field? "x-tazuna-sorted-by").isSome || (schema.field? "x-tazuna-bag").isSome ||
    (schema.field? "x-tazuna-set").isSome ||
  (match _ha : unionOptions schema with
    | some options => options.attach.any fun ⟨o, _ho⟩ => holdsCollection o
    | none => false) ||
  (match _hi : schema.field? "items" with
    | some item => holdsCollection item
    | none => false) ||
  (match _hp : schema.field? "properties" with
    | some (.obj properties) => properties.attach.any fun ⟨(_, p), _hm⟩ => holdsCollection p
    | _ => false) ||
  (match _hc : schema.field? "additionalProperties" with
    | some c => holdsCollection c
    | none => false)
termination_by sizeOf schema
decreasing_by
  · have := List.sizeOf_lt_of_mem _ho
    have := unionOptions_lt _ha
    omega
  · exact Value.field?_lt _hi
  · have h1 := List.sizeOf_lt_of_mem _hm
    have h2 := Value.field?_lt _hp
    simp only [Prod.mk.sizeOf_spec, Value.obj.sizeOf_spec] at h1 h2
    omega
  · exact Value.field?_lt _hc

/-- The issues of the schema at `path` and below, each with the path of field names that leads to it. -/
def issues (path : List String) (schema : Value) : List (List String × Issue) :=
  let own :=
    (match schema.field? "x-tazuna-sorted-by", schema.field? "items" with
      | some (.str key), some item => if orderedKey item key then [] else [(path, .unorderedSortKey key)]
      | some (.str key), none => [(path, .unorderedSortKey key)]
      | _, _ => []) ++
    (match unionOptions schema with
      | some options => if options.any holdsCollection && !allApart options then [(path, .ambiguousUnion)] else []
      | none => [])
  own ++
  (match _ha : unionOptions schema with
    | some options => options.attach.flatMap fun ⟨o, _ho⟩ => issues path o
    | none => []) ++
  (match _hi : schema.field? "items" with
    | some item => issues path item
    | none => []) ++
  (match _hp : schema.field? "properties" with
    | some (.obj properties) => properties.attach.flatMap fun ⟨(k, p), _hm⟩ => issues (path ++ [k]) p
    | _ => []) ++
  (match _hc : schema.field? "additionalProperties" with
    | some c => issues path c
    | none => [])
termination_by sizeOf schema
decreasing_by
  · have := List.sizeOf_lt_of_mem _ho
    have := unionOptions_lt _ha
    omega
  · exact Value.field?_lt _hi
  · have h1 := List.sizeOf_lt_of_mem _hm
    have h2 := Value.field?_lt _hp
    simp only [Prod.mk.sizeOf_spec, Value.obj.sizeOf_spec] at h1 h2
    omega
  · exact Value.field?_lt _hc

/-- The JSON Schemas of a definition, each with the keyword path that holds it. -/
def schemasOf (d : Definition) : List (List String × Value) :=
  match d.body with
  | .entity e => [(["fields"], e.fields)]
  | .event e => [(["payload"], e.payload)]
  | .command c => [(["input"], c.input)] ++ (c.output.map fun o => [(["output"], o)]).getD []
  | .query q => [(["input"], q.input)] ++ (q.output.map fun o => [(["output"], o)]).getD []
  | .automation _ => []
  | .machine c | .screen c =>
    [(["context"], c.context), (["input"], c.input), (["output"], c.output)] ++
      c.controls.filterMap (fun (k, p) => p.map ((["controls", k, "payload"], ·))) ++
      c.states.flatMap fun st =>
        (st.map.map fun m => [([st.name, "key"], m.key), ([st.name, "context"], m.context)]).getD [] ++
          (st.held.map fun h => [([st.name, "held"], h.schema)]).getD []

def illegal (d : Definition) : List String × Issue → Illegal
  | (path, .unorderedSortKey key) => .unorderedSortKey d.ref path key
  | (path, .ambiguousUnion) => .ambiguousUnion d.ref path

def check (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d => (schemasOf d).flatMap fun x => (issues x.1 x.2).map (illegal d)

end Tazuna.Validation.Schemas
