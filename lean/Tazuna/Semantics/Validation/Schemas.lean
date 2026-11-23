import Tazuna.Semantics.Value.Collections
import Tazuna.Semantics.Validation.Illegal

/-!
The schema rules that keep each collection's order defined by its encoded value, which sortCollections orders, and that
forbid a default in a map state's key.
-/

namespace Tazuna.Semantics.Validation.Schemas

open Tazuna.Ir
open Tazuna.Ir

/--
Whether the field `key` of `item` is required with no default, so every element written from outside has it, and is a
number or a date label, which SortKey orders.
-/
def orderedKey (item : Value) (key : String) : Bool :=
  match propertyOf item key with
  | some p =>
    (requiredOf item).contains key && (p.field? "default").isNone &&
    match p.field? "type", p.field? "format" with
    | some (.str "number"), _ | some (.str "integer"), _ => true
    | some (.str "string"), some (.str "date") => true
    | _, _ => false
  | none => false

/-- What a schema breaks at a path: a sortedBy key that its encoded value does not order, or an ambiguous union. -/
inductive Issue where
  | unorderedSortKey (key : String)
  | ambiguousUnion
deriving DecidableEq, Repr

/--
The schemas that sortCollections walks into from `schema`: its union options, items, properties, each with its name,
and additionalProperties.
-/
def children (schema : Value) : List (Option String × Value) :=
  ((unionOptions schema).getD []).map (none, ·) ++
  (schema.field? "items").toList.map (none, ·) ++
  (match schema.field? "properties" with
    | some (.obj properties) => properties.map fun (k, p) => (some k, p)
    | _ => []) ++
  (schema.field? "additionalProperties").toList.map (none, ·)

theorem children_lt {schema : Value} {c : Option String × Value} (h : c ∈ children schema) :
    sizeOf c.2 < sizeOf schema := by
  simp only [children, List.mem_append, List.mem_map] at h
  rcases h with ((⟨o, ho, rfl⟩ | ⟨i, hi, rfl⟩) | hp) | ⟨a, ha, rfl⟩
  · cases hu : unionOptions schema with
    | none => simp [hu] at ho
    | some os =>
      simp only [hu, Option.getD_some] at ho
      have := List.sizeOf_lt_of_mem ho
      have := unionOptions_lt hu
      simp only
      omega
  · exact Value.field?_lt (Option.mem_toList.mp hi)
  · split at hp
    · rename_i properties hps
      obtain ⟨⟨k, p⟩, hm, rfl⟩ := List.mem_map.mp hp
      have h1 := List.sizeOf_lt_of_mem hm
      have h2 := Value.field?_lt hps
      simp only [Prod.mk.sizeOf_spec, Value.obj.sizeOf_spec] at h1 h2 ⊢
      omega
    · simp at hp
  · exact Value.field?_lt (Option.mem_toList.mp ha)

/-- Whether the schema has a bag, set, or sortedBy array at any depth of its `children`. -/
def holdsCollection (schema : Value) : Bool :=
  (schema.field? "x-tazuna-sorted-by").isSome || (schema.field? "x-tazuna-bag").isSome ||
    (schema.field? "x-tazuna-set").isSome ||
  (children schema).attach.any fun ⟨c, _h⟩ => holdsCollection c.2
termination_by sizeOf schema
decreasing_by exact children_lt _h

/-- The issues of the schema at `path` and below, each with the path of field names that leads to it. -/
def issues (path : List String) (schema : Value) : List (List String × Issue) :=
  (match schema.field? "x-tazuna-sorted-by", schema.field? "items" with
    | some (.str key), some item => if orderedKey item key then [] else [(path, .unorderedSortKey key)]
    | some (.str key), none => [(path, .unorderedSortKey key)]
    | _, _ => []) ++
  (match unionOptions schema with
    | some options => if options.any holdsCollection && !allApart options then [(path, .ambiguousUnion)] else []
    | none => []) ++
  (children schema).attach.flatMap fun ⟨c, _h⟩ => issues (path ++ c.1.toList) c.2
termination_by sizeOf schema
decreasing_by exact children_lt _h

/-- The key schema of the map state `st`, with the keyword path that holds it. -/
def mapKeyOf (st : State) : Option (List String × Value) := st.type.map?.map fun m => ([st.name, "key"], m.key)

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
        (mapKeyOf st).toList ++ (st.type.map?.map fun m => [([st.name, "context"], m.context)]).getD [] ++
          (st.held.map fun h => [([st.name, "held"], h.schema)]).getD []

def illegal (d : Definition) : List String × Issue → Illegal
  | (path, .unorderedSortKey key) => .unorderedSortKey d.ref path key
  | (path, .ambiguousUnion) => .ambiguousUnion d.ref path

/-- The paths at and below `path` whose schema declares a default. -/
def defaultPaths (path : List String) (schema : Value) : List (List String) :=
  ((schema.field? "default").toList.map fun _ => path) ++
  (children schema).attach.flatMap fun ⟨c, _h⟩ => defaultPaths (path ++ c.1.toList) c.2
termination_by sizeOf schema
decreasing_by exact children_lt _h

/-- The key schema of each map state of a definition, with the keyword path that holds it. -/
def mapKeysOf (d : Definition) : List (List String × Value) :=
  match d.body with
  | .machine c | .screen c => c.states.filterMap mapKeyOf
  | _ => []

def check (s : Structure) : List Illegal :=
  s.definitions.flatMap fun d =>
    (schemasOf d).flatMap (fun x => (issues x.1 x.2).map (illegal d)) ++
      (mapKeysOf d).flatMap fun x => (defaultPaths x.1 x.2).map (.defaultedMapKey d.ref)

end Tazuna.Semantics.Validation.Schemas
