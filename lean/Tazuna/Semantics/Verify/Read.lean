import Tazuna.Semantics.Value.Parse
import Tazuna.Semantics.Verify.Compare

/-!
How verify reads a value by its definition's JSON Schema: each top-level field that parses by its own schema encoded
again, with its default where it is absent, and any other field as it is; then each bag and set as a bag, each sortedBy
array as runs of equal keys, and each string whose schema is a key reference (`x-tazuna-key`) as a reference to that
entity.
-/

namespace Tazuna.Semantics.Verify

open Tazuna.Ir

/-- `v` with each field of the object schema `schema` that parses encoded again, as verify compares it. -/
def canonicalFields (schema v : Value) : Value :=
  match v with
  | .obj fields =>
    let properties := match schema.field? "properties" with
      | some (.obj ps) => ps
      | _ => []
    let extra := fields.filter fun (k, _) => (properties.lookup k).isNone
    let own := properties.filterMap fun (k, p) =>
      let given := fields.lookup k
      match parseValue p given with
      | .ok r => if r.issues.isEmpty then r.value.map (k, ·) else given.map (k, ·)
      | .error () => given.map (k, ·)
    .obj (own ++ extra)
  | v => v

/-- `v` read by `schema`: its bags, sortedBy runs and key references wrapped. -/
partial def cvalueBy (schema v : Value) : CValue :=
  match v, schema.field? "x-tazuna-key" with
  | .str s, some (.str entity) => .ref entity s
  | _, _ =>
    if schema.field? "x-tazuna-nullable" == some (.bool true) then
      if v == .null then .leaf .null else cvalueBy (nullableInner schema) v
    else match unionOptions schema with
    | some options =>
      match options.find? (fits · v) with
      | some option => cvalueBy option v
      | none => CValue.ofValue v
    | none =>
      match v with
      | .arr xs =>
        let read (x : Value) := match schema.field? "items" with
          | some item => cvalueBy item x
          | none => CValue.ofValue x
        match schema.field? "x-tazuna-sorted-by", schema.field? "x-tazuna-bag", schema.field? "x-tazuna-set" with
        | some (.str key), _, _ => .runs ((adjacentRuns key xs).map fun run => .bag (run.map read))
        | _, some (.bool true), _ | _, _, some (.bool true) => .bag (xs.map read)
        | _, _, _ => .arr (xs.map read)
      | .obj fields =>
        .obj (fields.map fun (k, x) => (k, match propertyOf schema k with
          | some p => cvalueBy p x
          | none => CValue.ofValue x))
      | v => .leaf v

/-- The value `v` of the part `part` of `d`, read by its JSON Schema as verify compares it. -/
def readValueOf (s : Structure) (d : Definition) (part : Part) (v : Value) : CValue :=
  let schema := match part with
    | .input => Schema.input d.ref
    | .output => .output d.ref
    | .payload => .payload d.ref
    | .control name => .control d.ref name
  match s.schemaOf schema with
  | some json => cvalueBy json (canonicalFields json v)
  | none => CValue.ofValue v

end Tazuna.Semantics.Verify
