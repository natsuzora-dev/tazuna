import Tazuna.Ir.Value

/-!
The one rule that picks the option of a union that a value takes, read from the encoded value and the options' JSON
Schemas, and its complement: two options that no value fits both ways. Check reports a union that holds a collection
and has two options that are not `apart` (Illegal.ambiguousUnion), and `apart_disjoint` shows that the option that fits
is then the only one.
-/

namespace Tazuna.Semantics

open Tazuna.Ir

theorem Value.field?_lt {v : Value} {k : String} {x : Value} (h : v.field? k = some x) : sizeOf x < sizeOf v := by
  cases v with
  | obj fields =>
    simp only [Value.field?, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', x'⟩, hf, rfl⟩ := h
    have := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some hf)
    simp only [Value.obj.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢
    omega
  | _ => simp [Value.field?] at h

/-- The options of a union schema: its `anyOf`, which Zod writes for z.union, or its `oneOf`, for z.discriminatedUnion. -/
def unionOptions (schema : Value) : Option (List Value) :=
  match schema.field? "anyOf" with
  | some (.arr options) => some options
  | _ =>
    match schema.field? "oneOf" with
    | some (.arr options) => some options
    | _ => none

theorem unionOptions_lt {schema : Value} {options : List Value} (h : unionOptions schema = some options) :
    sizeOf options < sizeOf schema := by
  unfold unionOptions at h
  split at h
  · rename_i ha
    cases h
    have := Value.field?_lt ha
    simp only [Value.arr.sizeOf_spec] at this
    omega
  · split at h
    · rename_i ho
      cases h
      have := Value.field?_lt ho
      simp only [Value.arr.sizeOf_spec] at this
      omega
    · cases h

/-- The JSON Schema type names that take the value: an integer is also a number. -/
def typeNames : Value → List String
  | .null => ["null"]
  | .bool _ => ["boolean"]
  | .num _ => ["number", "integer"]
  | .str _ => ["string"]
  | .arr _ => ["array"]
  | .obj _ => ["object"]

/-- Whether the schema's `type`, one name or a list of them, takes the value. -/
def fitsType (schema v : Value) : Bool :=
  match schema.field? "type" with
  | none => true
  | some (.str t) => (typeNames v).contains t
  | some (.arr ts) => ts.any fun | .str t => (typeNames v).contains t | _ => false
  | some _ => false

/-- The values that the schema allows by its `const`, which Zod writes for one literal, or its `enum`, if any. -/
def allowed (schema : Value) : Option (List Value) :=
  match schema.field? "const", schema.field? "enum" with
  | some c, _ => some [c]
  | none, some (.arr values) => some values
  | _, _ => none

def admits (schema v : Value) : Bool :=
  (allowed schema).all (·.contains v)

def requiredOf (schema : Value) : List String :=
  match schema.field? "required" with
  | some (.arr required) => required.filterMap fun | .str k => some k | _ => none
  | _ => []

def propertyOf (schema : Value) (k : String) : Option Value :=
  (schema.field? "properties").bind (·.field? k)

/-- Whether the schema takes no field outside its properties, as every object does once parsing is strict. -/
def closed (schema : Value) : Bool :=
  schema.field? "additionalProperties" == some (.bool false)

/--
Whether `v` fits a union option on its surface: its `type`, its `const` or `enum`, the `const` or `enum` of each field
that `v` has, no field outside its properties when it is closed, and its `required` fields.
-/
def fits (option v : Value) : Bool :=
  fitsType option v && admits option v &&
  match v with
  | .obj fields =>
    fields.all (fun (k, x) =>
      match propertyOf option k with
      | some p => admits p x
      | none => !closed option) &&
    (requiredOf option).all fun k => (v.field? k).isSome
  | _ => true

/-- A value of each JSON type, which is all that `typeNames` reads of a value. -/
def typeSamples : List Value := [.null, .bool false, .num 0, .str "", .arr [], .obj []]

/-- Whether two `allowed` lists exist and share no value. -/
def disjoint : Option (List Value) → Option (List Value) → Bool
  | some xs, some ys => xs.all fun x => !ys.contains x
  | _, _ => false

def objectTyped (schema : Value) : Bool :=
  schema.field? "type" == some (.str "object")

/-- Whether `a` is closed and lacks a field that `b` requires. -/
def missesRequired (a b : Value) : Bool :=
  closed a && (requiredOf b).any fun k => (propertyOf a k).isNone

/--
Whether no value fits both options: their types take no common value, their `allowed` values are disjoint, or, for
objects, a field that one requires has disjoint `allowed` values in each, or one is closed and lacks a field that the
other requires.
-/
def apart (a b : Value) : Bool :=
  typeSamples.all (fun w => !(fitsType a w && fitsType b w)) ||
  disjoint (allowed a) (allowed b) ||
  ((objectTyped a || objectTyped b) &&
    ((requiredOf a ++ requiredOf b).any (fun k =>
      match propertyOf a k, propertyOf b k with
      | some p, some q => disjoint (allowed p) (allowed q)
      | _, _ => false) ||
    missesRequired a b || missesRequired b a))

/-- Whether every two options are `apart`. -/
def allApart : List Value → Bool
  | [] => true
  | o :: os => os.all (apart o) && allApart os

end Tazuna.Semantics
