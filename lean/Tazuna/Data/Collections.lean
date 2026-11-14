import Tazuna.Data.Value
import Tazuna.Data.Time

/-!
This module sorts the elements of each bag and set by their canonical text, and each array whose JSON Schema has
`x-tazuna-sorted-by` by that key in ascending order, with equal keys by their canonical text.
-/

namespace Tazuna.Data

/-- The key that orders an element. Keys of different kinds compare equal. -/
inductive SortKey where
  | num (mantissa : Int) (exponent : Nat)
  | instant (ms : Int)
  | date (days : Int)
  | other
deriving DecidableEq, Repr, Inhabited

def SortKey.of : Value → SortKey
  | .num n => .num n.mantissa n.exponent
  | .str s =>
    match parseTime s with
    | .ok t => .instant t
    | .error _ =>
      match parseDate s with
      | .ok d => .date d
      | .error _ => .other
  | _ => .other

def SortKey.lt : SortKey → SortKey → Bool
  | .num m e, .num m' e' => decide (m * 10 ^ e' < m' * 10 ^ e)
  | .instant a, .instant b => decide (a < b)
  | .date a, .date b => decide (a < b)
  | _, _ => false

def keyOf (key : String) (v : Value) : SortKey := SortKey.of ((v.field? key).getD .null)

def insertByKey (key : String) (c : Value) : List Value → List Value
  | [] => [c]
  | d :: ds => if (keyOf key d).lt (keyOf key c) then d :: insertByKey key c ds else c :: d :: ds

/-- The elements sorted by `key`. The sort is stable: elements with equal keys keep their order. -/
def sortByKey (key : String) : List Value → List Value
  | [] => []
  | c :: cs => insertByKey key c (sortByKey key cs)

/-- The elements sorted by their canonical text. -/
def sortCanonical (xs : List Value) : List Value :=
  xs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

def fitsType (schema v : Value) : Bool :=
  match schema.field? "type", v with
  | none, _ => true
  | some (.str "null"), .null => true
  | some (.str "boolean"), .bool _ => true
  | some (.str "number"), .num _ | some (.str "integer"), .num _ => true
  | some (.str "string"), .str _ => true
  | some (.str "array"), .arr _ => true
  | some (.str "object"), .obj _ => true
  | _, _ => false

theorem Value.field?_lt {v : Value} {k : String} {x : Value} (h : v.field? k = some x) : sizeOf x < sizeOf v := by
  cases v with
  | obj fields =>
    simp only [Value.field?, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', x'⟩, hf, rfl⟩ := h
    have := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some hf)
    simp only [Value.obj.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢
    omega
  | _ => simp [Value.field?] at h

/--
The value with each array sorted as its schema says. The recursion follows the schema (anyOf options, items,
properties), so it terminates.
-/
def sortCollections (schema v : Value) : Value :=
  match _ha : schema.field? "anyOf" with
  | some (.arr options) =>
    match _hf : options.find? (fitsType · v) with
    | some option => sortCollections option v
    | none => v
  | _ =>
    match v with
    | .arr xs =>
      let items := match (schema.field? "items").attach with
        | some ⟨item, _hi⟩ => xs.map (sortCollections item)
        | none => xs
      match schema.field? "x-tazuna-sorted-by", schema.field? "x-tazuna-bag", schema.field? "x-tazuna-set" with
      | some (.str key), _, _ => .arr (sortByKey key (sortCanonical items))
      | _, some (.bool true), _ | _, _, some (.bool true) => .arr (sortCanonical items)
      | _, _, _ => .arr items
    | .obj fields =>
      match _hp : schema.field? "properties" with
      | some properties =>
        .obj (fields.map fun (k, x) => (k, match _hk : properties.field? k with
          | some p => sortCollections p x
          | none => x))
      | none => .obj fields
    | v => v
termination_by sizeOf schema
decreasing_by
  · have h1 := Value.field?_lt _ha
    have h2 := List.sizeOf_lt_of_mem (List.mem_of_find?_eq_some _hf)
    simp only [Value.arr.sizeOf_spec] at h1
    omega
  · exact Value.field?_lt (Option.mem_def.mp _hi)
  · exact Nat.lt_trans (Value.field?_lt _hk) (Value.field?_lt _hp)

end Tazuna.Data
