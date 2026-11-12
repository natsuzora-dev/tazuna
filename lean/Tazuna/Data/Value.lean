import Lean.Data.Json.Basic
import Lean.Data.Json.Printer

namespace Tazuna.Data

/-- A JSON value. Object fields keep their order, because the TS runtime compares values by `JSON.stringify`. -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (n : Lean.JsonNumber)
  | str (s : String)
  | arr (elements : List Value)
  | obj (fields : List (String × Value))
deriving Repr, Inhabited

mutual

def decValue (v₁ v₂ : Value) : Decidable (v₁ = v₂) :=
  match v₁, v₂ with
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
    if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; injection e; contradiction)
  | .num a, .num b =>
    if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; injection e; contradiction)
  | .str a, .str b =>
    if h : a = b then isTrue (by rw [h]) else isFalse (by intro e; injection e; contradiction)
  | .arr a, .arr b =>
    match decValueList a b with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro e; injection e; contradiction)
  | .obj a, .obj b =>
    match decFieldList a b with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro e; injection e; contradiction)
  | .null, .bool _ | .null, .num _ | .null, .str _ | .null, .arr _ | .null, .obj _
  | .bool _, .null | .bool _, .num _ | .bool _, .str _ | .bool _, .arr _ | .bool _, .obj _
  | .num _, .null | .num _, .bool _ | .num _, .str _ | .num _, .arr _ | .num _, .obj _
  | .str _, .null | .str _, .bool _ | .str _, .num _ | .str _, .arr _ | .str _, .obj _
  | .arr _, .null | .arr _, .bool _ | .arr _, .num _ | .arr _, .str _ | .arr _, .obj _
  | .obj _, .null | .obj _, .bool _ | .obj _, .num _ | .obj _, .str _ | .obj _, .arr _ =>
    isFalse (by intro e; injection e)

def decValueList (a b : List Value) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | _ :: _, [] | [], _ :: _ => isFalse (by intro e; injection e)
  | x :: xs, y :: ys =>
    match decValue x y, decValueList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse h, _ => isFalse (by intro e; injection e; contradiction)
    | _, isFalse h => isFalse (by intro e; injection e; contradiction)

def decFieldList (a b : List (String × Value)) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | _ :: _, [] | [], _ :: _ => isFalse (by intro e; injection e)
  | (k₁, x) :: xs, (k₂, y) :: ys =>
    if hk : k₁ = k₂ then
      match decValue x y, decFieldList xs ys with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [hk, h₁, h₂])
      | isFalse h, _ => isFalse (by intro e; injection e with e₁ e₂; injection e₁; contradiction)
      | _, isFalse h => isFalse (by intro e; injection e; contradiction)
    else isFalse (by intro e; injection e with e₁ e₂; injection e₁; contradiction)

end

instance : DecidableEq Value := decValue

def Value.field? : Value → String → Option Value
  | .obj fields, name => (fields.find? (·.1 == name)).map (·.2)
  | _, _ => none

/-- The string that TS `String(payload[key])` gives. -/
def Value.keyString : Value → String
  | .str s => s
  | .num n => toString n
  | .bool b => toString b
  | .null => "null"
  | _ => "[object Object]"

mutual

/-- The strings in the value, excluding object field names. -/
def Value.strings : Value → List String
  | .str s => [s]
  | .arr vs => Value.stringsOfList vs
  | .obj fs => Value.stringsOfFields fs
  | _ => []

def Value.stringsOfList : List Value → List String
  | [] => []
  | v :: vs => v.strings ++ Value.stringsOfList vs

def Value.stringsOfFields : List (String × Value) → List String
  | [] => []
  | (_, v) :: fs => v.strings ++ Value.stringsOfFields fs

end

mutual

/-- The value with each string, excluding object field names, replaced by `f` of it. -/
def Value.mapStrings (f : String → String) : Value → Value
  | .str s => .str (f s)
  | .arr vs => .arr (Value.mapStringsList f vs)
  | .obj fs => .obj (Value.mapStringsFields f fs)
  | v => v

def Value.mapStringsList (f : String → String) : List Value → List Value
  | [] => []
  | v :: vs => v.mapStrings f :: Value.mapStringsList f vs

def Value.mapStringsFields (f : String → String) : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, v.mapStrings f) :: Value.mapStringsFields f fs

end

/-- The value of JS `{...a, ...b}`. -/
def Value.merge : Value → Value → Value
  | .obj a, .obj b => .obj (a.map (fun (k, v) => (k, (b.lookup k).getD v)) ++ b.filter fun (k, _) => (a.lookup k).isNone)
  | _, b => b

class ToValue (α : Type) where
  toValue : α → Value

instance : ToValue String := ⟨.str⟩

instance : ToValue Bool := ⟨.bool⟩

instance : ToValue Nat := ⟨fun n => .num n⟩

instance : ToValue Value := ⟨id⟩

instance {α : Type} [ToValue α] : ToValue (Option α) := ⟨fun o => (o.map ToValue.toValue).getD .null⟩

instance {α : Type} [ToValue α] : ToValue (List α) := ⟨fun l => .arr (l.map ToValue.toValue)⟩

/-- A list of keys and values is an object, in the list's order. -/
instance (priority := high) {α : Type} [ToValue α] : ToValue (List (String × α)) :=
  ⟨fun l => .obj (l.map fun (key, a) => (key, ToValue.toValue a))⟩

class FromValue (α : Type) where
  fromValue : Value → Except String α

instance : FromValue String := ⟨fun
  | .str s => pure s
  | _ => throw "expected a string"⟩

instance : FromValue Bool := ⟨fun
  | .bool b => pure b
  | _ => throw "expected a boolean"⟩

instance : FromValue Nat := ⟨fun
  | .num ⟨m, 0⟩ => if m ≥ 0 then pure m.toNat else throw "expected a natural number"
  | _ => throw "expected a natural number"⟩

instance : FromValue Value := ⟨pure⟩

instance {α : Type} [FromValue α] : FromValue (Option α) := ⟨fun
  | .null => pure none
  | v => some <$> FromValue.fromValue v⟩

instance {α : Type} [FromValue α] : FromValue (List α) := ⟨fun
  | .arr vs => vs.mapM FromValue.fromValue
  | _ => throw "expected an array"⟩

instance (priority := high) {α : Type} [FromValue α] : FromValue (List (String × α)) := ⟨fun
  | .obj fields => fields.mapM fun (key, v) => do pure (key, ← FromValue.fromValue v)
  | _ => throw "expected an object"⟩

/-- The JSON text of a string. -/
def quoted (s : String) : String := Lean.Json.renderString s

/-- The JSON text of an object, with the fields in name order. -/
def objectText (fs : List (String × String)) : String :=
  "{" ++ ",".intercalate ((fs.mergeSort fun a b => decide (a.1 ≤ b.1)).map fun (k, v) => quoted k ++ ":" ++ v) ++ "}"

def arrayText (xs : List String) : String := "[" ++ ",".intercalate xs ++ "]"

mutual

/--
The JSON text with the fields in name order by code point, so the texts of two values are equal exactly when the values
differ only in field order, as with TS `canonicalJson`.
-/
def Value.canonical : Value → String
  | .null => "null"
  | .bool b => toString b
  | .num n => toString n
  | .str s => quoted s
  | .arr vs => arrayText (canonicalList vs)
  | .obj fs => objectText (canonicalFields fs)

def canonicalList : List Value → List String
  | [] => []
  | v :: vs => v.canonical :: canonicalList vs

def canonicalFields : List (String × Value) → List (String × String)
  | [] => []
  | (k, v) :: fs => (k, v.canonical) :: canonicalFields fs

end

end Tazuna.Data
