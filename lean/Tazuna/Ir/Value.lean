import Lean.Data.Json.Basic
import Lean.Data.Json.Printer

namespace Tazuna.Ir

/-- A JSON value. Object fields keep their order, which the trace lines that the engine writes keep too. -/
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

mutual

/-- `v` with the fields of `w` in place, at any depth: an object merges its fields, and any other value of `w` replaces. -/
def Value.overlay : Value → Value → Value
  | .obj fs, .obj gs => .obj (Value.overlayFields fs gs ++ gs.filter fun (k, _) => (fs.lookup k).isNone)
  | _, w => w

def Value.overlayFields : List (String × Value) → List (String × Value) → List (String × Value)
  | [], _ => []
  | (k, v) :: fs, gs => (k, match gs.lookup k with | some w => v.overlay w | none => v) :: Value.overlayFields fs gs

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

instance : ToValue Int := ⟨fun n => .num ⟨n, 0⟩⟩

instance : ToValue Value := ⟨id⟩

instance {α : Type} [ToValue α] : ToValue (Option α) := ⟨fun o => (o.map ToValue.toValue).getD .null⟩

instance {α : Type} [ToValue α] : ToValue (List α) := ⟨fun l => .arr (l.map ToValue.toValue)⟩

/-- A list of keys and values is an object, in the list's order. -/
instance (priority := high) {α : Type} [ToValue α] : ToValue (List (String × α)) :=
  ⟨fun l => .obj (l.map fun (key, a) => (key, ToValue.toValue a))⟩

/-- A pair is an array of its two values. -/
instance {α β : Type} [ToValue α] [ToValue β] : ToValue (α × β) :=
  ⟨fun (a, b) => .arr [ToValue.toValue a, ToValue.toValue b]⟩

class FromValue (α : Type) where
  fromValue : Value → Except String α

instance : FromValue String := ⟨fun
  | .str s => pure s
  | _ => throw "expected a string"⟩

instance : FromValue Bool := ⟨fun
  | .bool b => pure b
  | _ => throw "expected a boolean"⟩

/-- Whether `m` is a safe integer, which Zod's z.int() takes: JSON numbers are doubles. -/
def isSafeInteger (m : Int) : Bool := -9007199254740991 ≤ m && m ≤ 9007199254740991

instance : FromValue Nat := ⟨fun
  | .num ⟨m, 0⟩ => if m ≥ 0 && isSafeInteger m then pure m.toNat else throw "expected a natural number"
  | _ => throw "expected a natural number"⟩

instance : FromValue Int := ⟨fun
  | .num ⟨m, 0⟩ => if isSafeInteger m then pure m else throw "expected a safe integer"
  | _ => throw "expected an integer"⟩

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

instance {α β : Type} [FromValue α] [FromValue β] : FromValue (α × β) := ⟨fun
  | .arr [a, b] => do pure (← FromValue.fromValue a, ← FromValue.fromValue b)
  | _ => throw "expected an array of two values"⟩

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

end Tazuna.Ir
