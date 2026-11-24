/-! Types after elaboration, the declarations of the types a program defines, and the types Lean owns. -/

namespace Tazuna.Ir

/-- A type after elaboration. `adt i args variants` is the `i`-th declaration of the program's type table at `args`,
carrying each variant's field types. No declaration refers to itself, directly or through others, so every type is a
finite tree and the meaning of a type follows its structure. `param k` is the `k`-th parameter of the declaration a
field type belongs to, or a rigid type variable of a generic function body. -/
inductive Ty where
  | int
  | str
  | list (t : Ty)
  | tuple (ts : List Ty)
  | fn (ps : List Ty) (r : Ty)
  | adt (i : Nat) (args : List Ty) (variants : List (List Ty))
  | param (k : Nat)
  /-- A multiset: equal when each value occurs as often in both. -/
  | bag (t : Ty)
  /-- A finite map: equal when it has the same keys, each with an equal value. -/
  | table (k v : Ty)
  /-- A day, without a calendar: only adding days and counting days between two dates have meaning. -/
  | date
  /-- An identifier a step makes fresh; only `==` has meaning. -/
  | id
deriving Repr, Inhabited

namespace Ty

mutual
/-- Evidence that two types are equal, when they are; elaboration casts terms with it. -/
def same : (a b : Ty) → Option (PLift (a = b))
  | .int, .int => some ⟨rfl⟩
  | .str, .str => some ⟨rfl⟩
  | .list a, .list b => (same a b).map fun ⟨h⟩ => ⟨h ▸ rfl⟩
  | .tuple a, .tuple b => (sames a b).map fun ⟨h⟩ => ⟨h ▸ rfl⟩
  | .fn a r, .fn b u => match sames a b, same r u with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | .adt i a v, .adt j b w =>
    if hi : i = j then match sames a b, samess v w with
      | some ⟨h⟩, some ⟨h'⟩ => some ⟨hi ▸ h ▸ h' ▸ rfl⟩
      | _, _ => none
    else none
  | .param i, .param j => if h : i = j then some ⟨h ▸ rfl⟩ else none
  | .bag a, .bag b => (same a b).map fun ⟨h⟩ => ⟨h ▸ rfl⟩
  | .table k v, .table k' v' => match same k k', same v v' with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | .date, .date => some ⟨rfl⟩
  | .id, .id => some ⟨rfl⟩
  | _, _ => none
def sames : (a b : List Ty) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | x :: xs, y :: ys => match same x y, sames xs ys with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | _, _ => none
def samess : (a b : List (List Ty)) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | x :: xs, y :: ys => match sames x y, samess xs ys with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | _, _ => none
end

mutual
/-- Replaces `param k` with `args[k]`. -/
def inst (args : List Ty) : Ty → Ty
  | .int => .int
  | .str => .str
  | .list t => .list (inst args t)
  | .tuple ts => .tuple (insts args ts)
  | .fn ps r => .fn (insts args ps) (inst args r)
  | .adt i ts vs => .adt i (insts args ts) (instss args vs)
  | .param k => args[k]?.getD (.param k)
  | .bag t => .bag (inst args t)
  | .table k v => .table (inst args k) (inst args v)
  | .date => .date
  | .id => .id
def insts (args : List Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => inst args t :: insts args ts
def instss (args : List Ty) : List (List Ty) → List (List Ty)
  | [] => []
  | ts :: vs => insts args ts :: instss args vs
end

mutual
/-- Whether `==` may compare values of this type: Gleam compares functions by reference, which has no meaning here. -/
def comparable : Ty → Bool
  | .int | .str | .param _ | .date | .id => true
  | .list t | .bag t => comparable t
  | .table k v => comparable k && comparable v
  | .tuple ts => comparables ts
  | .adt _ _ vs => comparabless vs
  | .fn .. => false
def comparables : List Ty → Bool
  | [] => true
  | t :: ts => comparable t && comparables ts
def comparabless : List (List Ty) → Bool
  | [] => true
  | ts :: vs => comparables ts && comparabless vs
end

/-- Evidence that every variant has a field of type `ft` at index `k`, when it does. -/
def fieldAt (k : Nat) (ft : Ty) : (vs : List (List Ty)) → Option (PLift (∀ fs ∈ vs, fs[k]? = some ft))
  | [] => some ⟨by simp⟩
  | fs :: vs => match h : fs[k]?, fieldAt k ft vs with
    | some f, some ⟨p⟩ => (same f ft).map fun ⟨e⟩ => ⟨by
        intro gs hg
        cases hg with
        | head => rw [h, e]
        | tail _ hm => exact p gs hm⟩
    | _, _ => none

end Ty

structure Field where
  label : Option String
  ty : Ty
deriving Inhabited

structure Variant where
  name : String
  fields : List Field
deriving Inhabited

structure TypeDecl where
  name : String
  params : List String
  variants : List Variant
deriving Inhabited

namespace TypeDecl

/-- Each variant's field types at `args`: what `Ty.adt` carries. -/
def variantTys (d : TypeDecl) (args : List Ty) : List (List Ty) :=
  d.variants.map fun v => Ty.insts args (v.fields.map (·.ty))

/-- Gleam's record accessor: the field with this label sits at the same index with the same type in every variant. -/
def accessor (d : TypeDecl) (label : String) : Option (Nat × Ty) :=
  match d.variants with
  | [] => none
  | v :: _ => do
    let k ← v.fields.findIdx? (·.label == some label)
    let f ← v.fields[k]?
    if d.variants.all fun w => match w.fields[k]? with
        | some g => g.label == some label && (Ty.same g.ty f.ty).isSome
        | none => false
    then some (k, f.ty) else none

end TypeDecl

/-- The types every program has, at fixed indices: Lean owns them, the IR never declares them. -/
def prelude : List TypeDecl :=
  [ { name := "Bool", params := [], variants := [⟨"True", []⟩, ⟨"False", []⟩] },
    { name := "Nil", params := [], variants := [⟨"Nil", []⟩] },
    { name := "Result", params := ["a", "e"],
      variants := [⟨"Ok", [⟨none, .param 0⟩]⟩, ⟨"Error", [⟨none, .param 1⟩]⟩] },
    { name := "gleam/option.Option", params := ["a"],
      variants := [⟨"Some", [⟨none, .param 0⟩]⟩, ⟨"None", []⟩] },
    { name := "tazuna.Spec", params := [], variants := [] },
    { name := "tazuna.PickError", params := [], variants := [⟨"Empty", []⟩, ⟨"Tie", []⟩] } ]

def Ty.bool : Ty := .adt 0 [] [[], []]
def Ty.spec : Ty := .adt 4 [] []
def Ty.pickError : Ty := .adt 5 [] [[], []]
def Ty.result (a e : Ty) : Ty := .adt 2 [a, e] [[a], [e]]
def Ty.option (a : Ty) : Ty := .adt 3 [a] [[a], []]

/-- The prelude's types at fixed indices are the ones the helpers above name. -/
example : prelude[0]?.map (fun d => Ty.adt 0 [] (d.variantTys [])) = some Ty.bool := rfl
example : prelude[5]?.map (fun d => Ty.adt 5 [] (d.variantTys [])) = some Ty.pickError := rfl
example (a e : Ty) : prelude[2]?.map (fun d => Ty.adt 2 [a, e] (d.variantTys [a, e])) = some (Ty.result a e) := rfl
example (a : Ty) : prelude[3]?.map (fun d => Ty.adt 3 [a] (d.variantTys [a])) = some (Ty.option a) := rfl

end Tazuna.Ir
