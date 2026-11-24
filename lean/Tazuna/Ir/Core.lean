/-! The elaborated IR: terms indexed by their type, so an ill-typed program cannot be represented. Elaboration
(`Tazuna.Ir.Elab`) is the only producer; it resolves names, labels and Gleam's surface syntax away. -/

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
  | .int | .str | .param _ => true
  | .list t => comparable t
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
    { name := "tazuna.Spec", params := [], variants := [] } ]

def Ty.bool : Ty := .adt 0 [] [[], []]
def Ty.spec : Ty := .adt 4 [] []

/-- A variable of type `t` in the context `Γ`, the innermost binding first. -/
inductive Var : List Ty → Ty → Type
  | here {Γ t} : Var (t :: Γ) t
  | there {Γ t u} : Var Γ t → Var (u :: Γ) t

/-- The variable at position `i` from the innermost, if it has type `t`. -/
def Var.at? : (Γ : List Ty) → Nat → (t : Ty) → Option (Var Γ t)
  | [], _, _ => none
  | u :: _, 0, t => (Ty.same u t).map fun ⟨h⟩ => h ▸ .here
  | _ :: Γ, i + 1, t => (Var.at? Γ i t).map .there

/-- Operators with their operand and result types. Int arithmetic follows Gleam on Erlang: unbounded, `/` and `%`
truncate, and dividing by zero gives zero. -/
inductive BinOp : Ty → Ty → Ty → Type
  | add : BinOp .int .int .int
  | sub : BinOp .int .int .int
  | mul : BinOp .int .int .int
  | div : BinOp .int .int .int
  | mod : BinOp .int .int .int
  | lt : BinOp .int .int .bool
  | le : BinOp .int .int .bool
  | gt : BinOp .int .int .bool
  | ge : BinOp .int .int .bool
  | and : BinOp .bool .bool .bool
  | or : BinOp .bool .bool .bool
  | concat : BinOp .str .str .str
  | eq {t} (h : t.comparable = true) : BinOp t t .bool
  | ne {t} (h : t.comparable = true) : BinOp t t .bool

mutual
/-- A pattern matching values of type `t` and binding variables of types `Δ`, the first binding innermost. -/
inductive Pat : Ty → List Ty → Type
  | wild {t} : Pat t []
  | bind {t} : Pat t [t]
  | int (n : Int) : Pat .int []
  | str (s : String) : Pat .str []
  | tuple {ts Δ} (ps : Pats ts Δ) : Pat (.tuple ts) Δ
  | ctor {i args vs Δ} (v : Fin vs.length) (ps : Pats (vs.get v) Δ) : Pat (.adt i args vs) Δ
  /-- `p as name`: the name binds after the variables of `p`. -/
  | as {t Δ} (p : Pat t Δ) : Pat t (Δ ++ [t])
inductive Pats : List Ty → List Ty → Type
  | nil : Pats [] []
  | cons {t ts Δ Δ'} (p : Pat t Δ) (ps : Pats ts Δ') : Pats (t :: ts) (Δ ++ Δ')
end

mutual
/-- A term of type `t` over the globals `G` (earlier definitions only, so references are acyclic by construction) and
the locals `Γ`. Calls are positional: elaboration has placed every labelled argument. -/
inductive Expr (G : List Ty) : List Ty → Ty → Type
  | int {Γ} (n : Int) : Expr G Γ .int
  | str {Γ} (s : String) : Expr G Γ .str
  | var {Γ t} (v : Var Γ t) : Expr G Γ t
  | global {Γ t} (v : Var G t) : Expr G Γ t
  | ctor {Γ i args vs} (v : Fin vs.length) (es : Exprs G Γ (vs.get v)) : Expr G Γ (.adt i args vs)
  /-- Gleam's record accessor: the field sits at index `k` with type `ft` in every variant. -/
  | field {Γ i args vs ft} (label : String) (k : Nat) (hk : ∀ fs ∈ vs, fs[k]? = some ft)
      (e : Expr G Γ (.adt i args vs)) : Expr G Γ ft
  | index {Γ ts} (e : Expr G Γ (.tuple ts)) (k : Fin ts.length) : Expr G Γ (ts.get k)
  /-- Record update, only on a type with one variant, so it never meets another variant at run time. -/
  | update {Γ i args fs} (e : Expr G Γ (.adt i args [fs])) (p : Patch G Γ fs) : Expr G Γ (.adt i args [fs])
  | call {Γ ps r} (f : Expr G Γ (.fn ps r)) (args : Exprs G Γ ps) : Expr G Γ r
  | lam {Γ ps r} (body : Expr G (ps ++ Γ) r) : Expr G Γ (.fn ps r)
  | let_ {Γ t r} (e : Expr G Γ t) (body : Expr G (t :: Γ) r) : Expr G Γ r
  | case {Γ t r} (e : Expr G Γ t) (cs : Clauses G Γ t r) : Expr G Γ r
  | list {Γ t} (items : Items G Γ t) : Expr G Γ (.list t)
  | tuple {Γ ts} (es : Exprs G Γ ts) : Expr G Γ (.tuple ts)
  | bin {Γ a b c} (op : BinOp a b c) (l : Expr G Γ a) (r : Expr G Γ b) : Expr G Γ c
  | not {Γ} (e : Expr G Γ .bool) : Expr G Γ .bool
  | neg {Γ} (e : Expr G Γ .int) : Expr G Γ .int
inductive Exprs (G : List Ty) : List Ty → List Ty → Type
  | nil {Γ} : Exprs G Γ []
  | cons {Γ t ts} (e : Expr G Γ t) (es : Exprs G Γ ts) : Exprs G Γ (t :: ts)
inductive Items (G : List Ty) : List Ty → Ty → Type
  | nil {Γ t} : Items G Γ t
  | cons {Γ t} (e : Expr G Γ t) (es : Items G Γ t) : Items G Γ t
/-- For each field in order, keep it or replace it. -/
inductive Patch (G : List Ty) : List Ty → List Ty → Type
  | nil {Γ} : Patch G Γ []
  | keep {Γ t ts} (rest : Patch G Γ ts) : Patch G Γ (t :: ts)
  | set {Γ t ts} (e : Expr G Γ t) (rest : Patch G Γ ts) : Patch G Γ (t :: ts)
/-- Clauses in order; the first whose pattern matches and whose guard holds is taken. -/
inductive Clauses (G : List Ty) : List Ty → Ty → Ty → Type
  | nil {Γ t r} : Clauses G Γ t r
  | cons {Γ t r} {Δ : List Ty} (p : Pat t Δ) (body : Expr G (Δ ++ Γ) r) (rest : Clauses G Γ t r) :
      Clauses G Γ t r
  | guarded {Γ t r} {Δ : List Ty} (p : Pat t Δ) (guard : Expr G (Δ ++ Γ) .bool) (body : Expr G (Δ ++ Γ) r)
      (rest : Clauses G Γ t r) : Clauses G Γ t r
end

/-- Global definitions in dependency order: each body sees only the definitions before it. A function is a definition
whose body is a lambda. -/
inductive Defs : List Ty → Type
  | nil : Defs []
  | snoc {G} (defs : Defs G) (t : Ty) (body : Expr G [] t) : Defs (t :: G)

/-- A loaded program: its type table (the prelude first), its definitions, and the root definition. -/
structure Program (rootTy : Ty) where
  types : List TypeDecl
  globals : List Ty
  defs : Defs globals
  root : Var globals rootTy

end Tazuna.Ir
