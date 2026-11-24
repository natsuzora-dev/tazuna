/-! The elaborated IR: terms indexed by their type, so an ill-typed program cannot be represented. Elaboration
(`Tazuna.Ir.Elab`) is the only producer; it resolves names, labels and Gleam's surface syntax away. -/

namespace Tazuna.Ir

/-- A type after elaboration. `adt i` is the `i`-th declaration of the program's type table; `param k` is the `k`-th
parameter of the declaration a field type belongs to, or a rigid type variable of a generic function body. -/
inductive Ty where
  | int
  | str
  | list (t : Ty)
  | tuple (ts : List Ty)
  | fn (ps : List Ty) (r : Ty)
  | adt (i : Nat) (args : List Ty)
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
  | .adt i a, .adt j b => if hi : i = j then (sames a b).map fun ⟨h⟩ => ⟨hi ▸ h ▸ rfl⟩ else none
  | .param i, .param j => if h : i = j then some ⟨h ▸ rfl⟩ else none
  | _, _ => none
def sames : (a b : List Ty) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | x :: xs, y :: ys => match same x y, sames xs ys with
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
  | .adt i ts => .adt i (insts args ts)
  | .param k => args[k]?.getD (.param k)
def insts (args : List Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => inst args t :: insts args ts
end

mutual
/-- Whether `==` may compare values of this type: Gleam compares functions by reference, which has no meaning here. -/
def comparable : Ty → Bool
  | .int | .str | .param _ => true
  | .list t => comparable t
  | .tuple ts | .adt _ ts => comparables ts
  | .fn .. => false
def comparables : List Ty → Bool
  | [] => true
  | t :: ts => comparable t && comparables ts
end

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

def fieldTys (d : TypeDecl) (v : Fin d.variants.length) (args : List Ty) : List Ty :=
  Ty.insts args ((d.variants.get v).fields.map (·.ty))

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

def Ty.bool : Ty := .adt 0 []
def Ty.spec : Ty := .adt 4 []

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
inductive Pat (T : List TypeDecl) : Ty → List Ty → Type
  | wild {t} : Pat T t []
  | bind {t} : Pat T t [t]
  | int (n : Int) : Pat T .int []
  | str (s : String) : Pat T .str []
  | tuple {ts Δ} (ps : Pats T ts Δ) : Pat T (.tuple ts) Δ
  | ctor {i args Δ} (d : TypeDecl) (h : T[i]? = some d) (v : Fin d.variants.length)
      (ps : Pats T (d.fieldTys v args) Δ) : Pat T (.adt i args) Δ
  /-- `p as name`: the name binds after the variables of `p`. -/
  | as {t Δ} (p : Pat T t Δ) : Pat T t (Δ ++ [t])
inductive Pats (T : List TypeDecl) : List Ty → List Ty → Type
  | nil : Pats T [] []
  | cons {t ts Δ Δ'} (p : Pat T t Δ) (ps : Pats T ts Δ') : Pats T (t :: ts) (Δ ++ Δ')
end

mutual
/-- A term of type `t` over the globals `G` (earlier definitions only, so references are acyclic by construction) and
the locals `Γ`. Calls are positional: elaboration has placed every labelled argument. -/
inductive Expr (T : List TypeDecl) (G : List Ty) : List Ty → Ty → Type
  | int {Γ} (n : Int) : Expr T G Γ .int
  | str {Γ} (s : String) : Expr T G Γ .str
  | var {Γ t} (v : Var Γ t) : Expr T G Γ t
  | global {Γ t} (v : Var G t) : Expr T G Γ t
  | ctor {Γ i args} (d : TypeDecl) (h : T[i]? = some d) (v : Fin d.variants.length)
      (es : Exprs T G Γ (d.fieldTys v args)) : Expr T G Γ (.adt i args)
  | field {Γ i args k ft} (d : TypeDecl) (h : T[i]? = some d) (label : String) (hk : d.accessor label = some (k, ft))
      (e : Expr T G Γ (.adt i args)) : Expr T G Γ (ft.inst args)
  | index {Γ ts} (e : Expr T G Γ (.tuple ts)) (k : Fin ts.length) : Expr T G Γ (ts.get k)
  /-- Record update, only on a type with one variant, so it never meets another variant at run time. -/
  | update {Γ i args} (d : TypeDecl) (h : T[i]? = some d) (hv : 0 < d.variants.length)
      (e : Expr T G Γ (.adt i args)) (p : Patch T G Γ (d.fieldTys ⟨0, hv⟩ args)) : Expr T G Γ (.adt i args)
  | call {Γ ps r} (f : Expr T G Γ (.fn ps r)) (args : Exprs T G Γ ps) : Expr T G Γ r
  | lam {Γ ps r} (body : Expr T G (ps ++ Γ) r) : Expr T G Γ (.fn ps r)
  | let_ {Γ t r} (e : Expr T G Γ t) (body : Expr T G (t :: Γ) r) : Expr T G Γ r
  | case {Γ t r} (e : Expr T G Γ t) (cs : Clauses T G Γ t r) : Expr T G Γ r
  | list {Γ t} (items : Items T G Γ t) : Expr T G Γ (.list t)
  | tuple {Γ ts} (es : Exprs T G Γ ts) : Expr T G Γ (.tuple ts)
  | bin {Γ a b c} (op : BinOp a b c) (l : Expr T G Γ a) (r : Expr T G Γ b) : Expr T G Γ c
  | not {Γ} (e : Expr T G Γ .bool) : Expr T G Γ .bool
  | neg {Γ} (e : Expr T G Γ .int) : Expr T G Γ .int
inductive Exprs (T : List TypeDecl) (G : List Ty) : List Ty → List Ty → Type
  | nil {Γ} : Exprs T G Γ []
  | cons {Γ t ts} (e : Expr T G Γ t) (es : Exprs T G Γ ts) : Exprs T G Γ (t :: ts)
inductive Items (T : List TypeDecl) (G : List Ty) : List Ty → Ty → Type
  | nil {Γ t} : Items T G Γ t
  | cons {Γ t} (e : Expr T G Γ t) (es : Items T G Γ t) : Items T G Γ t
/-- For each field in order, keep it or replace it. -/
inductive Patch (T : List TypeDecl) (G : List Ty) : List Ty → List Ty → Type
  | nil {Γ} : Patch T G Γ []
  | keep {Γ t ts} (rest : Patch T G Γ ts) : Patch T G Γ (t :: ts)
  | set {Γ t ts} (e : Expr T G Γ t) (rest : Patch T G Γ ts) : Patch T G Γ (t :: ts)
/-- Clauses in order; the first whose pattern matches and whose guard holds is taken. -/
inductive Clauses (T : List TypeDecl) (G : List Ty) : List Ty → Ty → Ty → Type
  | nil {Γ t r} : Clauses T G Γ t r
  | cons {Γ t r} {Δ : List Ty} (p : Pat T t Δ) (body : Expr T G (Δ ++ Γ) r) (rest : Clauses T G Γ t r) :
      Clauses T G Γ t r
  | guarded {Γ t r} {Δ : List Ty} (p : Pat T t Δ) (guard : Expr T G (Δ ++ Γ) .bool) (body : Expr T G (Δ ++ Γ) r)
      (rest : Clauses T G Γ t r) : Clauses T G Γ t r
end

/-- Global definitions in dependency order: each body sees only the definitions before it. A function is a definition
whose body is a lambda. -/
inductive Defs (T : List TypeDecl) : List Ty → Type
  | nil : Defs T []
  | snoc {G} (defs : Defs T G) (t : Ty) (body : Expr T G [] t) : Defs T (t :: G)

/-- A loaded program: its type table (the prelude first), its definitions, and the root definition. -/
structure Program (rootTy : Ty) where
  types : List TypeDecl
  globals : List Ty
  defs : Defs types globals
  root : Var globals rootTy

end Tazuna.Ir
