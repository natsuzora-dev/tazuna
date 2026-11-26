import Tazuna.Ir.Builtin

/-! The elaborated IR: terms indexed by their type, so an ill-typed program cannot be represented. Elaboration
(`Tazuna.Ir.Elab`) is the only producer; it resolves names, labels and Gleam's surface syntax away. -/

namespace Tazuna.Ir

/-- Where a program writes a kept function: the module, the line and column in its source, and the index of the
global that holds it. Positions alone repeat across modules, and a generic function's repeat in each of its
instances, each a global of its own. -/
structure SiteId where
  module : String
  line : Nat
  col : Nat
  index : Nat
deriving DecidableEq, Repr

/-- A variable of type `t` in the context `Γ`, the innermost binding first. -/
inductive Var : List Ty → Ty → Type
  | here {Γ t} : Var (t :: Γ) t
  | there {Γ t u} : Var Γ t → Var (u :: Γ) t

/-- The variable at position `i` from the innermost, if it has type `t`. -/
def Var.at? : (Γ : List Ty) → Nat → (t : Ty) → Option (Var Γ t)
  | [], _, _ => none
  | u :: _, 0, t => (Ty.same u t).map fun ⟨h⟩ => h ▸ .here
  | _ :: Γ, i + 1, t => (Var.at? Γ i t).map .there

/-- The variable's position from the innermost. -/
def Var.idx : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

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
  | str (s : Str) : Pat .str []
  | tuple {ts Δ} (ps : Pats ts Δ) : Pat (.tuple ts) Δ
  | ctor {i args vs Δ} (v : Fin vs.length) (ps : Pats (vs.get v) Δ) : Pat (.adt i args vs) Δ
  /-- `p as name`: the name binds after the variables of `p`. -/
  | as {t Δ} (p : Pat t Δ) : Pat t (Δ ++ [t])
inductive Pats : List Ty → List Ty → Type
  | nil : Pats [] []
  | cons {t ts Δ Δ'} (p : Pat t Δ) (ps : Pats ts Δ') : Pats (t :: ts) (Δ ++ Δ')
end


/-! Exhaustiveness. A case is checked when it is loaded, so evaluation never meets a value no clause matches. The check
works on the shapes of the unguarded clauses' patterns: specializing a pattern matrix by each variant, as Gleam's own
check does. A literal never counts as covering anything, since Int and String have no last value. -/

inductive Shape where
  | any
  | lit
  /-- Variant `k` of an ADT, or `0` for a tuple, with the shapes of its fields. -/
  | ctor (k : Nat) (args : List Shape)
deriving Inhabited

mutual
def Pat.shape {t : Ty} {Δ : List Ty} : Pat t Δ → Shape
  | .wild | .bind => .any
  | .int _ | .str _ => .lit
  | .tuple ps => .ctor 0 (Pats.shapes ps)
  | .ctor v ps => .ctor v.val (Pats.shapes ps)
  | .as p => Pat.shape p
def Pats.shapes {ts : List Ty} {Δ : List Ty} : Pats ts Δ → List Shape
  | .nil => []
  | .cons p ps => Pat.shape p :: Pats.shapes ps
end

namespace Shape

/-- The rows that can match variant `k` (of `arity` fields) in the first column, with that column replaced by the
variant's fields. -/
def specialize (k arity : Nat) : List (List Shape) → List (List Shape)
  | [] => []
  | (.any :: rest) :: rows => (List.replicate arity .any ++ rest) :: specialize k arity rows
  | (.ctor j args :: rest) :: rows =>
    if j = k ∧ args.length = arity then (args ++ rest) :: specialize k arity rows else specialize k arity rows
  | _ :: rows => specialize k arity rows

/-- The rows whose first column matches anything, without that column. -/
def dflt : List (List Shape) → List (List Shape)
  | [] => []
  | (.any :: rest) :: rows => rest :: dflt rows
  | _ :: rows => dflt rows

/-- Whether `c` holds of the matrix specialized by each variant `k`, `k + 1`, ... of `vs`. -/
def eachVariant (c : List (List Shape) → List Ty → Bool) (rows : List (List Shape)) (ts : List Ty) (k : Nat) :
    List (List Ty) → Bool
  | [] => true
  | fs :: vs => c (specialize k fs.length rows) (fs ++ ts) && eachVariant c rows ts (k + 1) vs

/-- Whether every list of values of the types `ts` matches some row. `fuel` bounds the steps; running out answers
false, which refuses a case rather than accepting one. -/
def covers : (fuel : Nat) → List (List Shape) → List Ty → Bool
  | _, rows, [] => rows.any (·.isEmpty)
  | 0, _, _ :: _ => false
  | n + 1, rows, .adt _ _ vs :: ts => eachVariant (covers n) rows ts 0 vs
  | n + 1, rows, .tuple us :: ts => covers n (specialize 0 us.length rows) (us ++ ts)
  | n + 1, rows, _ :: ts => covers n (dflt rows) ts

end Shape

mutual
/-- The number of columns the exhaustiveness check can split a type into; fuel that always suffices. -/
def Ty.size : Ty → Nat
  | .tuple ts => 1 + Ty.sizes ts
  | .adt _ _ vs => 1 + Ty.sizess vs
  | _ => 1
def Ty.sizes : List Ty → Nat
  | [] => 0
  | t :: ts => Ty.size t + Ty.sizes ts
def Ty.sizess : List (List Ty) → Nat
  | [] => 0
  | ts :: vs => Ty.sizes ts + Ty.sizess vs
end

/-- Clauses whose unguarded patterns have the shapes `sh` cover every value of `t`. -/
def Exhaustive (t : Ty) (sh : List Shape) : Prop := ∃ fuel, Shape.covers fuel (sh.map fun s => [s]) [t] = true

/-- Decides `Exhaustive` with fuel that suffices. -/
def exhaustive? (t : Ty) (sh : List Shape) : Option (PLift (Exhaustive t sh)) :=
  if h : Shape.covers (t.size + 1) (sh.map fun s => [s]) [t] = true then some ⟨⟨_, h⟩⟩ else none

mutual
/-- A term of type `t` over the globals `G` (earlier definitions only, so references are acyclic by construction) and
the locals `Γ`. Calls are positional: elaboration has placed every labelled argument. -/
inductive Expr (G : List Ty) : List Ty → Ty → Type
  | int {Γ} (n : Int) : Expr G Γ .int
  | str {Γ} (s : Str) : Expr G Γ .str
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
  | case {Γ t r sh} (e : Expr G Γ t) (cs : Clauses G Γ t r sh) (hc : Exhaustive t sh) : Expr G Γ r
  | list {Γ t} (items : Items G Γ t) : Expr G Γ (.list t)
  | tuple {Γ ts} (es : Exprs G Γ ts) : Expr G Γ (.tuple ts)
  | bin {Γ a b c} (op : BinOp a b c) (l : Expr G Γ a) (r : Expr G Γ b) : Expr G Γ c
  | not {Γ} (e : Expr G Γ .bool) : Expr G Γ .bool
  | neg {Γ} (e : Expr G Γ .int) : Expr G Γ .int
  /-- A built-in at the type arguments `args`, which meet its demands. -/
  | prim {Γ} (p : Prim) (args : List Ty) (h : p.ok args = true) : Expr G Γ (p.ty.inst args)
  /-- A function a structure value keeps: its source `body` over the values `env` it captures, all data, so the
  function's code is `body`'s encoding. Elaboration closes each function a structure built-in keeps over the
  variables it uses, and names it by `site`, where it is written. -/
  | close {Γ Γ' t} (site : SiteId) (env : Exprs G Γ Γ') (hΓ : (Ty.tuple Γ').isData = true) (ht : t.isData = true)
      (body : Expr G Γ' t) : Expr G Γ (.dsl .closure [t])
  /-- A function a structure value keeps that takes data and returns effects (a machine's `effect`, a reaction's
  `react`): its source `body` over the values `env` it captures, named by `site` as `close` names one. -/
  | closeEffect {Γ Γ' ps r} (site : SiteId) (env : Exprs G Γ Γ') (hΓ : (Ty.tuple Γ').isData = true)
      (hps : (Ty.tuple ps).isData = true) (body : Expr G Γ' (.fn ps r)) : Expr G Γ (.dsl .effectClosure [.fn ps r])
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
/-- Clauses in order; the first whose pattern matches and whose guard holds is taken. The last index lists the shapes
of the unguarded patterns, which the exhaustiveness check reads. -/
inductive Clauses (G : List Ty) : List Ty → Ty → Ty → List Shape → Type
  | nil {Γ t r} : Clauses G Γ t r []
  | cons {Γ t r sh} {Δ : List Ty} (p : Pat t Δ) (body : Expr G (Δ ++ Γ) r) (rest : Clauses G Γ t r sh) :
      Clauses G Γ t r (p.shape :: sh)
  | guarded {Γ t r sh} {Δ : List Ty} (p : Pat t Δ) (guard : Expr G (Δ ++ Γ) .bool) (body : Expr G (Δ ++ Γ) r)
      (rest : Clauses G Γ t r sh) : Clauses G Γ t r sh
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
