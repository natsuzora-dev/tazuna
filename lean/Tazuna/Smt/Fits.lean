import Tazuna.Semantics.Eval

/-! Whether an evaluation stays within slot counts: the semantic side of a code's condition. `S` gives each collection
type its slot count. Evaluating an expression fits when every list literal and every bag or table a built-in builds
has at most its type's slot count of items, counted only where `eval` evaluates: the clause a case takes, the guard
of a clause whose pattern matches, `use`'s continuation only past a holding `require` or a found `ref`, a function's
body at each argument it is applied to. A value of a function type carries, for each argument, whether its
application fits and what its result carries (`FT`); data carries nothing. `encode_exact` proves a code's condition
holds exactly when its evaluation fits. -/

namespace Tazuna.Smt

open Tazuna.Ir

mutual
/-- What a value of a type carries about fitting: for a function, at each argument and what the arguments carry,
whether its application fits and what its result carries; nothing for data. -/
def FT : Ty → Type
  | .fn ps r => Ty.dens ps → FTs ps → Prop × FT r
  | .dsl _ _ | .list _ | .int | .str | .tuple _ | .adt .. | .param _ | .bag _ | .table .. | .date | .id => Unit
def FTs : List Ty → Type
  | [] => Unit
  | t :: ts => FT t × FTs ts
end

mutual
/-- What a function that always fits carries. -/
def FT.dflt : (t : Ty) → FT t
  | .fn _ r => fun _ _ => (True, FT.dflt r)
  | .dsl _ _ | .list _ | .int | .str | .tuple _ | .adt .. | .param _ | .bag _ | .table .. | .date | .id => ()
def FTs.dflt : (ts : List Ty) → FTs ts
  | [] => ()
  | t :: ts => (FT.dflt t, FTs.dflt ts)
end

def FTs.append : {a b : List Ty} → FTs a → FTs b → FTs (a ++ b)
  | [], _, (), ys => ys
  | _ :: _, _, (x, xs), ys => (x, FTs.append xs ys)

def _root_.Tazuna.Ir.Var.ft : {Γ : List Ty} → {t : Ty} → Var Γ t → FTs Γ → FT t
  | _ :: _, _, .here, (x, _) => x
  | _ :: _, _, .there v, (_, xs) => v.ft xs

/-- Whether each global's evaluation fits, and what its value carries. -/
def GFits : List Ty → Type
  | [] => Unit
  | t :: ts => (Prop × FT t) × GFits ts

def _root_.Tazuna.Ir.Var.gfit : {G : List Ty} → {t : Ty} → Var G t → GFits G → Prop × FT t
  | _ :: _, _, .here, (x, _) => x
  | _ :: _, _, .there v, (_, xs) => v.gfit xs

/-- What a pattern's variables carry: a variable bound to the whole value carries what the value does. The fields of
tuples and constructors are data (a code with a function field has no term). -/
def _root_.Tazuna.Ir.Pat.fts {t : Ty} : {Δ : List Ty} → Pat t Δ → FT t → FTs Δ
  | _, .bind, x => (x, ())
  | _, .as p, x => FTs.append (p.fts x) (x, ())
  | Δ, _, _ => FTs.dflt Δ

/-- Each item satisfies `P`. -/
def allFit {α : Type} (xs : List α) (P : α → Prop) : Prop := ∀ x ∈ xs, P x

/-- Each table `table.from_list` builds on its way, inserting the pairs in turn into `t`, has at most `n` entries. -/
def insertsFit {k v : Sem} (n : Nat) : List (k.1 × v.1 × Unit) → (Sem.table k v).1 → Prop
  | [], _ => True
  | (key, val, ()) :: ps, t => (Builtin.tableInsert key val t).1.length ≤ n ∧ insertsFit n ps (Builtin.tableInsert key val t)

section
variable (S : Ty → Nat)

/-- What each built-in carries: a built-in that builds a bag or table fits when the result has at most its type's
slot count of items, one that applies a function fits when each application does, and `require` and `ref` fit when
the continuation they take does. -/
def _root_.Tazuna.Ir.Prim.fits : (p : Prim) → (args : List Ty) → p.ok args = true → FT (p.ty.inst args)
  | .bagFromList, args, _ => fun (xs, ()) _ => (xs.length ≤ S (.bag ((Ty.param 0).inst args)), ())
  | .bagInsert, args, _ => fun (xs, _, ()) _ => (xs.length + 1 ≤ S (.bag ((Ty.param 0).inst args)), ())
  | .bagFilter, _, _ | .bagCount, _, _ | .bagSum, _, _ | .bagAny, _, _ | .bagAll, _, _ | .bagMinBy, _, _
  | .bagMaxBy, _, _ => fun (xs, _, ()) (_, ff, ()) => (allFit xs (fun x => (ff (x, ()) (FT.dflt _, ())).1), ())
  | .bagMap, args, _ => fun (xs, _, ()) (_, ff, ()) =>
    (allFit xs (fun x => (ff (x, ()) (FT.dflt _, ())).1) ∧ xs.length ≤ S (.bag ((Ty.param 1).inst args)), ())
  | .tableFilter, _, _ | .tableCount, _, _ | .tableAny, _, _ | .tableAll, _, _ => fun (t, _, ()) (_, ff, ()) =>
    (allFit t.1 (fun e => (ff (e.1, e.2, ()) (FT.dflt _, FT.dflt _, ())).1), ())
  | .tableMap, args, _ => fun (t, _, ()) (_, ff, ()) =>
    (allFit t.1 (fun e => (ff (e.1, e.2, ()) (FT.dflt _, FT.dflt _, ())).1) ∧
      t.1.length ≤ S (.table ((Ty.param 0).inst args) ((Ty.param 2).inst args)), ())
  | .tableKeys, args, _ => fun (t, ()) _ => (t.1.length ≤ S (.bag ((Ty.param 0).inst args)), ())
  | .tableValues, args, _ => fun (t, ()) _ => (t.1.length ≤ S (.bag ((Ty.param 1).inst args)), ())
  | .tableInsert, args, _ => fun (t, k, v, ()) _ =>
    ((Builtin.tableInsert k v t).1.length ≤ S (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args)), ())
  | .tableFromList, args, _ => fun (pairs, ()) _ =>
    (insertsFit (S (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))) pairs Builtin.tableEmpty, ())
  | .require, _, _ => fun (holds, _, _, ()) (_, _, fn, ()) => (if Ty.toBool holds then (fn () ()).1 else True, ())
  | .tableLookup, args, _ => fun (t, k, _, _, ()) (_, _, _, fn, ()) =>
    (match lookupBy (Ty.deq (args[0]?.getD (.param 0))) k t.1 with
      | .some v => (fn (v, ()) (FT.dflt _, ())).1
      | .none => True, ())
  | p, args, _ => FT.dflt (p.ty.inst args)

variable {G : List Ty} (D : Defs G) (g : Ty.dens G) (gf : GFits G)

mutual
/-- Whether evaluating an expression fits, and what its value carries, where its variables carry `φ`. -/
def Expr.fits {Γ : List Ty} {t : Ty} : Expr G Γ t → Ty.dens Γ → FTs Γ → Prop × FT t
  | .int _, _, _ | .str _, _, _ => (True, FT.dflt _)
  | .var v, _, φ => (True, v.ft φ)
  | .global v, _, _ => v.gfit gf
  | .ctor _ es, ρ, φ | .tuple es, ρ, φ | .close _ es _ _ _, ρ, φ => ((Exprs.fits es ρ φ).1, FT.dflt _)
  | .field _ _ _ e, ρ, φ | .index e _, ρ, φ | .not e, ρ, φ | .neg e, ρ, φ => ((Expr.fits e ρ φ).1, FT.dflt _)
  | .update e p, ρ, φ => ((Expr.fits e ρ φ).1 ∧ Patch.fits p ρ φ, FT.dflt _)
  | .call f args, ρ, φ =>
    let r := (Expr.fits f ρ φ).2 (Exprs.eval D g args ρ) (Exprs.fits args ρ φ).2
    ((Expr.fits f ρ φ).1 ∧ (Exprs.fits args ρ φ).1 ∧ r.1, r.2)
  | .lam body, ρ, φ => (True, fun xs φs => Expr.fits body (Dens.append xs ρ) (FTs.append φs φ))
  | .let_ e body, ρ, φ =>
    let b := Expr.fits body (Expr.eval D g e ρ, ρ) ((Expr.fits e ρ φ).2, φ)
    ((Expr.fits e ρ φ).1 ∧ b.1, b.2)
  | .case e cs hc, ρ, φ =>
    let x := Expr.eval D g e ρ
    let b := Clauses.fits cs ρ φ x (Expr.fits e ρ φ).2 (hc.sound x)
    ((Expr.fits e ρ φ).1 ∧ b.1, b.2)
  | @Expr.list _ _ u items, ρ, φ => (Items.fits items ρ φ ∧ (Items.eval D g items ρ).length ≤ S (.list u), ())
  | .bin _ l r, ρ, φ => ((Expr.fits l ρ φ).1 ∧ (Expr.fits r ρ φ).1, FT.dflt _)
  | .prim p args h, _, _ => (True, p.fits S args h)
  | .closeEffect .., _, _ => (True, FT.dflt _)
def Exprs.fits {Γ : List Ty} {ts : List Ty} : Exprs G Γ ts → Ty.dens Γ → FTs Γ → Prop × FTs ts
  | .nil, _, _ => (True, ())
  | .cons e es, ρ, φ => ((Expr.fits e ρ φ).1 ∧ (Exprs.fits es ρ φ).1, ((Expr.fits e ρ φ).2, (Exprs.fits es ρ φ).2))
def Items.fits {Γ : List Ty} {t : Ty} : Items G Γ t → Ty.dens Γ → FTs Γ → Prop
  | .nil, _, _ => True
  | .cons e es, ρ, φ => (Expr.fits e ρ φ).1 ∧ Items.fits es ρ φ
def Patch.fits {Γ : List Ty} {ts : List Ty} : Patch G Γ ts → Ty.dens Γ → FTs Γ → Prop
  | .nil, _, _ => True
  | .keep rest, ρ, φ => Patch.fits rest ρ φ
  | .set e rest, ρ, φ => (Expr.fits e ρ φ).1 ∧ Patch.fits rest ρ φ
/-- The clause `eval` takes: its guard's fit where its pattern matches, then its body's, or the rest's. -/
def Clauses.fits {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → Ty.dens Γ → FTs Γ → (x : t.den) →
    FT t → (∃ s ∈ sh, Shape.Matches t s x) → Prop × FT r
  | .nil, _, _, _, _, h => False.elim (by simp at h)
  | .cons p body rest, ρ, φ, x, fx, h =>
    match hm : p.match x with
    | some δ => Expr.fits body (Dens.append δ ρ) (FTs.append (p.fts fx) φ)
    | none => Clauses.fits rest ρ φ x fx (Clauses.skip hm h)
  | .guarded p guard body rest, ρ, φ, x, fx, h =>
    match p.match x with
    | some δ =>
      let pg := (Expr.fits guard (Dens.append δ ρ) (FTs.append (p.fts fx) φ)).1
      if Ty.toBool (Expr.eval D g guard (Dens.append δ ρ)) then
        let b := Expr.fits body (Dens.append δ ρ) (FTs.append (p.fts fx) φ)
        (pg ∧ b.1, b.2)
      else
        let b := Clauses.fits rest ρ φ x fx h
        (pg ∧ b.1, b.2)
    | none => Clauses.fits rest ρ φ x fx h
end

end

/-- Whether each global's evaluation fits, each from the ones before it. -/
def _root_.Tazuna.Ir.Defs.fits (S : Ty → Nat) : {G : List Ty} → Defs G → GFits G
  | [], .nil => ()
  | _ :: _, .snoc defs _ body => let gf := defs.fits S; (Expr.fits S defs defs.eval gf body () (), gf)

/-- Whether a kept function's source evaluation fits, and what its value carries; it captured data. -/
def _root_.Tazuna.Ir.Fun.fits (S : Ty → Nat) {t : Ty} (f : Fun t) : Prop × FT t :=
  Expr.fits S f.defs f.defs.eval (f.defs.fits S) f.body (Ty.up _ f.hΓ f.env) (FTs.dflt _)

/-- The same for a kept function that returns effects. -/
def _root_.Tazuna.Ir.EffectFun.fits (S : Ty → Nat) {ps : List Ty} {r : Ty} (f : EffectFun ps r) :
    Prop × FT (.fn ps r) :=
  Expr.fits S f.defs f.defs.eval (f.defs.fits S) f.body (Ty.up _ f.hΓ f.env) (FTs.dflt _)

end Tazuna.Smt
