import Tazuna.Semantics.Builtin
import Tazuna.Semantics.Match

/-! Evaluation of the typed IR. It is total by construction: types are finite trees, globals see only earlier
globals, a function value is a Lean function, and every case carries the proof that some unguarded clause matches
each value. So `eval` needs neither fuel nor a failure value. -/

namespace Tazuna.Ir

private def intLt (a b : Int) : Bool := decide (a < b)
private def intLe (a b : Int) : Bool := decide (a ≤ b)

def BinOp.eval {a b c : Ty} : BinOp a b c → a.den → b.den → c.den
  | .add, x, y => @HAdd.hAdd Int Int Int _ x y
  | .sub, x, y => @HSub.hSub Int Int Int _ x y
  | .mul, x, y => @HMul.hMul Int Int Int _ x y
  | .div, x, y => Gleam.div x y
  | .mod, x, y => Gleam.mod x y
  | .lt, x, y => Ty.ofBool (intLt x y)
  | .le, x, y => Ty.ofBool (intLe x y)
  | .gt, x, y => Ty.ofBool (intLt y x)
  | .ge, x, y => Ty.ofBool (intLe y x)
  | .and, x, y => Ty.ofBool (Ty.toBool x && Ty.toBool y)
  | .or, x, y => Ty.ofBool (Ty.toBool x || Ty.toBool y)
  | .concat, x, y => @HAppend.hAppend String String String _ x y
  | @BinOp.eq t _, x, y => Ty.ofBool (t.deq x y)
  | @BinOp.ne t _, x, y => Ty.ofBool (!t.deq x y)

theorem Clauses.skip {t : Ty} {Δ : List Ty} {sh : List Shape} {p : Pat t Δ} {x : t.den} (hm : p.match x = none)
    (h : ∃ s ∈ p.shape :: sh, Shape.Matches t s x) : ∃ s ∈ sh, Shape.Matches t s x := by
  obtain ⟨s, hs, m⟩ := h
  cases hs with
  | head => have := Pat.match_of_matches p x m; simp [hm] at this
  | tail _ hs => exact ⟨s, hs, m⟩

section
variable {G : List Ty} (g : Ty.dens G)

mutual
def Expr.eval {Γ : List Ty} {t : Ty} : Expr G Γ t → Ty.dens Γ → t.den
  | .int n, _ => n
  | .str s, _ => s
  | .var v, ρ => v.get ρ
  | .global v, _ => v.get g
  | .ctor v es, ρ => Alts.inj v (Exprs.eval es ρ)
  | .field _ k hk e, ρ =>
    let ⟨v, fs⟩ := Alts.view (Expr.eval e ρ)
    Dens.field fs k (hk _ (List.get_mem _ v))
  | .index e k, ρ => Dens.get (Expr.eval e ρ) k
  | .update e p, ρ => Alts.inj ⟨0, by simp⟩ (Patch.eval p ρ (Alts.only (Expr.eval e ρ)))
  | .call f args, ρ => Expr.eval f ρ (Exprs.eval args ρ)
  | .lam body, ρ => fun xs => Expr.eval body (Dens.append xs ρ)
  | .let_ e body, ρ => Expr.eval body (Expr.eval e ρ, ρ)
  | .case e cs hc, ρ =>
    let x := Expr.eval e ρ
    Clauses.eval cs ρ x (hc.sound x)
  | .list items, ρ => Items.eval items ρ
  | .tuple es, ρ => Exprs.eval es ρ
  | .bin op l r, ρ => op.eval (Expr.eval l ρ) (Expr.eval r ρ)
  | .not e, ρ => Ty.ofBool (!Ty.toBool (Expr.eval e ρ))
  | .neg e, ρ => @Neg.neg Int _ (Expr.eval e ρ)
  | .prim p args h, _ => p.den args h
def Exprs.eval {Γ : List Ty} {ts : List Ty} : Exprs G Γ ts → Ty.dens Γ → Ty.dens ts
  | .nil, _ => ()
  | .cons e es, ρ => (Expr.eval e ρ, Exprs.eval es ρ)
def Items.eval {Γ : List Ty} {t : Ty} : Items G Γ t → Ty.dens Γ → List t.den
  | .nil, _ => []
  | .cons e es, ρ => Expr.eval e ρ :: Items.eval es ρ
def Patch.eval {Γ : List Ty} {ts : List Ty} : Patch G Γ ts → Ty.dens Γ → Ty.dens ts → Ty.dens ts
  | .nil, _, () => ()
  | .keep rest, ρ, (x, xs) => (x, Patch.eval rest ρ xs)
  | .set e rest, ρ, (_, xs) => (Expr.eval e ρ, Patch.eval rest ρ xs)
/-- The first clause whose pattern matches and whose guard holds. `h` says an unguarded clause matches, so the clauses
never run out. -/
def Clauses.eval {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → Ty.dens Γ → (x : t.den) →
    (∃ s ∈ sh, Shape.Matches t s x) → r.den
  | .nil, _, _, h => False.elim (by simp at h)
  | .cons p body rest, ρ, x, h =>
    match hm : p.match x with
    | some δ => Expr.eval body (Dens.append δ ρ)
    | none => Clauses.eval rest ρ x (Clauses.skip hm h)
  | .guarded p guard body rest, ρ, x, h =>
    match p.match x with
    | some δ =>
      if Ty.toBool (Expr.eval guard (Dens.append δ ρ)) then Expr.eval body (Dens.append δ ρ)
      else Clauses.eval rest ρ x h
    | none => Clauses.eval rest ρ x h
end

end

/-- Every global's value, each computed from the ones before it. -/
def Defs.eval : {G : List Ty} → Defs G → Ty.dens G
  | [], .nil => ()
  | _ :: _, .snoc defs _ body => let g := defs.eval; (body.eval g (), g)

/-- The value of a loaded program's root. -/
def Program.eval {rootTy : Ty} (p : Program rootTy) : rootTy.den := p.root.get p.defs.eval

end Tazuna.Ir
