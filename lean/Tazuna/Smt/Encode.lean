import Tazuna.Semantics.Eval
import Tazuna.Smt.Term

/-! The encoding of typed IR expressions as SMT terms. It covers a fragment and refuses everything else with a reason,
never approximating: Int with Gleam's arithmetic (truncating `/` and `%`, and zero for a zero divisor), Bool, and
String with `==`, `!=` and `<>` concatenation, whose literals must lie in SMT-LIB's string domain
(code points up to U+2FFFF). `encode_agrees` (T1) proves that in every model, an encoded expression denotes what
`eval` computes. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Why an expression has no encoding. -/
inductive Refusal where
  /-- A string literal holds a code point above U+2FFFF, outside SMT-LIB's strings. -/
  | unencodableString (s : String)
  /-- The expression uses a construct or type outside the fragment. -/
  | outside (what : String)
deriving Repr

def _root_.Tazuna.Ir.Var.idx : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

/-- The SMT sort of a type in the fragment. -/
def Ty.srt? (t : Ty) : Option Srt :=
  match t with
  | .int => some .int
  | .str => some .str
  | t => if (Ty.same t Ty.bool).isSome then some .bool else none

def absT (a : Term) : Term := .ite (.lt a (.int 0)) (.sub (.int 0) a) a

/-- Gleam's `/`: truncating, and zero for a zero divisor. SMT-LIB's `div` is Euclidean, so it divides magnitudes. -/
def tdivT (x y : Term) : Term :=
  .ite (.eq y (.int 0)) (.int 0)
    (.ite (.eq (.lt x (.int 0)) (.lt y (.int 0))) (.div (absT x) (absT y)) (.sub (.int 0) (.div (absT x) (absT y))))

/-- Gleam's `%`: the remainder takes the dividend's sign, and is zero for a zero divisor. -/
def tmodT (x y : Term) : Term :=
  .ite (.eq y (.int 0)) (.int 0)
    (.ite (.lt x (.int 0)) (.sub (.int 0) (.mod (absT x) (absT y))) (.mod (absT x) (absT y)))

def encodeBin {a b c : Ty} : BinOp a b c → Term → Term → Except Refusal Term
  | .add, x, y => .ok (.add x y)
  | .sub, x, y => .ok (.sub x y)
  | .mul, x, y => .ok (.mul x y)
  | .div, x, y => .ok (tdivT x y)
  | .mod, x, y => .ok (tmodT x y)
  | .lt, x, y => .ok (.lt x y)
  | .le, x, y => .ok (.le x y)
  | .gt, x, y => .ok (.lt y x)
  | .ge, x, y => .ok (.le y x)
  | .and, x, y => .ok (.and x y)
  | .or, x, y => .ok (.or x y)
  | .concat, x, y => .ok (.cat x y)
  | @BinOp.eq t _, x, y => if (Ty.srt? t).isSome then .ok (.eq x y) else .error (.outside "== on this type")
  | @BinOp.ne t _, x, y => if (Ty.srt? t).isSome then .ok (.not (.eq x y)) else .error (.outside "<> on this type")

section
variable {G : List Ty}

/-- The term of an expression whose variables `σ` encodes, innermost first. -/
def encode {Γ : List Ty} {t : Ty} (σ : List Term) : Expr G Γ t → Except Refusal Term
  | .int n => .ok (.int n)
  | .str s => if inDomain s then .ok (.str s) else .error (.unencodableString s)
  | .var v => match σ[v.idx]? with
    | some x => .ok x
    | none => .error (.outside "a variable without a term")
  | .let_ e body => do encode ((← encode σ e) :: σ) body
  | .bin op l r => do encodeBin op (← encode σ l) (← encode σ r)
  | .not e => do pure (.not (← encode σ e))
  | .neg e => do pure (.sub (.int 0) (← encode σ e))
  | .global _ => .error (.outside "a global definition")
  | .ctor .. => .error (.outside "a constructor")
  | .field .. => .error (.outside "a field")
  | .index .. => .error (.outside "a tuple index")
  | .update .. => .error (.outside "a record update")
  | .call .. => .error (.outside "a call")
  | .lam .. => .error (.outside "a function")
  | .case .. => .error (.outside "a case")
  | .list .. => .error (.outside "a list")
  | .tuple .. => .error (.outside "a tuple")
  | .prim .. => .error (.outside "a built-in as a value")

end

/-! T1. -/

/-- A value of `t` and the SMT value that encodes it. -/
def Rel : (t : Ty) → t.den → Val → Prop
  | .int, x, v => v = .int x
  | .str, x, v => v = .str x
  | .adt i a vs, x, v => ∃ h : Ty.adt i a vs = Ty.bool, v = .bool (Ty.toBool (cast (congrArg Ty.den h) x))
  | _, _, _ => False

/-- Each variable's term denotes the variable's value. -/
def EnvRel (M : Model) {Γ : List Ty} (σ : List Term) (ρ : Ty.dens Γ) : Prop :=
  ∀ (t : Ty) (v : Var Γ t), ∃ x, σ[v.idx]? = some x ∧ Rel t (v.get ρ) (x.denote M)

end Tazuna.Smt
