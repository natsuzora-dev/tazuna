import Tazuna.Ir.Core

/-! What a spec's values are. A type means a Lean type, by recursion on its structure: functions are Lean functions,
an ADT value is one variant with its fields, and a type variable of a generic body stands for `Unit`, which a
parametric body never inspects. -/

namespace Tazuna.Ir

mutual
def Ty.den : Ty → Type
  | .int => Int
  | .str => String
  | .list t => List t.den
  | .tuple ts => Ty.dens ts
  | .fn ps r => Ty.dens ps → r.den
  | .adt _ _ vs => Ty.alts vs
  | .param _ => Unit
/-- Values of the types `ts`, in order. -/
def Ty.dens : List Ty → Type
  | [] => Unit
  | t :: ts => t.den × Ty.dens ts
/-- One variant's fields: the first variant's on the left. -/
def Ty.alts : List (List Ty) → Type
  | [] => Empty
  | fs :: vs => Ty.dens fs ⊕ Ty.alts vs
end

def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Ty.dens Γ → t.den
  | _ :: _, _, .here, (x, _) => x
  | _ :: _, _, .there v, (_, xs) => v.get xs

namespace Dens

def append : {a b : List Ty} → Ty.dens a → Ty.dens b → Ty.dens (a ++ b)
  | [], _, (), ys => ys
  | _ :: _, _, (x, xs), ys => (x, append xs ys)

def get : {ts : List Ty} → Ty.dens ts → (k : Fin ts.length) → (ts.get k).den
  | _ :: _, (x, _), ⟨0, _⟩ => x
  | _ :: _, (_, xs), ⟨k + 1, h⟩ => get xs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The value at index `k`, whose type the proof names. -/
def field : {ts : List Ty} → {t : Ty} → Ty.dens ts → (k : Nat) → ts[k]? = some t → t.den
  | [], _, _, _, h => nomatch h
  | _ :: _, _, (x, _), 0, h => by simp at h; exact h ▸ x
  | _ :: _, _, (_, xs), k + 1, h => field xs k (by simpa using h)

end Dens

namespace Alts

def inj : {vs : List (List Ty)} → (v : Fin vs.length) → Ty.dens (vs.get v) → Ty.alts vs
  | _ :: _, ⟨0, _⟩, x => .inl x
  | _ :: _, ⟨k + 1, h⟩, x => .inr (inj ⟨k, Nat.lt_of_succ_lt_succ h⟩ x)

/-- The variant a value is, with its fields. -/
def view : {vs : List (List Ty)} → Ty.alts vs → (v : Fin vs.length) × Ty.dens (vs.get v)
  | [], e => nomatch e
  | _ :: _, .inl x => ⟨⟨0, by simp⟩, x⟩
  | _ :: _, .inr y =>
    let ⟨⟨k, h⟩, x⟩ := view y
    ⟨⟨k + 1, by simp; omega⟩, x⟩

/-- The fields, when the value is variant `v`. -/
def proj : {vs : List (List Ty)} → Ty.alts vs → (v : Fin vs.length) → Option (Ty.dens (vs.get v))
  | _ :: _, .inl x, ⟨0, _⟩ => some x
  | _ :: _, .inr y, ⟨k + 1, h⟩ => proj y ⟨k, Nat.lt_of_succ_lt_succ h⟩
  | _ :: _, _, _ => none

def only {fs : List Ty} : Ty.alts [fs] → Ty.dens fs
  | .inl x => x

theorem inj_view : {vs : List (List Ty)} → (x : Ty.alts vs) → inj (view x).1 (view x).2 = x
  | [], e => nomatch e
  | _ :: _, .inl _ => rfl
  | _ :: _, .inr y => by
    have := inj_view y
    simp only [view, inj]
    exact congrArg Sum.inr this

end Alts

def Ty.ofBool : Bool → Ty.bool.den
  | true => .inl ()
  | false => .inr (.inl ())

def Ty.toBool : Ty.bool.den → Bool
  | .inl _ => true
  | .inr _ => false

def listBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => f x y && listBeq f xs ys
  | _, _ => false

mutual
/-- Gleam's `==`: structural. Functions never meet it, since `==` needs a comparable type. -/
def Ty.deq : (t : Ty) → t.den → t.den → Bool
  | .int, x, y => @BEq.beq Int _ x y
  | .str, x, y => @BEq.beq String _ x y
  | .list t, x, y => listBeq (Ty.deq t) x y
  | .tuple ts, x, y => Ty.deqs ts x y
  | .fn .., _, _ => false
  | .adt _ _ vs, x, y => Ty.deqAlts vs x y
  | .param _, _, _ => true
def Ty.deqs : (ts : List Ty) → Ty.dens ts → Ty.dens ts → Bool
  | [], _, _ => true
  | t :: ts, (x, xs), (y, ys) => Ty.deq t x y && Ty.deqs ts xs ys
def Ty.deqAlts : (vs : List (List Ty)) → Ty.alts vs → Ty.alts vs → Bool
  | fs :: _, .inl x, .inl y => Ty.deqs fs x y
  | _ :: vs, .inr x, .inr y => Ty.deqAlts vs x y
  | _ :: _, _, _ => false
end

end Tazuna.Ir
