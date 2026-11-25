import Tazuna.Semantics.Structure

/-! What a spec's values are. A type means a Lean type, by recursion on its structure: functions are Lean functions,
an ADT value is one variant with its fields, and a type variable of a generic body stands for `Unit`, which a
parametric body never inspects. -/

namespace Tazuna.Ir

abbrev Ty.sem (t : Ty) : Sem := Ty.semWith Dsl.val t
abbrev Ty.den (t : Ty) : Type := t.sem.1
abbrev Ty.dens (ts : List Ty) : Type := (Ty.semsWith Dsl.val ts).1
abbrev Ty.alts (vs : List (List Ty)) : Type := (Ty.semAltsWith Dsl.val vs).1
/-- Gleam's `==`: structural. -/
abbrev Ty.deq (t : Ty) : t.den → t.den → Bool := t.sem.2

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


/-- Multiset equality reads neither list's order. -/
theorem bagBeq_perm {α : Type} (f : α → α → Bool) {xs xs' ys ys' : List α} (hx : xs.Perm xs') (hy : ys.Perm ys') :
    bagBeq f xs ys = bagBeq f xs' ys' := by
  simp only [bagBeq, countBy, hx.length_eq, hy.length_eq, hx.all_eq, fun z => (hx.filter (f z)).length_eq,
    fun z => (hy.filter (f z)).length_eq]

/-- `==` on bags ignores order: reordering a bag gives an equal bag. -/
theorem Ty.deq_bag_perm (t : Ty) {xs ys : List t.den} (h : xs.Perm ys) : Ty.deq (.bag t) xs ys = true := by
  show bagBeq (Ty.deq t) xs ys = true
  simp only [bagBeq, countBy, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  exact ⟨h.length_eq, fun x _ => (h.filter _).length_eq⟩

end Tazuna.Ir
