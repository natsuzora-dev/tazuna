import Tazuna.Ir.Core

/-! What a spec's values are. A type means a Lean type, by recursion on its structure: functions are Lean functions,
an ADT value is one variant with its fields, and a type variable of a generic body stands for `Unit`, which a
parametric body never inspects. -/

namespace Tazuna.Ir

/-- A key-value list whose keys differ pairwise by `f`, checked in both directions. -/
def KeysUnique {κ ν : Type} (f : κ → κ → Bool) (xs : List (κ × ν)) : Prop :=
  xs.Pairwise fun a b => f a.1 b.1 = false ∧ f b.1 a.1 = false

/-- How often a value occurs, by the equality `f`. -/
def countBy {α : Type} (f : α → α → Bool) (x : α) (xs : List α) : Nat := (xs.filter (f x)).length

/-- Multiset equality by `f`: as many items, each occurring as often in both. -/
def bagBeq {α : Type} (f : α → α → Bool) (xs ys : List α) : Bool :=
  xs.length == ys.length && xs.all fun x => countBy f x xs == countBy f x ys

def lookupBy {κ ν : Type} (f : κ → κ → Bool) (k : κ) : List (κ × ν) → Option ν
  | [] => none
  | (k', v) :: rest => if f k k' then some v else lookupBy f k rest

/-- Map equality: the same number of keys, and each key of one has an equal value in the other. -/
def tableBeq {κ ν : Type} (fk : κ → κ → Bool) (fv : ν → ν → Bool) (xs ys : List (κ × ν)) : Bool :=
  xs.length == ys.length && xs.all fun (k, v) => match lookupBy fk k ys with
    | some w => fv v w
    | none => false

def listBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => f x y && listBeq f xs ys
  | _, _ => false

/-- A carrier type with Gleam's `==` on it. -/
abbrev Sem := (α : Type) × (α → α → Bool)

def Sem.pair (a b : Sem) : Sem := ⟨a.1 × b.1, fun x y => a.2 x.1 y.1 && b.2 x.2 y.2⟩

def Sem.sum (a b : Sem) : Sem := ⟨a.1 ⊕ b.1, fun
  | .inl x, .inl y => a.2 x y
  | .inr x, .inr y => b.2 x y
  | _, _ => false⟩

def Sem.table (k v : Sem) : Sem :=
  ⟨{ xs : List (k.1 × v.1) // KeysUnique k.2 xs }, fun x y => tableBeq k.2 v.2 x.1 y.1⟩

mutual
/-- What a type means and what `==` means on it, in one recursion: a table's keys are unique by the equality of its
key type, so the carrier of a table needs that equality. -/
def Ty.sem : Ty → Sem
  | .int => ⟨Int, fun x y => @BEq.beq Int _ x y⟩
  | .str => ⟨String, fun x y => @BEq.beq String _ x y⟩
  | .list t => ⟨List (Ty.sem t).1, listBeq (Ty.sem t).2⟩
  | .tuple ts => Ty.sems ts
  -- Functions never meet `==`, since `==` needs a comparable type.
  | .fn ps r => ⟨(Ty.sems ps).1 → (Ty.sem r).1, fun _ _ => false⟩
  | .adt _ _ vs => Ty.semAlts vs
  | .param _ => ⟨Unit, fun _ _ => true⟩
  -- Order carries no meaning: every operation on bags gives equal results for reordered lists.
  | .bag t => ⟨List (Ty.sem t).1, bagBeq (Ty.sem t).2⟩
  -- Each key at most once by construction, so equality of tables is equality of finite maps.
  | .table k v => Sem.table (Ty.sem k) (Ty.sem v)
  -- Days from an arbitrary origin.
  | .date => ⟨Int, fun x y => @BEq.beq Int _ x y⟩
  | .id => ⟨Nat, fun x y => @BEq.beq Nat _ x y⟩
/-- Values of the types `ts`, in order. -/
def Ty.sems : List Ty → Sem
  | [] => ⟨Unit, fun _ _ => true⟩
  | t :: ts => Sem.pair (Ty.sem t) (Ty.sems ts)
/-- One variant's fields: the first variant's on the left. -/
def Ty.semAlts : List (List Ty) → Sem
  | [] => ⟨Empty, fun _ _ => false⟩
  | fs :: vs => Sem.sum (Ty.sems fs) (Ty.semAlts vs)
end

abbrev Ty.den (t : Ty) : Type := t.sem.1
abbrev Ty.dens (ts : List Ty) : Type := (Ty.sems ts).1
abbrev Ty.alts (vs : List (List Ty)) : Type := (Ty.semAlts vs).1
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


/-- `==` on bags ignores order: reordering a bag gives an equal bag. -/
theorem Ty.deq_bag_perm (t : Ty) {xs ys : List t.den} (h : xs.Perm ys) : Ty.deq (.bag t) xs ys = true := by
  show bagBeq (Ty.deq t) xs ys = true
  simp only [bagBeq, countBy, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  exact ⟨h.length_eq, fun x _ => (h.filter _).length_eq⟩

/-- `==` on Int and String is Lean's equality. -/
theorem Ty.deq_int (a b : Int) : Ty.deq .int a b = true ↔ a = b := by simp [Ty.deq, Ty.sem]
theorem Ty.deq_str (a b : String) : Ty.deq .str a b = true ↔ a = b := by simp [Ty.deq, Ty.sem]

end Tazuna.Ir
