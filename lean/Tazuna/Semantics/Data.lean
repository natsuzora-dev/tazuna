import Tazuna.Ir.Core

/-! What a type means, given what each structure type means. Data types mean the same at every level; structure
types hold values of data types, so their meaning (`Tazuna.Semantics.Value`) is built on the meaning of data types
here, which gives every structure type a placeholder. -/

namespace Tazuna.Ir

/-- A key-value list whose keys differ pairwise by `f`, checked in both directions. -/
def KeysUnique {κ ν : Type} (f : κ → κ → Bool) (xs : List (κ × ν)) : Prop :=
  xs.Pairwise fun a b => f a.1 b.1 = false ∧ f b.1 a.1 = false

instance {κ ν : Type} (f : κ → κ → Bool) (xs : List (κ × ν)) : Decidable (KeysUnique f xs) := by
  unfold KeysUnique; infer_instance

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

/-- An id: one a step made fresh, by the step's counter and the index the spec gave, or one from outside the service,
which a trace and a scenario know by its name. The two never meet, so no fresh id equals an outside one. -/
inductive IdV where
  | fresh (step : Nat) (index : Int)
  | named (name : String)
deriving DecidableEq, Repr, Inhabited

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
def Ty.semWith (D : Dsl → List Ty → Sem) : Ty → Sem
  | .int => ⟨Int, fun x y => @BEq.beq Int _ x y⟩
  | .str => ⟨String, fun x y => @BEq.beq String _ x y⟩
  | .list t => ⟨List (Ty.semWith D t).1, listBeq (Ty.semWith D t).2⟩
  | .tuple ts => Ty.semsWith D ts
  -- Functions never meet `==`, since `==` needs a comparable type.
  | .fn ps r => ⟨(Ty.semsWith D ps).1 → (Ty.semWith D r).1, fun _ _ => false⟩
  | .adt _ _ vs => Ty.semAltsWith D vs
  | .param _ => ⟨Unit, fun _ _ => true⟩
  -- Order carries no meaning: every operation on bags gives equal results for reordered lists.
  | .bag t => ⟨List (Ty.semWith D t).1, bagBeq (Ty.semWith D t).2⟩
  -- Each key at most once by construction, so equality of tables is equality of finite maps.
  | .table k v => Sem.table (Ty.semWith D k) (Ty.semWith D v)
  -- Days from an arbitrary origin.
  | .date => ⟨Int, fun x y => @BEq.beq Int _ x y⟩
  | .id => ⟨IdV, fun x y => decide (x = y)⟩
  | .dsl k args => D k args
/-- Values of the types `ts`, in order. -/
def Ty.semsWith (D : Dsl → List Ty → Sem) : List Ty → Sem
  | [] => ⟨Unit, fun _ _ => true⟩
  | t :: ts => Sem.pair (Ty.semWith D t) (Ty.semsWith D ts)
/-- One variant's fields: the first variant's on the left. -/
def Ty.semAltsWith (D : Dsl → List Ty → Sem) : List (List Ty) → Sem
  | [] => ⟨Empty, fun _ _ => false⟩
  | fs :: vs => Sem.sum (Ty.semsWith D fs) (Ty.semAltsWith D vs)
end


/-- What structure types mean among data: nothing, except a fresh-id source, which is a counter. -/
def Dsl.base : Dsl → List Ty → Sem
  | .fresh, _ => ⟨Nat, fun x y => @BEq.beq Nat _ x y⟩
  | _, _ => ⟨Unit, fun _ _ => false⟩

/-- The meaning of a data type, where structure types hold their data. -/
abbrev Ty.den0 (t : Ty) : Type := (Ty.semWith Dsl.base t).1

section
variable {D : Dsl → List Ty → Sem}

mutual
theorem Ty.semWith_data (hD : ∀ a, D .fresh a = Dsl.base .fresh a) : (t : Ty) → t.isData = true → Ty.semWith D t = Ty.semWith Dsl.base t
  | .int, _ | .str, _ | .param _, _ | .date, _ | .id, _ => rfl
  | .list t, h => by simp only [Ty.semWith]; rw [Ty.semWith_data hD t (by simpa [Ty.isData] using h)]
  | .bag t, h => by simp only [Ty.semWith]; rw [Ty.semWith_data hD t (by simpa [Ty.isData] using h)]
  | .tuple ts, h => by simp only [Ty.semWith]; exact Ty.semsWith_data hD ts (by simpa [Ty.isData] using h)
  | .fn ps r, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp only [Ty.semWith]; rw [Ty.semsWith_data hD ps h.1, Ty.semWith_data hD r h.2]
  | .adt _ _ vs, h => by simp only [Ty.semWith]; exact Ty.semAltsWith_data hD vs (by simpa [Ty.isData] using h)
  | .table k v, h => by
    simp only [Ty.isData, Bool.and_eq_true] at h
    simp only [Ty.semWith]; rw [Ty.semWith_data hD k h.1, Ty.semWith_data hD v h.2]
  | .dsl k a, h => by
    simp only [Ty.isData, beq_iff_eq] at h
    subst h; exact hD a
theorem Ty.semsWith_data (hD : ∀ a, D .fresh a = Dsl.base .fresh a) : (ts : List Ty) → Ty.isDatas ts = true → Ty.semsWith D ts = Ty.semsWith Dsl.base ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.isDatas, Bool.and_eq_true] at h
    simp only [Ty.semsWith]; rw [Ty.semWith_data hD t h.1, Ty.semsWith_data hD ts h.2]
theorem Ty.semAltsWith_data (hD : ∀ a, D .fresh a = Dsl.base .fresh a) : (vs : List (List Ty)) → Ty.isDatass vs = true →
    Ty.semAltsWith D vs = Ty.semAltsWith Dsl.base vs
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.isDatass, Bool.and_eq_true] at h
    simp only [Ty.semAltsWith]; rw [Ty.semsWith_data hD ts h.1, Ty.semAltsWith_data hD vs h.2]
end

end

end Tazuna.Ir
