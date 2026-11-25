import Tazuna.Linter

/-! The SMT-LIB terms tazuna sends to a solver, and what each means in a model (`Term.denote`). The solver is any that
reads standard SMT-LIB 2.6 with the theories of Ints and Strings and declared datatypes; `denote` states the
meaning those standards give each operation, so the theorems about the encoding hold for every model a solver may
return. Where the standard leaves a value open (dividing by zero, a selector applied to another constructor), the
model chooses it. -/

namespace Tazuna.Smt

/-- A sort (`Sort` is a Lean keyword): Int, Bool, String, or the `i`-th datatype a script declares. -/
inductive Srt where
  | int
  | bool
  | str
  | dt (i : Nat)
deriving DecidableEq, Repr, Inhabited

/-- A datatype: its constructors, each with the sorts of its fields. A datatype refers only to datatypes declared
before it, so none is recursive. Names are generated: datatype `i` is `D<i>`, its constructor `k` is `D<i>_<k>`, and
that constructor's field `j` is selected by `D<i>_<k>_<j>`. -/
structure Datatype where
  ctors : List (List Srt)
deriving DecidableEq, Repr, Inhabited

/-- A term. Variable `n` is the constant `v<n>` a script declares. An Int literal below zero is written `(- n)`;
negation is `(- 0 a)`. -/
inductive Term where
  | var (n : Nat)
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  | not (a : Term)
  | and (a b : Term)
  | or (a b : Term)
  | ite (c a b : Term)
  | eq (a b : Term)
  | lt (a b : Term)
  | le (a b : Term)
  | add (a b : Term)
  | sub (a b : Term)
  | mul (a b : Term)
  /-- SMT-LIB's `div` and `mod`: Euclidean, so the remainder is never negative. -/
  | div (a b : Term)
  | mod (a b : Term)
  /-- `str.len`: the number of characters, which are code points up to U+2FFFF. -/
  | len (a : Term)
  /-- `str.++`. -/
  | cat (a b : Term)
  /-- `str.<`: lexicographic order on code points. -/
  | slt (a b : Term)
  /-- Constructor `k` of datatype `d`. -/
  | ctor (d k : Nat) (args : List Term)
  /-- `(_ is D<d>_<k>)`: whether the value is built by constructor `k`. -/
  | is (d k : Nat) (a : Term)
  /-- Field `j` of constructor `k` of datatype `d`. -/
  | sel (d k j : Nat) (a : Term)
  /-- `t`, which a script defines once however often it occurs (`Term.share` builds it). `h` is a hash of `t` that
  finds repeats quickly; it never decides one. -/
  | shared (h : UInt64) (t : Term)
  /-- The definition `s<i>` a script makes of a shared term. -/
  | ref (i : Nat)
deriving Repr, Inhabited

mutual
/-- Equality of terms. Deriving `DecidableEq` fails for a nested inductive, so it is written out. -/
def Term.beq : Term → Term → Bool
  | .var a, .var b | .ref a, .ref b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .bool a, .bool b => a == b
  | .not a, .not b | .len a, .len b => a.beq b
  | .and a b, .and c d | .or a b, .or c d | .eq a b, .eq c d | .lt a b, .lt c d | .le a b, .le c d
  | .add a b, .add c d | .sub a b, .sub c d | .mul a b, .mul c d | .div a b, .div c d | .mod a b, .mod c d
  | .cat a b, .cat c d | .slt a b, .slt c d => a.beq c && b.beq d
  | .ite a b c, .ite a' b' c' => a.beq a' && b.beq b' && c.beq c'
  | .ctor d k as, .ctor d' k' bs => d == d' && k == k' && Term.beqs as bs
  | .is d k a, .is d' k' b => d == d' && k == k' && a.beq b
  | .sel d k j a, .sel d' k' j' b => d == d' && k == k' && j == j' && a.beq b
  | .shared h a, .shared h' b => h == h' && a.beq b
  | _, _ => false
def Term.beqs : List Term → List Term → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Term.beqs as bs
  | _, _ => false
end

mutual
theorem Term.beq_refl : (t : Term) → t.beq t = true
  | .var _ | .ref _ | .int _ | .str _ | .bool _ => by simp [Term.beq]
  | .not a | .len a => by simp [Term.beq, Term.beq_refl a]
  | .and a b | .or a b | .eq a b | .lt a b | .le a b | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .cat a b | .slt a b => by simp [Term.beq, Term.beq_refl a, Term.beq_refl b]
  | .ite a b c => by simp [Term.beq, Term.beq_refl a, Term.beq_refl b, Term.beq_refl c]
  | .ctor _ _ as => by simp [Term.beq, Term.beqs_refl as]
  | .is _ _ a | .sel _ _ _ a | .shared _ a => by simp [Term.beq, Term.beq_refl a]
theorem Term.beqs_refl : (ts : List Term) → Term.beqs ts ts = true
  | [] => rfl
  | t :: ts => by simp [Term.beqs, Term.beq_refl t, Term.beqs_refl ts]
end

mutual
theorem Term.eq_of_beq : (a b : Term) → a.beq b = true → a = b
  | .var _, b, h | .ref _, b, h | .int _, b, h | .str _, b, h | .bool _, b, h => by
    cases b <;> try (simp [Term.beq] at h; done)
    all_goals simp only [Term.beq, beq_iff_eq] at h; rw [h]
  | .not a, b, h | .len a, b, h => by
    cases b <;> try (simp [Term.beq] at h; done)
    all_goals simp only [Term.beq] at h; rw [Term.eq_of_beq a _ h]
  | .and a b, e, h | .or a b, e, h | .eq a b, e, h | .lt a b, e, h | .le a b, e, h | .add a b, e, h
  | .sub a b, e, h | .mul a b, e, h | .div a b, e, h | .mod a b, e, h | .cat a b, e, h
  | .slt a b, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    all_goals simp only [Term.beq, Bool.and_eq_true] at h; rw [Term.eq_of_beq a _ h.1, Term.eq_of_beq b _ h.2]
  | .ite a b c, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    simp only [Term.beq, Bool.and_eq_true] at h
    rw [Term.eq_of_beq a _ h.1.1, Term.eq_of_beq b _ h.1.2, Term.eq_of_beq c _ h.2]
  | .ctor d k as, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1, h.1.2, Term.eq_of_beqs as _ h.2]
  | .is d k a, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1, h.1.2, Term.eq_of_beq a _ h.2]
  | .sel d k j a, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1.1, h.1.1.2, h.1.2, Term.eq_of_beq a _ h.2]
  | .shared g a, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, Term.eq_of_beq a _ h.2]
theorem Term.eq_of_beqs : (as bs : List Term) → Term.beqs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Term.beqs, Bool.and_eq_true] at h; rw [Term.eq_of_beq a b h.1, Term.eq_of_beqs as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Term.beqs] at h
end

/-- Equality of terms that answers at once when both are the same object in memory, as a repeated shared term
is. -/
def Term.same (a b : Term) : Bool := withPtrEq a b (fun _ => a.beq b) (fun h => h ▸ Term.beq_refl a)

theorem Term.eq_of_same {a b : Term} (h : a.same b = true) : a = b := Term.eq_of_beq a b h

mutual
/-- A hash of the term that reads a shared term's stored hash instead of its body, so it costs the term's size up to
the shared terms in it. -/
def Term.hash0 : Term → UInt64
  | .var n => mixHash 1 (hash n)
  | .int n => mixHash 2 (hash n)
  | .str s => mixHash 3 (hash s)
  | .bool b => mixHash 4 (hash b)
  | .not a => mixHash 5 a.hash0
  | .and a b => mixHash 6 (mixHash a.hash0 b.hash0)
  | .or a b => mixHash 7 (mixHash a.hash0 b.hash0)
  | .ite c a b => mixHash 8 (mixHash c.hash0 (mixHash a.hash0 b.hash0))
  | .eq a b => mixHash 9 (mixHash a.hash0 b.hash0)
  | .lt a b => mixHash 10 (mixHash a.hash0 b.hash0)
  | .le a b => mixHash 11 (mixHash a.hash0 b.hash0)
  | .add a b => mixHash 12 (mixHash a.hash0 b.hash0)
  | .sub a b => mixHash 13 (mixHash a.hash0 b.hash0)
  | .mul a b => mixHash 14 (mixHash a.hash0 b.hash0)
  | .div a b => mixHash 15 (mixHash a.hash0 b.hash0)
  | .mod a b => mixHash 16 (mixHash a.hash0 b.hash0)
  | .len a => mixHash 17 a.hash0
  | .cat a b => mixHash 18 (mixHash a.hash0 b.hash0)
  | .slt a b => mixHash 23 (mixHash a.hash0 b.hash0)
  | .ctor d k args => mixHash 19 (mixHash (hash (d, k)) (Term.hash0s args))
  | .is d k a => mixHash 20 (mixHash (hash (d, k)) a.hash0)
  | .sel d k j a => mixHash 21 (mixHash (hash (d, k, j)) a.hash0)
  | .shared h _ => h
  | .ref i => mixHash 22 (hash i)
def Term.hash0s : List Term → UInt64
  | [] => 23
  | t :: ts => mixHash t.hash0 (Term.hash0s ts)
end

/-- `t`, marked so that a script defines it once and refers to it wherever it recurs. The encoding marks each value
it may use more than once, so a script grows with the operations, not with the tree of their terms. -/
def Term.share (t : Term) : Term :=
  match t with
  | .var _ | .int _ | .str _ | .bool _ | .ref _ | .shared .. => t
  | t => .shared t.hash0 t

/-- A value in a model. -/
inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  | str (s : String)
  | ctor (d k : Nat) (args : List Val)
deriving Repr, Inhabited

mutual
def Val.beq : Val → Val → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .str a, .str b => a == b
  | .ctor d k as, .ctor d' k' bs => d == d' && k == k' && Val.beqs as bs
  | _, _ => false
def Val.beqs : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => Val.beq a b && Val.beqs as bs
  | _, _ => false
end

instance : BEq Val := ⟨Val.beq⟩

def Val.toBool : Val → Bool
  | .bool b => b
  | _ => false

def Val.toInt : Val → Int
  | .int n => n
  | _ => 0

def Val.toStr : Val → String
  | .str s => s
  | _ => ""

/-- A model: the value of each variable, and the values the standard leaves open. -/
structure Model where
  vars : Nat → Val
  /-- `(div a 0)` and `(mod a 0)`, which SMT-LIB leaves to the model. -/
  divZero : Int → Int
  modZero : Int → Int
  /-- A selector applied to a value of another constructor, which SMT-LIB leaves to the model. -/
  selOther : Nat → Nat → Nat → Val → Val
  /-- The value of each definition `s<i>`; a model of a script gives each the value of its body. -/
  defs : Nat → Val

-- SMT-LIB leaves a selector on a field its constructor lacks to the model, and the default stands for that value.
set_option linter.tazuna.silentDefault false in
mutual
def Term.denote (M : Model) : Term → Val
  | .var n => M.vars n
  | .int n => .int n
  | .str s => .str s
  | .bool b => .bool b
  | .not a => .bool !(a.denote M).toBool
  | .and a b => .bool ((a.denote M).toBool && (b.denote M).toBool)
  | .or a b => .bool ((a.denote M).toBool || (b.denote M).toBool)
  | .ite c a b => if (c.denote M).toBool then a.denote M else b.denote M
  | .eq a b => .bool (a.denote M == b.denote M)
  | .lt a b => .bool (decide ((a.denote M).toInt < (b.denote M).toInt))
  | .le a b => .bool (decide ((a.denote M).toInt ≤ (b.denote M).toInt))
  | .add a b => .int ((a.denote M).toInt + (b.denote M).toInt)
  | .sub a b => .int ((a.denote M).toInt - (b.denote M).toInt)
  | .mul a b => .int ((a.denote M).toInt * (b.denote M).toInt)
  | .div a b =>
    let x := (a.denote M).toInt
    let y := (b.denote M).toInt
    .int (if y = 0 then M.divZero x else x / y)
  | .mod a b =>
    let x := (a.denote M).toInt
    let y := (b.denote M).toInt
    .int (if y = 0 then M.modZero x else x % y)
  | .len a => .int (a.denote M).toStr.length
  | .cat a b => .str ((a.denote M).toStr ++ (b.denote M).toStr)
  | .slt a b => .bool (decide ((a.denote M).toStr < (b.denote M).toStr))
  | .ctor d k args => .ctor d k (Term.denotes M args)
  | .is d k a => .bool (match a.denote M with
    | .ctor d' k' _ => d' == d && k' == k
    | _ => false)
  | .sel d k j a => match a.denote M with
    | .ctor d' k' vs => if d' = d ∧ k' = k then vs[j]?.getD default else M.selOther d k j (.ctor d' k' vs)
    | v => M.selOther d k j v
  | .shared _ t => t.denote M
  | .ref i => M.defs i
def Term.denotes (M : Model) : List Term → List Val
  | [] => []
  | t :: ts => t.denote M :: Term.denotes M ts
end

@[simp] theorem Term.denote_share (M : Model) (t : Term) : t.share.denote M = t.denote M := by
  unfold Term.share; split <;> simp [Term.denote]

/-- The largest code point an SMT-LIB string holds. -/
def maxChar : Nat := 0x2FFFF

/-- Whether a string lies in SMT-LIB's string domain: every character at most U+2FFFF. -/
def inDomain (s : String) : Bool := s.toList.all (·.toNat ≤ maxChar)

end Tazuna.Smt
