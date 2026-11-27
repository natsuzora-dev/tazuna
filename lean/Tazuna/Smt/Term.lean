import Tazuna.Ir.Str
import Std.Data.HashMap

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
  /-- `(u<f> args)`: a function from Ints to an Int that the script declares and leaves to the model, an
  uninterpreted function. -/
  | app (f : Nat) (args : List Term)
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
  | .app f as, .app f' bs => f == f' && Term.beqs as bs
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
  | .ctor _ _ as | .app _ as => by simp [Term.beq, Term.beqs_refl as]
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
  | .app f as, e, h => by
    cases e <;> try (simp [Term.beq] at h; done)
    simp only [Term.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, Term.eq_of_beqs as _ h.2]
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

mutual
/-- `Term.beq` that answers at once wherever two shared terms below are the same object in memory, with its
equality to `Term.beq` carried along. Encodings build equal shared terms as separate objects, and comparing them as
trees costs time exponential in how deeply shared terms nest. -/
def Term.beqS : (a b : Term) → {r : Bool // r = a.beq b}
  | .shared h a, .shared h' b => ⟨h == h' && withPtrEq a b (fun _ => (Term.beqS a b).1)
      (fun e => by subst e; rw [(Term.beqS a a).2]; exact Term.beq_refl a),
    by simp [Term.beq, withPtrEq, (Term.beqS a b).2]⟩
  | .not a, .not b => ⟨(Term.beqS a b).1, by simp [Term.beq, (Term.beqS a b).2]⟩
  | .len a, .len b => ⟨(Term.beqS a b).1, by simp [Term.beq, (Term.beqS a b).2]⟩
  | .and a b, .and c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .or a b, .or c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .eq a b, .eq c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .lt a b, .lt c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .le a b, .le c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .add a b, .add c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .sub a b, .sub c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .mul a b, .mul c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .div a b, .div c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .mod a b, .mod c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .cat a b, .cat c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .slt a b, .slt c d => ⟨(Term.beqS a c).1 && (Term.beqS b d).1, by simp [Term.beq, (Term.beqS a c).2, (Term.beqS b d).2]⟩
  | .ite a b c, .ite a' b' c' => ⟨(Term.beqS a a').1 && (Term.beqS b b').1 && (Term.beqS c c').1,
    by simp [Term.beq, (Term.beqS a a').2, (Term.beqS b b').2, (Term.beqS c c').2]⟩
  | .ctor d k as, .ctor d' k' bs => ⟨d == d' && k == k' && (Term.beqsS as bs).1,
    by simp [Term.beq, (Term.beqsS as bs).2]⟩
  | .app f as, .app f' bs => ⟨f == f' && (Term.beqsS as bs).1, by simp [Term.beq, (Term.beqsS as bs).2]⟩
  | .is d k a, .is d' k' b => ⟨d == d' && k == k' && (Term.beqS a b).1, by simp [Term.beq, (Term.beqS a b).2]⟩
  | .sel d k j a, .sel d' k' j' b => ⟨d == d' && k == k' && j == j' && (Term.beqS a b).1,
    by simp [Term.beq, (Term.beqS a b).2]⟩
  | a, b => ⟨a.beq b, rfl⟩
def Term.beqsS : (as bs : List Term) → {r : Bool // r = Term.beqs as bs}
  | a :: as, b :: bs => ⟨(Term.beqS a b).1 && (Term.beqsS as bs).1, by simp [Term.beqs, (Term.beqS a b).2, (Term.beqsS as bs).2]⟩
  | as, bs => ⟨Term.beqs as bs, rfl⟩
end

def Term.beqFast (a b : Term) : Bool := (Term.beqS a b).1

/-- Compiled code compares terms with `beqFast` (`csimp`, as the printer's `print_eq_printFast`). -/
@[csimp] theorem Term.beq_eq_beqFast : @Term.beq = @Term.beqFast := by
  funext a b; exact (Term.beqS a b).2.symm

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
  | .app f args => mixHash 24 (mixHash (hash f) (Term.hash0s args))
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
  /-- Each function `u<f>` the script declares, from Ints to an Int. -/
  funs : Nat → List Int → Int

mutual
/-- The value is one of the sort `s` in a script declaring the datatypes `dts`: an Int, a Bool, a string of SMT-LIB's
domain, or a constructor of the datatype with fields of their sorts. -/
def Val.InSrt (dts : List Datatype) : Srt → Val → Prop
  | .int, .int _ | .bool, .bool _ => True
  | .str, .str s => inDomain s = true
  | .dt i, .ctor e k vs => e = i ∧ ∃ fs, (dts[i]?.bind (·.ctors[k]?)) = some fs ∧ Val.InSrts dts fs vs
  | _, _ => False
def Val.InSrts (dts : List Datatype) : List Srt → List Val → Prop
  | [], [] => True
  | s :: ss, v :: vs => Val.InSrt dts s v ∧ Val.InSrts dts ss vs
  | _, _ => False
end

/-- The sort of field `j` of constructor `k` of datatype `d`. -/
def fieldSrt? (dts : List Datatype) (d k j : Nat) : Option Srt := (dts[d]?.bind (·.ctors[k]?)).bind (·[j]?)

/-- A selector applied to a value of another constructor gives a value of its field's sort, wherever that sort holds
one: SMT-LIB 2.6 leaves the value open but keeps it in the sort (Definition 8 and Remark 11), and a solver accepts only
datatypes whose sorts hold values (Section 4.2.3), so every field sort of a script it answers does. -/
def SelSorted (dts : List Datatype) (M : Model) : Prop :=
  ∀ d k j s v, fieldSrt? dts d k j = some s → (∃ w, Val.InSrt dts s w) → Val.InSrt dts s (M.selOther d k j v)

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
  | .app f args => .int (M.funs f ((Term.denotes M args).map Val.toInt))
def Term.denotes (M : Model) : List Term → List Val
  | [] => []
  | t :: ts => t.denote M :: Term.denotes M ts
end

@[simp] theorem Term.denote_share (M : Model) (t : Term) : t.share.denote M = t.denote M := by
  unfold Term.share; split <;> simp [Term.denote]

/-! Evaluation with sharing. `Term.denote` follows the tree, so a term whose shared parts nest (an unrolled run's
states, each read by the next step) costs time exponential in the nesting. `Term.evalC` gives each shared term its
value once, kept by the stored hash and confirmed by `Term.same`, as extraction does; `evalC_ok` proves it is
`Term.denote`, and `denote_eq_denoteFast` makes compiled code use it (`csimp`, as the printer's `print_eq_printFast`). -/

/-- Values of shared terms already evaluated, by the shared term's hash. -/
abbrev EvalCache := Std.HashMap UInt64 (List (Term × Val))

/-- Every value in the cache is its term's in the model. -/
def EvalCache.Ok (M : Model) (c : EvalCache) : Prop :=
  ∀ (h : UInt64) (l : List (Term × Val)), c[h]? = some l → ∀ p ∈ l, p.2 = p.1.denote M

def EvalCache.find? (c : EvalCache) (h : UInt64) (t : Term) : Option Val :=
  match c[h]? with
  | some l => (l.find? fun p => p.1.same t).map (·.2)
  | none => none

def EvalCache.add (c : EvalCache) (h : UInt64) (t : Term) (w : Val) : EvalCache :=
  match c[h]? with
  | some l => c.insert h ((t, w) :: l)
  | none => c.insert h [(t, w)]

-- SMT-LIB leaves a selector on a field its constructor lacks to the model, and the default stands for that value, as
-- in `Term.denote`.
set_option linter.tazuna.silentDefault false in
mutual
/-- The term's value, as `Term.denote` gives it, with each shared term evaluated once. -/
def Term.evalC (M : Model) : Term → EvalCache → Val × EvalCache
  | .shared h t, c => match c.find? h t with
    | some w => (w, c)
    | none => let (w, c) := t.evalC M c; (w, c.add h t w)
  | .var n, c => (M.vars n, c)
  | .int n, c => (.int n, c)
  | .str s, c => (.str s, c)
  | .bool b, c => (.bool b, c)
  | .ref i, c => (M.defs i, c)
  | .not a, c => let (x, c) := a.evalC M c; (.bool !x.toBool, c)
  | .len a, c => let (x, c) := a.evalC M c; (.int x.toStr.length, c)
  | .is d k a, c => let (x, c) := a.evalC M c
    (.bool (match x with | .ctor d' k' _ => d' == d && k' == k | _ => false), c)
  | .sel d k j a, c => let (x, c) := a.evalC M c
    (match x with
      | .ctor d' k' vs => if d' = d ∧ k' = k then vs[j]?.getD default else M.selOther d k j (.ctor d' k' vs)
      | v => M.selOther d k j v, c)
  | .and a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.bool (x.toBool && y.toBool), c)
  | .or a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.bool (x.toBool || y.toBool), c)
  | .eq a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.bool (x == y), c)
  | .lt a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.bool (decide (x.toInt < y.toInt)), c)
  | .le a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.bool (decide (x.toInt ≤ y.toInt)), c)
  | .add a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.int (x.toInt + y.toInt), c)
  | .sub a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.int (x.toInt - y.toInt), c)
  | .mul a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.int (x.toInt * y.toInt), c)
  | .div a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c
    (.int (if y.toInt = 0 then M.divZero x.toInt else x.toInt / y.toInt), c)
  | .mod a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c
    (.int (if y.toInt = 0 then M.modZero x.toInt else x.toInt % y.toInt), c)
  | .cat a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.str (x.toStr ++ y.toStr), c)
  | .slt a b, c => let (x, c) := a.evalC M c; let (y, c) := b.evalC M c; (.bool (decide (x.toStr < y.toStr)), c)
  | .ite a b e, c => let (x, c) := a.evalC M c; if x.toBool then b.evalC M c else e.evalC M c
  | .ctor d k args, c => let (xs, c) := Term.evalsC M args c; (.ctor d k xs, c)
  | .app f args, c => let (xs, c) := Term.evalsC M args c; (.int (M.funs f (xs.map Val.toInt)), c)
def Term.evalsC (M : Model) : List Term → EvalCache → List Val × EvalCache
  | [], c => ([], c)
  | t :: ts, c => let (x, c) := t.evalC M c; let (xs, c) := Term.evalsC M ts c; (x :: xs, c)
end

theorem EvalCache.find?_ok {M : Model} {c : EvalCache} (hc : c.Ok M) {h : UInt64} {t : Term} {w : Val}
    (hf : c.find? h t = some w) : w = t.denote M := by
  unfold EvalCache.find? at hf
  split at hf
  · rename_i l hl
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hf
    have hs : p.1.same t = true := by simpa using List.find?_some hp
    rw [hc h l hl p (List.mem_of_find?_eq_some hp), Term.eq_of_same hs]
  · cases hf

theorem EvalCache.add_ok {M : Model} {c : EvalCache} (hc : c.Ok M) (h : UInt64) (t : Term) :
    (c.add h t (t.denote M)).Ok M := by
  intro h' l hl p hp
  unfold EvalCache.add at hl
  by_cases hh : h = h'
  · subst hh
    split at hl
    · rename_i l0 heq
      simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hl
      subst hl
      rcases List.mem_cons.1 hp with rfl | hp
      · rfl
      · exact hc h l0 heq p hp
    · simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hl
      subst hl
      rcases List.mem_cons.1 hp with rfl | hp
      · rfl
      · cases hp
  · split at hl <;> simp [Std.HashMap.getElem?_insert, hh] at hl <;> exact hc h' l hl p hp

mutual
theorem Term.evalC_ok (M : Model) : (t : Term) → (c : EvalCache) → c.Ok M →
    (t.evalC M c).1 = t.denote M ∧ (t.evalC M c).2.Ok M
  | .shared h t, c, hc => by
    unfold Term.evalC
    split
    · rename_i w hf; exact ⟨(EvalCache.find?_ok hc hf).trans rfl, hc⟩
    · have ih := Term.evalC_ok M t c hc
      refine ⟨by simp [Term.denote, ih.1], ?_⟩
      simp only
      rw [ih.1]
      exact EvalCache.add_ok ih.2 h t
  | .var _, c, hc | .int _, c, hc | .str _, c, hc | .bool _, c, hc | .ref _, c, hc => ⟨rfl, hc⟩
  | .not a, c, hc | .len a, c, hc | .is _ _ a, c, hc | .sel _ _ _ a, c, hc => by
    have ih := Term.evalC_ok M a c hc
    simp only [Term.evalC, Term.denote, ih.1]
    exact ⟨by first | rfl | trivial, ih.2⟩
  | .and a b, c, hc | .or a b, c, hc | .eq a b, c, hc | .lt a b, c, hc | .le a b, c, hc | .add a b, c, hc
  | .sub a b, c, hc | .mul a b, c, hc | .div a b, c, hc | .mod a b, c, hc | .cat a b, c, hc
  | .slt a b, c, hc => by
    have ha := Term.evalC_ok M a c hc
    have hb := Term.evalC_ok M b _ ha.2
    simp only [Term.evalC, Term.denote, ha.1, hb.1]
    exact ⟨by first | rfl | trivial, hb.2⟩
  | .ite a b e, c, hc => by
    have ha := Term.evalC_ok M a c hc
    simp only [Term.evalC, Term.denote, ha.1]
    split
    · exact Term.evalC_ok M b _ ha.2
    · exact Term.evalC_ok M e _ ha.2
  | .ctor d k args, c, hc => by
    have h := Term.evalsC_ok M args c hc
    simp only [Term.evalC, Term.denote, h.1]
    exact ⟨by first | rfl | trivial, h.2⟩
  | .app f args, c, hc => by
    have h := Term.evalsC_ok M args c hc
    simp only [Term.evalC, Term.denote, h.1]
    exact ⟨by first | rfl | trivial, h.2⟩
theorem Term.evalsC_ok (M : Model) : (ts : List Term) → (c : EvalCache) → c.Ok M →
    (Term.evalsC M ts c).1 = Term.denotes M ts ∧ (Term.evalsC M ts c).2.Ok M
  | [], c, hc => ⟨rfl, hc⟩
  | t :: ts, c, hc => by
    have ht := Term.evalC_ok M t c hc
    have hs := Term.evalsC_ok M ts _ ht.2
    simp only [Term.evalsC, Term.denotes, ht.1, hs.1]
    exact ⟨by first | rfl | trivial, hs.2⟩
end

theorem EvalCache.ok_empty (M : Model) : ({} : EvalCache).Ok M := by
  intro h l hl; simp at hl

/-- The term's value, each shared term in it evaluated once. -/
def Term.denoteFast (M : Model) (t : Term) : Val := (t.evalC M {}).1

/-- Compiled code evaluates terms with sharing: a model read off an unrolled run's states costs their size as
definitions, not as trees. The theorems are about `Term.denote`, which this makes the code compute. -/
@[csimp] theorem Term.denote_eq_denoteFast : @Term.denote = @Term.denoteFast := by
  funext M t
  exact (Term.evalC_ok M t {} (EvalCache.ok_empty M)).1.symm

end Tazuna.Smt
