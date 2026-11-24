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
  /-- Constructor `k` of datatype `d`. -/
  | ctor (d k : Nat) (args : List Term)
  /-- `(_ is D<d>_<k>)`: whether the value is built by constructor `k`. -/
  | is (d k : Nat) (a : Term)
  /-- Field `j` of constructor `k` of datatype `d`. -/
  | sel (d k j : Nat) (a : Term)
deriving Repr, Inhabited

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
  | .ctor d k args => .ctor d k (Term.denotes M args)
  | .is d k a => .bool (match a.denote M with
    | .ctor d' k' _ => d' == d && k' == k
    | _ => false)
  | .sel d k j a => match a.denote M with
    | .ctor d' k' vs => if d' = d ∧ k' = k then vs[j]?.getD default else M.selOther d k j (.ctor d' k' vs)
    | v => M.selOther d k j v
def Term.denotes (M : Model) : List Term → List Val
  | [] => []
  | t :: ts => t.denote M :: Term.denotes M ts
end

/-- The largest code point an SMT-LIB string holds. -/
def maxChar : Nat := 0x2FFFF

/-- Whether a string lies in SMT-LIB's string domain: every character at most U+2FFFF. -/
def inDomain (s : String) : Bool := s.toList.all (·.toNat ≤ maxChar)

end Tazuna.Smt
