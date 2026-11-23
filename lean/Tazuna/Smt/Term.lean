import Tazuna.Ir.Eval

/-!
The SMT-LIB terms that prove sends to Z3, and what each term means for an assignment of its variables (`Term.denote`).
The theorems of Thm.Smt state the encoding's agreement with Ir.eval through `denote`; the printer writes each
constructor as the SMT-LIB operation of the same meaning. A JSON scalar or `undefined` is the datatype `V`.
-/

namespace Tazuna.Smt

/-- The sorts of the terms: SMT-LIB's Bool, Int and String, and the datatype `V` of JSON scalars and `undefined`. -/
inductive Ty where
  | bool
  | int
  | str
  | val
deriving DecidableEq, Repr, Inhabited

/-- A value of `V`: `undefined`, or a JSON null, boolean, integer or string. -/
inductive Scalar where
  | undef
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
deriving DecidableEq, Repr, Inhabited

/-- A value of a term. -/
inductive Lit where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | val (v : Scalar)
deriving DecidableEq, Repr, Inhabited

inductive Term where
  | var (name : String) (sort : Ty)
  | lit (value : Lit)
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
  /-- `str.len`: the number of characters. -/
  | len (a : Term)
  /-- `str.prefixof a b`: whether `a` starts `b`. -/
  | prefixOf (a b : Term)
  /-- `str.suffixof a b`: whether `a` ends `b`. -/
  | suffixOf (a b : Term)
  /-- `str.contains a b`: whether `b` occurs in `a`. -/
  | contains (a b : Term)
  | mkBool (a : Term)
  | mkInt (a : Term)
  | mkStr (a : Term)
  | isUndef (a : Term)
  | isNull (a : Term)
  | isBool (a : Term)
  | isInt (a : Term)
  | isStr (a : Term)
  /-- The selectors of `V`, which the encoding reads only under the matching tester, so their value elsewhere is moot. -/
  | boolOf (a : Term)
  | intOf (a : Term)
  | strOf (a : Term)
deriving DecidableEq, Repr, Inhabited

/-- The values of the variables, by name. A variable reads its value as one of its sort, as SMT-LIB sorts it. -/
abbrev Model := String → Lit

def Lit.toBool : Lit → Bool
  | .bool b => b
  | _ => false

def Lit.toInt : Lit → Int
  | .int n => n
  | _ => 0

def Lit.toStr : Lit → String
  | .str s => s
  | _ => ""

def Lit.toScalar : Lit → Scalar
  | .val v => v
  | _ => .undef

def Term.denote (M : Model) : Term → Lit
  | .var x .bool => .bool (M x).toBool
  | .var x .int => .int (M x).toInt
  | .var x .str => .str (M x).toStr
  | .var x .val => .val (M x).toScalar
  | .lit v => v
  | .not a => .bool !(a.denote M).toBool
  | .and a b => .bool ((a.denote M).toBool && (b.denote M).toBool)
  | .or a b => .bool ((a.denote M).toBool || (b.denote M).toBool)
  | .ite c a b => if (c.denote M).toBool then a.denote M else b.denote M
  | .eq a b => .bool (decide (a.denote M = b.denote M))
  | .lt a b => .bool (decide ((a.denote M).toInt < (b.denote M).toInt))
  | .le a b => .bool (decide ((a.denote M).toInt ≤ (b.denote M).toInt))
  | .add a b => .int ((a.denote M).toInt + (b.denote M).toInt)
  | .sub a b => .int ((a.denote M).toInt - (b.denote M).toInt)
  | .mul a b => .int ((a.denote M).toInt * (b.denote M).toInt)
  | .len a => .int (a.denote M).toStr.length
  | .prefixOf a b => .bool ((a.denote M).toStr.toList.isPrefixOf (b.denote M).toStr.toList)
  | .suffixOf a b =>
    .bool ((a.denote M).toStr.toList.reverse.isPrefixOf (b.denote M).toStr.toList.reverse)
  | .contains a b => .bool (Ir.isInfix (b.denote M).toStr.toList (a.denote M).toStr.toList)
  | .mkBool a => .val (.bool (a.denote M).toBool)
  | .mkInt a => .val (.int (a.denote M).toInt)
  | .mkStr a => .val (.str (a.denote M).toStr)
  | .isUndef a => .bool (match (a.denote M).toScalar with | .undef => true | _ => false)
  | .isNull a => .bool (match (a.denote M).toScalar with | .null => true | _ => false)
  | .isBool a => .bool (match (a.denote M).toScalar with | .bool _ => true | _ => false)
  | .isInt a => .bool (match (a.denote M).toScalar with | .int _ => true | _ => false)
  | .isStr a => .bool (match (a.denote M).toScalar with | .str _ => true | _ => false)
  | .boolOf a => .bool (match (a.denote M).toScalar with | .bool b => b | _ => false)
  | .intOf a => .int (match (a.denote M).toScalar with | .int n => n | _ => 0)
  | .strOf a => .str (match (a.denote M).toScalar with | .str s => s | _ => "")

/-- Whether the term holds under `M`. -/
abbrev Term.holds (M : Model) (t : Term) : Bool := (t.denote M).toBool

def tt : Term := .lit (.bool true)
def ff : Term := .lit (.bool false)
def undefT : Term := .lit (.val .undef)

/-- The conjunction of `ts`. -/
def conj (ts : List Term) : Term := ts.foldr .and tt

/-- The disjunction of `ts`. -/
def disj (ts : List Term) : Term := ts.foldr .or ff

end Tazuna.Smt
