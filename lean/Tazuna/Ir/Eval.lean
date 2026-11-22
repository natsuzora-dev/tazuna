import Tazuna.Data.Time
import Tazuna.Ir.Expr
import Tazuna.Service.Functions

/-!
The evaluator of IR expressions. A value is a JSON value or none, which is JS `undefined`. Values stay as JSON encodes
them: the converter has chosen each operation by the TS type of its operands (an instant compare, a Bag's `every`), so no
value needs decoding.
-/

namespace Tazuna.Ir

open Tazuna.Data Tazuna.Service

/-- A value as an expression sees it; none is `undefined`. -/
abbrev Val := Option Value

/-- Whether JS takes the value as true: all but `undefined`, null, false, 0 and the empty string. -/
def truthy : Val → Bool
  | none | some .null => false
  | some (.bool b) => b
  | some (.num n) => n.mantissa != 0
  | some (.str s) => !s.isEmpty
  | some _ => true

/-- JS `===` on scalars, null and undefined. Two arrays or objects are never the same value. -/
def same : Val → Val → Bool
  | none, none => true
  | some .null, some .null => true
  | some (.bool a), some (.bool b) => a == b
  | some (.num a), some (.num b) => a.mantissa * 10 ^ b.exponent == b.mantissa * 10 ^ a.exponent
  | some (.str a), some (.str b) => a == b
  | _, _ => false

/-- The number, ms or days that `order` reads of a value to compare it, as a numerator over 10 ^ the exponent. -/
def ordinal (order : Order) : Val → Option (Int × Nat)
  | some (.num n) => if order == .number then some (n.mantissa, n.exponent) else none
  | some (.str s) =>
    match order with
    | .instant => (parseTime s).toOption.map (·, 0)
    | .date => (parseDate s).toOption.map (·, 0)
    | .number => none
  | _ => none

def Relation.holds (r : Relation) (a b : Int) : Bool :=
  match r with
  | .lt => a < b
  | .le => a ≤ b
  | .gt => a > b
  | .ge => a ≥ b
  | .eq => a == b

def thrown {α : Type} : Except Issue α := throw (.thrown none)

/-- A string operation's operands, or the TypeError of reading a property of null or undefined. -/
def strings (string search : Val) : Except Issue (String × String) :=
  match string, search with
  | some (.str s), some (.str p) => pure (s, p)
  | _, _ => thrown

def isInfix (p s : List Char) : Bool := (List.range (s.length + 1)).any fun i => p.isPrefixOf (s.drop i)

/--
The value of `e` with `args` and the variables `vars`. A property of null or undefined is the TypeError `thrown none`,
as JS throws it; so is a variable that no binder declares, which the converter never writes.
-/
def eval (args : Arg → Val) (vars : List (String × Val)) : Expr → Except Issue Val
  | .undef => pure none
  | .lit v => pure (some v)
  | .arg a => pure (args a)
  | .var x => match vars.lookup x with
    | some v => pure v
    | none => thrown
  | .let x e body => do eval args ((x, ← eval args vars e) :: vars) body
  | .ite c yes no => do if truthy (← eval args vars c) then eval args vars yes else eval args vars no
  | .and a b => do
    let v ← eval args vars a
    if truthy v then eval args vars b else pure v
  | .or a b => do
    let v ← eval args vars a
    if truthy v then pure v else eval args vars b
  | .coalesce a b => do
    match ← eval args vars a with
    | none | some .null => eval args vars b
    | v => pure v
  | .not a => do pure (some (.bool !truthy (← eval args vars a)))
  | .eq a b => do pure (some (.bool (same (← eval args vars a) (← eval args vars b))))
  | .compare r order a b => do
    match ordinal order (← eval args vars a), ordinal order (← eval args vars b) with
    | some (m, e), some (m', e') => pure (some (.bool (r.holds (m * 10 ^ e') (m' * 10 ^ e))))
    | _, _ => thrown
  | .field o name => do
    match ← eval args vars o with
    | none | some .null => thrown
    | some v => pure (v.field? name)
  | .fieldOpt o name => do
    match ← eval args vars o with
    | none | some .null => pure none
    | some v => pure (v.field? name)
  | .strLen s => do
    match ← eval args vars s with
    | some (.str s) => pure (some (.num s.length))
    | _ => thrown
  | .startsWith s p => do
    let (s, p) ← strings (← eval args vars s) (← eval args vars p)
    pure (some (.bool (p.toList.isPrefixOf s.toList)))
  | .endsWith s p => do
    let (s, p) ← strings (← eval args vars s) (← eval args vars p)
    pure (some (.bool (p.toList.reverse.isPrefixOf s.toList.reverse)))
  | .strIncludes s p => do
    let (s, p) ← strings (← eval args vars s) (← eval args vars p)
    pure (some (.bool (isInfix p.toList s.toList)))
  | .size c => do
    match ← eval args vars c with
    | some (.arr vs) => pure (some (.num vs.length))
    | _ => thrown
  | .filter _ c x body => do
    let vs ← elements (← eval args vars c)
    let kept ← vs.filterM fun v => do pure (truthy (← eval args ((x, some v) :: vars) body))
    pure (some (.arr kept))
  | .some .array c x body => do
    let vs ← elements (← eval args vars c)
    pure (some (.bool (← vs.anyM fun v => do pure (truthy (← eval args ((x, some v) :: vars) body)))))
  | .some .bag c x body => do
    let results ← (← elements (← eval args vars c)).mapM fun v => eval args ((x, some v) :: vars) body
    pure (some (.bool (results.contains (some (.bool true)))))
  | .every .array c x body => do
    let vs ← elements (← eval args vars c)
    pure (some (.bool (← vs.allM fun v => do pure (truthy (← eval args ((x, some v) :: vars) body)))))
  | .every .bag c x body => do
    let results ← (← elements (← eval args vars c)).mapM fun v => eval args ((x, some v) :: vars) body
    pure (some (.bool !(results.contains (some (.bool false)))))
where
  elements : Val → Except Issue (List Value)
    | some (.arr vs) => pure vs
    | _ => thrown

/-- The name of the first of `conditions` whose value is not truthy, in order, as TS `firstFailing` finds it. -/
def firstFailing (args : Arg → Val) : List Condition → Except Issue (Option String)
  | [] => pure none
  | c :: cs => do if truthy (← eval args [] c.body) then firstFailing args cs else pure (some c.name)

end Tazuna.Ir
