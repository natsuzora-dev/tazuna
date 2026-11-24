import Tazuna.Ir.Expr

namespace Tazuna.Ir

def Expr.children : Expr → List Expr
  | .undef | .lit _ | .arg _ | .var _ | .table _ | .single _ | .createKey _ => []
  | .let _ v b => [v, b]
  | .ite c y n => [c, y, n]
  | .and a b | .or a b | .coalesce a b | .eq a b | .compare _ _ a b | .startsWith a b | .endsWith a b
  | .strIncludes a b | .lookup a b | .concat a b | .includes a b | .arith _ a b | .addDays a b => [a, b]
  | .not a | .field a _ | .fieldOpt a _ | .strLen a | .size a | .only a | .emit _ a => [a]
  | .filter _ c _ b | .some _ c _ b | .every _ c _ b | .map _ c _ b | .sum c _ b | .min _ c _ b | .max _ c _ b
  | .sortedBy _ c _ b => [c, b]
  | .obj fs => fs.map (·.value)
  | .arr vs => vs

/-- The names that a callback of `e` binds in its body, which is the last of `e`'s children. -/
def Expr.binds : Expr → Option String
  | .filter _ _ x _ | .some _ _ x _ | .every _ _ x _ | .map _ _ x _ | .sum _ x _ | .min _ _ x _ | .max _ _ x _
  | .sortedBy _ _ x _ => Option.some x
  | _ => none

/--
The fields of the argument `a` that `e` reads, none when it reads the argument as a whole. `names` are the variables
that hold the argument, as the converter binds a destructured parameter with `let`.
-/
partial def argReadsIn (a : Arg) (names : List String) : Expr → Option (List String)
  | .field (.arg b) n | .fieldOpt (.arg b) n => some (if a == b then [n] else [])
  | .field (.var x) n | .fieldOpt (.var x) n => some (if x ∈ names then [n] else [])
  | .arg b => if a == b then none else some []
  | .var x => if x ∈ names then none else some []
  | .let x v body => do
    let held := match v with
      | .arg b => a == b
      | .var y => y ∈ names
      | _ => false
    let inValue ← if held then pure [] else argReadsIn a names v
    let inBody ← argReadsIn a (if held then x :: names else names.filter (· != x)) body
    pure (inValue ++ inBody)
  | e =>
    let children := Expr.children e
    let inner := match (Expr.binds e) with
      | some x => names.filter (· != x)
      | none => names
    children.zipIdx.foldlM (fun acc (c, i) => do
      pure (acc ++ (← argReadsIn a (if (Expr.binds e).isSome && i + 1 == children.length then inner else names) c))) []

def argReads (a : Arg) (e : Expr) : Option (List String) := argReadsIn a [] e

end Tazuna.Ir
