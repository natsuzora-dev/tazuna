import Tazuna.Data.Wire
import Tazuna.Spec.Structure

/-!
The intermediate representation of spec function bodies: data that Lean evaluates in place of the TS function. TS
converts a function only when every construct in it is one of these, so the IR keeps the semantics that JS gives it.
-/

namespace Tazuna.Ir

open Tazuna.Data

/-- An argument that a spec function receives, as the callback that evaluates it passes it. -/
inductive Arg where
  | input
  | output
  | events
  | record
deriving DecidableEq, Repr, Inhabited

derive_wire Arg

inductive Relation where
  | lt
  | le
  | gt
  | ge
  | eq
deriving DecidableEq, Repr, Inhabited

derive_wire Relation

/--
What a comparison orders: numbers, as JS `<` does, or instants or dates, as `Temporal.Instant.compare` and
`Temporal.PlainDate.compare` do, which a value holds in its encoded text.
-/
inductive Order where
  | number
  | instant
  | date
deriving DecidableEq, Repr, Inhabited

derive_wire Order

/--
How a callback method visits a collection: an array as JS does, or a Bag, which runs the callback on every value and
whose `some` and `every` count only a callback that returns `true` or `false`.
-/
inductive Collection where
  | array
  | bag
deriving DecidableEq, Repr, Inhabited

derive_wire Collection

/-- An expression. `and`, `or` and `coalesce` give an operand's value and skip the other, as JS `&&`, `||` and `??`. -/
inductive Expr where
  | undef
  /-- A null, boolean, number or string. -/
  | lit (value : Value)
  | arg (arg : Arg)
  | var (name : String)
  | «let» (name : String) (value body : Expr)
  | ite (cond yes no : Expr)
  | and (left right : Expr)
  | or (left right : Expr)
  | coalesce (left right : Expr)
  | not (operand : Expr)
  /-- JS `===` on scalars, null or undefined. -/
  | eq (left right : Expr)
  | compare (relation : Relation) (order : Order) (left right : Expr)
  | field (object : Expr) (name : String)
  /-- `object?.name`. -/
  | fieldOpt (object : Expr) (name : String)
  /-- The length of a string in code points. -/
  | strLen (string : Expr)
  | startsWith (string search : Expr)
  | endsWith (string search : Expr)
  | strIncludes (string search : Expr)
  /-- The length of an array or the size of a Bag. -/
  | size (collection : Expr)
  | filter (visit : Collection) (collection : Expr) (name : String) (body : Expr)
  | some (visit : Collection) (collection : Expr) (name : String) (body : Expr)
  | every (visit : Collection) (collection : Expr) (name : String) (body : Expr)
deriving Repr, Inhabited

derive_wire_mutual (Expr tag "op")

/-- A named condition of a definition, such as one requires condition of a query. -/
structure Condition where
  definition : Spec.Ref
  name : String
  body : Expr
deriving Repr, Inhabited

derive_wire Condition

/--
The spec functions that TS converted, by the Functions callback that evaluates them. `invariants` and `closeEnsures`
hold every condition of an entity or screen in the order the spec writes them, or none of them.
-/
structure Program where
  «requires» : List Condition := []
  ensures : List Condition := []
  invariants : List Condition := []
  closeEnsures : List Condition := []
deriving Repr, Inhabited

derive_wire Program

end Tazuna.Ir
