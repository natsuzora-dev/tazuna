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
  | payload
  | now
  /-- The binds values of a command or automation, by name. -/
  | bound
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

mutual

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
  /-- `records.<entity>` of a keyed entity: a Bag of its records, which reads its keys when an operation visits it. -/
  | table (entity : String)
  /-- `records.<entity>` of a single entity. -/
  | single (entity : String)
  /-- `table.get(key)`: the record, which reads whether it exists, or `undefined`. -/
  | lookup (table key : Expr)
  /-- An object literal, its fields in written order. -/
  | obj (fields : List Field)
  /-- An array literal. -/
  | arr (values : List Expr)
  | map (visit : Collection) (collection : Expr) (name : String) (body : Expr)
  /-- A Bag's sum, which throws unless every value and the sum are safe integers. -/
  | sum (collection : Expr) (name : String) (body : Expr)
  /-- A Bag's least key, `undefined` when it is empty. -/
  | min (order : Order) (collection : Expr) (name : String) (body : Expr)
  | max (order : Order) (collection : Expr) (name : String) (body : Expr)
  /-- A Bag's one value, `undefined` when it is empty; more values are the Issue `notOnly`. -/
  | only (collection : Expr)
  /-- A Bag's values in groups of equal key, in ascending key order. -/
  | sortedBy (order : Order) (collection : Expr) (name : String) (body : Expr)
  | concat (left right : Expr)

structure Field where
  name : String
  value : Expr

end

deriving instance Repr for Expr, Field
instance : Inhabited Expr := ⟨.undef⟩

derive_wire_mutual (Expr tag "op") (Field)

/-- A converted condition, such as a requires, ensures, guard or invariant, or a binds value. -/
structure Condition where
  name : String
  body : Expr
deriving Repr, Inhabited

derive_wire Condition

/-- The converted conditions of one definition, in the order the spec writes them. -/
structure Conditions where
  definition : Spec.Ref
  conditions : List Condition
deriving Repr, Inhabited

derive_wire Conditions

/-- A converted spec function of a definition that has one, such as a query's resolve. -/
structure Fn where
  definition : Spec.Ref
  body : Expr
deriving Repr, Inhabited

derive_wire Fn

/--
The spec functions that TS converted, by the Functions callback that evaluates them. A callback that runs every
condition of a definition, such as `invariant`, holds all of them or no entry for the definition; so do `binding` and
`automationBinding`, since a requires, guard or ensures reads every binds value, and those hold entries only where the
binds have one. A service invariant names its service as its definition.
-/
structure Program where
  inputRequirement : List Conditions := []
  resultEnsures : List Conditions := []
  invariant : List Conditions := []
  closeEnsures : List Conditions := []
  binding : List Conditions := []
  requirement : List Conditions := []
  ensures : List Conditions := []
  queryEnsures : List Conditions := []
  serviceInvariant : List Conditions := []
  automationBinding : List Conditions := []
  automationGuard : List Conditions := []
  resolve : List Fn := []
deriving Repr, Inhabited

derive_wire Program

end Tazuna.Ir
