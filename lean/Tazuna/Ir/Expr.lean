import Tazuna.Data.Wire
import Tazuna.Spec.Definition

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
  | context
  | shown
  | active
  | held
  /-- The key of a map state's copy. -/
  | key
  /-- The rejection that a transition takes, as `{ kind }`. -/
  | rejection
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

/-- What a comparison orders: numbers, as JS `<` does, or date labels `YYYY-MM-DD`, by the day they name. -/
inductive Order where
  | number
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

/-- An integer operation, exact: spec numbers are integers. -/
inductive Arith where
  | add
  | sub
  | mul
deriving DecidableEq, Repr, Inhabited

derive_wire Arith

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
  /-- Two Bags or arrays together; an array spread, `[...a, b]`, is the concat of `a` and `[b]`. -/
  | concat (left right : Expr)
  /-- `array.includes(value)` of an array of scalars, null or undefined. -/
  | includes (array value : Expr)
  | arith (operation : Arith) (left right : Expr)
  /-- `addDays(date, days)`: the date label `days` days after `date`, which throws outside years 0000 through 9999. -/
  | addDays (date days : Expr)
  /-- `emit(event, payload)` of an event that the command lists. -/
  | emit (event : Spec.Ref) (payload : Expr)
  /--
  `createKey(ref(entity))`: the next key of the entity, which the evaluation notes as created. The converter writes it
  only where TS passes createKey, and never inside a callback, so the keys made follow the written order.
  -/
  | createKey (entity : String)

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

/-- Where in a state a transition that enters a state with parameters starts: a transition, or its parent's initial. -/
inductive Entry where
  | transition (transition : Spec.TransitionRef)
  | initial (parent : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Entry tag "kind"

/-- Where a machine or screen writes functions, as the question that evaluates them names the place. -/
inductive Site where
  /-- The chart's invariants. -/
  | invariants
  /-- The guard conditions of a transition. -/
  | guards (transition : Spec.TransitionRef)
  /-- The `at` of a deadline of a state. -/
  | deadline (state name : String)
  /-- The items of a map state. -/
  | items (state : String)
  /-- The offers of a control in a state, or in the chart itself. -/
  | offers (state : Option String) (control : String)
  /-- The input of an activity of a state, by its keyword: `calls`, `sends`, `shows` or `opens`. -/
  | input (state keyword key : String)
  /-- The parameters of `state` that an entry fills, in the order of the state's held schema. -/
  | held (entry : Entry) (state : String)
  | initialContext
  /-- A screen's resolve. -/
  | close
  /-- The assign of a transition, by field, in the order the spec writes them. -/
  | transitionAssign (transition : Spec.TransitionRef)
  | entryAssign (state : String)
  | exitAssign (state : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Site tag "kind"

/--
The converted functions of one site of a chart, all of them in the order the question reads them. A site of one
function names it with the empty string.
-/
structure ChartFns where
  chart : Spec.Ref
  site : Site
  functions : List Condition
deriving Repr, Inhabited

derive_wire ChartFns

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
  /-- The `when` and the `expect` of an entity's responses, each named after its response. -/
  responseWhen : List Conditions := []
  responseExpect : List Conditions := []
  automationBinding : List Conditions := []
  automationGuard : List Conditions := []
  resolve : List Fn := []
  /-- A command's decide, where its binds have an entry. -/
  decide : List Fn := []
  /-- An automation's input of the command it sends, where its binds have an entry. -/
  react : List Fn := []
  chart : List ChartFns := []
deriving Repr, Inhabited

derive_wire Program

end Tazuna.Ir
