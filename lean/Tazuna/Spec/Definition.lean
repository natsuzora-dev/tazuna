import Tazuna.Data.Answer
import Tazuna.Data.Trace
import Tazuna.Data.Value
import Tazuna.Data.Wire
import Tazuna.Spec.Tree

namespace Tazuna.Spec

open Tazuna.Data

structure Ref where
  service : String
  name : String
deriving DecidableEq, Repr, Inhabited

derive_wire Ref

inductive CallOutcome where
  | onFulfilled
  | onRejected
deriving DecidableEq, Repr, Inhabited

derive_wire CallOutcome

inductive SendOutcome where
  | onAccepted
  | onRejected
deriving DecidableEq, Repr, Inhabited

derive_wire SendOutcome

/-- What fires a transition array: the key that the chart writes the array under, typed per keyword. -/
inductive Trigger where
  | on (key : String)
  | after (deadline : String)
  | always
  | onDone
  | calls (key : String) (outcome : CallOutcome)
  | sends (key : String) (outcome : SendOutcome)
  /-- The `onDone` of an `opens`, taken when the opened screen closes. -/
  | opens (key : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Trigger tag "type"

/-- A chart's transition at `index` of the array on `trigger` in state `state` (none for the chart's own `on`). -/
structure TransitionRef where
  state : Option String
  trigger : Trigger
  index : Nat
deriving DecidableEq, Repr, Inhabited

derive_wire TransitionRef

/-- The name of `r` in the traces of `service`. A definition of another service has its service name as a prefix. -/
def Ref.traceName (r : Ref) (service : String) : String :=
  if r.service == service then r.name else s!"{r.service}.{r.name}"

/--
An activity of a state. `name` is the key under the keyword, and `definition` is the query, command, or screen of
that key. `onRejected` says whether the body writes a transition on a rejected answer.
-/
inductive Activity where
  | calls (name : String) (definition : Ref) (onRejected : Bool)
  | sends (name : String) (definition : Ref) (onRejected : Bool)
  | shows (name : String) (definition : Ref)
  | opens (name : String) (definition : Ref) (modal : Bool)
deriving Repr, Inhabited

derive_wire Activity tag "keyword"

structure Transition where
  /-- The source state, or null for the chart's own `on`. -/
  source : Option String
  trigger : Trigger
  index : Nat
  target : Option String
  guards : List String
  reenter : Option Bool
deriving Repr, Inhabited

derive_wire Transition

def Transition.guarded (t : Transition) : Bool := !t.guards.isEmpty

/--
Whether the transition has `reenter: true`. A missing `reenter` is false. For a target that is neither the source
nor its descendant, the value does not change the domain.
-/
def Transition.reenters (t : Transition) : Bool := t.reenter == some true

/-- What an offers entry gives its control: every payload that matches the schema (`any`), or what its function lists. -/
inductive Offer where
  | any
  | listed
deriving DecidableEq, Repr, Inhabited

derive_wire Offer

/--
A key position of a schema (an entity's fields, a context, or a map state's item key): the field path to a value whose
schema is `ref(entity)`, `ref.self()` in `entity`'s fields, or `entity`'s key field (its own key field included).
Array elements and union options do not extend the path. Lines, records, and instances rename created keys at these
positions.
-/
structure KeyPosition where
  path : List String
  entity : Ref
deriving Repr, Inhabited

derive_wire KeyPosition

/-- How a deadline's time is computed. -/
inductive DeadlineTime where
  /-- `now` plus the delay in milliseconds, or null when the delay is no safe integer. -/
  | delay (ms : Option Int)
  /-- What its `at` function computes. -/
  | «at»
deriving DecidableEq, Repr, Inhabited

derive_wire DeadlineTime tag "kind"

/-- Whether the run can add the delay of `time` to an instant: true for an `at`, which computes an instant. -/
def DeadlineTime.isExact : DeadlineTime → Bool
  | .delay ms => ms.isSome
  | .at => true

/-- Whether the delay of `time` is below zero, which would arm the deadline before its state was entered. -/
def DeadlineTime.isNegative : DeadlineTime → Bool
  | .delay ms => ms.any (· < 0)
  | .at => false

structure Deadline where
  name : String
  time : DeadlineTime
deriving DecidableEq, Repr, Inhabited

derive_wire Deadline flatten time

/--
What a map state adds to a state: the JSON Schemas of its item key and of its own context, which each copy holds, and
the key positions of both.
-/
structure MapState where
  key : Value
  context : Value
  itemKeys : List KeyPosition
  contextKeys : List KeyPosition
deriving Repr, Inhabited

derive_wire MapState

/-- The kind that a state's `type` names (StateKind), carrying what a map state adds. -/
inductive StateType where
  | plain
  | parallel
  | final
  | history
  | map (map : MapState)
deriving Repr, Inhabited

derive_wire StateType tag "kind"

def StateType.toKind : StateType → StateKind
  | .plain => .plain
  | .parallel => .parallel
  | .final => .final
  | .history => .history
  | .map _ => .map

def StateType.map? : StateType → Option MapState
  | .map m => some m
  | _ => none

/-- The JSON Schema of a state's parameters and their key positions. -/
structure Held where
  schema : Value
  keys : List KeyPosition
deriving Repr, Inhabited

derive_wire Held

structure State where
  name : String
  /-- The names from a child of the root down to the state itself. -/
  path : List String
  parent : Option String
  type : StateType
  initial : Option String
  children : List String
  offers : List (String × Offer)
  /-- The activities, in the order calls, sends, shows, opens. -/
  activities : List Activity
  transitions : List Transition
  /-- The deadlines that the body writes under `after`, in declaration order. -/
  deadlines : List Deadline
  /-- The state's parameters (`held`), which the edge that enters the state fills; null for a state without them. -/
  held : Option Held
deriving Repr, Inhabited

derive_wire State flatten type

def State.kind (st : State) : StateKind := st.type.toKind

def State.hasParameters (st : State) : Bool := st.held.isSome

def State.shape (st : State) : Shape :=
  { name := st.name, path := st.path, parent := st.parent, initial := st.initial, children := st.children,
    kind := st.kind, targets := st.transitions.filterMap (·.target) }

structure ChartFields where
  initial : String
  /-- The JSON Schema of the context. -/
  context : Value
  /-- The key positions of the context. -/
  contextKeys : List KeyPosition
  /-- The JSON Schema of the input. A machine has no fields in it or in `output`, and no `requires` or `ensures`. -/
  input : Value
  output : Value
  «requires» : List String
  ensures : List String
  on : List Transition
  /-- The chart's own offers, which name every control. -/
  offers : List (String × Offer)
  /-- The states, in document order. -/
  states : List State
  /-- The payload schema of each control, or null for a control without a payload. -/
  controls : List (String × Option Value)
  receives : List (String × Ref)
  commands : List (String × Ref)
  queries : List (String × Ref)
  screens : List (String × Ref)
deriving Repr, Inhabited

derive_wire ChartFields

structure Chart extends ChartFields where
  shaped : chartTree (states.map (·.shape)) initial (on.filterMap (·.target)) = true := by decide
deriving Repr

def Chart.tryFrom (c : ChartFields) : Except String Chart :=
  if h : chartTree (c.states.map (·.shape)) c.initial (c.on.filterMap (·.target)) = true then
    pure { toChartFields := c, shaped := h }
  else throw "expected the states as a tree in document order (the parent path of each state is a prefix of the path of the state before it), with unique names, parents, children, and initial states that match the paths, an initial state for each state with children other than a parallel state, no children of final and history states, no map or final state under a map state, and transition targets inside the same map state as their source or outside every map state, and an initial state of the chart among the children of the root"

derive_wire Chart try_from ChartFields

def Chart.tree (c : Chart) : Tree := { states := c.states.map (·.shape), shaped := stateTree_of_chartTree c.shaped }

/-- A `ref()` field and the entity it points to. -/
structure Reference where
  field : String
  entity : Ref
deriving Repr, Inhabited

derive_wire Reference

inductive ChangeKind where
  | create
  | update
  | delete
deriving DecidableEq, Repr, Inhabited

derive_wire ChangeKind

/-- How an entity event changes the records of `entity`. -/
structure Change where
  kind : ChangeKind
  entity : Ref
deriving Repr, Inhabited

derive_wire Change

/-- A bounded response of an entity: once `when` holds of a record, `expect` must hold of it within `within` ms. -/
structure ResponseTime where
  name : String
  within : Int
deriving DecidableEq, Repr, Inhabited

derive_wire ResponseTime

/-- An entity. `key` is null for a single entity, whose `unique` is empty. `references` are in field order. -/
structure EntityBody where
  key : Option String
  /-- The JSON Schema of the fields. -/
  fields : Value
  unique : List String
  references : List Reference
  /-- The key positions of the fields. -/
  keys : List KeyPosition
  /-- The responses, in definition order. -/
  responses : List ResponseTime
deriving Repr, Inhabited

derive_wire EntityBody

structure EventBody where
  /-- How the event changes records, or null for an event that changes none. -/
  change : Option Change
  payload : Value
deriving Repr, Inhabited

derive_wire EventBody

/--
A kind of caller that a command or query takes: the records of an entity of its service, or the service named
`service`. Cedar's `appliesTo.principalTypes` lists the principals of an action the same way.
-/
inductive CallerType where
  | entity (entity : String)
  | service (service : String)
deriving DecidableEq, Repr, Inhabited

derive_wire CallerType untagged

/-- Whether a caller of this type may be `caller`. -/
def CallerType.admits : CallerType → Caller → Bool
  | .entity e, .entity e' _ => e == e'
  | .service s, .service s' => s == s'
  | _, _ => false

/--
A command. For a command of an external service, `rejects` lists the rejection kinds that it declares, and `emits`
lists the events that may arrive as results of an accepted request (resultOf). For a command of a spec service,
`rejects` is null. `references` are in field order.
-/
structure CommandBody where
  rejects : Option (List RejectionKind)
  /-- The kinds of caller that may send the command, in written order. -/
  callers : List CallerType
  input : Value
  output : Option Value
  emits : List Ref
  references : List Reference
  binds : List String
  «requires» : List String
  ensures : List String
deriving Repr, Inhabited

derive_wire CommandBody

/--
A query. For a query of an external service, `rejects` lists the rejection kinds that it declares. For a query of a
spec service, `rejects` is null.
-/
structure QueryBody where
  rejects : Option (List RejectionKind)
  /-- The kinds of caller that may send the query, in written order. -/
  callers : List CallerType
  input : Value
  output : Option Value
  «requires» : List String
  ensures : List String
deriving Repr, Inhabited

derive_wire QueryBody

structure AutomationBody where
  receives : Ref
  command : Ref
  binds : List String
  guard : List String
  /-- Whether the automation writes `onRejected`. -/
  onRejected : Bool
deriving Repr, Inhabited

derive_wire AutomationBody

/-- A definition's body, whose fields the definition writes in its place. -/
inductive Body where
  | entity (body : EntityBody)
  | event (body : EventBody)
  | command (body : CommandBody)
  | query (body : QueryBody)
  | automation (body : AutomationBody)
  | machine (body : Chart)
  | screen (body : Chart)
deriving Repr, Inhabited

derive_wire Body tag "kind" flatten body

structure Definition where
  service : String
  name : String
  body : Body
deriving Repr, Inhabited

derive_wire Definition flatten body

def Definition.ref (d : Definition) : Ref := { service := d.service, name := d.name }

def Definition.kind (d : Definition) : String := d.body.kind

def Definition.hasOutput (d : Definition) : Bool :=
  match d.body with
  | .command c => c.output.isSome
  | .query q => q.output.isSome
  | _ => false

def Definition.chart? (d : Definition) : Option Chart :=
  match d.body with
  | .machine c | .screen c => some c
  | _ => none

def Definition.isScreen (d : Definition) : Bool :=
  match d.body with
  | .screen _ => true
  | _ => false

def Definition.traceName (d : Definition) (service : String) : String := d.ref.traceName service

structure Contract where
  service : String
  /-- The `contract()` keys and their definitions, with null for schemas and constants. -/
  members : List (String × Option Ref)
deriving Repr, Inhabited

derive_wire Contract

structure ServiceInfo where
  name : String
  external : Bool
  /-- The entity names, in the order of the service's `entities`. -/
  entities : List String
deriving Repr, Inhabited

derive_wire ServiceInfo

/-- Whether `v` has the form `<e>-<n>` of the `n`-th createKey value of entity `e`: `n` > 0 in decimal digits. -/
def isKeyOf (e v : String) : Bool :=
  let head := e.toList ++ ['-']
  let digits := v.toList.drop head.length
  v.toList.take head.length == head && !digits.isEmpty && digits.all Char.isDigit && digits.head? != some '0'

end Tazuna.Spec

namespace Tazuna

/--
A schema that a definition declares. `mapContext` is the copy context of the map state `map`, and `record` the fields
of the entity `entity`.
-/
inductive Schema where
  | input (definition : Spec.Ref)
  | payload (event : Spec.Ref)
  | output (definition : Spec.Ref)
  | control (screen : Spec.Ref) (control : String)
  | held (chart : Spec.Ref) (state : String)
  | context (chart : Spec.Ref)
  | mapContext (chart : Spec.Ref) (map : String)
  | mapKey (chart : Spec.Ref) (map : String)
  | record (entity : Spec.Ref)
deriving DecidableEq, Repr, Inhabited

derive_wire Schema tag "kind"

def Schema.owner : Schema → Spec.Ref
  | .input d | .output d => d
  | .payload e => e
  | .control screen _ => screen
  | .held chart .. | .context chart | .mapContext chart _ | .mapKey chart _ => chart
  | .record entity => entity

/-- A step into a JSON Schema: a property of an object, the items of an array, or an option of a union or a type list. -/
inductive SchemaStep where
  | field (name : String)
  | items
  | option (index : Nat)
deriving DecidableEq, Repr, Inhabited

derive_wire SchemaStep tag "kind"

end Tazuna

namespace Tazuna.Spec

open Tazuna.Data

/--
The `bounds()` of the service `service`: the most records of each of its keyed entities that prove creates, keys never
reused.
-/
structure Bounds where
  service : String
  creates : List (String × Nat)
deriving Repr, Inhabited

derive_wire Bounds

end Tazuna.Spec
