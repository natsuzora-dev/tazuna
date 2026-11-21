import Tazuna.Data.Answer
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

/--
A deadline's delay, as Temporal.Duration reads it: the count of each unit. TS reads it and Lean decides what it means
(delayMs?).
-/
structure Delay where
  years : Int
  months : Int
  weeks : Int
  days : Int
  hours : Int
  minutes : Int
  seconds : Int
  milliseconds : Int
  microseconds : Int
  nanoseconds : Int
deriving DecidableEq, Repr, Inhabited

derive_wire Delay

/--
The length of `d` in milliseconds, which the run adds to an instant, or none when a date unit, which has no fixed
length for an instant, or a part below a millisecond, which the run's time cannot count, is not zero.
-/
def delayMs? (d : Delay) : Option Int :=
  if d.years == 0 && d.months == 0 && d.weeks == 0 && d.days == 0 && d.microseconds == 0 && d.nanoseconds == 0 then
    some (((d.hours * 60 + d.minutes) * 60 + d.seconds) * 1000 + d.milliseconds)
  else none

/-- How a deadline's time is computed. -/
inductive DeadlineTime where
  /-- `now` plus the delay, or null when Temporal.Duration does not read the delay. -/
  | delay (delay : Option Delay)
  /-- What its `at` function computes. -/
  | «at»
deriving DecidableEq, Repr, Inhabited

derive_wire DeadlineTime tag "kind"

/-- Whether the run can add the delay of `time` to an instant: true for an `at`, which computes an instant. -/
def DeadlineTime.isExact : DeadlineTime → Bool
  | .delay d => (d.bind delayMs?).isSome
  | .at => true

/-- Whether the delay of `time` is below zero, which would arm the deadline before its state was entered. -/
def DeadlineTime.isNegative : DeadlineTime → Bool
  | .delay d => (d.bind delayMs?).any (· < 0)
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

/-- An entity. `key` is null for a single entity, whose `unique` is empty. `references` are in field order. -/
structure EntityBody where
  key : Option String
  /-- The JSON Schema of the fields. -/
  fields : Value
  unique : List String
  references : List Reference
  /-- The key positions of the fields. -/
  keys : List KeyPosition
deriving Repr, Inhabited

derive_wire EntityBody

structure EventBody where
  /-- How the event changes records, or null for an event that changes none. -/
  change : Option Change
  payload : Value
deriving Repr, Inhabited

derive_wire EventBody

/--
A command. For a command of an external service, `rejects` lists the rejection kinds that it declares, and `emits`
lists the events that may arrive as results of an accepted request (resultOf). For a command of a spec service,
`rejects` is null. `references` are in field order.
-/
structure CommandBody where
  rejects : Option (List RejectionKind)
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
The values that explore gives the node at `path` of the JSON Schema of `schema`: the values of the one `domain()` that
names the node, which TS load decides from Zod object identity (Malformed.overlappingDomain).
-/
structure Domain where
  schema : Schema
  path : List SchemaStep
  values : List Value
deriving Repr, Inhabited

derive_wire Domain

/-- The `explore()` call of the service `service`: the most moves on a path after its scenarios, and its domains. -/
structure Explore where
  service : String
  depth : Nat
  /-- The domains at the nodes of the schemas that the service's moves may carry, at most one per schema and path. -/
  domains : List Domain
deriving Repr, Inhabited

derive_wire Explore

/-- The whole spec without function bodies and source locations, as TS `structureOf` writes it. -/
structure Structure where
  services : List ServiceInfo
  contracts : List Contract
  /-- The definitions, in the order of the spec. -/
  definitions : List Definition
  /-- The `explore()` calls, at most one per service. -/
  explores : List Explore
deriving Repr, Inhabited

derive_wire Structure

def Structure.body? (s : Structure) (r : Ref) : Option Body :=
  (s.definitions.find? (·.ref == r)).map (·.body)

def Structure.state? (s : Structure) (chart : Ref) (state : String) : Option State :=
  (s.body? chart).bind fun
    | .machine c | .screen c => c.states.find? (·.name == state)
    | _ => none

/--
The JSON Schema that `schema` names: a control without a payload's as an object without fields. None when the
structure has no such schema.
-/
def Structure.schemaOf (s : Structure) : Schema → Option Value
  | .input d => (s.body? d).bind fun
    | .command c => some c.input
    | .query q => some q.input
    | .machine c | .screen c => some c.input
    | _ => none
  | .output d => (s.body? d).bind fun
    | .command c => c.output
    | .query q => q.output
    | .machine c | .screen c => some c.output
    | _ => none
  | .payload e => (s.body? e).bind fun
    | .event b => some b.payload
    | _ => none
  | .control screen control => (s.body? screen).bind fun
    | .screen c => (c.controls.lookup control).map (·.getD (.obj []))
    | _ => none
  | .held chart state => ((s.state? chart state).bind (·.held)).map (·.schema)
  | .context chart => (s.body? chart).bind fun
    | .machine c | .screen c => some c.context
    | _ => none
  | .mapContext chart map => ((s.state? chart map).bind (·.type.map?)).map (·.context)
  | .mapKey chart map => ((s.state? chart map).bind (·.type.map?)).map (·.key)
  | .record entity => (s.body? entity).bind fun
    | .entity b => some b.fields
    | _ => none

/-- The commands that the automations and charts of `service` send. -/
def Structure.sentOf (s : Structure) (service : String) : List Ref :=
  (s.definitions.filter (·.service == service)).flatMap fun d =>
    match d.body with
    | .automation a => [a.command]
    | .machine c | .screen c => c.commands.map (·.2)
    | _ => []

/-- The commands and queries that the automations and charts of `service` send, each once. -/
def Structure.requestsOf (s : Structure) (service : String) : List Ref :=
  (s.sentOf service ++ (s.definitions.filter (·.service == service)).flatMap fun d =>
    match d.body with
    | .machine c | .screen c => c.queries.map (·.2)
    | _ => []).eraseDups

/--
The events of other services' contracts that the definitions of `service` receive: an automation's or a chart's
event, or a result event of a command that an automation or a chart sends.
-/
def Structure.receivesOf (s : Structure) (service : String) : List Ref :=
  let listed := s.contracts.filter (·.service != service) |>.flatMap fun c =>
    c.members.filterMap fun (_, r) => r.bind fun r =>
      if s.definitions.any (fun d => d.kind == "event" && d.ref == r) then some r else none
  let heard := (s.definitions.filter (·.service == service)).flatMap fun d =>
    match d.body with
    | .automation a => [a.receives]
    | .machine c | .screen c => c.receives.map (·.2)
    | _ => []
  let sent := s.sentOf service
  let results := s.definitions.flatMap fun d =>
    match d.body with
    | .command c => if sent.contains d.ref then c.emits else []
    | _ => []
  listed.filter (heard ++ results).contains

def Chart.state? (c : Chart) (n : String) : Option State := c.states.find? (·.name == n)

def Structure.isOpenedByScreen (s : Structure) (r : Ref) : Bool :=
  s.definitions.any fun d =>
    match d.body with
    | .screen c => c.screens.any (·.2 == r)
    | _ => false

/-- The definition with trace name `name` whose kind is one of `kinds`. -/
def Structure.named (s : Structure) (service : String) (name : Option String) (kinds : List String) :
    Option Definition :=
  name.bind fun n => s.definitions.find? fun d => kinds.contains d.kind && d.traceName service == n

/-- The services whose contract lists `r`. -/
def Structure.contractsListing (s : Structure) (r : Ref) : List String :=
  (s.contracts.filter (·.members.any (·.2 == some r))).map (·.service)

/--
The kinds that an answer to the command or query `r` may be rejected with when a definition of `service` sends it: for
an external `r`, the kinds it declares. Otherwise `requires` needs a requires condition or a binds value, `notFound` an
input ref field, and `alreadyExists` an emitted event that creates or updates a record, and a request to another
service may also be rejected with `unavailable`, and a command to another service with `reusedId`. An answer
rejected with `invalidInput` is the sender's fault (rejectedInput?), so it is not listed.
-/
def Structure.rejectionKinds (s : Structure) (service : String) (r : Ref) : List RejectionKind :=
  let other (kinds : List RejectionKind) := if r.service == service then [] else kinds
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.query { rejects := some kinds, .. }) | some (.command { rejects := some kinds, .. }) => kinds
  | some (.query q) => (if q.requires.isEmpty then [] else [.requires]) ++ other [.unavailable]
  | some (.command c) =>
    let writes := c.emits.any fun e => s.definitions.any fun d =>
      d.ref == e && match d.body with
        | .event { change := some { kind := .create, .. }, .. }
        | .event { change := some { kind := .update, .. }, .. } => true
        | _ => false
    other [.reusedId] ++ (if c.references.isEmpty then [] else [.notFound]) ++
      (if c.binds.isEmpty && c.requires.isEmpty then [] else [.requires]) ++
      (if writes then [.alreadyExists] else []) ++ other [.unavailable]
  | _ => []

/-- The events that `r` lists in its emits, or no events when `r` is no command. -/
def Structure.emitsOf (s : Structure) (r : Ref) : List Ref :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command c) => c.emits
  | _ => []

/-- The requires and ensures conditions of `r`, or none when `r` is no command or query. -/
def Structure.conditionsOf? (s : Structure) (r : Ref) : Option (List String × List String) :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command c) => some (c.requires, c.ensures)
  | some (.query q) => some (q.requires, q.ensures)
  | _ => none

/-- The reasons that a requires rejection of the command or query `r` may name: its binds, then its requires. -/
def Structure.rejectionReasons (s : Structure) (r : Ref) : List String :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command c) => c.binds ++ c.requires
  | some (.query q) => q.requires
  | _ => []

def Structure.hasOutput (s : Structure) (r : Ref) : Bool :=
  (s.definitions.find? (·.ref == r)).any (·.hasOutput)

/--
Whether an answer to the command or query `r` is checked against `r`'s assumed contract: `r` is a command or query of
an external service. test checks an answer from another service in the same spec against that service's run instead
(peerFindings).
-/
def Structure.isAssumed (s : Structure) (r : Ref) : Bool :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.query ..) | some (.command ..) => (s.services.find? (·.name == r.service)).any (·.external)
  | _ => false

/-- Why an event cannot be the result (resultOf) of a request. -/
inductive ResultOfMismatch where
  /-- The resultOf of the event names a request to a target that is not a command. -/
  | resultOfNonCommand
  /-- The resultOf of the event names a request that the answer did not accept. -/
  | resultOfUnacceptedRequest
  /-- The resultOf of the event names a request to a command whose emits do not list the event. -/
  | resultOfUnlistedEvent
deriving DecidableEq, Repr, Inhabited

derive_wire ResultOfMismatch

/--
Why `event` cannot be the result of a request to `target` that got `answers`, or none when it can. `event` can be the
result only when `target` is a command that lists `event` in its emits and no answer did not accept the request. A
request that no answer reached may have results, as an API response may be lost after the webhook is sent.
-/
def Structure.resultOfMismatch (s : Structure) (target : Ref) (answers : List Answer) (event : Ref) :
    Option ResultOfMismatch :=
  match (s.definitions.find? (·.ref == target)).map Definition.body with
  | some (.command c) =>
    if !answers.all (· matches .accepted _) then some .resultOfUnacceptedRequest
    else if c.emits.contains event then none
    else some .resultOfUnlistedEvent
  | _ => some .resultOfNonCommand

/-- What an answer to a request, or its result events, break of the target's contract. -/
inductive AssumptionMismatch where
  /-- The answer rejects the request with a kind that the target does not list. -/
  | unlistedRejectionKind (rejection : Rejection)
  /-- The answer has an output that does not match the target's output schema. -/
  | answerOutputSchema
  /-- The answer rejects the request for requires, although the input meets the target's assumed requires. -/
  | rejectedAssumedRequires
  /-- The answer is no rejection, although the input fails the target's assumed requires `condition`. -/
  | failedAssumedRequires (condition : String)
  /-- The answer, or the result events so far, fail the target's assumed ensures `condition`. -/
  | failedAssumedEnsures (condition : String)
deriving DecidableEq, Repr, Inhabited

derive_wire AssumptionMismatch tag "kind"

/--
The assumption that an answer breaks, given the first assumed requires that fails and, when the requires hold and
the answer is no rejection, the first assumed ensures that fails. A broken requires promises no ensures.
-/
def assumptionMismatch (answer : Answer) (failedRequires failedEnsures : Option String) : Option AssumptionMismatch :=
  match answer, failedRequires with
  | .rejected r, none => if r.kind == .requires then some .rejectedAssumedRequires else none
  | .rejected _, some _ => none
  | _, some c => some (.failedAssumedRequires c)
  | _, none => failedEnsures.map .failedAssumedEnsures

def schemaProperties (schema : Value) : List String :=
  match schema.field? "properties" with
  | some (.obj fields) => fields.map (·.1)
  | _ => []

end Tazuna.Spec
