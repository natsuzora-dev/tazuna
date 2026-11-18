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

def sameRef : Option Ref → Option Ref → Bool
  | some a, some b => a == b
  | _, _ => false

/-- The name of `r` in the traces of `service`. A definition of another service has its service name as a prefix. -/
def Ref.traceName (r : Ref) (service : String) : String :=
  if r.service == service then r.name else s!"{r.service}.{r.name}"

/-- The ref that a trace name as seen from `service` spells: the part before the last dot, if any, is the service. -/
def Ref.ofTraceName (service traceName : String) : Ref :=
  match (traceName.splitOn ".").reverse with
  | name :: owner@(_ :: _) => { service := ".".intercalate owner.reverse, name }
  | _ => { service, name := traceName }

/--
An activity of a state. `name` is the key under the keyword, and `definition` is the query, command, or screen of
that key, or null when the key names no definition.
-/
inductive Activity where
  | calls (name : String) (definition : Option Ref)
  | sends (name : String) (definition : Option Ref)
  | shows (name : String) (definition : Option Ref)
  | opens (name : String) (definition : Option Ref) (modal : Bool)
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

structure State where
  name : String
  /-- The names from a child of the root down to the state itself. -/
  path : List String
  parent : Option String
  /-- The kind. A compound state has children and is neither parallel nor map. -/
  kind : StateKind
  initial : Option String
  children : List String
  offers : List (String × Offer)
  /-- The activities, in the order calls, sends, shows, opens. -/
  activities : List Activity
  transitions : List Transition
  /-- The names of the deadlines that the body writes under `after`. -/
  deadlines : List String
deriving Repr, Inhabited

derive_wire State

def State.shape (st : State) : Shape :=
  { name := st.name, path := st.path, parent := st.parent, initial := st.initial, children := st.children,
    kind := st.kind, targets := st.transitions.filterMap (·.target) }

structure ChartFields where
  initial : String
  context : List String
  /-- The input fields. A machine has none, and no `output`, `requires`, or `ensures`. -/
  input : List String
  output : List String
  «requires» : List String
  ensures : List String
  on : List Transition
  /-- The chart's own offers, which name every control. -/
  offers : List (String × Offer)
  /-- The states, in document order. -/
  states : List State
  /-- The payload schema of each control, or null for a control without a payload. -/
  controls : List (String × Option Value)
  receives : List (String × Option Ref)
  commands : List (String × Option Ref)
  queries : List (String × Option Ref)
  screens : List (String × Option Ref)
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

/-- A `ref()` field and the entity it points to, null when the entity is no definition. -/
structure Reference where
  field : String
  entity : Option Ref
deriving Repr, Inhabited

derive_wire Reference

inductive Change where
  | none
  | create
  | update
  | delete
deriving DecidableEq, Repr, Inhabited

derive_wire Change

inductive Body where
  /-- An entity. `key` is null for a single entity, whose `unique` is empty. `references` are in field order. -/
  | entity (key : Option String) (fields : List String) (unique : List String) (references : List Reference)
  /-- An event. `entity` is null when `change` is none. -/
  | event (change : Change) (entity : Option Ref) (payload : Value)
  /--
  A command. For a command of an external service, `rejects` lists the rejection kinds that it declares, and `emits`
  lists the events that may arrive as results of an accepted request (resultOf). For a command of a spec service,
  `rejects` is null. `references` are in field order.
  -/
  | command (rejects : Option (List RejectionKind)) (input : Value) (output : Option Value)
      (emits : List (Option Ref)) (references : List Reference) (binds : List String) («requires» : List String)
  /--
  A query. For a query of an external service, `rejects` lists the rejection kinds that it declares. For a query of
  a spec service, `rejects` is null.
  -/
  | query (rejects : Option (List RejectionKind)) (input : Value) (output : Option Value) («requires» : List String)
  | automation (receives : Option Ref) (command : Option Ref) (binds : List String) (guard : List String)
  | machine (chart : Chart)
  | screen (chart : Chart)
deriving Repr, Inhabited

derive_wire Body tag "kind" flatten chart

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
  | .command _ _ output .. | .query _ _ output .. => output.isSome
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

/-- The whole spec without function bodies and source locations, as TS `structureOf` writes it. -/
structure Structure where
  services : List ServiceInfo
  contracts : List Contract
  /-- The definitions, in the order of the spec. -/
  definitions : List Definition
deriving Repr, Inhabited

derive_wire Structure

def Chart.state? (c : Chart) (n : String) : Option State := c.states.find? (·.name == n)

def Structure.isOpenedByScreen (s : Structure) (r : Ref) : Bool :=
  s.definitions.any fun d =>
    match d.body with
    | .screen c => c.screens.any (sameRef ·.2 (some r))
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
rejected with `invalidInput` is the sender's fault (Requester.inputFault), so it is not listed.
-/
def Structure.rejectionKinds (s : Structure) (service : String) (r : Ref) : List RejectionKind :=
  let other (kinds : List RejectionKind) := if r.service == service then [] else kinds
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.query (some kinds) ..) | some (.command (some kinds) ..) => kinds
  | some (.query none _ _ conditions) => (if conditions.isEmpty then [] else [.requires]) ++ other [.unavailable]
  | some (.command none _ _ emits references binds conditions) =>
    let writes := emits.any fun e => s.definitions.any fun d =>
      some d.ref == e && match d.body with
        | .event .create .. | .event .update .. => true
        | _ => false
    other [.reusedId] ++ (if references.isEmpty then [] else [.notFound]) ++
      (if binds.isEmpty && conditions.isEmpty then [] else [.requires]) ++ (if writes then [.alreadyExists] else []) ++
      other [.unavailable]
  | _ => []

/-- The events that the command `command` lists in its emits, or no events when `command` names no command. -/
def Structure.emitsOf (s : Structure) (command : Option Ref) : List (Option Ref) :=
  (s.definitions.findSome? fun d =>
    match d.body with
    | .command _ _ _ emits .. => if sameRef (some d.ref) command then some emits else none
    | _ => none).getD []

/-- The requires conditions of the command or query `r`. -/
def Structure.requiresOf (s : Structure) (r : Ref) : List String :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command _ _ _ _ _ _ conditions) | some (.query _ _ _ conditions) => conditions
  | _ => []

/-- The reasons that a requires rejection of the command or query `r` may name: its binds, then its requires. -/
def Structure.rejectionReasons (s : Structure) (r : Ref) : List String :=
  match (s.definitions.find? (·.ref == r)).map Definition.body with
  | some (.command _ _ _ _ _ binds conditions) => binds ++ conditions
  | some (.query _ _ _ conditions) => conditions
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

/--
Why `event` cannot be the result of a request to `target`, or none when it can. `event` can be the result only when
`target` is a command that accepted the request and lists `event` in its emits.
-/
def Structure.resultOfMismatch (s : Structure) (target : Ref) (accepted : Bool) (event : Ref) :
    Option ResultOfMismatch :=
  match (s.definitions.find? (·.ref == target)).map Definition.body with
  | some (.command _ _ _ emits ..) =>
    if !accepted then some .resultOfUnacceptedRequest
    else if emits.contains (some event) then none
    else some .resultOfUnlistedEvent
  | _ => some .resultOfNonCommand

/-- What an answer to a request, or its result events, break of the target's contract. -/
inductive AssumptionMismatch where
  | unlistedRejectionKind (rejection : Rejection)
  | answerOutputSchema
  /-- The answer rejects the request for requires, although the input meets the target's assumed requires. -/
  | rejectedAssumedRequires
  /-- The answer is no rejection, although the input fails the target's assumed requires `condition`. -/
  | failedAssumedRequires (condition : String)
  /-- The answer, or the result events so far, fail the target's assumed ensures `condition`. -/
  | failedAssumedEnsures (condition : String)
deriving DecidableEq, Repr, Inhabited

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
