import Tazuna.Service.Records
import Tazuna.Service.Basic
import Tazuna.Service.Instance

/-!
Functions answers what the semantics cannot evaluate: schema validation and spec functions. Theorems take `m = Id` and
hold for every function; the executable takes `m = IO` and asks TS.
-/

namespace Tazuna.Service

open Tazuna.Data

/-- What createKey returns next for an entity: `<entity>-<n>` for its `n`-th createKey value, after `count` so far. -/
structure NextKeys where
  count : Nat
deriving DecidableEq, Repr, Inhabited

derive_wire NextKeys

/--
What createKey returns next: `next` per entity (an entity that `next` lacks has none so far), each `<entity>-<n>`
qualified as `<owner>/<entity>-<n>` by the running service `owner` of a simulation that creates it, as a received id is,
so that the running services' keys differ whatever order they are created in.
-/
structure Keys where
  owner : Option String := none
  next : List (String × NextKeys) := []
deriving DecidableEq, Repr, Inhabited

derive_wire Keys skip_serializing_none

/--
The createKey values, each with its entity, that createKey gives to calls for the entities `created`, in call order,
when `keys` holds what it returns next.
-/
def givenKeys (keys : Keys) (created : List String) : List (String × String) :=
  created.zipIdx.map fun (e, i) =>
    let k := (keys.next.lookup e).getD ⟨0⟩
    let before := ((created.take i).filter (· == e)).length
    let counted := s!"{e}-{k.count + before + 1}"
    (e, match keys.owner with
      | some owner => s!"{owner}/{counted}"
      | none => counted)

/-- The scope of a copy: its decoded item key and its own context. -/
structure CopyScope where
  key : Value
  context : Value
deriving DecidableEq, Repr, Inhabited

derive_wire CopyScope

local instance : ToValue Time := ⟨Time.toValue⟩
local instance : FromValue Time := ⟨Time.fromValue⟩

/--
The values passed to machine and screen expressions; TS builds the expressions' arguments from them and the records.
`id` is the evaluating instance or copy. `state` is the state that declares the expression (`none` for the chart's own
`on`); `held` holds the parameters of that state for its current visit (empty when it has none), so a transition reads
the parameters of the state that it exits. `active` holds the active state names of a copy and its owner. `context` is
the context of the instance (the owner's for a copy). `shown` holds the answer of each shows slot (null if none).
`input` is the screen's input.
-/
structure Scope where
  id : InstanceId
  state : Option String
  context : Value
  copy : Option CopyScope := none
  active : List String
  shown : List (String × Value) := []
  input : Value := .obj []
  held : Value := .obj []
  now : Time
deriving DecidableEq, Repr, Inhabited

derive_wire Scope

def Scope.machine (s : Scope) : String := s.id.chart

inductive Assignment where
  | transition (transition : Transition)
  | entry (state : String)
  | exit (state : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Assignment tag "kind"

/--
The edge that enters a state with parameters and fills them with its `with`: a transition that targets the state, or
the initial edge of its parent. The chart's initial state has no parameters, since the chart enters it without an edge.
-/
inductive Edge where
  | transition (transition : Transition)
  | initial (parent : String)
deriving DecidableEq, Repr, Inhabited

derive_wire Edge tag "kind"

/-- What caused the transition, as passed to its expressions. -/
inductive Extra where
  | none
  | payload (payload : Value)
  | output (output : Value)
  /-- A rejection, of which expressions receive only the kind. -/
  | rejection (rejection : Rejection)
deriving DecidableEq, Repr, Inhabited

derive_wire Extra tag "kind"

/--
The reason that a question has no answer: its author code threw (with `schema`, inside that schema's refinement or
codec), a value does not match `schema`, an expression read a `held` name that its state does not have, or it called
`only()` on a bag with more than one element.
-/
inductive Issue where
  | thrown (schema : Option Schema)
  | schema (schema : Schema)
  | unheld (held : String)
  | notOnly
deriving DecidableEq, Repr, Inhabited

derive_wire Issue tag "kind" skip_serializing_none

/--
The fault that `e` means at a site whose own author code belongs to `owner`. A throw names `owner`, or the owner of the
schema whose refinement or codec threw. An unheld read, a call of `only()` on more than one element, and a held value
that fails its schema, name `owner`; a value that fails any other schema is the site's `mismatch`, an exception where
the site checks no schema.
-/
def issueViolation (owner : Spec.Ref) (e : Issue)
    (mismatch : Schema → Fault := fun _ => .exception (some owner)) : Fault :=
  match e with
  | .thrown none => .exception (some owner)
  | .thrown (some s) => .exception (some s.owner)
  | .unheld held => .unheld owner held
  | .notOnly => .notOnly owner
  | .schema (.held _ state) => .heldSchema owner state
  | .schema s => mismatch s

/--
What one ensures of a request's target gives on the request's results: it holds, it fails, or it reads records, which
are the target's own and not the caller's.
-/
inductive Ensured where
  | holds
  | fails
  | readsRecords
deriving DecidableEq, Repr, Inhabited

derive_wire Ensured

/--
Whether a result ensures lets the request's results pass. One that reads records passes, because it reads the target's
records, which the caller does not have.
-/
def Ensured.passes : Ensured → Bool
  | .holds | .readsRecords => true
  | .fails => false

/--
The questions that the semantics asks about schemas and spec functions. Every question that runs author code answers its
value or the Issue that stopped the code. A value matches its schema only without a field that the schema lacks at any
depth, from outside or from a spec function alike: a field that nothing reads is the writer's mistake, so it is not
dropped. A spec function's value is encoded by one rule: each codec encodes its part and checks what it takes, a part
that it does not encode is a schema Issue, and no other check runs, since the run checks the value after it sorts it
(Functions.sorting).
- parse: a value from outside (a value that a scenario line writes, or a message of another service), or one that a
  spec function wrote, decoded and written back as JSON (only its codecs run, encoding) if it matches the schema (the
  canonical value), or none otherwise. It does not read a sortedBy array's key order (parseOutside).
- unordered: a value from outside or of a trace line as a simulation compares it: canonical, with the elements of
  every bag in canonical order and sortedBy elements with equal keys in canonical order, so that a scenario never
  writes an order that the spec does not define.
- binding: whether one binds value of a command is non-null.
- requirement: whether one requires condition of a command holds.
- inputRequirement: whether one requires condition holds on the input alone, for a query or a screen, whose requires
  read only the input, or for an external peer's answer to the service's command or query.
- decide: the events of a command whose binds are all non-null and whose requires all hold, in groups: the groups are in
  order, and the events of one group have none. Each payload of an event that the command lists is encoded by its
  event's schema in the order it was built, and one that does not match is a schema Issue; any other payload is null,
  since the run halts on its event (unlistedEmittedEvent) first.
- ensures: the name of the first failing ensures of an accepted command. Binds read the records before the event write
  (the third argument), and `records` in ensures reads those after it (the fourth argument).
- queryEnsures: the name of the first failing ensures of a fulfilled query; `output` is the answer's output.
- resultEnsures: what one ensures of the command or query that a request names gives on the request's input, its
  answer's output, and its result events so far.
- invariant, serviceInvariant, chartInvariant: the name of the first failing invariant of an entity record, the service,
  or a machine or screen instance. A service invariant reads only records, so it fails only by a throw, with the schema
  whose refinement or codec threw.
- resolve: a query's output, encoded by its schema in the order it was built, or a schema Issue.
- automationBinding: whether one binds value of an automation is non-null for the received payload.
- automationGuard: whether one guard condition of an automation holds for the received payload, once every binds value
  is non-null.
- react: the input of the command that an automation sends for an event, once its guard holds, as the sender writes it
  by the command's input schema. `keys` holds what createKey returns next per entity (an entity that `keys` lacks has
  none so far), and react also returns the entities that it called createKey for, in call order.
- comparable: a query answer as verify compares it, ignoring bag and set order and the order of sortedBy elements
  with equal keys.
- initialContext: the context that the initialContext of a machine or screen computes from the input (the parsed input
  of a screen that opens opened, or `{}` when nothing opens it), encoded and in the order it was built, `{}` without one.
  A field that its schema does not encode is a schema Issue. initialContextOf fills in the defaults of the fields that
  it leaves out and parses it.
- guard: whether one guard condition of a transition holds.
- offers: the payloads that a control's offers return in a state (`none` for the chart itself), schema-checked,
  encoded and in the order they were built.
- showInput: the query input of a shows slot, as the sender writes it.
- items: the keys that a map state's items return, encoded in the order they were built. The map state takes them as a
  set.
- defaults: the default value of each field of the schema that declares one, encoded and in the order it was built.
  Load runs those of a single entity's fields and of a map state's copy context, and reports one that throws or fails
  its schema.
- close: the output of a screen that closes in a final state: the resolve value, schema-checked, encoded and in the
  order it was built.
- closeEnsures: the name of the first failing ensures of a screen that closed with the input and the sorted output.
- assign: the context after the assign, unchanged where there is none, checked, encoded and in the order it was built,
  which Functions.sorting sorts. For a copy, copy context fields go to the copy and the rest to the owner, and assign
  returns both. `keys` and the returned entities are as in react.
- input: the input of the request that a state sends, or of the screen that it opens, on entry, as the sender writes
  it: only the receiver parses it. A sends input may call createKey; `keys` is as in react.
- held: the parameters of the state `n` that an edge enters, which its `with` computes, checked against the held schema
  of `n`, encoded and in the order they were built, which Functions.sorting sorts. A transition's `with` reads what its
  assign reads.
- deadlineAt: what the `at` of a state's `after` deadline computes on entering it, as
  Temporal.Instant.prototype.toString writes it, or none when it computes no Instant.
-/
structure Functions (m : Type → Type) where
  parse : Schema → Value → m (Except Issue (Option Value))
  unordered : Schema → Value → m (Except Issue Value)
  binding : String → String → Value → Records → Time → m (Except Issue Bool)
  requirement : String → String → Value → Records → Time → m (Except Issue Bool)
  inputRequirement : Spec.Ref → String → Value → m (Except Issue Bool)
  decide : String → Value → Records → Time → m (Except Issue (List (List Emit)))
  ensures : String → Value → Records → Records → Time → m (Except Issue (Option String))
  queryEnsures : String → Value → Value → Records → m (Except Issue (Option String))
  resultEnsures : Spec.Ref → String → Value → Option Value → List Emit → m (Except Issue Ensured)
  invariant : String → Value → m (Except Issue (Option String))
  serviceInvariant : Records → m (Except (Option Schema) (Option String))
  chartInvariant : Scope → Records → m (Except Issue (Option String))
  resolve : String → Value → Records → Time → m (Except Issue Value)
  automationBinding : String → String → Value → Records → Time → m (Except Issue Bool)
  automationGuard : String → String → Value → Records → Time → m (Except Issue Bool)
  react : String → Value → Records → Time → Keys → m (Except Issue (Value × List String))
  comparable : String → Answer → m (Except Issue Value)
  initialContext : String → Value → m (Except Issue Value)
  guard : Scope → Records → Transition → String → Extra → m (Except Issue Bool)
  assign : Scope → Records → Assignment → Extra → Keys →
    m (Except Issue (Value × Option Value × List String))
  input : Scope → Records → Activity → Keys → m (Except Issue (Value × List String))
  held : Scope → Records → String → Edge → Extra → m (Except Issue Value)
  deadlineAt : Scope → Records → String → m (Except Issue (Option String))
  offers : Scope → Records → String → m (Except Issue (List Value))
  showInput : Scope → Records → Activity → m (Except Issue Value)
  items : Scope → Records → m (Except Issue (List Value))
  defaults : Schema → m (Except Issue Value)
  close : Scope → Records → m (Except Issue Value)
  closeEnsures : String → Value → Value → m (Except Issue (Option String))

/-- `fs.parse` of a value that spec code made, sorted first, so that its checks read the order that the run keeps. -/
def Functions.parseSorted {m : Type → Type} [Monad m] [MonadNote m] (fs : Functions m) (st : Service)
    (schema : Schema) (v : Value) : m (Except Issue (Option Value)) := do
  fs.parse schema (← st.sorted schema v)

/--
`fs.parse` of a value from outside, which also lists each sortedBy array in key order (keyOrdered): tazuna sorts the
values that spec code makes, so only a value from outside can break the order. The order is read from `v` as written,
since parse may sort what it returns; a sort key is required with no default (Illegal.unorderedSortKey), so every
written element has one.
-/
def Functions.parseOutside {m : Type → Type} [Monad m] [MonadNote m] (fs : Functions m) (st : Service)
    (schema : Schema) (v : Value) : m (Except Issue (Option Value)) := do
  match ← fs.parse schema v with
  | .ok (some x) =>
    let json ← expectFound s!"schema {repr schema}" (st.schemaOf schema)
    pure (.ok (if keyOrdered json v then some x else none))
  | r => pure r

/-- Whether the command `command` lists the event of `e` in its emits. -/
def lists (st : Service) (command : String) (e : Emit) : Bool :=
  (st.«structure».emitsOf (st.ref command)).contains e.event

/-- Each of `xs` through `f`, in order, or the first Issue. -/
def mapChecked {m : Type → Type} [Monad m] {α β : Type} (f : α → m (Except Issue β)) :
    List α → m (Except Issue (List β))
  | [] => pure (.ok [])
  | x :: xs => do
    match ← f x with
    | .error e => pure (.error e)
    | .ok y =>
      match ← mapChecked f xs with
      | .error e => pure (.error e)
      | .ok ys => pure (.ok (y :: ys))

/-- A value that spec code made for `schema`, sorted and parsed (parseSorted), or a schema Issue when it does not match. -/
def Functions.checked {m : Type → Type} [Monad m] [MonadNote m] (fs : Functions m) (st : Service) (schema : Schema)
    (v : Value) : m (Except Issue Value) := do
  match ← fs.parseSorted st schema v with
  | .ok (some x) => pure (.ok x)
  | .ok none => pure (.error (.schema schema))
  | .error e => pure (.error e)

/--
The functions that answer as `fs` does, with each parsed value sorted by its schema: parse fills a missing field with
its default as the schema writes it, so the order that the run keeps must not depend on how a value was built.
-/
def Functions.sortingParse {m : Type → Type} [Monad m] [MonadNote m] (st : Service) (fs : Functions m) : Functions m :=
  { fs with
    parse := fun schema v => do
      match ← fs.parse schema v with
      | .ok (some x) => pure (.ok (some (← st.sorted schema x)))
      | r => pure r }

/--
The functions that answer as `fs` does, with each value that spec code made sorted by its schema, as the run keeps it,
and each parsed value sorted again (sortingParse). A value that its own service keeps is also parsed (`checked`), so
that its checks read the sorted order. An event that the command does not list keeps its payload as decide wrote it,
since the run halts on it (unlistedEmittedEvent) before it reads a payload. An input goes to its receiver, which parses
it, and initialContextOf parses an initial context merged with its defaults.
-/
def Functions.sorting {m : Type → Type} [Monad m] [MonadNote m] (st : Service) (fs : Functions m) : Functions m :=
  let fs := fs.sortingParse st
  let sortedInput (schema : Option Schema) (x : Except Issue (Value × List String)) : m (Except Issue (Value × List String)) :=
    match x with
    | .ok (input, keys) => do
      pure (.ok (← st.sorted (← expectFound "the receiver of an input" schema) input, keys))
    | .error e => pure (.error e)
  { fs with
    decide := fun name input records now => do
      match ← fs.decide name input records now with
      | .error e => pure (.error e)
      | .ok groups =>
        mapChecked (mapChecked fun e =>
          if st.lists name e then do
            pure ((← fs.checked st (.payload e.event) e.payload).map fun payload => { e with payload })
          else pure (.ok e)) groups
    resolve := fun name input records now => do
      match ← fs.resolve name input records now with
      | .ok output => fs.checked st (.output (st.ref name)) output
      | .error e => pure (.error e)
    react := fun name payload records now keys => do
      sortedInput ((st.automations.find? (·.name == name)).map (.input ·.sends.ref))
        (← fs.react name payload records now keys)
    initialContext := fun machine input => do
      match ← fs.initialContext machine input with
      | .ok context => pure (.ok (← st.sorted (.context (st.ref machine)) context))
      | .error e => pure (.error e)
    assign := fun scope records a extra keys => do
      let chart := st.ref scope.machine
      match ← fs.assign scope records a extra keys with
      | .error e => pure (.error e)
      | .ok (context, copy, keys) =>
        match ← fs.checked st (.context chart) context with
        | .error e => pure (.error e)
        | .ok context =>
          match copy with
          | none => pure (.ok (context, none, keys))
          | some c =>
            let map ← expectFound "the map state of a copy" scope.id.map?
            pure ((← fs.checked st (.mapContext chart map) c).map fun c => (context, some c, keys))
    input := fun scope records a keys => do sortedInput (some (.input a.ref)) (← fs.input scope records a keys)
    held := fun scope records n edge extra => do
      match ← fs.held scope records n edge extra with
      | .ok v => fs.checked st (.held (st.ref scope.machine) n) v
      | .error e => pure (.error e)
    offers := fun scope records control => do
      match ← fs.offers scope records control with
      | .ok payloads => mapChecked (fs.checked st (.control (st.ref scope.machine) control)) payloads
      | .error e => pure (.error e)
    showInput := fun scope records a => do
      match ← fs.showInput scope records a with
      | .ok input => pure (.ok (← st.sorted (.input a.ref) input))
      | .error e => pure (.error e)
    items := fun scope records => do
      match ← fs.items scope records with
      | .error e => pure (.error e)
      | .ok items =>
        let schema := .mapKey (st.ref scope.machine) (← expectFound "the map state of an items question" scope.state)
        mapChecked (fs.checked st schema) items
    defaults := fun schema => do
      match ← fs.defaults schema with
      | .ok v => pure (.ok (← st.sorted schema v))
      | .error e => pure (.error e)
    close := fun scope records => do
      match ← fs.close scope records with
      | .ok output => fs.checked st (.output (st.ref scope.machine)) output
      | .error e => pure (.error e) }

/--
The first of `names` that `test` finds false, in order: the semantics evaluates binds, requires and guards one by one
and stops at the first null binding or false condition.
-/
def firstFalse {m : Type → Type} [Monad m] (test : String → m (Except Issue Bool)) :
    List String → m (Except Issue (Option String))
  | [] => pure (.ok none)
  | n :: ns => do
    match ← test n with
    | .error e => pure (.error e)
    | .ok true => firstFalse test ns
    | .ok false => pure (.ok (some n))

end Tazuna.Service
