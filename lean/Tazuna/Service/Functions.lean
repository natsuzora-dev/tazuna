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
  | .schema (.held _ state name) => .heldSchema owner name state
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
value or the Issue that stopped the code. A value matches its schema only without a field that the schema lacks, whether
it comes from outside or from a spec function: a field that nothing reads is the writer's mistake, so it is not
dropped.
- parse: a value from outside (a value that a scenario line writes, or a message of another service), decoded and
  written back as JSON (only its codecs run, encoding) if it matches the schema (the canonical value), or none otherwise.
- unordered: a value from outside or of a trace line as a simulation compares it: canonical, with the elements of
  every bag in canonical order and sortedBy elements with equal keys in canonical order, so that a scenario never
  writes an order that the spec does not define.
- normalize: a value that a spec function made (a decide payload or a resolve output), canonical if it matches the
  schema, or none otherwise.
- binding: whether one binds value of a command is non-null.
- requirement: whether one requires condition of a command holds.
- inputRequirement: whether one requires condition holds on the input alone, for a query or a screen, whose requires
  read only the input, or for an external peer's answer to the service's command or query.
- decide: the events of a command whose binds are all non-null and whose requires all hold, in groups: the groups are in
  order, and the events of one group have none.
- ensures: the name of the first failing ensures of an accepted command. Binds read the records before the event write
  (the third argument), and `records` in ensures reads those after it (the fourth argument).
- queryEnsures: the name of the first failing ensures of a fulfilled query; `output` is the answer's output.
- resultEnsures: what one ensures of the command or query that a request names gives on the request's input, its
  answer's output, and its result events so far.
- invariant, serviceInvariant, chartInvariant: the name of the first failing invariant of an entity record, the service,
  or a machine or screen instance. A service invariant reads only records, so it fails only by a throw, with the schema
  whose refinement or codec threw.
- resolve: a query's output.
- automationBinding: whether one binds value of an automation is non-null for the received payload.
- automationGuard: whether one guard condition of an automation holds for the received payload, once every binds value
  is non-null.
- react: the input of the command that an automation sends for an event, once its guard holds, as the sender writes it
  (only its codecs run, encoding). `keys` holds what createKey returns next per entity (an entity that `keys` lacks has
  none so far), and react also returns the entities that it called createKey for, in call order.
- comparable: a query answer as verify compares it, ignoring bag and set order and the order of sortedBy elements
  with equal keys.
- initialContext: the context that the initialContext of a machine or screen computes from the input (the parsed input of
  a screen that opens opened, or `{}` when nothing opens it), as the sender writes it (only its codecs run, encoding),
  `{}` without one. initialContextOf fills in the defaults of the fields that it leaves out and normalizes it.
- guard: whether one guard condition of a transition holds.
- offers: the payloads that a control's offers return in a state (`none` for the chart itself), schema-checked and
  encoded.
- showInput: the query input of a shows slot, as the sender writes it (only its codecs run, encoding).
- items: the keys that a map state's items return, encoded and as canonical values. The map state takes them as a set.
- defaults: the default value of each field of the schema that declares one, encoded and sorted. Load runs those of a
  single entity's fields and of a map state's copy context, and reports one that throws or fails its schema.
- close: the output of a screen that closes in a final state (the resolve value, schema-checked and encoded) and the
  first failing ensures.
- assign: the context after the assign, unchanged where there is none. For a copy, copy context fields go to the copy
  and the rest to the owner, and assign returns both. `keys` and the returned entities are as in react.
- input: the input of the request that a state sends, or of the screen that it opens, on entry, as the sender writes
  it (only its codecs run, encoding): only the receiver parses it. A sends input may call createKey; `keys` is as in react.
- held: the parameters of the state `n` that an edge enters, which its `with` computes, checked against the held schema
  of `n` and encoded. A transition's `with` reads what its assign reads.
- deadlineAt: what the `at` of a state's `after` deadline computes on entering it, as
  Temporal.Instant.prototype.toString writes it, or none when it computes no Instant.
-/
structure Functions (m : Type → Type) where
  parse : Schema → Value → m (Except Issue (Option Value))
  unordered : Schema → Value → m (Except Issue Value)
  normalize : Schema → Value → m (Except Issue (Option Value))
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
  items : Scope → Records → m (Except Issue (List (Value × Value)))
  defaults : Schema → m (Except Issue Value)
  close : Scope → Records → m (Except Issue (Value × Option String))

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
