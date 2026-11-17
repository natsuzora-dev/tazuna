import Tazuna.Service.Records
import Tazuna.Service.Basic

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

/--
What createKey returns next: `next` per entity (an entity that `next` lacks has none so far), each `<entity>-<n>`
qualified as `<owner>/<entity>-<n>` by the running service `owner` of a simulation that creates it, as a received id is,
so that the running services' keys differ whatever order they are created in.
-/
structure Keys where
  owner : Option String := none
  next : List (String × NextKeys) := []
deriving DecidableEq, Repr, Inhabited

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

/-- The scope of a copy whose map state is `map`. -/
structure CopyScope where
  map : String
  key : Value
  context : Value
deriving DecidableEq, Repr, Inhabited

/--
The values passed to machine and screen expressions; TS builds the expressions' arguments from them and the records.
`resource` is the evaluating instance or copy, and `owner` is its owner (itself if it is not a copy). `state` is the
state that declares the expression (`none` for the chart's own `on`); `held` is looked up in the holds of that state and
its ancestors, so it depends on where the expression is written, not on the active states, and a transition can read
the holds of the state that it exits. `active` holds the active state names of a copy and its owner. `context` is the
context of the instance (the owner's for a copy). `shown` holds the answer of each shows slot (null if none). `input` is
the screen's input.
-/
structure Scope where
  machine : String
  resource : String
  owner : String
  state : Option String
  context : Value
  copy : Option CopyScope := none
  active : List String
  shown : List (String × Value) := []
  input : Value := .obj []
  now : Time
deriving DecidableEq, Repr, Inhabited

inductive Assignment where
  | transition (t : Transition)
  | entry (state : String)
  | exit (state : String)
deriving DecidableEq, Repr, Inhabited

/-- What caused the transition, as passed to its expressions. -/
inductive Extra where
  | none
  | payload (payload : Value)
  | output (output : Value)
  /-- A rejection, of which expressions receive only the kind. -/
  | rejection (rejection : Rejection)
deriving DecidableEq, Repr, Inhabited

inductive DeadlineTime where
  /-- A delay of `ms` milliseconds after entering the state. -/
  | delay (ms : Time)
  /-- A time that the run recomputes from current values whenever a message finishes. -/
  | atExpression
deriving DecidableEq, Repr, Inhabited

/--
The reason that a question has no answer: its author code threw (with `schema`, inside that schema's refinement or
codec), a value does not match `schema`, an expression read a `held` name that no enclosing state holds, or it called
`only()` on a bag with more than one element.
-/
inductive Issue where
  | thrown (schema : Option Schema)
  | schema (schema : Schema)
  | unheld (held : String)
  | notOnly
deriving DecidableEq, Repr, Inhabited

/--
The fault that `e` means at a site whose own author code belongs to `owner`. A throw names `owner`, or the owner of the
schema whose refinement or codec threw. An unheld read, a call of `only()` on more than one element, and a held value
that fails its schema, name `owner`; a value that fails any other schema is the site's `mismatch`, an exception where
the site checks no schema.
-/
def issueViolation (st : Service) (owner : Spec.Ref) (e : Issue)
    (mismatch : Schema → Fault := fun _ => .exception (some owner)) : Fault :=
  match e with
  | .thrown none => .exception (some owner)
  | .thrown (some s) => .exception (some (st.schemaOwner s))
  | .unheld held => .unheld owner held
  | .notOnly => .notOnly owner
  | .schema (.held _ state name) => .heldSchema owner name state
  | .schema s => mismatch s

/--
The questions that the semantics asks about schemas and spec functions. Every question that runs author code answers its
value or the Issue that stopped the code; deadlines (no author code), copyContext, and singleRecord (defaults, checked
at load) always answer.
- parse: a value from outside (a value that a scenario line writes, or a message of another service), decoded and re-encoded if it
  matches the schema (the canonical value), or none otherwise.
- canonical: an outside value as written to a trace line; fields that do not match the schema stay as they are.
- unordered: a value from outside or of a trace line as a simulation compares it: canonical, with the elements of
  every bag in canonical order and sortedBy elements with equal keys in canonical order, so that a scenario never
  writes an order that the spec does not define.
- normalize: a value that a spec function made (a decide payload, a resolve output, or a react input), canonical if it
  matches the schema, or none otherwise. Extra fields do not match.
- binding: whether one binds value of a command is non-null.
- requirement: whether one requires condition of a command holds.
- inputRequirement: whether one requires condition holds on the input alone, for a query or a screen, whose requires
  read only the input, or for an external peer's answer to the service's command or query.
- decide: the events of a command whose binds are all non-null and whose requires all hold, in groups: the groups are in
  order, and the events of one group have none.
- ensures: the name of the first failing ensures of an accepted command. Binds read the records before the event write
  (the third argument), and `records` in ensures reads those after it (the fourth argument).
- queryEnsures: the name of the first failing ensures of a fulfilled query; `output` is the answer's output.
- resultEnsures: the name of the first ensures of the command or query that a request names that fails on the request's
  input, its answer's output, and its result events so far. An ensures that reads records is skipped, because it reads
  the callee's records.
- invariant, serviceInvariant, chartInvariant: the name of the first failing invariant of an entity record, the service,
  or a machine or screen instance. A service invariant reads only records, so it fails only by a throw, with the schema
  whose refinement or codec threw.
- resolve: a query's output.
- react: the input of the command that an automation sends for an event, or none when a binds value is null or the
  guard fails. `keys` holds what createKey returns next per entity (an entity that `keys` lacks has none so far), and
  react also returns the entities that it called createKey for, in call order.
- comparable: a query answer as verify compares it, ignoring bag and set order and the order of sortedBy elements
  with equal keys.
- initialContext: the initial context of a machine or screen started with the input (the input that `input` checked for
  a screen that opens opened, or `{}` when nothing opens it).
- offers: the payloads that a control's offers return in a state (`none` for the chart itself), schema-checked and
  encoded.
- showInput: the query input of a shows slot, schema-checked and encoded.
- items: the keys that a map state's items return, encoded and as canonicalJson. The map state takes them as a set.
- copyContext: a copy's initial context (defaults, checked at load).
- singleRecord: the initial record of a single entity (defaults, checked at load).
- copyKey: the canonicalJson of the payload's key fields if the payload has all of them (none if they fail the schema),
  or none without them, in which case the payload reaches every copy.
- close: the output of a screen that closes in a final state (the resolve value, schema-checked and encoded) and the
  first failing ensures.
- assign: the context after the assign, unchanged where there is none. For a copy, copy context fields go to the copy
  and the rest to the owner, and assign returns both. `keys` and the returned entities are as in react.
- input: the schema-checked, encoded input of the request that a state sends, or of the screen that it opens, on entry.
  A sends input may call createKey; `keys` is as in react.
- holds: the check of a state's holds values against their held schemas.
- deadlines: a state's `after` deadline names and how each time is set, in declaration order.
-/
structure Functions (m : Type → Type) where
  parse : Schema → Value → m (Except Issue (Option Value))
  canonical : Schema → Value → m (Except Issue Value)
  unordered : Schema → Value → m (Except Issue Value)
  normalize : Schema → Value → m (Except Issue (Option Value))
  binding : String → String → Value → Records → Time → m (Except Issue Bool)
  requirement : String → String → Value → Records → Time → m (Except Issue Bool)
  inputRequirement : String → String → Value → m (Except Issue Bool)
  decide : String → Value → Records → Time → m (Except Issue (List (List Emit)))
  ensures : String → Value → Records → Records → Time → m (Except Issue (Option String))
  queryEnsures : String → Value → Value → Records → m (Except Issue (Option String))
  resultEnsures : String → Value → Option Value → List Emit → m (Except Issue (Option String))
  invariant : String → Value → m (Except Issue (Option String))
  serviceInvariant : Records → m (Except (Option Schema) (Option String))
  chartInvariant : Scope → Records → m (Except Issue (Option String))
  resolve : String → Value → Records → Time → m (Except Issue Value)
  react : String → Value → Records → Time → Keys →
    m (Except Issue (Option Value × List String))
  comparable : String → Answer → m (Except Issue Value)
  initialContext : String → Value → m (Except Issue Value)
  guard : Scope → Records → Transition → Extra → m (Except Issue Bool)
  assign : Scope → Records → Assignment → Extra → Keys →
    m (Except Issue (Value × Option Value × List String))
  input : Scope → Records → Activity → Keys → m (Except Issue (Value × List String))
  holds : Scope → Records → m (Except Issue Unit)
  deadlines : String → String → m (List (String × DeadlineTime))
  deadlineAt : Scope → Records → String → m (Except Issue Time)
  offers : Scope → Records → String → m (Except Issue (List Value))
  showInput : Scope → Records → Activity → m (Except Issue Value)
  items : Scope → Records → m (Except Issue (List (Value × String)))
  copyContext : String → String → m Value
  singleRecord : String → m Value
  copyKey : String → String → Value → m (Except Issue (Option (Option String)))
  close : Scope → Records → m (Except Issue (Value × Option String))

end Tazuna.Service
