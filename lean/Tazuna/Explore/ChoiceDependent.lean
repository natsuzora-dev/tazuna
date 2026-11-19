import Tazuna.Data.Binding
import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Explore.Instrument
import Tazuna.Service.Message
import Tazuna.Service.Note
import Tazuna.Service.Basic
import Tazuna.Service.Records

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service Tazuna.Sim

/--
A difference between the results of two executions. `original` is the result of the execution that takes the step that the
violation names first before the second, and `alternative` is the result of the execution that takes the second first.
`mismatch` is the first violation that verify finds in the alternative outputs, with the original outputs as the
snapshot. `state` is the state that a later input reads, the records and the open instances, when it differs.
-/
inductive Difference where
  | halt (original alternative : Option Violation)
  | outputs (mismatch : Violation)
  | state (original alternative : Value)
deriving Repr, Inhabited

derive_wire Difference tag "aspect"

/--
A result that depends on a choice nobody controls: the order of two steps of one processing that no cause orders, of two
deadlines of one service due at one time, or of two messages that one line delivers to one service. Every other order of
a simulation is a written line. stepOrder writes the pair in canonical order.
-/
inductive ChoiceDependent where
  /--
  The execution with the step order `originalOrder`, which takes `firstStep` before `secondStep`, and the execution with
  `alternativeOrder`, which takes `secondStep` first, differ by `difference`. An empty order is the execution without one.
  One order comes from the other (stepOrderSearch), so the pair is the steps whose order they swap. `definition` is the
  definition of the first step.
  -/
  | stepOrder (definition : Spec.Ref) (firstStep secondStep : StepName) (originalOrder alternativeOrder : List StepName)
      (difference : Difference)
  /--
  The search of the step orders of one processing ran `limit` (stepOrderLimit) orders and stopped with orders left, so
  a result that only those change is not reported. `definition` is the definition of the first step of the first pair
  that the search swapped.
  -/
  | searchLimit (definition : Spec.Ref) (limit : Nat)
  /--
  Comparing the states of two executions that a stepOrder violation at `definition` would name held more
  than `limit` (bindingLimit) renamings of created keys at one step: too many renaming candidates to compare, so whether
  the choice changes the state is not known.
  -/
  | uncomparable (definition : Spec.Ref) (limit : Nat)
deriving Repr, Inhabited

derive_group ChoiceDependent

/--
The number of step orders that the search of one processing runs at most (stepOrderSearch). It bounds the orders of a
processing with many steps that touch the same values, whose count grows factorially.
-/
def stepOrderLimit : Nat := 64

/--
The outcome of a run that did not halt, as the relation compares it: the trace lines that verify reads, which the
`outputs` difference compares, and the state that a later input reads (stateValue), its created keys as key references.
`created` holds the keys that the running services created, each with its domain `<service>/<entity>` as verify's
valueDomains names a key reference's; it renames, and is not compared.
-/
structure Finished where
  lines : List TraceLine
  state : CValue
  created : List (String × String)

/-- The outcome of a run: the violation that halted it, or how it finished. -/
inductive Outcome where
  | halted (violation : Violation)
  | finished (f : Finished)

def Outcome.halted? : Outcome → Option Violation
  | .halted v => some v
  | .finished _ => none

/-- The key positions `keys` that name a definition, each path with the entity it names. -/
def refsAt (keys : List Spec.KeyPosition) : List (List String × Spec.Ref) :=
  keys.filterMap fun k => k.entity.map (k.path, ·)

/-- The key positions of entity `e`'s records (Structure.KeyPosition). -/
def keyPaths (st : Service) (e : String) : List (List String × Spec.Ref) :=
  let found := st.structure.definitions.findSome? fun d =>
    match d.body with
    | .entity _ _ _ _ keys => if d.service == st.service && d.name == e then some keys else none
    | _ => none
  refsAt (found.getD [])

/-- The value `v` at field path `path` with the strings at the key positions `keys` as key references. -/
def keyed (keys : List (List String × Spec.Ref)) (path : List String) : Value → CValue
  | .str s => match keys.lookup path with
    | some r => .ref s!"{r.service}/{r.name}" s
    | none => .leaf (.str s)
  | .arr xs => .arr (xs.attach.map fun ⟨x, _⟩ => keyed keys path x)
  | .obj fs => .obj (fs.attach.map fun ⟨p, _⟩ => (p.1, keyed keys (path ++ [p.1]) p.2))
  | v => .leaf v
termination_by v => sizeOf v
decreasing_by all_goals nested_decreasing

/--
The records as the relation compares them: each keyed entity as a bag of its encoded rows, in key order, since renamed
keys no longer order them, and each single entity as its encoded row once it has one. Only the key positions
(keyPaths) rename.
-/
def recordsValue (st : Service) (records : Records) : CValue :=
  .obj (st.entities.filterMap fun e =>
    let keys := keyPaths st e
    let row (r : Row) := keyed keys [] r.value
    if e ∈ st.singles then (records.find? (·.entity == e)).map fun r => (e, row r)
    else
      let rows := (records.filter (·.entity == e)).mergeSort fun a b => decide (a.key.getD "" ≤ b.key.getD "")
      some (e, .bag (rows.map row)))

/-- The chart `name` of the running service `st`. -/
def chartNamed (st : Service) (name : String) : Option Spec.Chart :=
  st.structure.definitions.findSome? fun d => if d.service == st.service && d.name == name then d.chart? else none

/-- The map state `map` of the chart `name` of `st`. -/
def mapNamed (st : Service) (name map : String) : Option Spec.State :=
  (chartNamed st name).bind fun c => c.states.find? (·.name == map)

/--
The instance id `i` as the relation compares it: a copy's item key at its map state's key positions renames, also in
the opener of a screen.
-/
def idValue (st : Service) : InstanceId → CValue
  | .top c => CValue.ofValue (ToValue.toValue (InstanceId.top c))
  | .opened c o state key nth =>
    .obj [("kind", .leaf (.str "opened")), ("chart", .leaf (.str c)), ("opener", idValue st o),
      ("state", .leaf (.str state)), ("key", .leaf (.str key)), ("nth", .leaf (ToValue.toValue nth))]
  | .copy o m k =>
    .obj [("kind", .leaf (.str "copy")), ("owner", idValue st o), ("map", .leaf (.str m)),
      ("key", keyed (refsAt ((mapNamed st o.chart m).map (·.itemKeys) |>.getD [])) [] k)]

/-- `vs` in the order of their canonical texts. -/
def canonicalOrder (vs : List Value) : List Value := vs.mergeSort fun a b => decide (a.canonical ≤ b.canonical)

/--
An open instance as the relation compares it: its id, its active states and the children that each parent last left
(history), each in name order, since a later input reads which states are active and not the order they were entered
in; its context at the key positions of its chart or map state; and its pending deadlines, each with its state, name
and time, which a later clock line reads.
-/
def instanceValue (st : Service) (deadlines : List Deadline) (i : Instance) : CValue :=
  let contextKeys : Option (List Spec.KeyPosition) := match i.id.map? with
    | some m => (mapNamed st i.id.chart m).map Spec.State.contextKeys
    | none => (chartNamed st i.id.chart).map (·.toChartFields.contextKeys)
  let names (ns : List String) : Value := .arr (ns.mergeSort (· ≤ ·) |>.map .str)
  .obj [("id", idValue st i.id), ("states", .leaf (names i.active)),
    ("history", .leaf (.arr ((i.lastChildren.mergeSort fun a b => decide (a.1 ≤ b.1)).map fun (p, cs) =>
      .arr [.str p, names cs]))),
    ("context", keyed (refsAt (contextKeys.getD [])) [] i.context),
    ("deadlines", .leaf (.arr (canonicalOrder ((deadlines.filter (·.machine == i.id)).map fun d =>
      .obj [("state", .str d.state), ("name", .str d.name), ("time", Time.toValue d.time)]))))]

/--
The open instances as the relation compares them: a bag of instanceValue, in the order of their texts, since renamed
copy keys no longer order them. A closed instance is left out, since no input reaches it again.
-/
def instancesValue (st : Service) (s : State) : CValue :=
  let views := ((s.machines ++ s.copies).filter (!·.closed)).map (instanceValue st s.deadlines)
  .bag (views.mergeSort fun a b => decide (a.flatten.canonical ≤ b.flatten.canonical))

/-- The state that a later input reads: the records and the open instances, renamed together. -/
def stateValue (st : Service) (s : State) : CValue :=
  .obj [("records", recordsValue st s.records), ("instances", instancesValue st s)]

/-- The outcome of a run of the running service `st` that halted with `halted`, or else finished with `s`. -/
def Outcome.of (st : Service) (halted : Option Violation) (lines : List TraceLine) (s : State)
    (created : List (String × String)) : Outcome :=
  match halted with
  | some v => .halted v
  | none => .finished { lines, state := stateValue st s, created }

/--
The first violation that verify finds in the second lines, with the first lines as the snapshot, or else the set of
bindings that agree with every line (Data/Binding). The first argument refines what verify knows of the values
(Finished.renaming).
-/
abbrev Compare (m : Type → Type) :=
  (Values → Values) → List TraceLine → List TraceLine → m (Except Violation (List Binding))

/--
What a comparison of `original` with `alternative` knows of the values beyond verify's `v`: a key that `original`
created has its domain from `original.created`, so the lines and the state bind it alike; and it may stand only for a
key that `alternative` created in the same domain, never for "", a literal, or a Given key. It renames only at key
references (matchValue).
-/
def Finished.renaming (original alternative : Finished) (v : Values) : Values :=
  { v with
    domain := fun s => (original.created.lookup s).getD (v.domain s)
    image := fun s t =>
      match original.created.lookup s with
      | some d => alternative.created.lookup t == some d
      | none => v.image s t }

/--
Whether the states of `original` and `alternative` are equal under one of the bindings `set`, extended by a renaming
of the created keys of `original` (one to one within each entity's keys, created keys only); uncomparable when
matching held more than bindingLimit bindings and no binding of `set` made them equal. The records and the instances
match as one value, so one renaming holds for both, as TLA+ compares whole states.
-/
def sameState (set : List Binding) (original alternative : Finished) : Sameness :=
  let v := original.renaming alternative
    { domain := fun _ => "", fresh := original.created.map (·.1), image := fun _ _ => true }
  .any (set.map fun b => (matchValue v b original.state alternative.state).sameness)

/-- The identity of a halting violation. Two halting violations differ when their kinds or data differ. -/
def haltIdentity : Option Violation → Option (String × String)
  | some v => some (v.kind, v.data.canonical)
  | none => none

/-- What comparing two outcomes found: no difference, a difference, or too many renamings to tell (sameState). -/
inductive Comparison where
  | same
  | differ (difference : Difference)
  | uncomparable
deriving Repr, Inhabited

/-- The comparison of the states of `original` and `alternative` under the bindings `set` (sameState). -/
def compareStates (set : List Binding) (original alternative : Finished) : Comparison :=
  match sameState set original alternative with
  | .same => .same
  | .uncomparable => .uncomparable
  | .different => .differ (.state original.state.flatten alternative.state.flatten)

section

variable {m : Type → Type} [Monad m]

/--
The first difference: the halting violations, then the outputs as `compare` finds them with `original` as the
snapshot, then the state, which later inputs read, under the bindings of the outputs (sameState). Two outcomes without
a difference are equal up to a renaming of their created keys (symmetry, as TLA+ symmetry sets reduce states).
Outputs that `compare` cannot compare with themselves, as when equal requests get different answers, tell no choice
apart, so only the states are compared then.
-/
def difference (compare : Compare m) : Outcome → Outcome → m Comparison
  | .finished o, .finished a => do
    match ← compare (o.renaming a) o.lines a.lines with
    | .ok set => return compareStates set o a
    | .error mismatch =>
      match ← compare (o.renaming o) o.lines o.lines with
      | .ok _ => return .differ (.outputs mismatch)
      | .error _ => return compareStates [.empty] o a
  | o, a => return if haltIdentity o.halted? == haltIdentity a.halted? then .same
    else .differ (.halt o.halted? a.halted?)

/-- The violation, if any, that a comparison found for a choice at `definition`, with `found` for a difference. -/
def Comparison.violation (definition : Spec.Ref) (found : Difference → ChoiceDependent) :
    Comparison → Option ChoiceDependent
  | .same => none
  | .differ d => some (found d)
  | .uncomparable => some (.uncomparable definition bindingLimit)

/--
The ChoiceDependent violation, if any, for the order of steps `a` and `b`. `aFirst` takes `a` first and is the execution with
the step order `aOrder`, and `bFirst` takes `b` first and is the execution with `bOrder`. The pair is in the order of their
canonical texts.
-/
def stepOrder (compare : Compare m) (service : String) (a b : StepName) (aOrder bOrder : List StepName) (aFirst bFirst : Outcome) :
    m (Option ChoiceDependent) := do
  let (first, second, firstOrder, secondOrder, original, alternative) :=
    if (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical then (a, b, aOrder, bOrder, aFirst, bFirst)
    else (b, a, bOrder, aOrder, bFirst, aFirst)
  return (← difference compare original alternative).violation (first.definition service)
    (.stepOrder (first.definition service) first second firstOrder secondOrder)

end

end Tazuna.Explore
