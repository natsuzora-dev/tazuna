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
snapshot.
-/
inductive Difference where
  | halt (original alternative : Option Violation)
  | outputs (mismatch : Violation)
  | records (original alternative : Value)
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
  Comparing the records of two executions that a stepOrder violation at `definition` would name held more
  than `limit` (bindingLimit) renamings of created keys at one step: too many renaming candidates to compare, so whether
  the choice changes the records is not known.
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
The result of a run: the violation that halted it, the trace lines that verify reads, its records (recordsValue), and
the keys that its running services created, each with its domain `<service>/<entity>` as verify's valueDomains names a
key reference's.
-/
structure Outcome where
  halted : Option Violation
  lines : List TraceLine
  records : CValue
  created : List (String × String)

/-- The key positions of entity `e`'s records: its key field and its ref() fields, each with the entity it names. -/
def keyFields (st : Service) (e : String) : List (String × Spec.Ref) :=
  let found := st.structure.definitions.findSome? fun d =>
    match d.body with
    | .entity key _ _ references => if d.service == st.service && d.name == e then some (key, references) else none
    | _ => none
  match found with
  | some (key, references) => key.toList.map (·, st.ref e) ++ references.filterMap fun r => r.entity.map (r.field, ·)
  | none => []

/-- A record's encoded fields with the strings at its key positions `fields` as key references. -/
def rowValue (fields : List (String × Spec.Ref)) : Value → CValue
  | .obj fs => .obj (fs.map fun (k, x) => (k, match fields.lookup k, x with
      | some r, .str s => .ref s!"{r.service}/{r.name}" s
      | _, x => CValue.ofValue x))
  | v => CValue.ofValue v

/--
The records as the relation compares them: each keyed entity as a bag of its encoded rows, in key order, since renamed
keys no longer order them, and each single entity as its encoded row once it has one. Only the key positions
(keyFields) rename.
-/
def recordsValue (st : Service) (records : Records) : CValue :=
  .obj (st.entities.filterMap fun e =>
    let row (r : Row) := rowValue (keyFields st e) r.value
    if e ∈ st.singles then (records.find? (·.entity == e)).map fun r => (e, row r)
    else
      let rows := (records.filter (·.entity == e)).mergeSort fun a b => decide (a.key.getD "" ≤ b.key.getD "")
      some (e, .bag (rows.map row)))

/--
The outcome of a run as the relation compares it: only the violation that halted the run, or else its trace lines and
its records.
-/
def Outcome.of (st : Service) (halted : Option Violation) (lines : List TraceLine) (records : Records)
    (created : List (String × String)) : Outcome :=
  match halted with
  | some v => { halted := some v, lines := [], records := .leaf .null, created := [] }
  | none => { halted := none, lines, records := recordsValue st records, created }

/--
The first violation that verify finds in the second lines, with the first lines as the snapshot, or else the set of
bindings that agree with every line (Data/Binding). The first argument refines what verify knows of the values
(Outcome.renaming).
-/
abbrev Compare (m : Type → Type) :=
  (Values → Values) → List TraceLine → List TraceLine → m (Except Violation (List Binding))

/--
What a comparison of `original` with `alternative` knows of the values beyond verify's `v`: a key that `original`
created has its domain from `original.created`, so the lines and the records bind it alike; and it may stand only for a
key that `alternative` created in the same domain, never for "", a literal, or a Given key. It renames only at key
references (matchValue).
-/
def Outcome.renaming (original alternative : Outcome) (v : Values) : Values :=
  { v with
    domain := fun s => (original.created.lookup s).getD (v.domain s)
    image := fun s t =>
      match original.created.lookup s with
      | some d => alternative.created.lookup t == some d
      | none => v.image s t }

/--
Whether the records of `original` and `alternative` are equal under one of the bindings `set`, extended by a renaming
of the created keys of `original` (one to one within each entity's keys, created keys only); uncomparable when matching
held more than bindingLimit bindings and no binding of `set` made them equal.
-/
def sameRecords (set : List Binding) (original alternative : Outcome) : Sameness :=
  let v := original.renaming alternative
    { domain := fun _ => "", fresh := original.created.map (·.1), image := fun _ _ => true }
  .any (set.map fun b => (matchValue v b original.records alternative.records).sameness)

/-- The identity of a halting violation. Two halting violations differ when their kinds or data differ. -/
def haltIdentity : Option Violation → Option (String × String)
  | some v => some (v.kind, v.data.canonical)
  | none => none

/-- What comparing two outcomes found: no difference, a difference, or too many renamings to tell (sameRecords). -/
inductive Comparison where
  | same
  | differ (difference : Difference)
  | uncomparable
deriving Repr, Inhabited

section

variable {m : Type → Type} [Monad m]

/--
The first difference: the halting violations, then the outputs as `compare` finds them with `original` as the
snapshot, then the records, which later inputs read, under the bindings of the outputs (sameRecords). Two outcomes
without a difference are equal up to a renaming of their created keys (symmetry, as TLA+ symmetry sets reduce states).
Outputs that `compare` cannot compare with themselves, as when equal requests get different answers, tell no choice
apart, so only the records are compared then.
-/
def difference (compare : Compare m) (original alternative : Outcome) : m Comparison := do
  if original.halted.isSome || alternative.halted.isSome then
    return if haltIdentity original.halted == haltIdentity alternative.halted then .same
      else .differ (.halt original.halted alternative.halted)
  let records (set : List Binding) : Comparison :=
    match sameRecords set original alternative with
    | .same => .same
    | .different => .differ (.records original.records.flatten alternative.records.flatten)
    | .uncomparable => .uncomparable
  match ← compare (original.renaming alternative) original.lines alternative.lines with
  | .ok set => return records set
  | .error mismatch =>
    match ← compare (original.renaming original) original.lines original.lines with
    | .ok _ => return .differ (.outputs mismatch)
    | .error _ => return records [.empty]

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
