import Tazuna.Data.Binding
import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Observe.Instrument
import Tazuna.Service.Message
import Tazuna.Service.Note
import Tazuna.Service.Basic
import Tazuna.Service.Records

namespace Tazuna.Observe

open Tazuna.Data Tazuna.Semantics

/--
A difference between the results of two walks. `original` is the result of the walk that takes the step that the
violation names first before the second, and `alternative` is the result of the walk that takes the second first.
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
The handles of one group of `requests` to `target`: handle `j` names the group's message at place `handles[j]`, counted
in sending order.
-/
structure Assigned where
  target : Syntax.Ref
  handles : List Nat
deriving Repr, Inhabited

derive_wire Assigned

/--
A result that depends on a choice nobody controls: the order of two steps of one processing that no cause orders, or
of two deadlines of one service due at one time, or which of equal requests each handle of `requests` names. Every other
order of a simulation is a written line. stepOrder writes the pair in canonical order.
-/
inductive ChoiceDependent where
  /--
  The walk with the step order `originalOrder`, which takes `firstStep` before `secondStep`, and the walk with
  `alternativeOrder`, which takes `secondStep` first, differ by `difference`. An empty order is the walk without one.
  One order comes from the other (stepOrderSearch), so the pair is the steps whose order they swap. `definition` is the
  definition of the first step.
  -/
  | stepOrder (definition : Syntax.Ref) (firstStep secondStep : StepName) (originalOrder alternativeOrder : List StepName)
      (difference : Difference)
  /--
  The search of the step orders of one processing ran `limit` (stepOrderLimit) orders and stopped with orders left, so
  a result that only those change is not reported. `definition` is the definition of the first step of the first pair
  that the search swapped. The search of the assignments of one scenario stops alike at assignmentLimit, with the
  target of the first group as `definition`.
  -/
  | searchLimit (definition : Syntax.Ref) (limit : Nat)
  /--
  The walk in which each handle of `requests` names the message at its own place and the walk with the handles of each
  group as `assigned` lists them differ by `difference` in the outcome of the running service `service`. The requests
  are equal, so nothing outside tells which answer belongs to which. `definition` is the target of the first group that
  `assigned` changes.
  -/
  | assignment (definition : Syntax.Ref) (service : String) (assigned : List Assigned) (difference : Difference)
deriving Repr, Inhabited

derive_group ChoiceDependent

/--
The number of step orders that the search of one processing runs at most (stepOrderSearch). It bounds the orders of a
processing with many steps that touch the same values, whose count grows factorially.
-/
def stepOrderLimit : Nat := 64

/--
The number of assignments of handles of `requests` that the search of one scenario runs at most (assignmentSearch). It
bounds the assignments of many equal requests, whose count grows factorially.
-/
def assignmentLimit : Nat := 64

/--
The result of a run: the violation that halted it, the trace lines that verify reads, its records, and the keys that its
participants created, each with its domain `<participant>/<entity>` as verify's valueDomains names a key reference's.
-/
structure Outcome where
  halted : Option Violation
  lines : List TraceLine
  records : Value
  created : List (String × String)

/--
The records as the relation compares them: each keyed entity as its encoded rows in key order, and each single entity
as its encoded row once it has one.
-/
def recordsValue (st : Service) (records : Records) : Value :=
  .obj (st.entities.filterMap fun e =>
    if e ∈ st.singles then (records.find? (·.entity == e)).map fun r => (e, r.value)
    else
      let rows := (records.filter (·.entity == e)).mergeSort fun a b => decide (a.key.getD "" ≤ b.key.getD "")
      some (e, .arr (rows.map (·.value))))

/--
The outcome of a run as the relation compares it: only the violation that halted the run, or else its trace lines and
its records.
-/
def Outcome.of (st : Service) (halted : Option Violation) (lines : List TraceLine) (records : Records)
    (created : List (String × String)) : Outcome :=
  match halted with
  | some v => { halted := some v, lines := [], records := .null, created := [] }
  | none => { halted := none, lines, records := recordsValue st records, created }

/--
The first violation that verify finds in the second lines, with the first lines as the snapshot, or else the set of
bindings that agree with every line (Data/Binding).
-/
abbrev Compare (m : Type → Type) := List TraceLine → List TraceLine → m (Except Violation (List Binding))

/-- Records as matchValue compares them: each keyed entity's rows as a bag, since renamed keys no longer order them. -/
def recordsCValue : Value → CValue
  | .obj entities => .obj (entities.map fun (entity, rows) => (entity, match rows with
      | .arr rows => .bag (rows.map CValue.ofValue)
      | row => CValue.ofValue row))
  | other => CValue.ofValue other

/--
Whether the records of `original` and `alternative` are equal under one of the bindings `set`, extended by a renaming
of the created keys of `original` (one to one within each entity's keys, created keys only). Matches over bindingLimit
count as a difference, never as equal.
-/
def sameRecords (set : List Binding) (original alternative : Outcome) : Bool :=
  let v : Values := { domain := fun s => (original.created.lookup s).getD "", fresh := original.created.map (·.1) }
  set.any fun b =>
    match matchValue v b (recordsCValue original.records) (recordsCValue alternative.records) with
    | some (_ :: _) => true
    | _ => false

/-- The identity of a halting violation. Two halting violations differ when their kinds or data differ. -/
def haltIdentity : Option Violation → Option (String × String)
  | some v => some (v.kind, v.data.canonical)
  | none => none

section

variable {m : Type → Type} [Monad m]

/--
The first difference: the halting violations, then the outputs as `compare` finds them with `original` as the
snapshot, then the records, which later inputs read, under the bindings of the outputs (sameRecords). Two outcomes
without a difference are equal up to a renaming of their created keys (symmetry, as TLA+ symmetry sets reduce states).
Outputs that `compare` cannot compare with themselves, as when equal requests get different answers, tell no choice
apart, so only the records are compared then.
-/
def difference (compare : Compare m) (original alternative : Outcome) :
    m (Option Difference) := do
  if original.halted.isSome || alternative.halted.isSome then
    return if haltIdentity original.halted == haltIdentity alternative.halted then none
      else some (.halt original.halted alternative.halted)
  let records (set : List Binding) : Option Difference :=
    if sameRecords set original alternative then none else some (.records original.records alternative.records)
  match ← compare original.lines alternative.lines with
  | .ok set => return records set
  | .error mismatch =>
    match ← compare original.lines original.lines with
    | .ok _ => return some (.outputs mismatch)
    | .error _ => return records [.empty]

/--
The ChoiceDependent violation, if any, for the order of steps `a` and `b`. `aFirst` takes `a` first and is the walk with
the step order `aOrder`, and `bFirst` takes `b` first and is the walk with `bOrder`. The pair is in the order of their
canonical texts.
-/
def stepOrder (compare : Compare m) (a b : StepName) (aOrder bOrder : List StepName) (aFirst bFirst : Outcome) :
    m (Option ChoiceDependent) := do
  let (first, second, firstOrder, secondOrder, original, alternative) :=
    if (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical then (a, b, aOrder, bOrder, aFirst, bFirst)
    else (b, a, bOrder, aOrder, bFirst, aFirst)
  return (← difference compare original alternative).map
    (.stepOrder first.definition first second firstOrder secondOrder)

/--
The ChoiceDependent violation, if any, for the assignment `assigned` of handles of `requests`: the first difference,
in the order of `outcomes`, between the outcome of a running service in the walk with each handle at its own place and
in the walk with `assigned`. `definition` is the target of the first group that `assigned` changes.
-/
def assignment (compareFor : String → Compare m) (definition : Syntax.Ref) (assigned : List Assigned)
    (outcomes : List (String × Outcome × Outcome)) : m (Option ChoiceDependent) :=
  outcomes.foldlM (init := none) fun found (service, original, alternative) => do
    if found.isSome then return found
    return (← difference (compareFor service) original alternative).map (.assignment definition service assigned)

end

end Tazuna.Observe
