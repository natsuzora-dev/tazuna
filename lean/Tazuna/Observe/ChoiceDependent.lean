import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Service.Message
import Tazuna.Service.Note
import Tazuna.Service.Basic
import Tazuna.Service.Records

namespace Tazuna.Observe

open Tazuna.Data Tazuna.Semantics

/--
A difference between the results of two runs. `original` is the result of the order that the violation names first
(the first step of the pair before the second), and `alternative` is the result of the other.
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
A result that depends on an order nobody controls: the order of two steps of one processing that no cause orders,
between two walks of a scenario that differ only in it. Every other order of a simulation is a written line. stepOrder
writes the pair in canonical order.
-/
inductive ChoiceDependent where
  /-- `definition` is the definition of the first step. -/
  | stepOrder (definition : Syntax.Ref) (firstStep secondStep : StepName) (difference : Difference)
  /--
  The search of the step orders of one processing ran `limit` (stepOrderLimit) orders and stopped with orders left, so
  a result that only those change is not reported. `definition` is the definition of the first step of the first pair
  that the search swapped.
  -/
  | searchLimit (definition : Syntax.Ref) (limit : Nat)
deriving Repr, Inhabited

derive_group ChoiceDependent

/--
The number of step orders that the search of one processing runs at most. The search runs the other order of each pair
of a run's candidates, and of each run it reaches so, until no new order is left; this bounds the orders of a
processing with many steps that touch the same values, whose count grows factorially.
-/
def stepOrderLimit : Nat := 64

/-- The result of a run: the violation that halted it, the trace lines that verify reads, and its records. -/
structure Outcome where
  halted : Option Violation
  lines : List TraceLine
  records : Value

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
def Outcome.of (st : Service) (halted : Option Violation) (lines : List TraceLine) (records : Records) : Outcome :=
  match halted with
  | some v => { halted := some v, lines := [], records := .null }
  | none => { halted := none, lines, records := recordsValue st records }

/--
The first violation that verify finds in the second lines, with the first lines as the snapshot, or else the bindings
of the createKey values of the first lines to those of the second.
-/
abbrev Compare (m : Type → Type) := List TraceLine → List TraceLine → m (Except Violation Bindings)

/--
The text of records as the relation compares them, with each string that `bindings` binds replaced by its first bound
value, and each keyed entity's rows in the order of their texts, since the replaced keys no longer give their order.
-/
def recordsText (bindings : Bindings) (records : Value) : String :=
  match bindings.rename records with
  | .obj entities =>
    objectText (entities.map fun (entity, rows) => (entity, match rows with
      | .arr rows => arrayText ((rows.map (·.canonical)).mergeSort fun a b => decide (a ≤ b))
      | row => row.canonical))
  | other => other.canonical

/-- The identity of a halting violation. Two halting violations differ when their kinds or data differ. -/
def haltIdentity : Option Violation → Option (String × String)
  | some v => some (v.kind, v.data.canonical)
  | none => none

section

variable {m : Type → Type} [Monad m]

/--
The first difference: the halting violations, then the outputs as `compare` finds them with `original` as the
snapshot, then the records, which later inputs read, with the createKey values of `original` replaced by the values of
`alternative` that the outputs bind them to.
-/
def difference (compare : Compare m) (original alternative : Outcome) :
    m (Option Difference) := do
  if original.halted.isSome || alternative.halted.isSome then
    return if haltIdentity original.halted == haltIdentity alternative.halted then none
      else some (.halt original.halted alternative.halted)
  match ← compare original.lines alternative.lines with
  | .error mismatch => return some (.outputs mismatch)
  | .ok bindings =>
    return if recordsText bindings original.records == recordsText [] alternative.records then none
      else some (.records original.records alternative.records)

/--
The ChoiceDependent violation, if any, for the order of steps `a` and `b`. `aFirst` takes `a` first, and `bFirst` takes
`b` first. The pair is in the order of their canonical texts.
-/
def stepOrder (compare : Compare m) (a b : StepName) (aFirst bFirst : Outcome) : m (Option ChoiceDependent) := do
  let (first, second, original, alternative) :=
    if (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical then (a, b, aFirst, bFirst)
    else (b, a, bFirst, aFirst)
  return (← difference compare original alternative).map (.stepOrder first.definition first second)

end

end Tazuna.Observe
