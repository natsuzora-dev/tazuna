import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Observe.Instrument
import Tazuna.Service.Message
import Tazuna.Service.Note
import Tazuna.Service.Basic
import Tazuna.Service.Records
import Tazuna.Sim.Run

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
A result that depends on an order nobody controls: the order of two steps of one processing that no cause orders.
Every other order of a simulation is a written line. stepOrder writes the pair in canonical order.
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
  that the search swapped.
  -/
  | searchLimit (definition : Syntax.Ref) (limit : Nat)
deriving Repr, Inhabited

derive_group ChoiceDependent

/--
The number of step orders that the search of one processing runs at most (stepOrderSearch). It bounds the orders of a
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
  match bindings.substitute records with
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

end

/-- A walk of a scenario, with what each running service's instrumented functions collected. -/
structure Walk where
  world : Sim.World
  collect : String → Collect

/-- The span of the walk's processing `origin` of `service`. -/
def Walk.span? (w : Walk) (origin : Scenario.Origin) (service : String) : Option Sim.Span :=
  w.world.spans.find? fun s => s.service == service && s.origin == origin

/--
The steps that the internal queue of the processing of `span` took, by step number and name, in the order they began:
those that began while no step was open, except the steps of deadlines and barriers, which no order takes.
-/
def Walk.taken (w : Walk) (span : Sim.Span) : List (Nat × StepName) :=
  let s := w.world.state span.service
  (w.collect span.service).steps.toList.filterMap fun (n, a) =>
    let deadline := match a.name with
      | .deadline .. => true
      | _ => false
    if span.stepsFrom ≤ n && n < span.stepsTo && !deadline && !(s.steps[n]?.any (·.barrier)) then some (n, a.name)
    else none

/--
Whether the service of `span` halted while the processing of `span` ran: it halted, and the processing is its last.
A service acts once per origin, and a halted service acts no more.
-/
def Walk.haltedIn (w : Walk) (span : Sim.Span) : Bool :=
  (w.world.state span.service).halted.isSome &&
    ((w.world.spans.filter (·.service == span.service)).getLast?.map (·.origin)) == some span.origin

/--
The candidates of the processing of `span`: none when its service halted in it, which skips the steps after the halt,
and otherwise those of its steps, whether or not a later processing halts.
-/
def Walk.candidatesOf (w : Walk) (span : Sim.Span) : List (Nat × Nat) :=
  if w.haltedIn span then [] else
  (candidates { w.world.state span.service with halted := none } (w.collect span.service) none).filter
    fun (i, _) => span.stepsFrom ≤ i && i < span.stepsTo

/--
Whether the walk refused its step order for `service`: the service halted because the order named a step that was not
ready, or left entries unused. A walk without an order refuses none, so these are exactly the orders that no queue could
take.
-/
def Walk.refused (w : Walk) (service : String) : Bool :=
  match (w.world.state service).halted with
  | some v => v.kind == "InvalidInput.unreadyStep" || v.kind == "InvalidInput.unusedStepOrder"
  | none => false

/-- What the relation compares of the walk for the running service `st`. -/
def Walk.outcome (w : Walk) (st : Service) : Outcome :=
  let s := w.world.state st.service
  let lines := (trace s (w.collect st.service).causes).map fun (line, after, created) => traceLineOf line after created
  Outcome.of st s.halted lines s.records

/-- The verdict of the search on one step order: refused (Walk.refused), or the violation found, if any. -/
inductive Verdict where
  | refused
  | decided (found : Option ChoiceDependent)
deriving Repr, Inhabited

/-- A step order that the search ran, and its verdict. -/
structure Tried where
  order : List StepName
  verdict : Verdict
deriving Repr, Inhabited

/--
What the search of one processing did: each step order it ran in turn, and the violations it reports, each stepOrder
violation once as first found (by pair and difference), then searchLimit when it stopped with orders left.
-/
structure Search where
  tried : List Tried := []
  found : List ChoiceDependent := []
deriving Repr, Inhabited

/-- The identity of a found violation, by which the search reports it once. -/
def findingKey : ChoiceDependent → String
  | .stepOrder _ first second _ _ difference =>
    (Value.arr [ToValue.toValue first, ToValue.toValue second, ToValue.toValue difference]).canonical
  | .searchLimit .. => ""

/--
The order that runs the pair `(i, j)` of a walk's candidates the other way: the steps before `i` as the walk took them,
then the steps between that lead to `j`, then `b` (step `j`) and `a` (step `i`).
-/
def pairOrder (s : State) (taken : List (Nat × StepName)) (i j : Nat) (a b : StepName) : List StepName :=
  (taken.filter (·.1 < i)).map (·.2) ++ (taken.filter fun (n, _) => i < n && n < j && leadsTo s n j).map (·.2) ++ [b, a]

/-- The state of a search: what it did, the taken-step sequences it reached, the first step it swapped, and its queue. -/
structure Searching where
  search : Search := {}
  reached : List (List StepName)
  first : Option StepName := none
  /-- The walks left to search, each with its step order. -/
  queue : List (Walk × List StepName)
  stopped : Bool := false

section

variable {m : Type → Type} [Monad m]

/--
The search after the pair `(i, j)` of the walk `parent`, whose step order is `parentOrder`: the pair's order
(pairOrder) is run unless it ran before, compared with `parent` unless refused, and queued when it reaches a new
sequence of taken steps. At stepOrderLimit orders the search stops with searchLimit at the first step it swapped.
-/
def searchPair (compare : Compare m) (walkWith : List StepName → m Walk) (origin : Scenario.Origin) (st : Service)
    (parent : Walk) (parentOrder : List StepName) (parentOutcome : Outcome) (taken : List (Nat × StepName))
    (r : Searching) (pair : Nat × Nat) : m Searching := do
  let (i, j) := pair
  if r.stopped then return r
  let (some a, some b) := (taken.lookup i, taken.lookup j) | return r
  let order := pairOrder (parent.world.state st.service) taken i j a b
  if r.search.tried.any (·.order == order) then return r
  let first := r.first.getD a
  if r.search.tried.length == stepOrderLimit then
    return { r with stopped := true, first := some first,
                    search := { r.search with found := r.search.found ++ [.searchLimit first.definition stepOrderLimit] } }
  let r := { r with first := some first }
  let alternative ← walkWith order
  if alternative.refused st.service then
    return { r with search := { r.search with tried := r.search.tried ++ [{ order, verdict := .refused }] } }
  let found ← stepOrder compare a b parentOrder order parentOutcome (alternative.outcome st)
  let fresh := found.filter fun v => !r.search.found.any (findingKey · == findingKey v)
  let r := { r with search := { tried := r.search.tried ++ [{ order, verdict := .decided found }],
                                found := r.search.found ++ fresh.toList } }
  let some altSpan := alternative.span? origin st.service | return r
  let sequence := (alternative.taken altSpan).map (·.2)
  if r.reached.contains sequence then return r
  return { r with reached := r.reached ++ [sequence], queue := r.queue ++ [(alternative, order)] }

/-- The search after the walks of its queue, at most `fuel` of them. -/
def searchQueue (compare : Compare m) (walkWith : List StepName → m Walk) (origin : Scenario.Origin) (st : Service) :
    Nat → Searching → m Searching
  | 0, r => pure r
  | fuel + 1, r =>
    match r.queue with
    | [] => pure r
    | (walked, order) :: rest => do
      if r.stopped then return r
      let r := { r with queue := rest }
      let some span := walked.span? origin st.service | searchQueue compare walkWith origin st fuel r
      let taken := walked.taken span
      let r ← (walked.candidatesOf span).foldlM
        (searchPair compare walkWith origin st walked order (walked.outcome st) taken) r
      searchQueue compare walkWith origin st fuel r

/--
The search of the step orders of the processing `origin` of the running service `st` that change its result, from
`base`, the scenario walked up to that processing without an order; `walkWith` walks it with a step order of the
processing. Each pair of a walk's candidates runs in the other order (pairOrder) and is compared with that walk, and
each walk that reaches a new sequence of taken steps is searched in turn, so the search reaches every order of
dependent steps (dynamic partial-order reduction, Flanagan and Godefroid, POPL 2005), up to stepOrderLimit orders.
Each queued walk follows a new order, so stepOrderLimit + 1 walks bound the queue.
-/
def stepOrderSearch (compare : Compare m) (walkWith : List StepName → m Walk) (origin : Scenario.Origin)
    (st : Service) (base : Walk) : m Search := do
  let some span := base.span? origin st.service | return {}
  if (base.candidatesOf span).isEmpty then return {}
  let r ← searchQueue compare walkWith origin st (stepOrderLimit + 1)
    { reached := [(base.taken span).map (·.2)], queue := [(base, [])] }
  return r.search

/-- The search of the processing `origin` of `service`. -/
structure Searched where
  origin : Scenario.Origin
  service : String
  search : Search

/--
The searches of the processings of the walk `walked` of the scenario `sc` whose origin is the begin (when `from` is 0)
or a line from `from` on, each processing once, that have candidates: each on the scenario walked up to its line
(`walkWith` walks a scenario with step orders), so a later halt hides none. `compareFor` compares the trace
lines of a service.
-/
def stepOrderChanges (compareFor : String → Compare m)
    (walkWith : Scenario → List (Scenario.Origin × String × List StepName) → m Walk) (sc : Scenario) (walked : Walk)
    («from» : Nat) : m (List Searched) := do
  let spans := walked.world.spans.foldl (fun (seen : List Sim.Span) span =>
    let index := match span.origin with
      | .begin => none
      | .line i => some i
    let inRange := match index with
      | none => «from» == 0
      | some i => «from» ≤ i
    if !inRange || seen.any (fun s => s.origin == span.origin && s.service == span.service) then seen
    else seen ++ [span]) []
  spans.filterMapM fun span => do
    if (walked.candidatesOf span).isEmpty then return none
    let some st := walked.world.services.lookup span.service | return none
    let count := match span.origin with
      | .begin => 0
      | .line i => i + 1
    let pre := { sc with lines := sc.lines.take count, expectations := [] }
    let base ← walkWith pre []
    let search ← stepOrderSearch (compareFor span.service)
      (fun order => walkWith pre [(span.origin, span.service, order)]) span.origin st base
    if search.tried.isEmpty && search.found.isEmpty then return none
    return some { origin := span.origin, service := span.service, search }

end

end Tazuna.Observe
