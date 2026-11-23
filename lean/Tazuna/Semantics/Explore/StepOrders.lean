import Tazuna.Semantics.Explore.ChoiceDependent
import Tazuna.Semantics.Sim.Run
import Tazuna.Semantics.Sim.Trace

/-!
The step-order search: it executes a scenario's simulation again with other orders of the steps that no cause orders, and
compares each execution's outcome by ChoiceDependent.stepOrder.
-/

namespace Tazuna.Semantics.Explore

open Tazuna.Ir Tazuna.Semantics.Service
open Tazuna.Semantics.Scenario (Origin)

/-- An execution of a scenario, with what each running service's instrumented functions collected. -/
structure Execution where
  world : Sim.World
  collect : String → Collect

/-- The span of the execution's processing of `service` while `o` was processed. -/
def Execution.span? (w : Execution) (o : Origin) (service : String) : Option Sim.Span :=
  w.world.spans.find? fun s => s.service == service && s.origin == o

/--
The steps of the processing of `span` that an order takes, by step number and name, in the order they began: those
that the internal queue took when no step was open, and the deadlines of ties. Barriers and other
deadlines take no order.
-/
def Execution.taken (w : Execution) (span : Sim.Span) : List (Nat × StepName) :=
  let s := w.world.state span.service
  (w.collect span.service).steps.toList.filterMap fun (n, a) =>
    let fixed := (a.name.isDeadline && (s.steps[n]?.bind (·.origin.tie)).isNone) || s.steps[n]?.any (·.barrier)
    if span.stepsFrom ≤ n && n < span.stepsTo && !fixed then some (n, a.name) else none

/--
Whether the service of `span` halted while the processing of `span` ran: it halted, and the processing is its last.
A service acts once per origin, and a halted service acts no more.
-/
def Execution.haltedIn (w : Execution) (span : Sim.Span) : Bool :=
  (w.world.state span.service).halted.isSome &&
    ((w.world.spans.filter (·.service == span.service)).getLast?.map (·.origin)) == some span.origin

/--
The candidates of the processing of `span`: none when its service halted in it, which skips the steps after the halt,
and otherwise those of its steps, whether or not a later processing halts.
-/
def Execution.candidatesOf (w : Execution) (span : Sim.Span) : List (Nat × Nat) :=
  if w.haltedIn span then [] else
  (candidates { w.world.state span.service with halted := none } (w.collect span.service) none).filter
    fun (i, _) => span.stepsFrom ≤ i && i < span.stepsTo

/--
Whether the execution refused its step order for `service`: the service halted because the order named a step that was not
ready, or left entries unused. An execution without an order refuses none, so these are exactly the orders that no queue could
take.
-/
def Execution.refused (w : Execution) (service : String) : Bool :=
  match (w.world.state service).halted with
  | some (.invalidInput (.unreadyStep ..)) | some (.invalidInput (.unusedStepOrder _)) => true
  | _ => false

/-- What the relation compares of the execution for the running service `st`, whose state is `s`. -/
def Execution.outcomeWith (w : Execution) (st : Service) (s : Service.State) : Explore.Outcome :=
  let lines := (Sim.trace s).map fun (line, after, created) => Sim.traceLineOf st.service line after created
  Outcome.of st (s.halted.map (·.toViolation)) lines s (w.world.states.flatMap fun (q, x) =>
    x.created.map fun (entity, key) => (key, s!"{q}/{entity}"))

/-- What the relation compares of the execution for the running service `st`. -/
def Execution.outcome (w : Execution) (st : Service) : Explore.Outcome :=
  w.outcomeWith st (w.world.state st.service)

/-- The ids of the `in` lines of `span` in `s`: the messages that the processing took, in the order it took them. -/
def inIds (s : Service.State) (span : Sim.Span) : List LineId :=
  ((s.lines.extract span.from span.to).toList.filter (·.dir == .in)).map (·.id)

/--
`s` with the lines of `span` in the order of the messages `ids`: each `in` line moves with the `out` lines after it, so
two runs that took the messages of a tie in other orders compare by message, as verify pairs a trace's `in` lines with
the snapshot's.
-/
def alignTo (ids : List LineId) (span : Sim.Span) (s : Service.State) : Service.State :=
  let lines := (s.lines.extract span.from span.to).toList
  let pre := lines.takeWhile (·.dir != .in)
  let windows := ((lines.drop pre.length).foldl (fun (ws : List (List Line)) l =>
    if l.dir == .in then [l] :: ws else match ws with
      | w :: more => (l :: w) :: more
      | [] => [[l]]) []).reverse.map List.reverse
  let key (window : List Line) := (window.head?.bind fun l => ids.idxOf? l.id).getD ids.length
  let sorted := windows.mergeSort fun a b => decide (key a ≤ key b)
  { s with lines := s.lines.extract 0 span.from ++ (pre ++ sorted.flatten).toArray ++ s.lines.extract span.to s.lines.size }

/-- The verdict of the search on one step order: refused (Execution.refused), or the violation found, if any. -/
inductive Verdict where
  | refused
  | decided (found : Option Violation)
deriving Repr, Inhabited

/-- A step order that the search ran, and its verdict. -/
structure Tried where
  order : List StepName
  verdict : Verdict
deriving Repr, Inhabited

/--
What the search of one processing did: each step order it ran in turn, and the violation it reports. The search stops at
its first violation, as Concuerror, loom, and shuttle stop at the first failing schedule: Undecided.stepOrderLimit when it ran
stepOrderLimit orders with orders left, and otherwise the first order whose outcome differs.
-/
structure Search where
  tried : List Tried := []
  found : Option Violation := none
deriving Repr, Inhabited

/--
The order that runs the pair `(i, j)` of an execution's candidates the other way: the steps before `i` as the execution took them,
then the steps between that lead to `j`, then `b` (step `j`) and `a` (step `i`).
-/
def pairOrder (s : Service.State) (taken : List (Nat × StepName)) (i j : Nat) (a b : StepName) : List StepName :=
  (taken.filter (·.1 < i)).map (·.2) ++ (taken.filter fun (n, _) => i < n && n < j && leadsTo s n j).map (·.2) ++ [b, a]

/--
The outcome of `alternative` for the running service `st`, with the lines of its processing while `o` was processed in
the order in which `parent` took their messages (alignTo).
-/
def aligned (o : Origin) (st : Service) (parent alternative : Execution) : Explore.Outcome :=
  match parent.span? o st.service, alternative.span? o st.service with
  | some ps, some alt =>
    alternative.outcomeWith st (alignTo (inIds (parent.world.state st.service) ps) alt
      (alternative.world.state st.service))
  | _, _ => alternative.outcome st

/-- The state of a search: what it did, the taken-step sequences it reached, the first step it swapped, and its queue. -/
structure Searching where
  search : Search := {}
  reached : List (List StepName)
  first : Option StepName := none
  /-- The executions left to search, each with its step order. -/
  queue : List (Execution × List StepName)

section

variable {m : Type → Type} [Monad m]

/--
The search after the pair `(i, j)` of the execution `parent`, whose step order is `parentOrder`: unless the search
found a violation, the pair's order (pairOrder) is run unless it ran before or undoes the swap that made `parent` (its
order ends with `a` then `b`), compared with `parent` unless refused, and queued when it reaches a new sequence of taken
steps. At stepOrderLimit orders the search stops with Undecided.stepOrderLimit at the first step it swapped.

The undo is skipped to save its execution and its share of stepOrderLimit. Running it would find nothing: `parent` was
queued only because its outcome equals that of the execution `g` that it came from, and the undo runs `g`'s order of
the pair again. Skipping it misses no order either. If `a` conflicts with a step between, `g` reverses that pair itself.
If a step between conflicts with `b`, `g` reverses that pair, and its order is the skipped one. Otherwise the skipped
order commutes to the order of `g`. This rests on the premises of the search (steps whose reads and writes do not
overlap commute, and each race is reversed at the execution where it occurs), not on sleep sets, which carry a set down
every branch.
-/
def searchPair (compare : Compare m) (executeWith : List StepName → m Execution) (o : Origin) (st : Service)
    (parent : Execution) (parentOrder : List StepName) (parentOutcome : Explore.Outcome) (taken : List (Nat × StepName))
    (r : Searching) (pair : Nat × Nat) : m Searching := do
  let (i, j) := pair
  if r.search.found.isSome then return r
  let (some a, some b) := (taken.lookup i, taken.lookup j) | return r
  if parentOrder.drop (parentOrder.length - 2) == [a, b] then return r
  let order := pairOrder (parent.world.state st.service) taken i j a b
  if r.search.tried.any (·.order == order) then return r
  let first := r.first.getD a
  if r.search.tried.length == stepOrderLimit then
    return { r with first := some first,
                    search := { r.search with
                      found := some (Undecided.stepOrderLimit (first.definition st.service) stepOrderLimit).toViolation } }
  let r := { r with first := some first }
  let alternative ← executeWith order
  if alternative.refused st.service then
    return { r with search := { r.search with tried := r.search.tried ++ [{ order, verdict := .refused }] } }
  let found ← stepOrder compare st.service a b parentOrder order parentOutcome (aligned o st parent alternative)
  let r := { r with search := { tried := r.search.tried ++ [{ order, verdict := .decided found }], found } }
  if found.isSome then return r
  let some altSpan := alternative.span? o st.service | return r
  let sequence := (alternative.taken altSpan).map (·.2)
  if r.reached.contains sequence then return r
  return { r with reached := r.reached ++ [sequence], queue := r.queue ++ [(alternative, order)] }

/--
The search after the executions of its queue, at most `fuel` of them. stepOrderSearch gives fuel for every execution that
the queue can hold, so running out with executions left is a bug.
-/
def searchQueue [MonadNote m] (compare : Compare m) (executeWith : List StepName → m Execution) (o : Origin)
    (st : Service) : Nat → Searching → m Searching
  | 0, r => do
    if r.search.found.isNone && !r.queue.isEmpty then
      MonadNote.note (.bug "the step-order queue holds more than stepOrderLimit + 1 executions")
    pure r
  | fuel + 1, r =>
    match r.queue with
    | [] => pure r
    | (executed, order) :: rest => do
      if r.search.found.isSome then return r
      let r := { r with queue := rest }
      let some span := executed.span? o st.service | searchQueue compare executeWith o st fuel r
      let taken := executed.taken span
      let r ← (executed.candidatesOf span).foldlM
        (searchPair compare executeWith o st executed order (executed.outcome st) taken) r
      searchQueue compare executeWith o st fuel r

/--
The search of the step orders of the processing while `o` is processed of the running service `st` that change its
result, from `base`, the scenario executed up to that processing without an order; `executeWith` executes it with a step
order of the processing. Each pair of an execution's candidates runs in the other order (pairOrder) and is compared with
that execution, and each execution that reaches a new sequence of taken steps is searched in turn, so the search reaches
every order of dependent steps (dynamic partial-order reduction, Flanagan and Godefroid, POPL 2005), up to
stepOrderLimit orders or its first violation. Each queued execution follows a new order, so stepOrderLimit + 1
executions bound the queue.
-/
def stepOrderSearch [MonadNote m] (compare : Compare m) (executeWith : List StepName → m Execution) (o : Origin)
    (st : Service) (base : Execution) : m Search := do
  let some span := base.span? o st.service | return {}
  if (base.candidatesOf span).isEmpty then return {}
  let r ← searchQueue compare executeWith o st (stepOrderLimit + 1)
    { reached := [(base.taken span).map (·.2)], queue := [(base, [])] }
  return r.search

/-- The search of the processing of `service` while `origin` was processed. -/
structure Searched where
  origin : Origin
  service : String
  search : Search

/--
The searches of the processings of the execution `executed` of the scenario `sc` whose origin is the startup (when `from`
is 0) or a line from `from` on, each processing once, that have candidates: each on the
scenario executed up to its line (`executeWith` executes a scenario with step orders), so a later halt hides none.
`compareFor` compares the trace lines of a service.
-/
def stepOrderChanges [MonadNote m] (compareFor : String → Compare m)
    (executeWith : Scenario → List (Origin × String × List StepName) → m Execution) (sc : Scenario) (executed : Execution)
    («from» : Nat) : m (List Searched) := do
  let spans := executed.world.spans.foldl (fun (seen : List Sim.Span) span =>
    let index := match span.origin with
      | .startup => none
      | .line i => some i
    let inRange := match index with
      | none => «from» == 0
      | some i => «from» ≤ i
    if !inRange || seen.any (fun s => s.origin == span.origin && s.service == span.service) then seen
    else seen ++ [span]) []
  spans.filterMapM fun span => do
    if (executed.candidatesOf span).isEmpty then return none
    let some st := executed.world.services.lookup span.service | return none
    let count := match span.origin with
      | .startup => 0
      | .line i => i + 1
    let pre := { sc with lines := sc.lines.take count, expectations := [] }
    let base ← executeWith pre []
    let search ← stepOrderSearch (compareFor span.service)
      (fun order => executeWith pre [(span.origin, span.service, order)]) span.origin st base
    if search.tried.isEmpty && search.found.isNone then return none
    return some { origin := span.origin, service := span.service, search }

end

end Tazuna.Semantics.Explore
