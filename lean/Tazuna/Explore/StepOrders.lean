import Tazuna.Explore.ChoiceDependent
import Tazuna.Sim.Run

/-!
The step-order search: it executes a scenario's simulation again with other orders of the steps that no cause orders, and
compares each execution's outcome by ChoiceDependent.stepOrder.
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/-- An execution of a scenario, with what each running service's instrumented functions collected. -/
structure Execution where
  world : Sim.World
  collect : String → Collect

/-- The span of the execution's processing `origin` of `service`. -/
def Execution.span? (w : Execution) (origin : Scenario.Origin) (service : String) : Option Sim.Span :=
  w.world.spans.find? fun s => s.service == service && s.origin == origin

/--
The steps of the processing of `span` that an order takes, by step number and name, in the order they began: those
that the internal queue took when no step was open, and the deadlines of ties. Barriers and other
deadlines take no order.
-/
def Execution.taken (w : Execution) (span : Sim.Span) : List (Nat × StepName) :=
  let s := w.world.state span.service
  (w.collect span.service).steps.toList.filterMap fun (n, a) =>
    let fixed := (a.name.isDeadline && (s.steps[n]?.bind (·.tie)).isNone) || s.steps[n]?.any (·.barrier)
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
  let st := (w.world.services.lookup span.service).getD default
  (candidates st { w.world.state span.service with halted := none } (w.collect span.service) none).filter
    fun (i, _) => span.stepsFrom ≤ i && i < span.stepsTo

/--
Whether the execution refused its step order for `service`: the service halted because the order named a step that was not
ready, or left entries unused. An execution without an order refuses none, so these are exactly the orders that no queue could
take.
-/
def Execution.refused (w : Execution) (service : String) : Bool :=
  match (w.world.state service).halted with
  | some v => v.kind == "InvalidInput.unreadyStep" || v.kind == "InvalidInput.unusedStepOrder"
  | none => false

/-- What the relation compares of the execution for the running service `st`. -/
def Execution.outcome (w : Execution) (st : Service) : Explore.Outcome :=
  let s := w.world.state st.service
  let lines := (Sim.trace s (w.collect st.service).causes).map fun (line, after, created) => Sim.traceLineOf line after created
  Outcome.of st s.halted lines s.records (w.world.states.flatMap fun (q, x) =>
    x.created.map fun (entity, key) => (key, s!"{q}/{entity}"))

/-- The verdict of the search on one step order: refused (Execution.refused), or the violation found, if any. -/
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
  | .searchLimit .. | .assignment .. => ""

/--
The order that runs the pair `(i, j)` of an execution's candidates the other way: the steps before `i` as the execution took them,
then the steps between that lead to `j`, then `b` (step `j`) and `a` (step `i`).
-/
def pairOrder (s : State) (taken : List (Nat × StepName)) (i j : Nat) (a b : StepName) : List StepName :=
  (taken.filter (·.1 < i)).map (·.2) ++ (taken.filter fun (n, _) => i < n && n < j && Sim.leadsTo s n j).map (·.2) ++ [b, a]

/-- The state of a search: what it did, the taken-step sequences it reached, the first step it swapped, and its queue. -/
structure Searching where
  search : Search := {}
  reached : List (List StepName)
  first : Option StepName := none
  /-- The executions left to search, each with its step order. -/
  queue : List (Execution × List StepName)
  stopped : Bool := false

section

variable {m : Type → Type} [Monad m]

/--
The search after the pair `(i, j)` of the execution `parent`, whose step order is `parentOrder`: the pair's order
(pairOrder) is run unless it ran before, compared with `parent` unless refused, and queued when it reaches a new
sequence of taken steps. At stepOrderLimit orders the search stops with searchLimit at the first step it swapped.
-/
def searchPair (compare : Compare m) (executeWith : List StepName → m Execution) (origin : Scenario.Origin) (st : Service)
    (parent : Execution) (parentOrder : List StepName) (parentOutcome : Explore.Outcome) (taken : List (Nat × StepName))
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
  let alternative ← executeWith order
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

/-- The search after the executions of its queue, at most `fuel` of them. -/
def searchQueue (compare : Compare m) (executeWith : List StepName → m Execution) (origin : Scenario.Origin) (st : Service) :
    Nat → Searching → m Searching
  | 0, r => pure r
  | fuel + 1, r =>
    match r.queue with
    | [] => pure r
    | (executed, order) :: rest => do
      if r.stopped then return r
      let r := { r with queue := rest }
      let some span := executed.span? origin st.service | searchQueue compare executeWith origin st fuel r
      let taken := executed.taken span
      let r ← (executed.candidatesOf span).foldlM
        (searchPair compare executeWith origin st executed order (executed.outcome st) taken) r
      searchQueue compare executeWith origin st fuel r

/--
The search of the step orders of the processing `origin` of the running service `st` that change its result, from
`base`, the scenario executed up to that processing without an order; `executeWith` executes it with a step order of the
processing. Each pair of an execution's candidates runs in the other order (pairOrder) and is compared with that execution, and
each execution that reaches a new sequence of taken steps is searched in turn, so the search reaches every order of
dependent steps (dynamic partial-order reduction, Flanagan and Godefroid, POPL 2005), up to stepOrderLimit orders.
Each queued execution follows a new order, so stepOrderLimit + 1 executions bound the queue.
-/
def stepOrderSearch (compare : Compare m) (executeWith : List StepName → m Execution) (origin : Scenario.Origin)
    (st : Service) (base : Execution) : m Search := do
  let some span := base.span? origin st.service | return {}
  if (base.candidatesOf span).isEmpty then return {}
  let r ← searchQueue compare executeWith origin st (stepOrderLimit + 1)
    { reached := [(base.taken span).map (·.2)], queue := [(base, [])] }
  return r.search

/-- The search of the processing `origin` of `service`. -/
structure Searched where
  origin : Scenario.Origin
  service : String
  search : Search

/--
The searches of the processings of the execution `executed` of the scenario `sc` whose origin is the startup (when `from` is 0)
or a line from `from` on, each processing once, that have candidates: each on the scenario executed up to its line
(`executeWith` executes a scenario with step orders), so a later halt hides none. `compareFor` compares the trace
lines of a service.
-/
def stepOrderChanges (compareFor : String → Compare m)
    (executeWith : Scenario → List (Scenario.Origin × String × List StepName) → m Execution) (sc : Scenario) (executed : Execution)
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
    if search.tried.isEmpty && search.found.isEmpty then return none
    return some { origin := span.origin, service := span.service, search }

end

end Tazuna.Explore
