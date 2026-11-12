import Tazuna.Semantics.System.Run
import Tazuna.Observe.OrderDependent
import Tazuna.Observe.Trace

/-!
This module defines the instrumented run. It wraps Functions without changing the semantic run, collects the values
that each step and transition reads and writes, and checks whether query output depends on record order. TS records
reads as functions read records.
-/

namespace Tazuna.Observe

open Tazuna.Data Tazuna.Semantics

/-- The name of a context field, unique across the kinds of value, as RecordPart.name names record parts. -/
def contextKey (resource field : String) : String := s!"context:{resource}.{field}"

/-- The name of being in a state, which also names the copy set of a map state. -/
def stateKey (resource state : String) : String := s!"state:{resource}@{state}"

def shownKey (resource slot : String) : String := s!"shown:{resource}:{slot}"

/--
The values that a step reads and writes, by name. `keyWrites` holds the key sets of entities, which creating or
deleting a record writes.
-/
structure Footprint where
  reads : List String := []
  writes : List String := []
  keyWrites : List String := []
deriving Repr, Inhabited

def Footprint.union (a b : Footprint) : Footprint :=
  { reads := b.reads.foldl addNew a.reads, writes := b.writes.foldl addNew a.writes,
    keyWrites := b.keyWrites.foldl addNew a.keyWrites }

structure RecordAccess where
  reads : List RecordPart := []
  writes : List RecordPart := []
  keyWrites : List String := []
deriving Repr, Inhabited

def RecordAccess.union (a b : RecordAccess) : RecordAccess :=
  { reads := b.reads.foldl addNew a.reads, writes := b.writes.foldl addNew a.writes,
    keyWrites := b.keyWrites.foldl addNew a.keyWrites }

def RecordAccess.values (a : RecordAccess) : Footprint :=
  { reads := (a.reads.map (·.name)).foldl addNew [], writes := (a.writes.map (·.name)).foldl addNew [],
    keyWrites := a.keyWrites.map fun entity => (RecordPart.keys entity).name }

def uniqueReads (st : Service) (records : Records) (entity : String) (key : Option String) : List RecordPart :=
  match records.find? (fun r => r.entity == entity && r.key == key) with
  | none => []
  | some row =>
    let unique := st.uniqueOf entity
    if !uniqueChecked unique row.value then [] else
    .keys entity :: (records.filter (fun r => r.entity == entity && r.key != key)).flatMap fun r =>
      unique.map (.field entity r.key ·)

def eventFields (st : Service) (e : Emit) : List String :=
  match st.events.lookup e.event with
  | some (.create _ _ fields) | some (.update _ _ fields) | some (.delete _ _ fields) | some (.set _ fields) => fields
  | _ => []

def recordAccessOf (st : Service) (e : Emit) (ev : Evolved) : RecordAccess :=
  let fieldParts := (eventFields st e).map (.field ev.entity ev.key ·)
  match ev.change with
  | .create | .delete => { writes := ev.key.toList.map (.record ev.entity ·) ++ fieldParts, keyWrites := [ev.entity] }
  | .update => { writes := fieldParts }

def writesOf (st : Service) (records : Records) (emits : List Emit) : RecordAccess :=
  let (final, written, rows) := emits.foldl (fun (rs, acc, rows) e =>
    match evolve st rs e with
    | none => (rs, acc, rows)
    | some ev =>
      (ev.records, acc.union (recordAccessOf st e ev), if ev.change == .delete then rows else rows ++ [(ev.entity, ev.key)]))
    (records, ({} : RecordAccess), ([] : List (String × Option String)))
  written.union { reads := rows.foldl (fun acc (entity, key) => (uniqueReads st final entity key).foldl addNew acc) [] }

inductive Holder where
  | owner
  | copy
deriving DecidableEq, Repr, Inhabited

def Holder.resource (scope : Scope) : Holder → String
  | .owner => scope.owner
  | .copy => scope.resource

/-- The values that a chart function reads and writes. `shown` holds the owner's shows slots that it reads. -/
structure Access where
  context : List (Holder × String) := []
  active : List (Holder × String) := []
  assigned : List (Holder × String) := []
  shown : List String := []
deriving DecidableEq, Repr, Inhabited

def Access.valueOf (scope : Scope) : Holder × String → String × String
  | (holder, field) => (holder.resource scope, field)

def Access.reads (a : Access) (scope : Scope) : List (String × String) := a.context.map (Access.valueOf scope)

def Access.writes (a : Access) (scope : Scope) : List (String × String) := a.assigned.map (Access.valueOf scope)


structure TransitionAccess where
  reads : List (String × String) := []
  writes : List (String × String) := []
deriving Repr, Inhabited

def regionFindings (chart : Syntax.Ref) (access : Nat → TransitionAccess) (p : RegionPair) : List OrderDependent :=
  let a := access p.first
  let b := access p.second
  (b.writes.filterMap fun v =>
    if v ∈ a.writes then some (.bothAssign chart p.state p.firstRef p.secondRef v.2)
    else if v ∈ a.reads then some (.assignRead chart p.state p.secondRef p.firstRef v.2) else none) ++
  ((a.writes.filter (· ∉ b.writes)).filterMap fun v =>
    if v ∈ b.reads then some (.assignRead chart p.state p.firstRef p.secondRef v.2) else none)

/-- A step's access. `access` holds the values that the step and the steps open within it read and wrote. -/
structure StepAccess where
  name : StepName
  settledOwner : Option String := none
  access : Footprint := {}
deriving Repr, Inhabited

/-- Whether two steps commute, as always_step_independent proves. -/
def StepAccess.commutes (a b : StepAccess) : Bool :=
  a.settledOwner.isSome && a.settledOwner == b.settledOwner &&
    match a.name, b.name with
    | .always _, _ | _, .always _ => true
    | _, _ => false

/--
Whether two footprints overlap. Creating or deleting records with different keys commutes, so keyWrites never overlap
each other.
-/
def overlaps (a b : Footprint) : Bool :=
  a.writes.any (fun v => b.reads.contains v || b.writes.contains v) || b.writes.any a.reads.contains ||
    a.keyWrites.any b.reads.contains || b.keyWrites.any a.reads.contains

structure Collect where
  /-- The queries already reported for order-dependent output. -/
  reportedOrder : List String := []
  transition : Option Nat := none
  transitions : List (Nat × TransitionAccess) := []
  /-- For each step that began and has not ended, innermost first, the instance or copy that it starts. -/
  openSteps : List (Option String) := []
  /-- The step number and access of each step that began while no step was open, in the order they began. -/
  steps : Array (Nat × StepAccess) := #[]
  violations : List Violation := []
  causes : Causes := {}
deriving Repr, Inhabited

/--
The functions that the instrumented run asks besides Functions. `lastReads` gives the record parts read during the
previous call, and `reversed` gives a query's output with records in reverse key order.
-/
structure InstrumentFunctions (m : Type → Type) where
  lastReads : m (List RecordPart)
  lastAccess : m Access
  reversed : String → Value → Records → Time → m (Except Issue Value)

def Collect.reportOrder (c : Collect) (name : String) (v : Violation) : Collect :=
  { c with reportedOrder := c.reportedOrder ++ [name], violations := c.violations ++ [v] }

def Collect.accessOf (c : Collect) (k : Nat) : TransitionAccess := (c.transitions.lookup k).getD {}

def Collect.addAccess (c : Collect) (scope : Scope) (a : Access) : Collect :=
  match c.transition with
  | none => c
  | some k =>
    let p := c.accessOf k
    let p := { reads := (a.reads scope).foldl addNew p.reads, writes := (a.writes scope).foldl addNew p.writes }
    { c with transitions := (c.transitions.filter (·.1 != k)) ++ [(k, p)] }

/-- `c` with the outermost open step modified. That step began last of `steps`. -/
def Collect.modifyOutermost (c : Collect) (f : StepAccess → StepAccess) : Collect :=
  if c.openSteps.isEmpty then c else { c with steps := c.steps.modify (c.steps.size - 1) fun (k, a) => (k, f a) }

/--
Whether the value belongs to an instance or copy that one of the steps `openSteps` starts, or to its copies. Writes to
these values never overlap other steps.
-/
def startedValue (openSteps : List (Option String)) (key : String) : Bool :=
  openSteps.any fun
    | some r => key.startsWith s!"context:{r}." || key.startsWith s!"context:{r}@" || key.startsWith s!"state:{r}@"
    | none => false

def Collect.stepAccess (c : Collect) (f : Footprint) : Collect :=
  let opened := c.openSteps
  c.modifyOutermost fun a =>
    { a with access := a.access.union { f with writes := f.writes.filter (!startedValue opened ·),
                                               keyWrites := f.keyWrites.filter (!startedValue opened ·) } }

def Collect.callAccess (c : Collect) (scope : Option Scope) (parts : List RecordPart) (a : Access) : Collect :=
  let values : Footprint := match scope with
    | some scope =>
      let held (h : Holder) := h.resource scope
      { reads := a.context.map (fun (h, f) => contextKey (held h) f) ++
          a.active.map (fun (h, n) => stateKey (held h) n) ++ a.shown.map (shownKey (held .owner)),
        writes := a.assigned.map fun (h, f) => contextKey (held h) f }
    | none => {}
  let c := c.stepAccess (({ reads := parts.map (·.name) } : Footprint).union values)
  match scope with
  | some scope => c.addAccess scope a
  | none => c

def Collect.report (c : Collect) (v : Violation) : Collect :=
  if v ∈ c.violations then c else { c with violations := c.violations ++ [v] }

def Collect.checkRegions (c : Collect) (check : RegionCheck) : Collect :=
  let found := if check.halted then [] else check.pairs.flatMap (regionFindings check.chart c.accessOf)
  let c := found.foldl (fun c m => c.report m.toViolation) c
  { c with transition := none, transitions := [] }

instance {m : Type → Type} [Monad m] : MonadNote (StateT Collect m) where
  note n := modify fun c =>
    match n with
    | .read _ parts => c.stepAccess { reads := parts.map (·.name) }
    | .stepBegins step name startedResource =>
      { c with openSteps := startedResource :: c.openSteps,
               steps := if c.openSteps.isEmpty then c.steps.push (step, { name }) else c.steps }
    | .stepEnds => { c with openSteps := c.openSteps.tail }
    | .settlesAround owner => c.modifyOutermost ({ · with settledOwner := some owner })
    | .readStates states => c.stepAccess { reads := states.map fun (r, n) => stateKey r n }
    | .wroteState r n | .wroteCopies r n => c.stepAccess { writes := [stateKey r n] }
    | .wroteShown r slot => c.stepAccess { writes := [shownKey r slot] }
    | .transitionPart k => { c with transition := some k }
    | .microstepEnds check => c.checkRegions check
    | n => { c with causes := c.causes.notice n }

def liftFunctions {m n : Type → Type} [MonadLiftT m n] (fs : Functions m) : Functions n where
  parse a b := liftM (fs.parse a b)
  canonical a b := liftM (fs.canonical a b)
  normalize a b := liftM (fs.normalize a b)
  binding a b c d e := liftM (fs.binding a b c d e)
  requirement a b c d e := liftM (fs.requirement a b c d e)
  inputRequirement a b c := liftM (fs.inputRequirement a b c)
  decide a b c d := liftM (fs.decide a b c d)
  ensures a b c d e := liftM (fs.ensures a b c d e)
  queryEnsures a b c d := liftM (fs.queryEnsures a b c d)
  resultEnsures a b c d := liftM (fs.resultEnsures a b c d)
  invariant a b := liftM (fs.invariant a b)
  serviceInvariant a := liftM (fs.serviceInvariant a)
  chartInvariant a b := liftM (fs.chartInvariant a b)
  resolve a b c d := liftM (fs.resolve a b c d)
  react a b c d e := liftM (fs.react a b c d e)
  comparable a b := liftM (fs.comparable a b)
  initialContext a b := liftM (fs.initialContext a b)
  guard a b c d := liftM (fs.guard a b c d)
  assign a b c d e := liftM (fs.assign a b c d e)
  input a b c d := liftM (fs.input a b c d)
  holds a b := liftM (fs.holds a b)
  deadlines a b := liftM (fs.deadlines a b)
  deadlineAt a b c := liftM (fs.deadlineAt a b c)
  offers a b c := liftM (fs.offers a b c)
  showInput a b c := liftM (fs.showInput a b c)
  items a b := liftM (fs.items a b)
  copyContext a b := liftM (fs.copyContext a b)
  singleRecord a := liftM (fs.singleRecord a)
  copyKey a b c := liftM (fs.copyKey a b c)
  close a b := liftM (fs.close a b)

section

variable {m : Type → Type} [Monad m] (st : Service) (fs : Functions m) (ifs : InstrumentFunctions m)

/-- Asks Functions and collects from the answer without changing it. -/
def observe {α : Type} (x : m α) (f : α → StateT Collect m Unit) : StateT Collect m α := do
  let r ← liftM x
  f r
  pure r

/--
Runs query `name` again with records in reverse key order. It reports OrderDependent.reversedRecords when the
comparable output changes, OrderDependent.reversedOutputSchema when the output fails the schema, or
OrderDependent.reversedException when an Issue stops that run, the check of its output or its comparable value. It
reports at most once per query. An Issue in the comparable value of `output` is no order dependence and reports
nothing. The one reversed order approximates every order of the keys: an output that depends on the order only as the
reversal keeps it, such as on the middle of three keys, is not reported.
-/
def orderAudit (name : String) (input : Value) (records : Records) (now : Time) (output : Value) :
    StateT Collect m Unit := do
  if name ∈ (← get).reportedOrder then return
  let report (found : OrderDependent) : StateT Collect m Unit := modify (·.reportOrder name found.toViolation)
  let .ok reversed ← ifs.reversed name input records now | report (.reversedException (st.ref name))
  match ← normalizeOutput (m := m) st fs name reversed with
  | .error _ => report (.reversedException (st.ref name))
  | .ok none => report (.reversedOutputSchema (st.ref name))
  | .ok (some reversed) =>
    let .ok original ← fs.comparable name (.fulfilled output) | return
    let .ok reordered ← fs.comparable name (.fulfilled reversed) | report (.reversedException (st.ref name))
    if original == reordered then return
    report (.reversedRecords (st.ref name) output reversed)

def stepCollect (scope : Option Scope) : StateT Collect m Unit := do
  let parts ← ifs.lastReads
  let a ← match scope with
    | some _ => ifs.lastAccess
    | none => pure {}
  modify (·.callAccess scope parts a)

def resolveCollect (name : String) (input : Value) (records : Records) (now : Time) (r : Except Issue Value) :
    StateT Collect m Unit := do
  stepCollect ifs none
  if let .ok output := r then
    if let .ok (some output) ← normalizeOutput (m := m) st fs name output then
      orderAudit st fs ifs name input records now output

def decideCollect (name : String) (records : Records) (decided : Except Issue (List Emit)) : StateT Collect m Unit := do
  stepCollect ifs none
  let .ok emits := decided | pure ()
  if emits.any (!st.lists name ·) then return
  match ← normalizeEmits (m := m) st fs name emits with
  | .ok emits => modify (·.stepAccess (writesOf st records emits).values)
  | .error _ => pure ()

/-- Functions that return the same values as `fs` and collect what each call reads and writes. -/
def instrument : Functions (StateT Collect m) :=
  { liftFunctions fs with
    binding := fun name b input records now =>
      observe (fs.binding name b input records now) fun _ => stepCollect ifs none
    requirement := fun name c input records now =>
      observe (fs.requirement name c input records now) fun _ => stepCollect ifs none
    decide := fun name input records now => observe (fs.decide name input records now) (decideCollect st fs ifs name records)
    resolve := fun name input records now =>
      observe (fs.resolve name input records now) (resolveCollect st fs ifs name input records now)
    react := fun name payload records now keys =>
      observe (fs.react name payload records now keys) fun _ => stepCollect ifs none
    guard := fun scope records t extra =>
      observe (fs.guard scope records t extra) fun _ => stepCollect ifs (some scope)
    assign := fun scope records a extra keys =>
      observe (fs.assign scope records a extra keys) fun _ => stepCollect ifs (some scope)
    input := fun scope records a keys =>
      observe (fs.input scope records a keys) fun _ => stepCollect ifs (some scope)
    items := fun scope records => observe (fs.items scope records) fun _ => stepCollect ifs (some scope)
    offers := fun scope records control =>
      observe (fs.offers scope records control) fun _ => stepCollect ifs (some scope)
    showInput := fun scope records a => observe (fs.showInput scope records a) fun _ => stepCollect ifs (some scope)
    deadlineAt := fun scope records name =>
      observe (fs.deadlineAt scope records name) fun _ => stepCollect ifs (some scope)
    close := fun scope records => observe (fs.close scope records) fun _ => stepCollect ifs (some scope) }

def instrumentedRun (inputs : List Step) : StateT Collect m State :=
  runFrom (step st (instrument st fs ifs)) {} inputs

/--
The pairs of steps whose other order test runs: steps of one message, by step number in the order they began, whose
accesses overlap, that do not commute, whose names differ so that a `stepOrder` names each, and that no cause orders.
A run that halted (in the semantic run, or `stopped` from enabled) skips the steps after the halt, so it has none.
Precedent: dynamic partial-order reduction (Flanagan and Godefroid, POPL 2005), where dependence only selects the
orders to run.
-/
def candidates (s : State) (c : Collect) (stopped : Option Violation) : List (Nat × Nat) :=
  if (s.halted <|> stopped).isSome then [] else
  c.steps.toList.zipIdx.flatMap fun ((i, a), n) =>
    (c.steps.toList.drop (n + 1)).filterMap fun (j, b) =>
      if (s.steps[i]?.map (·.message)) == (s.steps[j]?.map (·.message)) && overlaps a.access b.access &&
          !a.commutes b && a.name != b.name && !leadsTo s i j then
        some (i, j)
      else none

/--
The violations that a run reports: the semantic violations, the collected violations, and then the halting violation
(from the semantic run, or `stopped` from enabled).
-/
def reportedViolations (s : State) (c : Collect) (stopped : Option Violation) : List Violation :=
  s.violations ++ c.violations ++ (s.halted <|> stopped).toList

end

end Tazuna.Observe
