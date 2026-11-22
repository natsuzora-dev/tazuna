import Tazuna.Service.Restart
import Tazuna.Explore.BagOrderDependent
import Tazuna.Sim.Order
import Tazuna.Data.Binding

/-!
This module defines the instrumented run. It wraps Functions without changing the semantic run and collects the values
that each step and transition reads and writes.
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service Tazuna.Sim

/--
The values that a step reads and writes. `keyWrites` holds the key sets of entities, which creating or deleting a record
writes.
-/
structure Footprint where
  reads : List ValueKey := []
  writes : List ValueKey := []
  keyWrites : List ValueKey := []
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
  { reads := (a.reads.map .record).foldl addNew [], writes := (a.writes.map .record).foldl addNew [],
    keyWrites := a.keyWrites.map fun entity => .record (.keys entity) }

def uniqueReads (st : Service) (records : Records) (entity : String) (key : Option String) : List RecordPart :=
  match records.find? (fun r => r.entity == entity && r.key == key) with
  | none => []
  | some row =>
    let unique := st.uniqueOf entity
    if !uniqueChecked unique row.value then [] else
    .keys entity :: (records.filter (fun r => r.entity == entity && r.key != key)).flatMap fun r =>
      unique.map (.field entity r.key ·)

def eventFields (st : Service) (e : Emit) : List String :=
  match st.changeOf e.event with
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

derive_wire Holder

def Holder.id (scope : Scope) : Holder → InstanceId
  | .owner => scope.id.owner
  | .copy => scope.id

/-- The values that a chart function reads and writes. `shown` holds the owner's shows slots that it reads. -/
structure Access where
  context : List (Holder × String) := []
  active : List (Holder × String) := []
  assigned : List (Holder × String) := []
  shown : List String := []
deriving DecidableEq, Repr, Inhabited

derive_wire Access

def Access.valueOf (scope : Scope) : Holder × String → InstanceId × String
  | (holder, field) => (holder.id scope, field)

def Access.reads (a : Access) (scope : Scope) : List (InstanceId × String) := a.context.map (Access.valueOf scope)

def Access.writes (a : Access) (scope : Scope) : List (InstanceId × String) := a.assigned.map (Access.valueOf scope)


structure TransitionAccess where
  reads : List (InstanceId × String) := []
  writes : List (InstanceId × String) := []
deriving Repr, Inhabited

def regionFindings (chart : Spec.Ref) (access : Nat → TransitionAccess) (p : RegionPair) : List BagOrderDependent :=
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
  settledOwner : Option InstanceId := none
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
  transition : Option Nat := none
  transitions : List (Nat × TransitionAccess) := []
  /-- For each step that began and has not ended, innermost first, the instance or copy that it starts. -/
  openSteps : List (Option InstanceId) := []
  /-- The step number and access of each step that began while no step was open, in the order they began. -/
  steps : Array (Nat × StepAccess) := #[]
  /-- The message whose afterMessage runs, while it runs. -/
  afterMessage : Option Nat := none
  /-- The place in `steps` of the step in which a message of a tie arrives, while it is processed (arrivalBegins). -/
  arrival : Option Nat := none
  /-- For each message, the values that its afterMessage read: subscription answers and invariants. -/
  afters : List (Nat × Footprint) := []
  violations : List Violation := []
  /-- The parts that the run reached, each once, in the order first reached. -/
  reached : List Uncovered := []
deriving Repr, Inhabited

/--
The functions that the instrumented run asks besides Functions: `lastReads` gives the record parts that the previous
call read, and `lastAccess` the chart values that it read and assigned.
-/
structure InstrumentFunctions (m : Type → Type) where
  lastReads : m (List RecordPart)
  lastAccess : m Access

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
Whether the value is a context field or state of an instance or copy that one of the steps `openSteps` starts, or of
its copies. Writes to these values never overlap other steps.
-/
def startedValue (openSteps : List (Option InstanceId)) : ValueKey → Bool
  | .context i _ | .state i _ => openSteps.any (·.any i.within)
  | _ => false

/--
`c` with `f` added to the outermost open step, or, while no step is open, to the afterMessage that runs, or else to the
step in which the message of a tie arrived. Other accesses outside any step, such as answering a query input, change
nothing that a later message observes.
-/
def Collect.stepAccess (c : Collect) (f : Footprint) : Collect :=
  if c.openSteps.isEmpty then
    match c.afterMessage, c.arrival with
    | some m, _ => { c with afters := (m, ((c.afters.lookup m).getD {}).union f) :: c.afters.filter (·.1 != m) }
    | none, some k => { c with steps := c.steps.modify k fun (n, a) => (n, { a with access := a.access.union f }) }
    | none, none => c
  else
  let opened := c.openSteps
  c.modifyOutermost fun a =>
    { a with access := a.access.union { f with writes := f.writes.filter (!startedValue opened ·),
                                               keyWrites := f.keyWrites.filter (!startedValue opened ·) } }

def Collect.callAccess (c : Collect) (scope : Option Scope) (parts : List RecordPart) (a : Access) : Collect :=
  let values : Footprint := match scope with
    | some scope =>
      let held (h : Holder) := h.id scope
      { reads := a.context.map (fun (h, f) => .context (held h) f) ++
          a.active.map (fun (h, n) => .state (held h) n) ++ a.shown.map (.shown (held .owner)),
        writes := a.assigned.map fun (h, f) => .context (held h) f }
    | none => {}
  let c := c.stepAccess (({ reads := parts.map .record } : Footprint).union values)
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
    | .read _ parts => c.stepAccess { reads := parts.map .record }
    | .stepBegins step name started =>
      { c with openSteps := started :: c.openSteps,
               steps := if c.openSteps.isEmpty then c.steps.push (step, { name }) else c.steps }
    | .stepEnds => { c with openSteps := c.openSteps.tail }
    | .arrivalBegins step name => { c with steps := c.steps.push (step, { name }), arrival := some c.steps.size }
    | .arrivalEnds => { c with arrival := none }
    | .settlesAround owner => c.modifyOutermost ({ · with settledOwner := some owner })
    | .readStates states => c.stepAccess { reads := states.map fun (r, n) => .state r n }
    | .wroteState r n | .wroteCopies r n => c.stepAccess { writes := [.state r n] }
    | .wroteShown r slot => c.stepAccess { writes := [.shown r slot] }
    | .transitionPart k => { c with transition := some k }
    | .microstepEnds check => c.checkRegions check
    | .afterMessageBegins message => { c with afterMessage := some message }
    | .afterMessageEnds => { c with afterMessage := none }
    | .reached part => if c.reached.contains part then c else { c with reached := c.reached ++ [part] }
    | .bug _ => c

/-- The functions that ask `fs` and carry each answer into `n` by `f`. -/
def _root_.Tazuna.Service.Functions.hoist {m n : Type → Type} (f : {α : Type} → m α → n α) (fs : Functions m) : Functions n where
  parse a b := f (fs.parse a b)
  unordered a b := f (fs.unordered a b)
  binding a b c d e := f (fs.binding a b c d e)
  requirement a b c d e := f (fs.requirement a b c d e)
  inputRequirement a b c := f (fs.inputRequirement a b c)
  decide a b c d := f (fs.decide a b c d)
  ensures a b c d e := f (fs.ensures a b c d e)
  queryEnsures a b c d := f (fs.queryEnsures a b c d)
  resultEnsures a b c d e := f (fs.resultEnsures a b c d e)
  invariant a b := f (fs.invariant a b)
  serviceInvariant a := f (fs.serviceInvariant a)
  chartInvariant a b := f (fs.chartInvariant a b)
  resolve a b c d := f (fs.resolve a b c d)
  automationBinding a b c d e := f (fs.automationBinding a b c d e)
  automationGuard a b c d e := f (fs.automationGuard a b c d e)
  react a b c d e := f (fs.react a b c d e)
  comparable a b := f (fs.comparable a b)
  initialContext a b := f (fs.initialContext a b)
  guard a b c d e := f (fs.guard a b c d e)
  assign a b c d e := f (fs.assign a b c d e)
  input a b c d := f (fs.input a b c d)
  held a b c d e := f (fs.held a b c d e)
  deadlineAt a b c := f (fs.deadlineAt a b c)
  offers a b c := f (fs.offers a b c)
  showInput a b c := f (fs.showInput a b c)
  items a b := f (fs.items a b)
  defaults a := f (fs.defaults a)
  close a b := f (fs.close a b)
  closeEnsures a b c := f (fs.closeEnsures a b c)

def liftFunctions {m n : Type → Type} [MonadLiftT m n] (fs : Functions m) : Functions n := fs.hoist liftM

section

variable {m : Type → Type} [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (ifs : InstrumentFunctions m)

/-- Asks Functions and collects from the answer without changing it. -/
def observe {α : Type} (x : m α) (f : α → StateT Collect m Unit) : StateT Collect m α := do
  let r ← liftM x
  f r
  pure r

def stepCollect (scope : Option Scope) : StateT Collect m Unit := do
  let parts ← ifs.lastReads
  let a ← match scope with
    | some _ => ifs.lastAccess
    | none => pure {}
  modify (·.callAccess scope parts a)

def decideCollect (name : String) (records : Records) (decided : Except Issue (List (List Emit))) :
    StateT Collect m Unit := do
  let .ok decided := decided | pure ()
  if decided.flatten.any (!st.lists name ·) then return
  modify (·.stepAccess (writesOf st records (orderedGroups decided decided.flatten).flatten).values)

/--
Functions that return the same values as `fs.sorting st`, so a run is given its spec functions sorted as it keeps their
values, and collect what each call reads and writes.
-/
def instrument : Functions (StateT Collect m) :=
  let fs := fs.sorting st
  let collect {α : Type} (scope : Option Scope) (x : m α) : StateT Collect m α := observe x fun _ => stepCollect ifs scope
  { liftFunctions fs with
    binding := fun name b input records now => collect none (fs.binding name b input records now)
    requirement := fun name c input records now => collect none (fs.requirement name c input records now)
    decide := fun name input records now =>
      observe (fs.decide name input records now) fun r => do
        stepCollect ifs none
        decideCollect (m := m) st name records r
    queryEnsures := fun name input output records => collect none (fs.queryEnsures name input output records)
    chartInvariant := fun scope records => collect (some scope) (fs.chartInvariant scope records)
    resolve := fun name input records now => collect none (fs.resolve name input records now)
    automationBinding := fun name b payload records now => collect none (fs.automationBinding name b payload records now)
    automationGuard := fun name c payload records now => collect none (fs.automationGuard name c payload records now)
    react := fun name payload records now keys => collect none (fs.react name payload records now keys)
    guard := fun scope records t c extra => collect (some scope) (fs.guard scope records t c extra)
    assign := fun scope records a extra keys => collect (some scope) (fs.assign scope records a extra keys)
    input := fun scope records a keys => collect (some scope) (fs.input scope records a keys)
    held := fun scope records n edge extra => collect (some scope) (fs.held scope records n edge extra)
    items := fun scope records => collect (some scope) (fs.items scope records)
    offers := fun scope records control => collect (some scope) (fs.offers scope records control)
    showInput := fun scope records a => collect (some scope) (fs.showInput scope records a)
    deadlineAt := fun scope records name => collect (some scope) (fs.deadlineAt scope records name)
    close := fun scope records => collect (some scope) (fs.close scope records) }

/--
Whether step `earlier` leads to step `later`. Nested steps are spans of their outer step, so only steps that write
event lines are compared. Reachability between them follows the cause chain and barriers, which the search of step
orders keeps fixed.
-/
def leadsTo (s : State) (earlier later : Nat) : Bool :=
  later == earlier ||
    (earlier < later && (s.steps[earlier]?.any (·.barrier)) &&
      (s.steps[earlier]?.map (·.message)) == (s.steps[later]?.map (·.message))) ||
    match s.steps[later]? with
    | some i =>
      (i.barrier && earlier < later && (s.steps[earlier]?.map (·.message)) == some i.message) ||
        match i.origin.cause with
        | some cause => if cause < later then leadsTo s earlier cause else false
        | none => false
    | none => false
termination_by later

/-- Whether steps `i` and `j` are of one tie: deadlines due at one time, or messages that one line delivered. -/
def tied (s : State) (i j : Nat) : Bool :=
  match s.steps[i]?.bind (·.origin.tie), s.steps[j]?.bind (·.origin.tie) with
  | some a, some b => a == b
  | _, _ => false

/-- Whether steps `i` and `j` are steps of one message that no tie chose. -/
def sameMessage (s : State) (i j : Nat) : Bool :=
  (s.steps[i]?.bind (·.origin.tie)).isNone && (s.steps[j]?.bind (·.origin.tie)).isNone &&
    (s.steps[i]?.map (·.message)) == (s.steps[j]?.map (·.message))

/--
The footprint of what step `n` stands for when the search swaps its order (one independence relation for every choice
of order): a step of a tie stands for its whole message, since its effects run in the later steps of that message
and the state at the end of the message is observed before the next deadline fires, so the reads of its afterMessage
count too; any other step stands for itself. The lines that the steps write are not in it: swapping steps that no cause
chain links changes no order of a snapshot (Sim.ordered). Keys that the steps create are not in it, since test compares
outcomes up to a renaming of created keys.
-/
def involved (s : State) (c : Collect) (n : Nat) (a : StepAccess) : Footprint :=
  let message := s.steps[n]?.map (·.message)
  let (steps, after) := if (s.steps[n]?.bind (·.origin.tie)).isSome then
      (c.steps.toList.filter fun (k, _) => s.steps[k]?.map (·.message) == message,
        (message.bind (c.afters.lookup ·)).getD {})
    else ([(n, a)], {})
  steps.foldl (fun f (_, x) => f.union x.access) after

/-- The footprint (involved) of each step of `c.steps`, by position. -/
def footprints (s : State) (c : Collect) : Array Footprint :=
  c.steps.map fun (n, a) => involved s c n a

/--
The pairs of steps whose other order test runs, by step number in the order they began, whose names differ so that a
`stepOrder` names each, that no cause orders, and whose order is a choice: the steps of one tie, or the steps of one
message that no tie chose. Each message of a tie arrives in a step named by its id, so equal messages pair like any
others. Of those, only the pairs whose footprints overlap and that do not commute run, the one independence relation of
the search. A run that halted (in the semantic run, or `stopped` from enabled) skips the steps after the halt, so it has
none. Precedent: dynamic partial-order reduction (Flanagan and Godefroid, POPL 2005), where dependence only selects the
orders to run.
-/
def candidates (s : State) (c : Collect) (stopped : Option Finding) : List (Nat × Nat) :=
  if (s.halted <|> stopped).isSome then [] else
  let fps := footprints s c
  c.steps.toList.zipIdx.flatMap fun ((i, a), n) =>
    (c.steps.toList.zipIdx.drop (n + 1)).filterMap fun ((j, b), k) =>
      if (tied s i j || sameMessage s i j) &&
          overlaps (fps[n]?.getD {}) (fps[k]?.getD {}) && !a.commutes b && a.name != b.name && !leadsTo s i j then
        some (i, j)
      else none

/--
The violations that a run reports: the semantic violations, the collected violations, and then the halting violation
(from the semantic run, or `stopped` from enabled).
-/
def reportedViolations (s : State) (c : Collect) (stopped : Option Finding) : List Violation :=
  s.violations.map (·.toViolation) ++ c.violations ++ ((s.halted <|> stopped).map (·.toViolation)).toList

end

end Tazuna.Explore
