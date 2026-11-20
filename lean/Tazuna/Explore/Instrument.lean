import Tazuna.Service.Restart
import Tazuna.Explore.BagOrderDependent
import Tazuna.Explore.Undecided
import Tazuna.Sim.Order
import Tazuna.Data.Binding

/-!
This module defines the instrumented run. It wraps Functions without changing the semantic run, collects the values
that each step and transition reads and writes, and checks whether the answers of spec functions depend on the order in
which a Bag visits its values. TS records reads as functions read records.
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
  /-- The definitions already reported by orderAudit. -/
  reportedOrder : List Spec.Ref := []
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
deriving Repr, Inhabited

/--
The functions that the instrumented run asks besides Functions. `lastReads` gives the record parts read during the
previous call, and `lastEnumerated` whether a Bag of two or more values ran a callback during it, the only way that
spec code sees the order of a Bag. `reversed` answers as Functions does with every Bag of records or of a decoded value
visiting its values in reverse order, and without telling what it reads.
-/
structure InstrumentFunctions (m : Type → Type) where
  lastReads : m (List RecordPart)
  lastAccess : m Access
  lastEnumerated : m Bool
  reversed : Functions m

def Collect.reportOrder (c : Collect) (definition : Spec.Ref) (v : Violation) : Collect :=
  { c with reportedOrder := c.reportedOrder ++ [definition], violations := c.violations ++ [v] }

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

def reportOrder (definition : Spec.Ref) (found : Violation) : StateT Collect m Unit :=
  modify (·.reportOrder definition found)

/--
Takes the answer of `again`, the question `function` asked again of `ifs.reversed`, and reports
BagOrderDependent.reversedException when an Issue stops it, BagOrderDependent.reversedResult when `same` tells it apart
from `original`, or Undecided.reversedBagBindings when `same` cannot tell. It reports at most once per definition. The one reversed order approximates every order of a Bag: an
answer that depends on the order only as the reversal keeps it, such as on the middle of three values, is not reported.
-/
def orderAudit {ε α : Type} (definition : Spec.Ref) (function : String) (original : α) (again : m (Except ε α))
    (same : α → α → Sameness) : StateT Collect m Unit := do
  if definition ∈ (← get).reportedOrder then return
  match ← again with
  | .error _ => reportOrder definition (BagOrderDependent.reversedException definition function).toViolation
  | .ok answer =>
    match same original answer with
    | .same => pure ()
    | .different => reportOrder definition (BagOrderDependent.reversedResult definition function).toViolation
    | .uncomparable => reportOrder definition (Undecided.reversedBagBindings definition function bindingLimit).toViolation

/--
Runs `collect` after the call of `call` that answered `r`, and audits the answer with orderAudit when that call
enumerated a Bag. An Issue needs no audit: the run halts with its Fault, which names the definition whatever the order,
and the message of a thrown error, which may name the value visited first, is TS's alone and is never compared.
-/
def auditCollect {ε α : Type} (collect : StateT Collect m Unit) (definition : Spec.Ref) (function : String)
    (call : Functions m → m (Except ε α)) (same : α → α → Sameness) (r : Except ε α) : StateT Collect m Unit := do
  collect
  if let .ok answer := r then
    if ← ifs.lastEnumerated then orderAudit definition function answer (call ifs.reversed) same

def stepCollect (scope : Option Scope) : StateT Collect m Unit := do
  let parts ← ifs.lastReads
  let a ← match scope with
    | some _ => ifs.lastAccess
    | none => pure {}
  modify (·.callAccess scope parts a)

/--
Audits a query's output as auditCollect does, comparing the comparable values of the outputs. An output whose
comparable value an Issue stops needs no audit, because the run reports it.
-/
def resolveCollect (name : String) (input : Value) (records : Records) (now : Time) (r : Except Issue Value) :
    StateT Collect m Unit := do
  stepCollect ifs none
  let .ok output := r | return
  unless ← ifs.lastEnumerated do return
  if st.ref name ∈ (← get).reportedOrder then return
  let .ok original ← fs.comparable name (.fulfilled output) | return
  let exception := reportOrder (st.ref name) (BagOrderDependent.reversedException (st.ref name) "resolve").toViolation
  let .ok reversed ← ifs.reversed.resolve name input records now | exception
  let .ok reordered ← fs.comparable name (.fulfilled reversed) | exception
  unless original == reordered do reportOrder (st.ref name) (BagOrderDependent.reversedResult (st.ref name) "resolve").toViolation

def decideCollect (name : String) (records : Records) (decided : Except Issue (List (List Emit))) :
    StateT Collect m Unit := do
  let .ok decided := decided | pure ()
  if decided.flatten.any (!st.lists name ·) then return
  modify (·.stepAccess (writesOf st records (orderedGroups decided decided.flatten).flatten).values)

/-- The texts in code-point order, which compare two lists as multisets. -/
def sortedTexts (texts : List String) : List String := texts.mergeSort fun a b => decide (a ≤ b)

/--
A value that one call made, with each array as a bag, since the call may build an array in the order of its keys, and
each key that the call created (`keys`, entity then key) as a key reference.
-/
def madeValue (keys : List (String × String)) : Value → CValue
  | .arr vs => .bag (vs.map (madeValue keys))
  | .obj fs => .obj (fs.map fun p => (p.1, madeValue keys p.2))
  | .str s => match keys.find? (·.2 == s) with
    | some (e, _) => .ref e s
    | none => .leaf (.str s)
  | v => .leaf v
decreasing_by all_goals nested_decreasing

/--
Whether two answers that made a value and created keys are equal up to a renaming of the created keys: one to one
within each entity's keys, and of the created keys only (matchValue). Arrays compare as bags then, since a renaming
reorders an array that the keys order.
-/
def sameMade (keys : Keys) (a b : Value × List String) : Sameness :=
  if sortedTexts a.2 != sortedTexts b.2 then .different else
    if a.2.isEmpty then .of (a.1.canonical == b.1.canonical) else
    let given := givenKeys keys a.2
    let entityOf (keys : List (String × String)) (s : String) := (keys.find? (·.2 == s)).map (·.1)
    let other := givenKeys keys b.2
    let v : Values := { domain := fun s => (entityOf given s).getD "", fresh := given.map (·.2),
                        image := fun s t => entityOf other t == entityOf given s }
    (matchValue v .empty (madeValue given a.1) (madeValue other b.1)).sameness

/-- The texts without order or repetition, which compare two lists as sets. -/
def textSet (texts : List String) : List String := (sortedTexts texts).eraseDups

/-- The texts of the events of each group in code-point order, which compare two answers of decide. -/
def groupTexts (groups : List (List Emit)) : List (List String) := groups.map fun g => sortedTexts (g.map (·.text))

/-- Whether two values are equal up to field order. -/
def sameValue (a b : Value) : Bool := a.canonical == b.canonical

/--
Functions that return the same values as `fs`, collect what each call reads and writes, and audit the answers of the
spec functions that read records or values. The service invariants are not audited, because they have no definition
for a report to name.
-/
def instrument : Functions (StateT Collect m) :=
  let auditBy {ε α : Type} (collect : StateT Collect m Unit) (definition : Spec.Ref) (function : String)
      (call : Functions m → m (Except ε α)) (same : α → α → Sameness) :=
    observe (call fs) (auditCollect ifs collect definition function call same)
  let audit {ε α : Type} (collect : StateT Collect m Unit) (definition : Spec.Ref) (function : String)
      (call : Functions m → m (Except ε α)) (same : α → α → Bool) :=
    auditBy collect definition function call fun a b => .of (same a b)
  let collect (scope : Option Scope) := stepCollect ifs scope
  { liftFunctions fs with
    binding := fun name b input records now =>
      audit (collect none) (st.ref name) "binding" (·.binding name b input records now) (· == ·)
    requirement := fun name c input records now =>
      audit (collect none) (st.ref name) "requirement" (·.requirement name c input records now) (· == ·)
    inputRequirement := fun target c input =>
      audit (pure ()) target "inputRequirement" (·.inputRequirement target c input) (· == ·)
    decide := fun name input records now =>
      observe (fs.decide name input records now) fun r => do
        auditCollect ifs (collect none) (st.ref name) "decide" (·.decide name input records now)
          (fun a b => .of (groupTexts a == groupTexts b)) r
        decideCollect (m := m) st name records r
    ensures := fun name input before after now =>
      audit (pure ()) (st.ref name) "ensures" (·.ensures name input before after now) (· == ·)
    queryEnsures := fun name input output records =>
      audit (collect none) (st.ref name) "queryEnsures" (·.queryEnsures name input output records) (· == ·)
    resultEnsures := fun target c input output events =>
      audit (pure ()) target "resultEnsures" (·.resultEnsures target c input output events) (· == ·)
    invariant := fun entity record => audit (pure ()) (st.ref entity) "invariant" (·.invariant entity record) (· == ·)
    chartInvariant := fun scope records =>
      audit (collect (some scope)) (st.ref scope.machine) "chartInvariant" (·.chartInvariant scope records) (· == ·)
    resolve := fun name input records now =>
      observe (fs.resolve name input records now) (resolveCollect st fs ifs name input records now)
    automationBinding := fun name b payload records now =>
      audit (collect none) (st.ref name) "automationBinding" (·.automationBinding name b payload records now) (· == ·)
    automationGuard := fun name c payload records now =>
      audit (collect none) (st.ref name) "automationGuard" (·.automationGuard name c payload records now) (· == ·)
    react := fun name payload records now keys =>
      auditBy (collect none) (st.ref name) "react" (·.react name payload records now keys) (sameMade keys)
    initialContext := fun machine input =>
      audit (pure ()) (st.ref machine) "initialContext" (·.initialContext machine input) sameValue
    guard := fun scope records t c extra =>
      audit (collect (some scope)) (st.ref scope.machine) "guard" (·.guard scope records t c extra) (· == ·)
    assign := fun scope records a extra keys =>
      let made (x : Value × Option Value × List String) : Value × List String := (.arr [x.1, x.2.1.getD .null], x.2.2)
      auditBy (collect (some scope)) (st.ref scope.machine) "assign" (·.assign scope records a extra keys)
        fun a b => sameMade keys (made a) (made b)
    input := fun scope records a keys =>
      auditBy (collect (some scope)) (st.ref scope.machine) "input" (·.input scope records a keys) (sameMade keys)
    held := fun scope records n edge extra =>
      audit (collect (some scope)) (st.ref scope.machine) "held" (·.held scope records n edge extra) sameValue
    items := fun scope records =>
      let texts (keys : List (Value × Value)) := textSet (keys.map (·.2.canonical))
      audit (collect (some scope)) (st.ref scope.machine) "items" (·.items scope records) fun a b => texts a == texts b
    offers := fun scope records control =>
      let texts (payloads : List Value) := textSet (payloads.map (·.canonical))
      audit (collect (some scope)) (st.ref scope.machine) "offers" (·.offers scope records control)
        fun a b => texts a == texts b
    showInput := fun scope records a =>
      audit (collect (some scope)) (st.ref scope.machine) "showInput" (·.showInput scope records a) sameValue
    deadlineAt := fun scope records name =>
      audit (collect (some scope)) (st.ref scope.machine) "deadlineAt" (·.deadlineAt scope records name) (· == ·)
    close := fun scope records =>
      audit (collect (some scope)) (st.ref scope.machine) "close" (·.close scope records) sameValue
    closeEnsures := fun screen input output =>
      audit (pure ()) (st.ref screen) "closeEnsures" (·.closeEnsures screen input output) (· == ·) }

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
