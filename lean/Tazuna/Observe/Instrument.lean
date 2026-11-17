import Tazuna.Service.Restart
import Tazuna.Observe.OrderDependent
import Tazuna.Observe.Trace

/-!
This module defines the instrumented run. It wraps Functions without changing the semantic run, collects the values
that each step and transition reads and writes, and checks whether the answers of spec functions depend on the order in
which a Bag visits its values. TS records reads as functions read records.
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
  /-- The definitions already reported by orderAudit. -/
  reportedOrder : List Syntax.Ref := []
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
previous call, and `lastEnumerated` whether a Bag of two or more values ran a callback during it, the only way that
spec code sees the order of a Bag. `reversed` answers as Functions does with every Bag of records or of a decoded value
visiting its values in reverse order, and without telling what it reads.
-/
structure InstrumentFunctions (m : Type → Type) where
  lastReads : m (List RecordPart)
  lastAccess : m Access
  lastEnumerated : m Bool
  reversed : Functions m

def Collect.reportOrder (c : Collect) (definition : Syntax.Ref) (v : Violation) : Collect :=
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

/-- The functions that ask `fs` and carry each answer into `n` by `f`. -/
def _root_.Tazuna.Semantics.Functions.hoist {m n : Type → Type} (f : {α : Type} → m α → n α) (fs : Functions m) : Functions n where
  parse a b := f (fs.parse a b)
  canonical a b := f (fs.canonical a b)
  unordered a b := f (fs.unordered a b)
  normalize a b := f (fs.normalize a b)
  binding a b c d e := f (fs.binding a b c d e)
  requirement a b c d e := f (fs.requirement a b c d e)
  inputRequirement a b c := f (fs.inputRequirement a b c)
  decide a b c d := f (fs.decide a b c d)
  ensures a b c d e := f (fs.ensures a b c d e)
  queryEnsures a b c d := f (fs.queryEnsures a b c d)
  resultEnsures a b c d := f (fs.resultEnsures a b c d)
  invariant a b := f (fs.invariant a b)
  serviceInvariant a := f (fs.serviceInvariant a)
  chartInvariant a b := f (fs.chartInvariant a b)
  resolve a b c d := f (fs.resolve a b c d)
  react a b c d e := f (fs.react a b c d e)
  comparable a b := f (fs.comparable a b)
  initialContext a b := f (fs.initialContext a b)
  guard a b c d := f (fs.guard a b c d)
  assign a b c d e := f (fs.assign a b c d e)
  input a b c d := f (fs.input a b c d)
  holds a b := f (fs.holds a b)
  deadlines a b := f (fs.deadlines a b)
  deadlineAt a b c := f (fs.deadlineAt a b c)
  offers a b c := f (fs.offers a b c)
  showInput a b c := f (fs.showInput a b c)
  items a b := f (fs.items a b)
  copyContext a b := f (fs.copyContext a b)
  singleRecord a := f (fs.singleRecord a)
  copyKey a b c := f (fs.copyKey a b c)
  close a b := f (fs.close a b)

def liftFunctions {m n : Type → Type} [MonadLiftT m n] (fs : Functions m) : Functions n := fs.hoist liftM

section

variable {m : Type → Type} [Monad m] (st : Service) (fs : Functions m) (ifs : InstrumentFunctions m)

/-- Asks Functions and collects from the answer without changing it. -/
def observe {α : Type} (x : m α) (f : α → StateT Collect m Unit) : StateT Collect m α := do
  let r ← liftM x
  f r
  pure r

def reportOrder (definition : Syntax.Ref) (found : OrderDependent) : StateT Collect m Unit :=
  modify (·.reportOrder definition found.toViolation)

/--
Takes the answer of `again`, the question `function` asked again of `ifs.reversed`, and reports
OrderDependent.reversedException when an Issue stops it, or OrderDependent.reversedResult when `same` tells it apart
from `original`. It reports at most once per definition. The one reversed order approximates every order of a Bag: an
answer that depends on the order only as the reversal keeps it, such as on the middle of three values, is not reported.
-/
def orderAudit {ε α : Type} (definition : Syntax.Ref) (function : String) (original : α) (again : m (Except ε α))
    (same : α → α → Bool) : StateT Collect m Unit := do
  if definition ∈ (← get).reportedOrder then return
  match ← again with
  | .error _ => reportOrder definition (.reversedException definition function)
  | .ok answer => unless same original answer do reportOrder definition (.reversedResult definition function)

/--
Runs `collect` after the call of `call` that answered `r`, and audits the answer with orderAudit when that call
enumerated a Bag. An Issue needs no audit: the run halts with its Fault, which names the definition whatever the order,
and the message of a thrown error, which may name the value visited first, is TS's alone and is never compared.
-/
def auditCollect {ε α : Type} (collect : StateT Collect m Unit) (definition : Syntax.Ref) (function : String)
    (call : Functions m → m (Except ε α)) (same : α → α → Bool) (r : Except ε α) : StateT Collect m Unit := do
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
Audits a query's output as auditCollect does, comparing the comparable values of the normalized outputs. An output that
fails its schema, or whose comparable value an Issue stops, needs no audit, because the run reports it.
-/
def resolveCollect (name : String) (input : Value) (records : Records) (now : Time) (r : Except Issue Value) :
    StateT Collect m Unit := do
  stepCollect ifs none
  let .ok output := r | return
  unless ← ifs.lastEnumerated do return
  if st.ref name ∈ (← get).reportedOrder then return
  let .ok (some output) ← normalizeOutput (m := m) st fs name output | return
  let .ok original ← fs.comparable name (.fulfilled output) | return
  let exception := reportOrder (st.ref name) (.reversedException (st.ref name) "resolve")
  let .ok raw ← ifs.reversed.resolve name input records now | exception
  let .ok (some reversed) ← normalizeOutput (m := m) st fs name raw | exception
  let .ok reordered ← fs.comparable name (.fulfilled reversed) | exception
  unless original == reordered do reportOrder (st.ref name) (.reversedResult (st.ref name) "resolve")

def decideCollect (name : String) (records : Records) (decided : Except Issue (List (List Emit))) :
    StateT Collect m Unit := do
  let .ok decided := decided | pure ()
  if decided.flatten.any (!st.lists name ·) then return
  match ← normalizeEmits (m := m) st fs name decided.flatten with
  | .ok normalized => modify (·.stepAccess (writesOf st records (orderedGroups decided normalized).flatten).values)
  | .error _ => pure ()

/--
The text that compares a value that one call made, as TS madeJson gives it. When the call created keys, each created
key becomes its entity and arrays lose their order, so that values equal up to a renaming of these keys compare equal.
-/
def madeText (keys : Keys) (created : List String) (v : Value) : String :=
  if created.isEmpty then v.canonical else
  let given := givenKeys keys created
  (v.mapStrings fun s => match given.find? (·.2 == s) with
    | some (e, _) => s!"{e}-*"
    | none => s).unorderedText

/-- The texts in code-point order, which compare two lists as multisets. -/
def sortedTexts (texts : List String) : List String := texts.mergeSort fun a b => decide (a ≤ b)

/-- Whether two answers that made a value and created keys are equal up to a renaming of the created keys. -/
def sameMade (keys : Keys) (a b : Value × List String) : Bool :=
  sortedTexts a.2 == sortedTexts b.2 && madeText keys a.2 a.1 == madeText keys b.2 b.1

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
  let audit {ε α : Type} (collect : StateT Collect m Unit) (definition : Syntax.Ref) (function : String)
      (call : Functions m → m (Except ε α)) (same : α → α → Bool) :=
    observe (call fs) (auditCollect ifs collect definition function call same)
  let collect (scope : Option Scope) := stepCollect ifs scope
  { liftFunctions fs with
    binding := fun name b input records now =>
      audit (collect none) (st.ref name) "binding" (·.binding name b input records now) (· == ·)
    requirement := fun name c input records now =>
      audit (collect none) (st.ref name) "requirement" (·.requirement name c input records now) (· == ·)
    inputRequirement := fun target c input =>
      audit (pure ()) (st.refOf target) "inputRequirement" (·.inputRequirement target c input) (· == ·)
    decide := fun name input records now =>
      observe (fs.decide name input records now) fun r => do
        auditCollect ifs (collect none) (st.ref name) "decide" (·.decide name input records now)
          (fun a b => groupTexts a == groupTexts b) r
        decideCollect st fs name records r
    ensures := fun name input before after now =>
      audit (pure ()) (st.ref name) "ensures" (·.ensures name input before after now) (· == ·)
    queryEnsures := fun name input output records =>
      audit (pure ()) (st.ref name) "queryEnsures" (·.queryEnsures name input output records) (· == ·)
    resultEnsures := fun target input output events =>
      audit (pure ()) (st.refOf target) "resultEnsures" (·.resultEnsures target input output events) (· == ·)
    invariant := fun entity record => audit (pure ()) (st.ref entity) "invariant" (·.invariant entity record) (· == ·)
    chartInvariant := fun scope records =>
      audit (pure ()) (st.ref scope.machine) "chartInvariant" (·.chartInvariant scope records) (· == ·)
    resolve := fun name input records now =>
      observe (fs.resolve name input records now) (resolveCollect st fs ifs name input records now)
    react := fun name payload records now keys =>
      audit (collect none) (st.ref name) "react" (·.react name payload records now keys)
        fun a b => sameMade keys (a.1.getD .null, a.2) (b.1.getD .null, b.2)
    initialContext := fun machine input =>
      audit (pure ()) (st.ref machine) "initialContext" (·.initialContext machine input) sameValue
    guard := fun scope records t extra =>
      audit (collect (some scope)) (st.ref scope.machine) "guard" (·.guard scope records t extra) (· == ·)
    assign := fun scope records a extra keys =>
      audit (collect (some scope)) (st.ref scope.machine) "assign" (·.assign scope records a extra keys)
        fun a b => sameMade keys (.arr [a.1, a.2.1.getD .null], a.2.2) (.arr [b.1, b.2.1.getD .null], b.2.2)
    input := fun scope records a keys =>
      audit (collect (some scope)) (st.ref scope.machine) "input" (·.input scope records a keys) (sameMade keys)
    holds := fun scope records => audit (pure ()) (st.ref scope.machine) "holds" (·.holds scope records) fun _ _ => true
    items := fun scope records =>
      audit (collect (some scope)) (st.ref scope.machine) "items" (·.items scope records)
        fun a b => textSet (a.map (·.2)) == textSet (b.map (·.2))
    offers := fun scope records control =>
      audit (collect (some scope)) (st.ref scope.machine) "offers" (·.offers scope records control)
        fun a b => textSet (a.map (·.canonical)) == textSet (b.map (·.canonical))
    showInput := fun scope records a =>
      audit (collect (some scope)) (st.ref scope.machine) "showInput" (·.showInput scope records a) sameValue
    deadlineAt := fun scope records name =>
      audit (collect (some scope)) (st.ref scope.machine) "deadlineAt" (·.deadlineAt scope records name) (· == ·)
    close := fun scope records =>
      audit (collect (some scope)) (st.ref scope.machine) "close" (·.close scope records)
        fun a b => sameValue a.1 b.1 && a.2 == b.2 }

/-- Whether steps `i` and `j` are deadlines of one tie that no line orders. -/
def tiedDeadlines (s : State) (i j : Nat) : Bool :=
  match s.steps[i]?.bind (·.tie), s.steps[j]?.bind (·.tie) with
  | some a, some b => a == b
  | _, _ => false

/--
The pairs of steps whose other order test runs, by step number in the order they began, whose names differ so that a
`stepOrder` names each, and that no cause orders: the deadlines of one tie that no line orders, whatever their steps
access, since each deadline's effects run in the later steps of its own message; and the steps of one message whose
accesses overlap and do not commute.
A run that halted (in the semantic run, or `stopped` from enabled) skips the steps after the halt, so it has none.
Precedent: dynamic partial-order reduction (Flanagan and Godefroid, POPL 2005), where dependence only selects the
orders to run.
-/
def candidates (s : State) (c : Collect) (stopped : Option Violation) : List (Nat × Nat) :=
  if (s.halted <|> stopped).isSome then [] else
  c.steps.toList.zipIdx.flatMap fun ((i, a), n) =>
    (c.steps.toList.drop (n + 1)).filterMap fun (j, b) =>
      if (tiedDeadlines s i j ||
            (s.steps[i]?.map (·.message)) == (s.steps[j]?.map (·.message)) && overlaps a.access b.access &&
              !a.commutes b) && a.name != b.name && !leadsTo s i j then
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
