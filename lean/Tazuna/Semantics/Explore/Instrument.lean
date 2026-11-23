import Tazuna.Semantics.Service.Restart
import Tazuna.Semantics.Explore.RegionOrderDependent

/-!
This module defines the instrumented run. It wraps Functions without changing the semantic run and collects what the
transitions of a microstep read and assign, which the check of parallel regions compares, and the parts the run reached.
-/

namespace Tazuna.Semantics.Explore

open Tazuna.Ir Tazuna.Semantics.Service

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

def regionFindings (chart : Ir.Ref) (access : Nat → TransitionAccess) (p : RegionPair) : List RegionOrderDependent :=
  let a := access p.first
  let b := access p.second
  (b.writes.filterMap fun v =>
    if v ∈ a.writes then some (.bothAssign chart p.state p.firstRef p.secondRef v.2)
    else if v ∈ a.reads then some (.assignRead chart p.state p.secondRef p.firstRef v.2) else none) ++
  ((a.writes.filter (· ∉ b.writes)).filterMap fun v =>
    if v ∈ b.reads then some (.assignRead chart p.state p.firstRef p.secondRef v.2) else none)

structure Collect where
  transition : Option Nat := none
  transitions : List (Nat × TransitionAccess) := []
  violations : List Violation := []
  /-- The parts that the run reached, each once, in the order first reached. -/
  reached : List Uncovered := []
deriving Repr, Inhabited

/-- The function that the instrumented run asks besides Functions: the chart values that the previous call read and assigned. -/
structure InstrumentFunctions (m : Type → Type) where
  lastAccess : m Access

def Collect.accessOf (c : Collect) (k : Nat) : TransitionAccess := (c.transitions.lookup k).getD {}

def Collect.addAccess (c : Collect) (scope : Scope) (a : Access) : Collect :=
  match c.transition with
  | none => c
  | some k =>
    let p := c.accessOf k
    let p := { reads := (a.reads scope).foldl addNew p.reads, writes := (a.writes scope).foldl addNew p.writes }
    { c with transitions := (c.transitions.filter (·.1 != k)) ++ [(k, p)] }

def Collect.report (c : Collect) (v : Violation) : Collect :=
  if v ∈ c.violations then c else { c with violations := c.violations ++ [v] }

def Collect.checkRegions (c : Collect) (check : RegionCheck) : Collect :=
  let found := if check.halted then [] else check.pairs.flatMap (regionFindings check.chart c.accessOf)
  let c := found.foldl (fun c m => c.report m.toViolation) c
  { c with transition := none, transitions := [] }

instance {m : Type → Type} [Monad m] : MonadNote (StateT Collect m) where
  note n := modify fun c =>
    match n with
    | .transitionPart k => { c with transition := some k }
    | .microstepEnds check => c.checkRegions check
    | .reached part => if c.reached.contains part then c else { c with reached := c.reached ++ [part] }
    | .bug _ => c

/-- The functions that ask `fs` and carry each answer into `n` by `f`. -/
def _root_.Tazuna.Semantics.Service.Functions.hoist {m n : Type → Type} (f : {α : Type} → m α → n α) (fs : Functions m) : Functions n where
  parse a b := f (fs.parse a b)
  unordered a b := f (fs.unordered a b)
  binding a b c d e g := f (fs.binding a b c d e g)
  requirement a b c d e g := f (fs.requirement a b c d e g)
  inputRequirement a b c := f (fs.inputRequirement a b c)
  decide a b c d e := f (fs.decide a b c d e)
  ensures a b c d e g := f (fs.ensures a b c d e g)
  queryEnsures a b c d e := f (fs.queryEnsures a b c d e)
  resultEnsures a b c d e := f (fs.resultEnsures a b c d e)
  invariant a b c := f (fs.invariant a b c)
  responses a b c := f (fs.responses a b c)
  serviceInvariant a b := f (fs.serviceInvariant a b)
  chartInvariant a b := f (fs.chartInvariant a b)
  resolve a b c d e := f (fs.resolve a b c d e)
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

def stepCollect (scope : Scope) : StateT Collect m Unit := do
  let a ← ifs.lastAccess
  modify (·.addAccess scope a)

/--
Functions that return the same values as `fs.sorting st`, so a run is given its spec functions sorted as it keeps their
values, and collect what each call reads and writes.
-/
def instrument : Functions (StateT Collect m) :=
  let fs := fs.sorting st
  let collect {α : Type} (scope : Scope) (x : m α) : StateT Collect m α := observe x fun _ => stepCollect ifs scope
  { liftFunctions fs with
    chartInvariant := fun scope records => collect scope (fs.chartInvariant scope records)
    guard := fun scope records t c extra => collect scope (fs.guard scope records t c extra)
    assign := fun scope records a extra keys => collect scope (fs.assign scope records a extra keys)
    input := fun scope records a keys => collect scope (fs.input scope records a keys)
    held := fun scope records n edge extra => collect scope (fs.held scope records n edge extra)
    items := fun scope records => collect scope (fs.items scope records)
    offers := fun scope records control => collect scope (fs.offers scope records control)
    showInput := fun scope records a => collect scope (fs.showInput scope records a)
    deadlineAt := fun scope records name => collect scope (fs.deadlineAt scope records name)
    close := fun scope records => collect scope (fs.close scope records) }

/--
The violations that a run reports: the semantic violations, the collected violations, and then the halting violation
(from the semantic run, or `stopped` from enabled).
-/
def reportedViolations (s : Service.State) (c : Collect) (stopped : Option Finding) : List Violation :=
  s.violations.map (·.toViolation) ++ c.violations ++ ((s.halted <|> stopped).map (·.toViolation)).toList

end

end Tazuna.Semantics.Explore
