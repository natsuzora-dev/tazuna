import Tazuna.Ir.Functions
import Tazuna.Verify.Read
import Tazuna.Explore.StepOrders
import Tazuna.Explore.Moves
import Tazuna.Explore.Enabled
import Tazuna.Explore.Fingerprint
import Tazuna.Explore.Coverage
import Tazuna.Sim.Run
import Tazuna.Sim.Trace

/-!
The runs that the CLI's test command asks of the engine: each scenario simulated, the step orders of its processings
searched, and the paths after it explored, with what every running service reports. The spec functions run as the
structure's IR (Ir.functionsOf).
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Explore

/-- What an instrumented simulation collects: one Collect per running service, and the service whose processing runs. -/
structure Acting where
  current : String := ""
  collects : List (String × Collect) := []

abbrev ActingIO := StateT Acting IO

def Acting.collect (a : Acting) (service : String) : Collect := (a.collects.lookup service).getD {}

/-- `x` run on the Collect of `service`. -/
def focus {α : Type} (service : String) (x : StateT Collect IO α) : ActingIO α := fun a => do
  let (r, c) ← x.run (a.collect service)
  pure (r, { a with collects := (service, c) :: a.collects.filter (·.1 != service) })

instance : MonadNote ActingIO where
  note
    | .bug message => throw (IO.userError message)
    | n => do focus (← get).current (MonadNote.note n : StateT Collect IO Unit)

instance : Sim.MonadActing ActingIO where
  acting service x := do
    let previous := (← get).current
    modify ({ · with current := service })
    let r ← x
    modify ({ · with current := previous })
    pure r

/-- The notes of a run outside a simulation, of which the engine hears only a bug, and stops on it. -/
instance : MonadNote IO where
  note
    | .bug message => throw (IO.userError message)
    | _ => pure ()

/-- The instrumented functions of each running service of `start`, which collect into that service's Collect. -/
def instrumentedOf (start : Sim.World) : IO (String → Functions ActingIO) := do
  let last ← IO.mkRef {}
  pure fun service =>
    match start.services.lookup service with
    | none => Ir.unansweredFunctions.hoist liftM
    | some st => (instrument st (Ir.functionsOf st last) (Ir.instrumentOf last)).hoist (focus service)

/-- A world with what each running service's instrumented functions collected on the way to it. -/
structure Ran where
  world : Sim.World
  acting : Acting

def Ran.execution (r : Ran) : Execution := { world := r.world, collect := r.acting.collect }

/-- The value of a definition's part as verify reads it. -/
def readIn (spec : Spec.Structure) (d : Spec.Definition) (part : Verify.Part) (v : Value) : IO CValue :=
  pure (Verify.readValueOf spec d part v)

/-- The comparison of two runs' trace lines of `service`, by which the step-order search compares them. -/
def compareFor (spec : Spec.Structure) (service : String) : Compare IO := fun renamed expected actual => do
  pure ((← Verify.compareTraces spec service (readIn spec) renamed expected actual).mapError fun
    | .mismatch m => Difference.outputs m.toViolation
    | .uncomparable u => .outputs u.toViolation
    | .after line subject snapshot trace => .after line subject snapshot trace)

/-- The scenario executed from its start, with the step orders `stepOrders`. -/
def executeWith (spec : Spec.Structure) (sc : Scenario) (stepOrders : List (Scenario.Origin × String × List StepName)) :
    IO Execution := do
  let start ← Sim.World.start spec sc
  let start := { start with stepOrders }
  let (world, acting) ← (Sim.execute spec (← instrumentedOf start) start sc).run {}
  pure { world, collect := acting.collect }

/-- The violations that the step orders of the processings of `executed` from line `from` on find. -/
def stepOrderViolations (spec : Spec.Structure) (sc : Scenario) (executed : Execution) («from» : Nat) :
    IO (List Violation) := do
  let searched ← stepOrderChanges (compareFor spec) (executeWith spec) sc executed «from»
  pure (searched.filterMap (·.search.found))

def halted (w : Sim.World) : Bool := w.halted.isSome || w.states.any (·.2.halted.isSome)

/-- A violation with the running service whose list it is in, if any. -/
structure Reported where
  violation : Violation
  service : Option String

/-- What a running service reports: its own violations, then those its instrument collected, then its halt. -/
def reportedOf (r : Ran) (service : String) (s : State) : List Violation :=
  reportedViolations s (r.acting.collect service) none

/-- The violations that the running services of `child` added since `parent`, which `child` continues. -/
def addedSince (parent child : Ran) : List Reported :=
  child.world.states.flatMap fun (service, s) =>
    let before := parent.world.state service
    let collected := (child.acting.collect service).violations
    let was := (parent.acting.collect service).violations.length
    let halt := match s.halted, before.halted with
      | some f, none => [f.toViolation]
      | _, _ => []
    ((s.violations.drop before.violations.length).map (·.toViolation) ++ collected.drop was ++ halt).map
      ({ violation := ·, service := some service })

/--
Whether the lines appended after `parent` are lines that someone could write: no report of the simulation and no
InvalidInput violation of a running service. explore discards the others.
-/
def givable (parent child : Ran) : Bool :=
  child.world.violations.length == parent.world.violations.length &&
    (child.world.halted.isNone || parent.world.halted.isSome) &&
    !(addedSince parent child).any (·.violation.kind.startsWith "InvalidInput.")

/-- A violation that an explored path reports, with the lines that the path appended to the scenario. -/
structure Found where
  violation : Violation
  service : Option String
  appended : List Scenario.Line

derive_wire Found serialize_only skip_serializing_none

/-- What explore found after a scenario, the parts it reached, and how many worlds it visited. -/
structure Explored where
  found : List Found := []
  reached : List Uncovered := []
  visited : Nat := 0

def Explored.reach (x : Explored) (r : Ran) : Explored :=
  if halted r.world then x else
  { x with reached := r.world.states.foldl (fun acc (service, _) =>
      (r.acting.collect service).reached.foldl (fun acc u => if acc.contains u then acc else acc ++ [u]) acc) x.reached }

/--
Explores the scenario: executes its lines, and the paths that append moves facing the own service, up to the depth of
its service's `explore()`, breadth-first, without extending a path whose world an earlier path reached, and discarding
a path whose last line no one could write (givable). Each path continues its parent's execution. It reports the
violations that each path added, the step orders of its last move's processings that change their result, and the
fault of computing the moves after it.
-/
def explore (spec : Spec.Structure) (sc : Scenario) : IO Explored := do
  let start ← Sim.World.start spec sc
  let fsOf ← instrumentedOf start
  let domains := (← exploreOf spec sc.service).domains
  let bound := (← exploreOf spec sc.service).depth
  let (world, acting) ← (Sim.execute spec fsOf start sc).run {}
  let base : Ran := { world, acting }
  let x : Explored := ({} : Explored).reach base
  if halted base.world || !base.world.violations.isEmpty then return x
  let own := sc.service
  let movesAfter (appended : List Scenario.Line) (r : Ran) : IO (Except Violation (List Move)) := do
    if halted r.world then return .ok []
    let some st := r.world.services.lookup own | return .ok []
    let s := r.world.state own
    let ran : ActingIO (Except Violation (List Move)) := do
      match ← Explore.enabled st (fsOf own) s with
      | .error f => pure (.error (Finding.fault f).toViolation)
      | .ok e => pure (.ok (← Explore.moves spec st { sc, lines := sc.lines ++ appended, domains } r.world e))
    pure (← ran.run' r.acting)
  let continued (parent : Ran) (appended : List Scenario.Line) (move : Move) : IO Ran := do
    let lines := sc.lines ++ appended ++ move
    let full := { sc with lines }
    let ran : ActingIO Sim.World :=
      ((lines.zipIdx).drop (sc.lines.length + appended.length)).foldlM (init := parent.world) fun w (l, i) =>
        w.step fsOf full l i
    let (world, acting) ← ran.run parent.acting
    pure { world, acting }
  let found ← IO.mkRef x
  let visited ← IO.mkRef ({} : Std.HashSet String)
  -- As search.ts extends a path: within the depth, at a fresh fingerprint, with the moves after it queued.
  let extend (path : List Move) (r : Ran) : IO (List (List Move × Ran × Move)) := do
    if path.length >= bound then return []
    let fingerprint ← worldFingerprint r.world
    if (← visited.get).contains fingerprint then return []
    visited.modify (·.insert fingerprint)
    let appended := path.flatten
    match ← movesAfter appended r with
    | .error v =>
      found.modify fun x => { x with found := x.found ++ [{ violation := v, service := some own, appended }] }
      return []
    | .ok moves => return moves.map (path, r, ·)
  let mut queue := (← extend [] base).toArray
  let mut i := 0
  while h : i < queue.size do
    let (path, parent, move) := queue[i]
    i := i + 1
    let appended := path.flatten
    let child ← continued parent appended move
    if !givable parent child then continue
    let added := appended ++ move
    let orders ← stepOrderViolations spec { sc with lines := sc.lines ++ added } child.execution
      (sc.lines.length + appended.length)
    found.modify fun x =>
      let x := x.reach child
      { x with found := x.found ++ (addedSince parent child).map (fun rep =>
          { violation := rep.violation, service := rep.service, appended := added }) ++
        orders.map ({ violation := ·, service := none, appended := added }) }
    queue := queue ++ (← extend (path ++ [move]) child).toArray
  pure { (← found.get) with visited := (← visited.get).size }

/-- What a running service of a scenario's simulation reports, and its trace as its snapshot holds it. -/
structure ServiceRun where
  service : String
  violations : List Violation
  lines : List TraceLine

derive_wire ServiceRun serialize_only

/-- What test finds of one scenario: its simulation, the step orders of its processings, and the paths after it. -/
structure ScenarioRun where
  /-- The simulation's InvalidScenario violations, then its halting one. -/
  violations : List Violation
  stepOrders : List Violation
  services : List ServiceRun
  /-- Whether the simulation or a running service halted, so that no snapshot is compared or written. -/
  halted : Bool
  found : List Found
  visited : Nat

derive_wire ScenarioRun serialize_only

/-- The simulation, step-order search and exploration of `sc`, and the parts that its exploration reached. -/
def runScenario (spec : Spec.Structure) (sc : Scenario) : IO (ScenarioRun × List Uncovered) := do
  let start ← Sim.World.start spec sc
  let (world, acting) ← (Sim.simulate spec (← instrumentedOf start) start sc).run {}
  let simulated : Ran := { world, acting }
  let orders ← stepOrderViolations spec sc simulated.execution 0
  let services := world.states.map fun (service, s) =>
    { service, violations := reportedOf simulated service s
      lines := (Sim.trace s).map fun (l, after, created) => Sim.traceLineOf service l after created }
  let explored ← explore spec sc
  pure ({ violations := world.violations.map (·.toViolation) ++ (world.halted.map (·.toViolation)).toList
          stepOrders := orders, services, halted := halted world, found := explored.found
          visited := explored.visited }, explored.reached)

/-- What test finds of each scenario, in order, and the parts of the spec that no exploration reached. -/
def test (spec : Spec.Structure) (scenarios : List Scenario) : IO (List ScenarioRun × List Violation) := do
  let (runs, reached) ← scenarios.foldlM (init := ([], [])) fun (runs, reached) sc => do
    let (run, more) ← runScenario spec sc
    pure (runs ++ [run], more.foldl (fun acc u => if acc.contains u then acc else acc ++ [u]) reached)
  pure (runs, (Explore.uncovered spec reached).map (·.toViolation))

end Tazuna.Engine
