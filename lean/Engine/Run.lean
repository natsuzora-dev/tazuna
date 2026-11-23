import Tazuna.Ir.Functions
import Tazuna.Verify.Read
import Tazuna.Explore.StepOrders
import Tazuna.Sim.Run
import Tazuna.Sim.Trace

/-!
The runs that the CLI's test command asks of the engine: each scenario simulated and the step orders of its processings
searched, with what every running service reports. The spec functions run as the
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
    | none => (Ir.functionsOf default last).hoist liftM
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

/-- What a running service reports: its own violations, then those its instrument collected, then its halt. -/
def reportedOf (r : Ran) (service : String) (s : State) : List Violation :=
  reportedViolations s (r.acting.collect service) none

/-- What a simulation shows of one running service: its trace lines, its violations, and its candidates. -/
structure SimulatedService where
  service : String
  lines : List TraceLine
  violations : List Violation
  candidates : List (Nat × Nat)

derive_wire SimulatedService serialize_only

/-- What a running service of a scenario's simulation reports, and its trace as its snapshot holds it. -/
structure ServiceRun where
  service : String
  violations : List Violation
  lines : List TraceLine

derive_wire ServiceRun serialize_only

/-- What test finds of one scenario: its simulation and the step orders of its processings. -/
structure ScenarioRun where
  /-- The simulation's InvalidScenario violations, then its halting one. -/
  violations : List Violation
  stepOrders : List Violation
  services : List ServiceRun
  /-- Whether the simulation or a running service halted, so that no snapshot is compared or written. -/
  halted : Bool

derive_wire ScenarioRun serialize_only

/-- The simulation and step-order search of `sc`. -/
def runScenario (spec : Spec.Structure) (sc : Scenario) : IO ScenarioRun := do
  let start ← Sim.World.start spec sc
  let (world, acting) ← (Sim.simulate spec (← instrumentedOf start) start sc).run {}
  let simulated : Ran := { world, acting }
  let orders ← stepOrderViolations spec sc simulated.execution 0
  let services := world.states.map fun (service, s) =>
    { service, violations := reportedOf simulated service s
      lines := (Sim.trace s).map fun (l, after, created) => Sim.traceLineOf service l after created }
  pure { violations := world.violations.map (·.toViolation) ++ (world.halted.map (·.toViolation)).toList
         stepOrders := orders, services, halted := halted world }

/--
The simulation of `sc`: each running service's trace lines, violations and candidates, and the simulation's violations
and its halting one.
-/
def simulate (spec : Spec.Structure) (sc : Scenario) :
    IO (List SimulatedService × List Sim.InvalidScenario × Option Sim.InvalidScenario) := do
  let start ← Sim.World.start spec sc
  let (w, acting) ← (Sim.simulate spec (← instrumentedOf start) start sc).run {}
  let services := w.states.map fun (service, s) =>
    let c := acting.collect service
    { service, lines := s.lines.toList.map (Sim.traceLineOf service · [] [])
      violations := reportedViolations s c none
      candidates := if (w.services.lookup service).isSome then candidates s c none else [] }
  pure (services, w.violations, w.halted)

/-- What test finds of each scenario, in order. -/
def test (spec : Spec.Structure) (scenarios : List Scenario) : IO (List ScenarioRun) :=
  scenarios.mapM (runScenario spec)

end Tazuna.Engine
