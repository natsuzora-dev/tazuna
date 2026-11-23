import Tazuna.Semantics.Eval.Functions
import Tazuna.Semantics.Verify.Read
import Tazuna.Semantics.Explore.Instrument
import Tazuna.Semantics.Sim.Run
import Tazuna.Semantics.Sim.Trace

/-!
The runs that the CLI's test command asks of the engine: each scenario simulated, with what every running service
reports. The spec functions run as the structure's IR (Eval.functionsOf).
-/

namespace Tazuna.Engine

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Explore

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

/-- The functions of `st`, instrumented to collect what each call reads and writes. -/
def instrumentedFunctions (st : Service) : IO (Functions (StateT Collect IO)) := do
  let last ← IO.mkRef {}
  pure (instrument st (Eval.functionsOf st last) (Eval.instrumentOf last))

/-- The instrumented functions of each running service of `start`, which collect into that service's Collect. -/
def instrumentedOf (start : Sim.World) : IO (String → Functions ActingIO) := do
  let last ← IO.mkRef {}
  pure fun service =>
    match start.services.lookup service with
    | none => (Eval.functionsOf default last).hoist liftM
    | some st => (instrument st (Eval.functionsOf st last) (Eval.instrumentOf last)).hoist (focus service)

def halted (w : Sim.World) : Bool := w.halted.isSome || w.states.any (·.2.halted.isSome)

/-- What a running service of a scenario's simulation reports, and its trace as its snapshot holds it. -/
structure ServiceRun where
  service : String
  violations : List Violation
  lines : List TraceLine

derive_wire ServiceRun serialize_only

/-- What test finds of one scenario. -/
structure ScenarioRun where
  /-- The simulation's InvalidScenario violations, then its halting one. -/
  violations : List Violation
  services : List ServiceRun
  /-- Whether the simulation or a running service halted, so that no snapshot is compared or written. -/
  halted : Bool

derive_wire ScenarioRun serialize_only

/-- The simulation of `sc`. -/
def runScenario (spec : Ir.Structure) (sc : Scenario) : IO ScenarioRun := do
  let start ← Sim.World.start spec sc
  let (world, acting) ← (Sim.simulate spec (← instrumentedOf start) start sc).run {}
  let services := world.states.map fun (service, s) =>
    { service, violations := reportedViolations s (acting.collect service) none
      lines := (Sim.trace s).map fun (l, after, created) => Sim.traceLineOf service l after created }
  pure { violations := world.violations.map (·.toViolation) ++ (world.halted.map (·.toViolation)).toList
         services, halted := halted world }

/-- What test finds of each scenario, in order. -/
def test (spec : Ir.Structure) (scenarios : List Scenario) : IO (List ScenarioRun) :=
  scenarios.mapM (runScenario spec)

end Tazuna.Engine
