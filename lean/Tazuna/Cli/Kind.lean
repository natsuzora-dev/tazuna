import Tazuna.Semantics.Step

/-- A step that cannot happen in a correct spec, by kind (`Tazuna.Ir.Fault` without its details). -/
inductive Tazuna.FaultKind : Type
  | invariant | ensures | cascadeLimit | answerUnmatched | invalidEffect
deriving DecidableEq

/-- What `test` found for one scenario. -/
inductive Tazuna.TestKind : Type
  /-- The trace equals the snapshot. -/
  | passed
  /-- The trace differs from the snapshot, or there is no snapshot: exit code 1. -/
  | changed
  /-- `test --update` wrote the snapshot. -/
  | written
  /-- A step cannot run, such as an answer that matches no pending request: exit code 1. -/
  | badStep
deriving DecidableEq

/-- Every kind of line the engine writes to stdout. test/e2e holds one case per kind, enumerated from `Kind.all`. -/
inductive Tazuna.Kind : Type
  /-- The IR the launcher handed over does not load: a converter bug, reported with exit code 4. -/
  | invalidIr
  /-- The spec's structure breaks a rule: the spec must change, exit code 1. -/
  | illegal (k : Tazuna.Ir.Illegal)
  /-- A scenario or a trace made the spec fault: the spec must change, exit code 1. -/
  | fault (k : Tazuna.FaultKind)
  | test (k : Tazuna.TestKind)
  /-- Every window of the trace equals the spec's out lines. -/
  | verifyPassed
  /-- A window of the trace differs from the spec's out lines: exit code 1. -/
  | verifyDiffers
  /-- A trace line does not read as a line of the service, or breaks the order of time: exit code 1. -/
  | traceInvalid

namespace Tazuna

def FaultKind.all : List FaultKind := [.invariant, .ensures, .cascadeLimit, .answerUnmatched, .invalidEffect]

theorem FaultKind.mem_all (k : FaultKind) : k ∈ FaultKind.all := by cases k <;> simp [FaultKind.all]

def FaultKind.name : FaultKind → String
  | .invariant => "invariant"
  | .ensures => "ensures"
  | .cascadeLimit => "cascadeLimit"
  | .answerUnmatched => "answerUnmatched"
  | .invalidEffect => "invalidEffect"

def Ir.Fault.kind : Ir.Fault → FaultKind
  | .invariant _ => .invariant
  | .ensures _ => .ensures
  | .cascadeLimit => .cascadeLimit
  | .answerUnmatched _ => .answerUnmatched
  | .invalidEffect .. => .invalidEffect

def TestKind.all : List TestKind := [.passed, .changed, .written, .badStep]

theorem TestKind.mem_all (k : TestKind) : k ∈ TestKind.all := by cases k <;> simp [TestKind.all]

def TestKind.name : TestKind → String
  | .passed => "passed"
  | .changed => "changed"
  | .written => "written"
  | .badStep => "badStep"

namespace Kind

/-- The name a line carries as its `kind`, such as `Illegal.wireName`. -/
def name : Kind → String
  | invalidIr => "Internal.invalidIr"
  | illegal k => "Illegal." ++ k.name
  | fault k => "Fault." ++ k.name
  | test k => "Test." ++ k.name
  | verifyPassed => "Verify.passed"
  | verifyDiffers => "Verify.differs"
  | traceInvalid => "Trace.invalid"

def all : List Kind :=
  invalidIr :: Ir.Illegal.all.map illegal ++ FaultKind.all.map fault ++ TestKind.all.map test ++
    [verifyPassed, verifyDiffers, traceInvalid]

theorem mem_all (k : Kind) : k ∈ all := by
  cases k with
  | illegal k => simp [all, Ir.Illegal.mem_all]
  | fault k => simp [all, FaultKind.mem_all]
  | test k => simp [all, TestKind.mem_all]
  | _ => simp [all]

end Kind

end Tazuna
