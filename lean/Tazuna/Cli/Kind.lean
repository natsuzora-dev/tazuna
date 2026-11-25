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

/-- What `prove` found for one question. -/
inductive Tazuna.ProveKind : Type
  /-- No step of the input kind from a state of the right shape breaks the target. -/
  | proved
  /-- No step of the input kind from a state of the right shape leaves the slots or a side condition. -/
  | withinBounds
  /-- A state and input whose step breaks the target: exit code 1. -/
  | violated
deriving DecidableEq

/-- Why `prove` has no verdict for a question: exit code 2 when nothing is violated. -/
inductive Tazuna.UndecidedKind : Type
  /-- The solver answered unknown or ran out of time or resources. -/
  | unknown
  /-- A step of the input kind can leave the slots its bounds give, so the step questions do not cover it. -/
  | boundReached
  /-- The spec uses what the encoding has no terms for. -/
  | limit
  /-- A string literal holds a code point above U+2FFFF, outside SMT-LIB's strings. -/
  | unencodableString
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
  | prove (k : Tazuna.ProveKind)
  | undecided (k : Tazuna.UndecidedKind)

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
  | .answerUnmatched => .answerUnmatched
  | .invalidEffect .. => .invalidEffect

def TestKind.all : List TestKind := [.passed, .changed, .written, .badStep]

theorem TestKind.mem_all (k : TestKind) : k ∈ TestKind.all := by cases k <;> simp [TestKind.all]

def TestKind.name : TestKind → String
  | .passed => "passed"
  | .changed => "changed"
  | .written => "written"
  | .badStep => "badStep"

def ProveKind.all : List ProveKind := [.proved, .withinBounds, .violated]

theorem ProveKind.mem_all (k : ProveKind) : k ∈ ProveKind.all := by cases k <;> simp [ProveKind.all]

def ProveKind.name : ProveKind → String
  | .proved => "proved"
  | .withinBounds => "withinBounds"
  | .violated => "violated"

def UndecidedKind.all : List UndecidedKind := [.unknown, .boundReached, .limit, .unencodableString]

theorem UndecidedKind.mem_all (k : UndecidedKind) : k ∈ UndecidedKind.all := by cases k <;> simp [UndecidedKind.all]

def UndecidedKind.name : UndecidedKind → String
  | .unknown => "unknown"
  | .boundReached => "boundReached"
  | .limit => "limit"
  | .unencodableString => "unencodableString"

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
  | prove k => "Prove." ++ k.name
  | undecided k => "Undecided." ++ k.name

def all : List Kind :=
  invalidIr :: Ir.Illegal.all.map illegal ++ FaultKind.all.map fault ++ TestKind.all.map test ++
    [verifyPassed, verifyDiffers, traceInvalid] ++ ProveKind.all.map prove ++ UndecidedKind.all.map undecided

theorem mem_all (k : Kind) : k ∈ all := by
  cases k with
  | illegal k => simp [all, Ir.Illegal.mem_all]
  | fault k => simp [all, FaultKind.mem_all]
  | test k => simp [all, TestKind.mem_all]
  | prove k => simp [all, ProveKind.mem_all]
  | undecided k => simp [all, UndecidedKind.mem_all]
  | _ => simp [all]

end Kind

end Tazuna
