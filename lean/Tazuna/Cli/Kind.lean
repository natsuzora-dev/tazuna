import Tazuna.Semantics.Step
import Tazuna.Cli.Restricted

/-- A step that cannot happen in a correct spec, by kind (`Tazuna.Ir.Fault` without its details). -/
inductive Tazuna.FaultKind : Type
  | invariant | ensures | cascadeLimit | answerUnmatched | invalidEffect
deriving DecidableEq

/-- What `test` found for one scenario. -/
inductive Tazuna.TestKind : Type
  /-- The trace equals the snapshot, and verify passes it. -/
  | passed
  /-- The trace differs from the snapshot, or there is no snapshot. -/
  | changed
  /-- `test --update` wrote the snapshot, a trace verify passes. -/
  | written
  /-- A step cannot run, such as an answer that matches no pending request. -/
  | badStep
deriving DecidableEq

/-- What `prove` found for one question. -/
inductive Tazuna.ProveKind : Type
  /-- No step of the input kind from a state of the right shape breaks the target, and no step of any kind goes past
  the slots the bounds give, while every input and the initial state fit them; so every state a run reaches is within
  the slots, and the line speaks of every run. -/
  | proved
  /-- No step of the input kind from a state of the right shape breaks the target while it stays within the slots,
  but such a step can go past them: the line names every bound a step of the service can go past (its tables and
  bags, and its pending requests where it sends any), the same for every run. For a bounded response: no run from the
  initial state of at most the spec's `steps` inputs within the slots, on which its `assumes` hold (valid inputs, no
  step faults, timely clock lines), violates it; the line names those bounds and `steps`. A success, as Alloy reports
  no counterexample within its scope. -/
  | withinBounds
  /-- A state and input whose step breaks the target, or for a bounded response a run from the initial state that
  violates it. -/
  | violated
deriving DecidableEq

/-- What `generate` found for one target. -/
inductive Tazuna.GenerateKind : Type
  /-- A run from the initial state whose last step shows the target's class of out line: its trace is written. -/
  | reached
  /-- No run of at most the spec's steps within the slots, on which its `assumes` hold (valid inputs, no step faults),
  shows the target's class at any step. Not "unreachable": a longer run or larger slots may reach it. -/
  | unreached
deriving DecidableEq

/-- Why a question or a trace has no verdict. -/
inductive Tazuna.UndecidedKind : Type
  /-- The solver answered unknown, or ran out of its resource limit, which stops it at the same point on every
  machine. -/
  | unknown
  /-- The solver ran past the wall-clock safety net before its resource limit stopped it: a solver fault, and the one
  line whose verdict may depend on the machine. -/
  | timeout
  /-- The spec uses what the encoding has no terms for, or a pair's counterexample needs a search for a renaming
  larger than prove runs or a comparison of the functions its two orders keep, or verify, or test replaying a
  scenario's trace, ran out of tries to bind the trace's names to the spec's ids. -/
  | limit
  /-- A string literal holds a code point above U+2FFFF, outside SMT-LIB's strings. -/
  | unencodableString
  /-- Two own steps whose orders the solver found different, with each step keeping the ids it made, end the same
  once those ids are renamed, as the oracle names ids by first appearance. The two orders are shown. -/
  | upToRenaming
deriving DecidableEq

/-- A bug of tazuna's own: no spec reaches it. -/
inductive Tazuna.InternalKind : Type
  /-- The IR the launcher handed over does not load: a converter bug. -/
  | invalidIr
  /-- The converter could not make sense of a module that `gleam build` accepted: a converter bug. -/
  | convert
  /-- The engine met a state its proofs rule out, or that it checks at run time where no proof exists yet: a search's
  job never ran, a solver's model does not decode, an encoder refused for a case the loaded program's types rule out
  (`Smt.Unexpected`), or verify would not pass the trace of one of tazuna's own scenario runs. -/
  | engine
deriving DecidableEq

/-- Why a command did not run as asked; the spec is not judged. -/
inductive Tazuna.UsageKind : Type
  /-- The command line names no command, or its arguments do not read as the command's: a missing root, an unknown
  option or kind. -/
  | arguments
  /-- The system refused what the command needs: a file or directory to read or write, a program to run (the engine,
  z3), or `TAZUNA_ENGINE` is not set. -/
  | system
deriving DecidableEq

/-- Every kind of line tazuna writes to stdout, the launcher's included. test/e2e holds one case per kind it covers
(`Kind.e2e`), enumerated from `Kind.all`. -/
inductive Tazuna.Kind : Type
  | internal (k : Tazuna.InternalKind)
  | usage (k : Tazuna.UsageKind)
  /-- Gleam outside the spec subset, which the launcher reports before Lean sees the spec: the spec must change. -/
  | restricted (k : Tazuna.Restricted)
  /-- The spec's structure breaks a rule: the spec must change. -/
  | illegal (k : Tazuna.Ir.Illegal)
  /-- The spec breaks no structure rule; `check` prints one line per service. -/
  | checkPassed
  /-- A scenario or a trace made the spec fault: the spec must change. -/
  | fault (k : Tazuna.FaultKind)
  | test (k : Tazuna.TestKind)
  /-- Every window of the trace equals the spec's out lines. -/
  | verifyPassed
  /-- A window of the trace differs from the spec's out lines. -/
  | verifyDiffers
  /-- A trace line does not read as a line of the service, or breaks the order of time. -/
  | traceInvalid
  | prove (k : Tazuna.ProveKind)
  | generate (k : Tazuna.GenerateKind)
  | undecided (k : Tazuna.UndecidedKind)
  /-- What a kind of line means, as `explain` prints it: the line's meaning, the theorems it rests on (as
  lean/Tazuna/Axioms.lean names its roots), its fields and its exit code. -/
  | explain

namespace Tazuna

def InternalKind.all : List InternalKind := [.invalidIr, .convert, .engine]

theorem InternalKind.mem_all (k : InternalKind) : k ∈ InternalKind.all := by cases k <;> simp [InternalKind.all]

def InternalKind.name : InternalKind → String
  | .invalidIr => "invalidIr"
  | .convert => "convert"
  | .engine => "engine"

def UsageKind.all : List UsageKind := [.arguments, .system]

theorem UsageKind.mem_all (k : UsageKind) : k ∈ UsageKind.all := by cases k <;> simp [UsageKind.all]

def UsageKind.name : UsageKind → String
  | .arguments => "arguments"
  | .system => "system"

/-- What a command's run comes to, by its worst line: the exit code. -/
inductive Exit : Type
  | ok | undecided | violation | usage | internal

/-- The exit code. Undecided ranks below a violation: one violated line decides the run. -/
def Exit.code : Exit → UInt32
  | .ok => 0
  | .violation => 1
  | .undecided => 2
  | .usage => 3
  | .internal => 4

def Exit.rank : Exit → Nat
  | .ok => 0
  | .undecided => 1
  | .violation => 2
  | .usage => 3
  | .internal => 4

/-- The worse of two outcomes. -/
def Exit.max (a b : Exit) : Exit := if a.rank < b.rank then b else a

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

def GenerateKind.all : List GenerateKind := [.reached, .unreached]

theorem GenerateKind.mem_all (k : GenerateKind) : k ∈ GenerateKind.all := by cases k <;> simp [GenerateKind.all]

def GenerateKind.name : GenerateKind → String
  | .reached => "reached"
  | .unreached => "unreached"

def UndecidedKind.all : List UndecidedKind := [.unknown, .timeout, .limit, .unencodableString, .upToRenaming]

theorem UndecidedKind.mem_all (k : UndecidedKind) : k ∈ UndecidedKind.all := by cases k <;> simp [UndecidedKind.all]

def UndecidedKind.name : UndecidedKind → String
  | .unknown => "unknown"
  | .timeout => "timeout"
  | .limit => "limit"
  | .unencodableString => "unencodableString"
  | .upToRenaming => "upToRenaming"

namespace Kind

/-- The name a line carries as its `kind`, such as `Illegal.wireName`. -/
def name : Kind → String
  | internal k => "Internal." ++ k.name
  | usage k => "Usage." ++ k.name
  | restricted k => "Restricted." ++ k.name
  | illegal k => "Illegal." ++ k.name
  | checkPassed => "Check.passed"
  | fault k => "Fault." ++ k.name
  | test k => "Test." ++ k.name
  | verifyPassed => "Verify.passed"
  | verifyDiffers => "Verify.differs"
  | traceInvalid => "Trace.invalid"
  | prove k => "Prove." ++ k.name
  | generate k => "Generate." ++ k.name
  | undecided k => "Undecided." ++ k.name
  | explain => "Explain.kind"

def all : List Kind :=
  InternalKind.all.map internal ++ UsageKind.all.map usage ++ Restricted.all.map restricted ++ Ir.Illegal.all.map illegal ++ [checkPassed] ++ FaultKind.all.map fault ++ TestKind.all.map test ++
    [verifyPassed, verifyDiffers, traceInvalid] ++ ProveKind.all.map prove ++
    GenerateKind.all.map generate ++ UndecidedKind.all.map undecided ++ [explain]

theorem mem_all (k : Kind) : k ∈ all := by
  cases k with
  | internal k => simp [all, InternalKind.mem_all]
  | usage k => simp [all, UsageKind.mem_all]
  | restricted k => simp [all, Restricted.mem_all]
  | illegal k => simp [all, Ir.Illegal.mem_all]
  | fault k => simp [all, FaultKind.mem_all]
  | test k => simp [all, TestKind.mem_all]
  | prove k => simp [all, ProveKind.mem_all]
  | generate k => simp [all, GenerateKind.mem_all]
  | undecided k => simp [all, UndecidedKind.mem_all]
  | _ => simp [all]

/-- Whether test/e2e has a case of the kind. A Restricted kind has its unit test in gleam/test/convert_test.gleam
instead, one per kind of the launcher's generated table; a converter bug has no input that reaches it, a solver
past the wall clock none that reaches it on every machine, and a string literal above U+2FFFF is
`Restricted.highCodePoint` before any encoder sees it. -/
def e2e : Kind → Bool
  | restricted _ | internal .convert | internal .engine | undecided .timeout | undecided .unencodableString => false
  | internal .invalidIr | usage _ | illegal _ | checkPassed | fault _ | test _ | verifyPassed | verifyDiffers | traceInvalid | prove _
  | generate _ | undecided .unknown | undecided .limit | undecided .upToRenaming
  | explain => true

/-- The outcome a line of the kind gives its command; the command exits with its worst line's (`Exit.max`). -/
def exit : Kind → Exit
  | internal _ => .internal
  | usage _ => .usage
  | restricted _ | illegal _ | fault _ | verifyDiffers | traceInvalid => .violation
  | test .passed | test .written => .ok
  | test .changed | test .badStep => .violation
  | checkPassed | verifyPassed | explain => .ok
  | prove .proved | prove .withinBounds => .ok
  | prove .violated => .violation
  | generate .reached | generate .unreached => .ok
  | undecided _ => .undecided

end Kind

end Tazuna
