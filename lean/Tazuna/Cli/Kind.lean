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
  the slots the model's scope gives, while every input and the initial state fit them; so every state a run reaches is within
  the slots, and the line speaks of every run. For a response: the line's step opens each trigger it does not answer
  with a deadline in time, keeps each waiting deadline no later until its answer, and as a clock line passes no
  waiting deadline; where every kind's line reads so, no run on valid inputs with timely clock lines violates the
  response, at any length. -/
  | proved
  /-- No step of the input kind from a state of the right shape breaks the target while it stays within the slots,
  but such a step can go past them: the line names every bound a step of the service can go past (its tables, bags
  and list types, and its pending requests where it sends any), the same for every run. For a response, the same of
  every run whose steps stay within the slots. -/
  | withinBounds
  /-- The initial state breaks the target, an invariant of the service: every run starts there, so the line needs no
  search. -/
  | violated
  /-- A state of the right shape whose invariants hold, and an input whose step from it breaks the target; for a
  response, also the trigger whose deadline the step breaks and which part it breaks. A counterexample to induction,
  not a violation: no run may reach the state. For a target a fault breaks (an invariant, an `ensures` rule, an own
  effect's acceptance, the cascade bound), generate searches for a run that does. A pair's or a timer machine's state
  is any state of the right shape, invariants or not. -/
  | unproved
  /-- No step from a state of the right shape whose invariants hold, of any input kind, shows the class of out line
  the generate target aims at unless it faults, no step of any kind goes past the slots the model's scope gives, and every
  input and the initial state fit them: no run on valid inputs that faults nowhere ever shows it, at any depth. A fact
  about the spec, not a violation: a defensive branch may be meant never to run. A target only a query's answer shows
  gets no line, nor does a target whose question has a model, which may be a state no run reaches. -/
  | unreachable
  /-- As `unreachable`, but only within the slots: a step can go past them, or an input or the initial state does not
  fit them, and the line names those bounds. No run on valid inputs that faults nowhere shows the class while its
  states and inputs fit them; a run past them may, so raising a bound the line names can make the target reachable. -/
  | unreachableWithinBounds
deriving DecidableEq

/-- What `generate` found for one target. -/
inductive Tazuna.GenerateKind : Type
  /-- A run from the initial state whose last step shows the target's class of out line: its trace is written. -/
  | reached
  /-- No run of at most the scope's steps within the slots, on which its `assumes` hold (valid inputs, no step faults),
  shows the target's class at any step. Not "unreachable": a longer run or larger slots may reach it. -/
  | unreached
  /-- Every input kind's dead-target question is unsat, no step goes past the slots and every input and the initial
  state fit them, as prove's line of the same name says: no run on which its `assumes` hold shows the target's class,
  at any length. generate asks the dead-target questions from its second depth on, once no run of one step reached the
  target, and prove's bound questions once a target is dead. -/
  | unreachable
  /-- As `unreachable`, but only within the slots the line names, as prove's line of the same name says: a step can go
  past them, or an input or the initial state does not fit them. A run past them may show the class. -/
  | unreachableWithinBounds
  /-- A run from the initial state on valid inputs whose steps before the last fault nowhere, and whose last step
  faults by a fault the target covers: prove's target is broken in a state a run reaches. Its trace is written, and
  verify replays it to that fault at its last line. -/
  | violated
  /-- prove found a step that breaks the target from a state whose invariants hold (`Prove.unproved`), and no run of at
  most the scope's steps within the slots, on valid inputs, whose steps before the last fault nowhere, faults by it at
  its last step. Not settled: a longer run or larger slots may break the target, or no run may. -/
  | unsettled
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
  z3), or the engine and z3 the launcher fetches on first run from the release of its version (none for the platform,
  a failed download, or a SHA-256 other than the one the package pins). -/
  | system
deriving DecidableEq

/-- Every kind of line tazuna writes to stdout, the launcher's included. -/
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
  /-- What a kind of line means, as `explain` prints it. -/
  | explain
  /-- The engine's version, which is the Gleam package's: `tazuna-engine` with no arguments prints it. -/
  | version
  /-- The run's `--timeout` passed before every target was done: the lines before this one are the ones a run without
  the flag prints for the finished targets, and this line lists the targets left, each as `--only` names it. Which
  targets finish depends on the machine; what a printed line says does not. -/
  | unfinished

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
  | ok | undecided | violation | unfinished | usage | internal

/-- Undecided ranks below a violation: one violated line decides the run. An unfinished run ranks above both, as its
lines leave targets out: a violation it printed still stands, but no line speaks for the targets it left. -/
def Exit.code : Exit → UInt32
  | .ok => 0
  | .violation => 1
  | .undecided => 2
  | .usage => 3
  | .internal => 4
  | .unfinished => 5

def Exit.rank : Exit → Nat
  | .ok => 0
  | .undecided => 1
  | .violation => 2
  | .unfinished => 3
  | .usage => 4
  | .internal => 5

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

def ProveKind.all : List ProveKind :=
  [.proved, .withinBounds, .violated, .unproved, .unreachable, .unreachableWithinBounds]

theorem ProveKind.mem_all (k : ProveKind) : k ∈ ProveKind.all := by cases k <;> simp [ProveKind.all]

def ProveKind.name : ProveKind → String
  | .proved => "proved"
  | .withinBounds => "withinBounds"
  | .violated => "violated"
  | .unproved => "unproved"
  | .unreachable => "unreachable"
  | .unreachableWithinBounds => "unreachableWithinBounds"

def GenerateKind.all : List GenerateKind :=
  [.reached, .unreached, .unreachable, .unreachableWithinBounds, .violated, .unsettled]

theorem GenerateKind.mem_all (k : GenerateKind) : k ∈ GenerateKind.all := by cases k <;> simp [GenerateKind.all]

def GenerateKind.name : GenerateKind → String
  | .reached => "reached"
  | .unreached => "unreached"
  | .unreachable => "unreachable"
  | .unreachableWithinBounds => "unreachableWithinBounds"
  | .violated => "violated"
  | .unsettled => "unsettled"

def UndecidedKind.all : List UndecidedKind := [.unknown, .timeout, .limit, .upToRenaming]

theorem UndecidedKind.mem_all (k : UndecidedKind) : k ∈ UndecidedKind.all := by cases k <;> simp [UndecidedKind.all]

def UndecidedKind.name : UndecidedKind → String
  | .unknown => "unknown"
  | .timeout => "timeout"
  | .limit => "limit"
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
  | version => "Engine.version"
  | unfinished => "Run.unfinished"

def all : List Kind :=
  InternalKind.all.map internal ++ UsageKind.all.map usage ++ Restricted.all.map restricted ++ Ir.Illegal.all.map illegal ++ [checkPassed] ++ FaultKind.all.map fault ++ TestKind.all.map test ++
    [verifyPassed, verifyDiffers, traceInvalid] ++ ProveKind.all.map prove ++
    GenerateKind.all.map generate ++ UndecidedKind.all.map undecided ++ [explain, version, unfinished]

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
instead, one per kind of the launcher's generated table; a converter bug has no input that reaches it, and a solver
past the wall clock none that reaches it on every machine. -/
def e2e : Kind → Bool
  | restricted _ | internal .convert | internal .engine | undecided .timeout => false
  | internal .invalidIr | usage _ | illegal _ | checkPassed | fault _ | test _ | verifyPassed | verifyDiffers | traceInvalid | prove _
  | generate _ | undecided .unknown | undecided .limit | undecided .upToRenaming
  | explain | version | unfinished => true

/-- The outcome a line of the kind gives its command; the command exits with its worst line's (`Exit.max`). -/
def exit : Kind → Exit
  | internal _ => .internal
  | usage _ => .usage
  | restricted _ | illegal _ | fault _ | verifyDiffers | traceInvalid => .violation
  | test .passed | test .written => .ok
  | test .changed | test .badStep => .violation
  | checkPassed | verifyPassed | explain | version => .ok
  | prove .proved | prove .withinBounds | prove .unreachable | prove .unreachableWithinBounds => .ok
  | prove .violated => .violation
  | prove .unproved => .undecided
  | generate .reached | generate .unreached | generate .unreachable | generate .unreachableWithinBounds => .ok
  | generate .violated => .violation
  | generate .unsettled => .undecided
  | undecided _ => .undecided
  | unfinished => .unfinished

end Kind

end Tazuna
