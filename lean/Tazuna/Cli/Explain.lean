import Tazuna.Cli.Check

/-! The `explain` command: what each kind of line means. A kind's meaning is the doc comment of its constructor, read
when this module is built, so the text `explain` prints and the text a reader of the source sees are one. -/

namespace Tazuna

open Lean (Json Name)

open Lean Elab Term in
/-- The doc comment of the constructor, on one line; a constructor without one fails the build. -/
elab "docOf% " n:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let some doc ← findDocString? (← getEnv) name | throwError "{name} has no doc comment for explain to print"
  return mkStrLit (" ".intercalate ((doc.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)))

/-- A field a line can carry, and what it holds. -/
structure Field where
  key : String
  holds : String

namespace Field

def message : Field := ⟨"message", "what is wrong, in words"⟩
def file : Field := ⟨"file", "the source file"⟩
def line : Field := ⟨"line", "the line number in the file, the trace or the snapshot, from 1"⟩
def col : Field := ⟨"col", "the column, from 1"⟩
def service : Field := ⟨"service", "the service"⟩
def scenario : Field := ⟨"scenario", "the scenario"⟩
def step : Field := ⟨"step", "for test, the scenario step, from 1; for prove, the input kind the question is about"⟩
def trace : Field := ⟨"trace", "the trace file"⟩
def rule : Field := ⟨"rule", "the name of the broken rule"⟩
def request : Field := ⟨"request", "the request the effect asked for"⟩
def rules : Field := ⟨"rules", "the rules the request's target broke"⟩
def path : Field := ⟨"path", "the snapshot file"⟩
def expected : Field := ⟨"expected", "the line or lines the snapshot or the spec has there, null for none"⟩
def actual : Field := ⟨"actual", "the line or lines the run or the trace has there, null for none"⟩
def target : Field := ⟨"target", "the target: an invariant, an ensures rule, an effect, a timer machine, a pair, a response"⟩
def assumes : Field := ⟨"assumes", "what the verdict assumes: the stated assumptions and the invariants it took as holding"⟩
def widened : Field := ⟨"widened", "a pair's own kinds that stand for any handle or site of their type"⟩
def scope : Field := ⟨"scope", "the model the verdict rests on and the values of it the verdict reads: model, its name; bounds, each bound a step or a run can go past (its type, where its slots come from, how many, and the machines whose instances it holds); steps, the most inputs searched; resourceLimit, the solver's resource limit per question"⟩
def fromField : Field := ⟨"from", "init: from the initial state; validState: from any state of the right shape"⟩
def state : Field := ⟨"state", "the state before the step, as wire values"⟩
def input : Field := ⟨"input", "the input of the step"⟩
def after : Field := ⟨"after", "the state the step reaches before its invariant check"⟩
def outcome : Field := ⟨"outcome", "how the step ended; for generate, the last step of the trace"⟩
def out : Field := ⟨"out", "the out lines of the step"⟩
def violated : Field := ⟨"violated", "the rules broken"⟩
def inst : Field := ⟨"instance", "a timer machine's instance: its key and state"⟩
def records : Field := ⟨"records", "the records the instance sees"⟩
def timer : Field := ⟨"timer", "the timer the instance waits for: its deadline and the state it enters"⟩
def next : Field := ⟨"next", "the timer that state waits for: its deadline and the state it enters"⟩
def first : Field := ⟨"first", "a pair's first step"⟩
def second : Field := ⟨"second", "a pair's second step"⟩
def firstThenSecond : Field := ⟨"firstThenSecond", "how the first step then the second ends"⟩
def secondThenFirst : Field := ⟨"secondThenFirst", "how the second step then the first ends"⟩
def steps : Field := ⟨"steps", "the number of inputs of the run, or the most searched"⟩
def trigger : Field := ⟨"trigger", "for a response, the waiting trigger whose deadline the step lets go, moves later or passes"⟩
def written : Field := ⟨"file", "the trace file written, under the directory given"⟩
def why : Field := ⟨"why", "what the solver said"⟩
def depth : Field := ⟨"depth", "the number of inputs of the run searched when the solver gave up"⟩
def limit : Field := ⟨"limit", "what the encoding or the search has no room for"⟩
def name : Field := ⟨"name", "the kind explained"⟩
def means : Field := ⟨"means", "what a line of the kind means"⟩
def exit : Field := ⟨"exit", "the exit code a line of the kind gives; a command exits with its worst line's"⟩
def backedBy : Field := ⟨"backedBy", "the theorems the line rests on, as lean/Tazuna/Axioms.lean names its roots"⟩
def fields : Field := ⟨"fields", "each field a line of the kind can carry, with what it holds"⟩
def version : Field := ⟨"version", "the version"⟩
def targets : Field := ⟨"targets", "the targets the run left unfinished, each as `<service>/<target>`, the name `--only` keeps"⟩

end Field

/-- What `explain` says of a kind besides its exit code. -/
structure Explanation where
  means : String
  backedBy : List Name := []
  fields : List Field

open Field

/-- Where a line of a pair question shows the two orders. -/
def pairFields : List Field := [fromField, state, first, second, firstThenSecond, secondThenFirst, widened]

/-- The fields of a prove line or a generate line before its own. -/
def questionFields : List Field := [service, target, step]

def InternalKind.explanation : InternalKind → Explanation
  | .invalidIr => ⟨docOf% InternalKind.invalidIr, [], [file, line, col, message]⟩
  | .convert => ⟨docOf% InternalKind.convert, [], [file, line, col, message]⟩
  | .engine => ⟨docOf% InternalKind.engine,
    [`Tazuna.Smt.questions_decode, `Tazuna.Smt.pair_decode, `Tazuna.Smt.timer_decode, `Tazuna.Smt.resp_decode,
      `Tazuna.Smt.generate_sound], [message]⟩

def UsageKind.explanation : UsageKind → Explanation
  | .arguments => ⟨docOf% UsageKind.arguments, [], [message]⟩
  | .system => ⟨docOf% UsageKind.system, [], [message]⟩

def Restricted.means : Restricted → String
  | .float => docOf% Restricted.float
  | .highCodePoint => docOf% Restricted.highCodePoint
  | .bitArray => docOf% Restricted.bitArray
  | .panic => docOf% Restricted.panic
  | .todo => docOf% Restricted.todo
  | .echo => docOf% Restricted.echo
  | .letAssert => docOf% Restricted.letAssert
  | .assert => docOf% Restricted.assert
  | .listSpread => docOf% Restricted.listSpread
  | .listPattern => docOf% Restricted.listPattern
  | .stringPrefixPattern => docOf% Restricted.stringPrefixPattern
  | .external => docOf% Restricted.external
  | .foreignFunction => docOf% Restricted.foreignFunction
  | .foreignType => docOf% Restricted.foreignType
  | .recursion => docOf% Restricted.recursion
  | .recursiveType => docOf% Restricted.recursiveType
  | .incomparable => docOf% Restricted.incomparable
  | .keptCapture => docOf% Restricted.keptCapture
  | .shadowedImport => docOf% Restricted.shadowedImport
  | .mixedReference => docOf% Restricted.mixedReference
  | .multiVariantUpdate => docOf% Restricted.multiVariantUpdate
  | .variantField => docOf% Restricted.variantField
  | .constructorValue => docOf% Restricted.constructorValue
  | .annotationNeeded => docOf% Restricted.annotationNeeded
  | .rootSpec => docOf% Restricted.rootSpec

def Ir.Illegal.means : Ir.Illegal → String
  | .wireName => docOf% Ir.Illegal.wireName
  | .owner => docOf% Ir.Illegal.owner
  | .unknownSource => docOf% Ir.Illegal.unknownSource
  | .creates => docOf% Ir.Illegal.creates
  | .wireType => docOf% Ir.Illegal.wireType
  | .stateType => docOf% Ir.Illegal.stateType
  | .bounds => docOf% Ir.Illegal.bounds
  | .scenario => docOf% Ir.Illegal.scenario
  | .rejection => docOf% Ir.Illegal.rejection
  | .machineKey => docOf% Ir.Illegal.machineKey
  | .unknownHandle => docOf% Ir.Illegal.unknownHandle
  | .handleName => docOf% Ir.Illegal.handleName
  | .tableKey => docOf% Ir.Illegal.tableKey
  | .response => docOf% Ir.Illegal.response
  | .callers => docOf% Ir.Illegal.callers
  | .tagLabel => docOf% Ir.Illegal.tagLabel
  | .initialInstances => docOf% Ir.Illegal.initialInstances
  | .model => docOf% Ir.Illegal.model

/-- A fault's line comes from test (at a scenario step) or verify (at a trace line). -/
def FaultKind.explanation : FaultKind → Explanation
  | .invariant => ⟨docOf% Ir.Fault.invariant, [], at_ ++ [rule]⟩
  | .ensures => ⟨docOf% Ir.Fault.ensures, [], at_ ++ [rule]⟩
  | .cascadeLimit => ⟨docOf% Ir.Fault.cascadeLimit, [], at_⟩
  | .answerUnmatched => ⟨docOf% Ir.Fault.answerUnmatched, [], at_⟩
  | .invalidEffect => ⟨docOf% Ir.Fault.invalidEffect, [], at_ ++ [request, rules]⟩
where
  at_ : List Field := [service, scenario, step, trace, line]

def TestKind.explanation : TestKind → Explanation
  | .passed => ⟨docOf% TestKind.passed, [`Tazuna.Trace.TraceFile.read_wires, `Tazuna.Trace.replay_iff],
    [service, scenario]⟩
  | .changed => ⟨docOf% TestKind.changed, [`Tazuna.Trace.TraceFile.read_wires],
    [service, scenario, path, line, expected, actual]⟩
  | .written => ⟨docOf% TestKind.written, [`Tazuna.Trace.TraceFile.read_wires, `Tazuna.Trace.replay_iff],
    [service, scenario, path]⟩
  | .badStep => ⟨docOf% TestKind.badStep, [], [service, scenario, step, message]⟩

def ProveKind.explanation : ProveKind → Explanation
  | .proved => ⟨docOf% ProveKind.proved, [`Tazuna.Smt.proved_sound, `Tazuna.Smt.run_lines, `Tazuna.Smt.response_holds],
    questionFields ++ [assumes, widened]⟩
  | .withinBounds => ⟨docOf% ProveKind.withinBounds,
    [`Tazuna.Smt.fault_sound, `Tazuna.Smt.run_lines, `Tazuna.Smt.response_scoped, `Tazuna.Smt.boundReached_iff],
    questionFields ++ [assumes, scope, widened]⟩
  | .violated => ⟨docOf% ProveKind.violated, [], questionFields ++ [fromField, state, Field.violated, assumes]⟩
  | .unproved => ⟨docOf% ProveKind.unproved,
    [`Tazuna.Smt.cti_sound, `Tazuna.Ir.step_settled, `Tazuna.Smt.timer_violates, `Tazuna.Smt.pair_violates],
    questionFields ++ [fromField, state, input, after, outcome, out, inst, records, timer, next, first, second,
      firstThenSecond, secondThenFirst, trigger, Field.violated, assumes, widened]⟩
  | .unreachable => ⟨docOf% ProveKind.unreachable, [`Tazuna.Smt.unshown_sound], [service, target, assumes]⟩
  | .unreachableWithinBounds => ⟨docOf% ProveKind.unreachableWithinBounds, [`Tazuna.Smt.unshown_within],
    [service, target, assumes, scope]⟩

def GenerateKind.explanation : GenerateKind → Explanation
  | .reached => ⟨docOf% GenerateKind.reached,
    [`Tazuna.Cli.generate_reaches, `Tazuna.Ir.targets_cover, `Tazuna.Cli.targetFile_inj],
    [service, target, written, steps]⟩
  | .unreached => ⟨docOf% GenerateKind.unreached, [`Tazuna.Smt.noModel_cubes],
    [service, target, scope, assumes]⟩
  | .unreachable => ⟨docOf% GenerateKind.unreachable, [`Tazuna.Smt.unshown_sound], [service, target, assumes]⟩
  | .unreachableWithinBounds => ⟨docOf% GenerateKind.unreachableWithinBounds, [`Tazuna.Smt.unshown_within],
    [service, target, assumes, scope]⟩
  | .violated => ⟨docOf% GenerateKind.violated, [`Tazuna.Cli.generate_breaks], [service, target, written, steps, outcome]⟩
  | .unsettled => ⟨docOf% GenerateKind.unsettled, [`Tazuna.Smt.noModel_breaks],
    [service, target, scope, assumes]⟩

def UndecidedKind.explanation : UndecidedKind → Explanation
  | .unknown => ⟨docOf% UndecidedKind.unknown, [], questionFields ++ [depth, why, scope]⟩
  | .timeout => ⟨docOf% UndecidedKind.timeout, [], questionFields ++ [depth, why]⟩
  | .limit => ⟨docOf% UndecidedKind.limit, [`Tazuna.Trace.replay_iff],
    questionFields ++ [scenario, trace, line, Field.limit] ++ pairFields ++ [input, after, outcome, out, trigger]⟩
  | .upToRenaming => ⟨docOf% UndecidedKind.upToRenaming, [`Tazuna.Smt.run_lines], questionFields ++ pairFields⟩

namespace Kind

def explanation : Kind → Explanation
  | internal k => k.explanation
  | usage k => k.explanation
  | restricted k => ⟨k.means, [], [file, line, col, message]⟩
  | illegal k => ⟨k.means, if k = .wireType then [`Tazuna.Smt.wireTys_wire] else [], [message]⟩
  | checkPassed => ⟨docOf% Kind.checkPassed, [`Tazuna.Smt.wireTys_wire], [service]⟩
  | fault k => k.explanation
  | test k => k.explanation
  | verifyPassed => ⟨docOf% Kind.verifyPassed, [`Tazuna.Trace.replay_iff], [trace]⟩
  | verifyDiffers => ⟨docOf% Kind.verifyDiffers, [`Tazuna.Trace.replay_iff], [trace, line, expected, actual]⟩
  | traceInvalid => ⟨docOf% Kind.traceInvalid, [`Tazuna.Trace.replay_iff], [trace, line, message]⟩
  | prove k => k.explanation
  | generate k => k.explanation
  | undecided k => k.explanation
  | explain => ⟨docOf% Kind.explain, [], [Field.name, Field.means, Field.exit, Field.backedBy, Field.fields]⟩
  | version => ⟨docOf% Kind.version, [], [Field.version]⟩
  | unfinished => ⟨docOf% Kind.unfinished, [], [Field.targets]⟩

/-- Every theorem `explain` names: lean/Tazuna/Axioms.lean fails the build unless each is one of its roots. -/
def backing : List Name := all.flatMap (·.explanation.backedBy)

/-- The line `explain` prints for the kind. -/
def explainFields (k : Kind) : List (String × Json) :=
  let e := k.explanation
  [("name", Json.str k.name), ("means", Json.str e.means), ("exit", Json.num k.exit.code.toNat),
    ("backedBy", Json.arr (e.backedBy.map (Json.str ·.toString)).toArray),
    ("fields", Json.mkObj (e.fields.map fun f => (f.key, Json.str f.holds)))]

end Kind

namespace Cli

/-- Prints what the kind named `name` means, or every kind's when none is named. -/
def explain : Option String → Cmd Unit
  | none => Kind.all.forM fun k => printLine .explain k.explainFields
  | some name => match Kind.all.find? (·.name == name) with
    | some k => printLine .explain k.explainFields
    | none => printLine (.usage .arguments)
      [("message", Json.str s!"no kind is named {name}; explain with no kind prints every kind")]

end Cli

end Tazuna
