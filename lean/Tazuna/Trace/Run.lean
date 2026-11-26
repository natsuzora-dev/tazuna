import Tazuna.Semantics.Step
import Tazuna.Trace.Line

/-! Running a scenario: each step becomes one input line, the step runs, and its outputs become out lines. The trace
names fresh ids `id1`, `id2`, ... and the requests the service sends `r1`, `r2`, ... in the order they first appear,
so a snapshot shows what a reader can compare, not the engine's numbering. A scenario never names an id by text: a command step hands the steps after it the source its
new ids came from. -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

/-- The names a trace gives ids, one to one, each from its first appearance: an id from outside the service is called
by its own name, and a fresh id by the next `idK` no other id is called. -/
structure Names where
  ids : List (IdV × String) := []
  next : Nat := 1
  wires : List (Nat × String) := []

def Names.name (ns : Names) (x : IdV) : Option String := ns.ids.lookup x

def Names.taken (ns : Names) (s : String) : Bool := ns.ids.any (·.2 == s)

/-- The name of the service's request with wire id `n`: `rK` for the `K`-th request the trace names. -/
def Names.wire (ns : Names) (n : Nat) : Names × String :=
  match ns.wires.lookup n with
  | some w => (ns, w)
  | none => let w := s!"r{ns.wires.length + 1}"; ({ ns with wires := ns.wires ++ [(n, w)] }, w)

-- One of ids.length + 1 candidate names is free, so the default is never read.
set_option linter.tazuna.silentDefault false in
def Names.bind (ns : Names) (xs : List IdV) : Names :=
  xs.foldl (fun ns x => if ns.ids.any (·.1 == x) then ns else match x with
    -- An outside id whose name another id has stays unnamed, so the value has no wire form.
    | .named s => if ns.taken s then ns else { ns with ids := ns.ids ++ [(x, s)] }
    | .fresh _ _ =>
      -- Of `ids.length + 1` candidates at most `ids.length` are taken.
      let k := ((List.range (ns.ids.length + 1)).find? fun j => !ns.taken s!"id{ns.next + j}").getD 0
      { ns with ids := ns.ids ++ [(x, s!"id{ns.next + k}")], next := ns.next + k + 1 }) ns

/-- The wire form of a value, naming the ids it holds first. -/
def Names.enc (ns : Names) (T : List TypeDecl) (t : Ty) (x : t.den0) : Names × Option Wire :=
  let ns := ns.bind (idsOf T t x)
  (ns, Trace.enc T ns.name t x)

/-- The wire form of an answer to a request: a command's output under `ok` and its rejection under `error`, a
query's output under `ok`. -/
def Names.answerWire (ns : Names) (T : List TypeDecl) (o : Ty) :
    (rj : Option Ty) → (answerTy o rj).den0 → Names × Option (Except Wire Wire)
  | some _, .inl (x, ()) => let (ns, w) := ns.enc T o x; (ns, w.map .ok)
  | some j, .inr (.inl (x, ())) => let (ns, w) := ns.enc T j x; (ns, w.map .error)
  | none, x => let (ns, w) := ns.enc T o x; (ns, w.map .ok)

/-- Why a scenario stopped before its end. -/
inductive Stop where
  /-- The spec faulted at step `step`. -/
  | fault (step : Nat) (f : Fault)
  /-- Step `step` cannot run: its answer matches no pending request or more than one, it waits a negative time, it
  sends a request the service does not list, or a value has no wire form. -/
  | badStep (step : Nat) (message : String)

def _root_.Tazuna.Ir.Sender.matches : Sender → Sender → Bool
  | .machine n ⟨t, k⟩, .machine n' ⟨t', k'⟩ =>
    n == n' && match Ty.same t t' with
      | some ⟨h⟩ => (Ty.semWith Dsl.base t').2 (h ▸ k) k'
      | none => false
  | .reaction n, .reaction n' => n == n'
  | _, _ => false

def finIdx {α : Type} (xs : List α) (p : α → Bool) : Option (Fin xs.length) :=
  (List.finRange xs.length).find? fun i => p (xs.get i)

section
variable (T : List TypeDecl) (v : ServiceV)

/-- The out lines of one step's result: the answer to a request (named by `answerTo`), each event applied, each
request sent. -/
def outLines (ns : Names) (answerTo : Option String) (r : Result v) : Names × Option (List Line) := Id.run do
  let mut ns := ns
  let mut lines : List Line := []
  let t := r.state.now
  if let some to := answerTo then
    let answer ← match r.outcome with
      | .accepted => pure (some Answer.accepted)
      | .answered ⟨ty, x⟩ => do let (ns', w) := ns.enc T ty x; ns := ns'; pure (w.map .answered)
      | .rejected ⟨ty, x⟩ => do let (ns', w) := ns.enc T ty x; ns := ns'; pure (w.map .rejected)
      | .invalid rules => pure (some (.invalid rules))
      | .fault _ => pure none
    match answer with
    | some a => lines := lines ++ [.answered t to a]
    | none => return (ns, none)
  for ev in r.events do
    let (ns', w) := ns.enc T v.event ev
    ns := ns'
    match w with
    | some w => lines := lines ++ [.applied t w]
    | none => return (ns, none)
  for o in r.out do
    let (ns', id) := ns.wire o.id
    let (ns', w) := ns'.enc T o.input.1 o.input.2
    ns := ns'
    match w with
    | some w => lines := lines ++ [.sent t id o.external o.name w]
    | none => return (ns, none)
  return (ns, some lines)

/-- What runs a scenario step needs between steps. -/
structure Run where
  state : State v
  names : Names := {}
  requests : Nat := 0
  lines : List Line := []

/-- Runs the input and appends its in lines and out lines. -/
def Run.finish' (run : Run v) (input : Input v) (inLines : List Line) (answerTo : Option String) (k : Nat) :
    Except Stop (Run v) := do
  let r := step T v run.state input
  if let .fault f := r.outcome then throw (.fault k f)
  let (ns, outs) := outLines T v run.names answerTo r
  let some outs := outs | throw (.badStep k "an output has no wire form")
  pure { run with state := r.state, names := ns, lines := run.lines ++ inLines ++ outs }

/-- One input, written as its in line, run, and its out lines: what scenarios and generate's traces share, so the two
cannot write an input differently. A request's id is the count of requests so far; an answer names the request by the
name the trace gave its wire id. -/
def Run.input (run : Run v) (k : Nat) : Input v → Except Stop (Run v)
  | .command i caller input => request (v.commands.get i).name (.command i caller input) caller ⟨_, input⟩
  | .query i caller input => request (v.queries.get i).name (.query i caller input) caller ⟨_, input⟩
  | .answer to ⟨ty, value⟩ => do
    let some p := run.state.pending.find? (·.id == to) | throw (.badStep k s!"no pending request has wire id {to}")
    let some ⟨h⟩ := Ty.same ty (answerTy p.request.output p.request.rejection)
      | throw (.badStep k s!"the answer's type is not the type of answers to {p.external}.{p.request.name}")
    let (ns, w) := run.names.wire p.id
    let (ns, a) := ns.answerWire T p.request.output p.request.rejection (h ▸ value)
    let some a := a | throw (.badStep k "the answer has no wire form")
    { run with names := ns }.finish' T v (.answer to ⟨ty, value⟩) [.answer run.state.now w a] none k
  | .event i value => do
    let sub := v.subscribes.get i
    let (ns, w) := run.names.enc T sub.event value
    let some w := w | throw (.badStep k "the event has no wire form")
    { run with names := ns }.finish' T v (.event i value) [.event run.state.now sub.source sub.name w] none k
  | .clock t => run.finish' T v (.clock t) [.clock t] none k
where
  request (name : String) (input : Input v) (caller : v.caller.den0) (value : WireVal) : Except Stop (Run v) := do
    let id := toString (run.requests + 1)
    let (ns, c) := run.names.enc T v.caller caller
    let (ns, i) := ns.enc T value.1 value.2
    let (some c, some i) := (c, i) | throw (.badStep k "the request has no wire form")
    { run with names := ns, requests := run.requests + 1 }.finish' T v input
      [.request run.state.now id name c i] (some id) k

/-- One scenario step: the input it names, through `Run.input`. -/
def Run.step (run : Run v) (k : Nat) : StepV v.records v.event v.caller → Except Stop (Run v)
  | .command x caller input _ => do
    let some i := finIdx v.commands fun c => c.name == x.name | throw (.badStep k s!"{v.name} lists no command {x.name}")
    let some ⟨h⟩ := Ty.same x.input (v.commands.get i).input | throw (.badStep k s!"{x.name} has another input type")
    run.input T v k (.command i caller (h ▸ input))
  | .query x caller input => do
    let some i := finIdx v.queries fun q => q.name == x.name | throw (.badStep k s!"{v.name} lists no query {x.name}")
    let some ⟨h⟩ := Ty.same x.input (v.queries.get i).input | throw (.badStep k s!"{x.name} has another input type")
    run.input T v k (.query i caller (h ▸ input))
  | .wait ms => do
    if ms < 0 then throw (.badStep k "a step waits a negative time")
    run.input T v k (.clock (run.state.now + ms))
  | .answer name input output rejection snd w => do
    let same (a b : Ty) := (Ty.same a b).isSome
    let ps := run.state.pending.filter fun p =>
      p.request.name == name && same p.request.input input && same p.request.output output &&
        (match p.request.rejection, rejection with
          | some a, some b => same a b
          | none, none => true
          | _, _ => false) && p.sender.matches snd
    let [p] := ps | throw (.badStep k s!"{ps.length} pending requests to {name} match the sender")
    run.input T v k (.answer p.id w)
  | .event name ⟨ty, x⟩ => do
    let some i := finIdx v.subscribes fun sub => sub.name == name && (Ty.same ty sub.event).isSome
      | throw (.badStep k s!"{v.name} subscribes to no source {name} of this event type")
    let some ⟨h⟩ := Ty.same ty (v.subscribes.get i).event | throw (.badStep k s!"{name} has another type")
    run.input T v k (.event i (h ▸ x))

end

/-- The header line of a trace of `service`. -/
def header (service : String) : Wire := .obj [("trace", .num 1), ("service", .str service)]

/-- The service a header line names. -/
def headerService? : Wire → Option String
  | .obj kvs => match kvs.lookup "trace", kvs.lookup "service" with
    | some (.num 1), some (.str s) => some s
    | _, _ => none
  | _ => none

/-- A trace: the service its header names, and its lines after the header. -/
structure TraceFile where
  service : String
  lines : List Line

/-- The trace as its file holds it, one wire value per line: the header, then each line. -/
def TraceFile.wires (tr : TraceFile) : List Wire := header tr.service :: tr.lines.map Line.toWire

/-- The lines, each with its line number in the trace's file, where the header is line 1: as verify numbers them. -/
def TraceFile.numbered (tr : TraceFile) : List (Nat × Line) := tr.lines.zipIdx.map fun (l, k) => (k + 2, l)

/-- Reading a trace's wire values back gives what was written: the header names its service, and every line after it
reads as itself (`Line.ofWire_toWire`). Between the wire values and the file's text stands only Lean's JSON printer
and parser. -/
theorem TraceFile.read_wires (tr : TraceFile) :
    tr.wires = header tr.service :: tr.lines.map Line.toWire ∧ headerService? (header tr.service) = some tr.service ∧
      (tr.lines.map Line.toWire).mapM Line.ofWire = some tr.lines := by
  refine ⟨rfl, by simp [headerService?, header, List.lookup], ?_⟩
  induction tr.lines with
  | nil => rfl
  | cons l ls ih => simp [List.mapM_cons, Line.ofWire_toWire, ih]

/-- The trace of a run of the inputs from the initial state: what generate writes, in the format of snapshots, or why
a step stopped. -/
def traceOf (T : List TypeDecl) (v : ServiceV) (xs : List (Input v)) : Except Stop TraceFile := do
  let (run, _) ← xs.foldlM (fun (run, k) x => do pure (← run.input T v (k + 1) x, k + 1))
    (({ state := State.init v } : Run v), 0)
  pure ⟨v.name, run.lines⟩

instance : Inhabited Stop := ⟨.badStep 0 ""⟩

/-- Runs the steps in order, numbering them from `k + 1`; the steps a command hands on run right after it. A
continuation is a function the spec wrote, so nothing bounds how deep it nests and the run is `partial`. -/
partial def runSteps (T : List TypeDecl) (v : ServiceV) (run : Run v) (k : Nat) :
    List (StepV v.records v.event v.caller) → Except Stop (Run v × Nat)
  | [] => pure (run, k)
  | st :: rest => do
    let fresh := run.state.fresh
    let run ← run.step T v (k + 1) st
    match st with
    | .command _ _ _ next =>
      let (run, k) ← runSteps T v run (k + 1) (next fresh)
      runSteps T v run k rest
    | _ => runSteps T v run (k + 1) rest

/-- The trace of a scenario, or why it stopped. -/
def runScenario (T : List TypeDecl) (v : ServiceV) (steps : List (StepV v.records v.event v.caller)) :
    Except Stop TraceFile := do
  let (run, _) ← runSteps T v ({ state := State.init v } : Run v) 0 steps
  pure ⟨v.name, run.lines⟩

end Tazuna.Trace
