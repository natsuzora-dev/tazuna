import Std.Data.HashMap
import DiffTest.Json
import DiffTest.Protocol
import Tazuna.Explore.Assignments
import Tazuna.Sim.Run

/-!
tazuna-lean exchanges one JSON value per line with TS over stdio (precedents: leanprover-community/repl, the Lean LSP).
DiffTest/Protocol.lean defines the messages.

Service asks TS for a spec function's value whenever it needs one. While computing it, TS sends `read` for each record
a TS function reads; Lean serves the value from its own records and remembers the parts read, which Instrument records
in the accesses of steps. Within one run tree, Lean reuses the reply that TS gave to the same question when the values
that Lean serves for the reads that TS made then are the same now: a TS reply depends only on the question and those
values.
-/

open Tazuna Tazuna.Data Tazuna.Service Tazuna.Explore Tazuna.Json Tazuna.DiffTest

structure Log where
  parts : List RecordPart := []
  replied : Option Replied := none

abbrev Reads := IO.Ref Log

def sendLine {α : Type} [ToValue α] (stdout : IO.FS.Stream) (message : α) : IO Unit := do
  stdout.putStrLn (render (ToValue.toValue message))
  stdout.flush

def Log.add (l : Log) (part : RecordPart) : Log :=
  { l with parts := if part ∈ l.parts then l.parts else l.parts ++ [part] }

/-- A read of a record that TS sends while it answers. -/
structure Read where
  entity : String
  key : Option String
  field : Option String
  beforeEventWrite : Bool

def serve (records : Records) (read : Read) : Option Value × RecordPart :=
  let rows := records.filter (·.entity == read.entity)
  match read.key, read.field with
  | none, none => (some (.arr ((records.keys read.entity).map .str)), .keys read.entity)
  | some key, none => (some (.bool (rows.any (·.key == some key))), .record read.entity key)
  | key, some name => ((rows.find? (·.key == key)).bind (·.value.field? name), .field read.entity key name)

/-- The value that `read` asks for, and the part read, from `records`, or from `before` when it reads before the write. -/
def serveRead (records before : Records) (read : Read) : Option Value × RecordPart :=
  serve (if read.beforeEventWrite then before else records) read

/-- A reply that TS gave, with each read that TS sent while replying and the value that Lean served for it. -/
structure Answered where
  reads : Array (Read × Option Value)
  replied : Replied

/-- The replies that TS gave in one run tree, by the question's line. -/
abbrev Memo := IO.Ref (Std.HashMap String Answered)

/-- The reply that TS gives to `asked`. While it waits, it serves each read and adds the part read to `reads`. -/
partial def exchange (stdin stdout : IO.FS.Stream) (reads : Reads) (records before : Records) (asked : Asked) :
    IO Answered := do
  reads.set {}
  sendLine stdout asked
  let rec wait (served : Array (Read × Option Value)) : IO Answered := do
    let line ← stdin.getLine
    -- getLine returns "" once TS closes stdin.
    if line.isEmpty then IO.Process.exit 0
    let replied : Replied ← IO.ofExcept (parse line >>= FromValue.fromValue)
    match replied.reply with
    | .read entity key field beforeEventWrite =>
      let read := { entity, key, field, beforeEventWrite := beforeEventWrite == some true }
      let (value, part) := serveRead records before read
      reads.modify (·.add part)
      sendLine stdout ({ question := .served value } : Asked)
      wait (served.push (read, value))
    | _ =>
      reads.modify fun l => { l with replied := some replied }
      pure { reads := served, replied }
  wait #[]

/--
The reply to `question`, with the parts read in `reads`: the one in `memo` when Lean serves every read recorded with it
the same value now, otherwise the one TS gives, which `memo` then records.
-/
def ask (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool) (service : Option String)
    (records : Records) (question : Question) (before : Records := []) : IO Reply := do
  let asked : Asked := { service, reversed := if reversed then some true else none, question }
  let line := render (ToValue.toValue asked)
  if let some answered := (← memo.get)[line]? then
    let served := answered.reads.map fun (read, value) => (serveRead records before read, value)
    if served.all fun ((now, _), value) => now == value then
      reads.set { served.foldl (fun (l : Log) ((_, part), _) => l.add part) {} with replied := answered.replied }
      return answered.replied.reply
  let answered ← exchange stdin stdout reads records before asked
  memo.modify (·.insert line answered)
  pure answered.replied.reply

/-- The answer that `reply` gives to `question`, which `read` takes from the reply of the question's name. -/
def answer {α : Type} (question : Question) (reply : Reply) (read : Reply → Option α) : IO (Except Issue α) :=
  match reply with
  | .issue issue => pure (.error issue)
  | reply => match read reply with
    | some a => pure (.ok a)
    | none => throw (IO.userError s!"TS answered {question.type} with {reply.type}")

/--
The functions that ask TS, which answers with every Bag in reverse order when `reversed` is set, about the service
`service` when given, or else the request's service.
-/
def functions (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool)
    (service : Option String := none) : Functions IO :=
  let asking (records : Records) (question : Question) (before : Records := []) :=
    ask stdin stdout reads memo reversed service records question before
  let answered {α : Type} (question : Question) (read : Reply → Option α) (records : Records := [])
      (before : Records := []) : IO (Except Issue α) := do
    answer question (← asking records question before) read
  let always {α : Type} (question : Question) (read : Reply → Option α) : IO α := do
    match ← answered question read with
    | .ok a => pure a
    | .error issue => throw (IO.userError s!"TS answered {question.type} with {repr issue}, which has no issue")
  { parse := fun schema value => answered (.parse schema value) fun | .parse v => some v | _ => none
    unordered := fun schema value => answered (.unordered schema value) fun | .unordered v => some v | _ => none
    normalize := fun schema value => answered (.normalize schema value) fun | .normalize v => some v | _ => none
    binding := fun name binding input records now =>
      answered (.binding name binding input now) (records := records) fun | .binding b => some b | _ => none
    requirement := fun name condition input records now =>
      answered (.requirement name condition input now) (records := records) fun
        | .requirement h => some h | _ => none
    inputRequirement := fun name condition input =>
      answered (.inputRequirement name condition input) fun | .inputRequirement h => some h | _ => none
    ensures := fun name input before after now =>
      answered (.ensures name input now) (records := after) (before := before) fun
        | .ensures f => some f | _ => none
    queryEnsures := fun name input output records =>
      answered (.queryEnsures name input output) (records := records) fun | .queryEnsures f => some f | _ => none
    resultEnsures := fun target input output events =>
      answered (.resultEnsures target input output events) fun | .resultEnsures f => some f | _ => none
    invariant := fun entity row => answered (.invariant entity row) fun | .invariant f => some f | _ => none
    serviceInvariant := fun records => do
      match ← answered .serviceInvariant (records := records) fun | .serviceInvariant f => some f | _ => none with
      | .ok failed => pure (.ok failed)
      | .error (.thrown schema) => pure (.error schema)
      | .error issue => throw (IO.userError s!"serviceInvariant answered {repr issue}, which is no throw")
    chartInvariant := fun scope records =>
      answered (.chartInvariant scope) (records := records) fun | .chartInvariant f => some f | _ => none
    decide := fun name input records now =>
      answered (.decide name input now) (records := records) fun | .decide groups => some groups | _ => none
    resolve := fun name input records now =>
      answered (.resolve name input now) (records := records) fun | .resolve output => some output | _ => none
    react := fun name payload records now keys =>
      answered (.react name payload now keys) (records := records) fun
        | .react input created => some (input, created) | _ => none
    comparable := fun name a => answered (.comparable name a) fun | .comparable v => some v | _ => none
    initialContext := fun name input =>
      answered (.initialContext name input) fun | .initialContext context => some context | _ => none
    guard := fun scope records t extra =>
      answered (.guard scope t extra) (records := records) fun | .guard passes => some passes | _ => none
    assign := fun scope records a extra keys =>
      answered (.assign scope a extra keys) (records := records) fun
        | .assign context copy created => some (context, copy, created) | _ => none
    input := fun scope records a keys =>
      answered (.input scope a keys) (records := records) fun
        | .input input created => some (input, created) | _ => none
    holds := fun scope records => answered (.holds scope) (records := records) fun | .holds => some () | _ => none
    deadlines := fun machine state => do
      let deadlines ← always (.deadlines machine state) fun | .deadlines ds => some ds | _ => none
      pure (deadlines.map fun d => (d.name, (d.delay.map fun ms => DeadlineTime.delay ms).getD .atExpression))
    deadlineAt := fun scope records name =>
      answered (.deadlineAt scope name) (records := records) fun | .deadlineAt time => some time | _ => none
    offers := fun scope records control =>
      answered (.offers scope control) (records := records) fun | .offers payloads => some payloads | _ => none
    showInput := fun scope records a =>
      answered (.showInput scope a) (records := records) fun | .showInput input => some input | _ => none
    items := fun scope records =>
      answered (.items scope) (records := records) fun
        | .items keys => some (keys.map fun k => (k.key, k.encodedKey)) | _ => none
    copyContext := fun chart map =>
      always (.copyContext chart map) fun | .copyContext context => some context | _ => none
    singleRecord := fun entity => always (.singleRecord entity) fun | .singleRecord record => some record | _ => none
    copyKey := fun chart map payload =>
      answered (.copyKey chart map payload) fun | .copyKey key => some key | _ => none
    close := fun scope records =>
      answered (.close scope) (records := records) fun | .close output failed => some (output, failed) | _ => none }

/-- The comparable value that verify reads, which TS computes. -/
def askComparable (stdin stdout : IO.FS.Stream) (reads : Reads) (d : Spec.Definition) (part : Verify.Part)
    (value : Value) : IO CValue := do
  let question := Question.comparableValue d.kind { service := d.service, name := d.name } part value
  let { replied, .. } ← exchange stdin stdout reads [] [] { question }
  match replied.reply with
  | .comparableValue v => IO.ofExcept (CValue.decode v)
  | reply => throw (IO.userError s!"TS answered comparableValue with {reply.type}")

/--
The first violation, by line, that verify finds in `actual` with `expected` as the snapshot, as TS `compareTrace`
returns.
-/
def compareOf (spec : Spec.Structure) (service : String)
    (ask : Spec.Definition → Verify.Part → Value → IO CValue) : Compare IO := fun renamed expected actual => do
  let compared ← Verify.verifyLines spec service ask (expected.map some) (actual.map .line) renamed
  let numbered := compared.findings.map fun f =>
    (f.line, match f with
      | .mismatch m => m.toViolation
      | .uncomparable u => u.toViolation)
  pure (match (numbered.mergeSort fun a b => decide (a.1 ≤ b.1)).head? with
    | some (_, v) => .error v
    | none => .ok compared.bindings)

/-- The comparison violations of `trace` against `snapshot`, and the pairs of each binding that it ends with. -/
def verify (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (service : String)
    (snapshot : List (Option TraceLine)) (trace : List (FileLine TraceLine)) : IO Value := do
  let compared ← Verify.verifyLines spec service (askComparable stdin stdout (← IO.mkRef {})) snapshot trace id
  pure (.obj [("type", .str "verified"), ("findings", .arr (compared.findings.map Verify.Finding.toValue)),
    ("bindings", .arr (compared.bindings.map fun b => .arr (b.strings.map fun (s, t) => .arr [.str s, .str t])))])

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
  note n := do focus (← get).current (MonadNote.note n : StateT Collect IO Unit)

instance : Sim.MonadActing ActingIO where
  acting service x := do
    let previous := (← get).current
    modify ({ · with current := service })
    let r ← x
    modify ({ · with current := previous })
    pure r

/--
The functions of each running service of `start`, instrumented as Instrument does, which collect into that service's
Collect. Each question to TS names its service.
-/
def instrumentedOf (stdin stdout : IO.FS.Stream) (start : Sim.World) : IO (String → Functions ActingIO) := do
  let reads ← IO.mkRef {}
  let memo ← IO.mkRef {}
  pure fun service =>
    let fs := functions stdin stdout reads memo false (some service)
    match start.services.lookup service with
    | none => liftFunctions fs
    | some st =>
      let ifs : InstrumentFunctions IO := {
        lastReads := do pure (← reads.get).parts
        lastAccess := do pure (((← reads.get).replied.bind (·.access)).getD {})
        lastEnumerated := do pure (((← reads.get).replied.bind (·.enumerated)) == some true)
        reversed := functions stdin stdout reads memo true (some service) }
      (instrument st fs ifs).hoist (focus service)

/-- The start of the world of `sc`, with the step orders that the request names. -/
def worldOf (spec : Spec.Structure) (sc : Scenario) (stepOrders : List StepOrder) : IO Sim.World := do
  let start ← IO.ofExcept (Sim.World.start spec sc)
  pure { start with stepOrders := stepOrders.map fun o => (o.origin, o.service, o.order) }

/--
The reply to request `simulate`, which takes a structure, a scenario, and step orders, and returns each running
service's trace lines, violations (its own, then those Instrument collected, then its halt), and candidates, and the
simulation's violations and halting violation. With `execute` true, the lines take place as explore runs them (Sim.execute), and
each running service that did not halt also returns what it enables next.
-/
def simulateRequest (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (sc : Scenario) (executing : Bool)
    (stepOrders : List StepOrder) : IO Value := do
  let start ← worldOf spec sc stepOrders
  let fsOf ← instrumentedOf stdin stdout start
  let ran : ActingIO Sim.World :=
    if executing then Sim.execute spec fsOf start sc else Sim.simulate spec fsOf start sc
  let (w, acting) ← ran.run {}
  let (services, _) ← (w.states.mapM fun ((service, s) : String × State) => do
    let c := acting.collect service
    let enabled ← match executing, s.halted, w.services.lookup service with
      | true, none, some st => do
        match ← Explore.enabled st (fsOf service) s with
        | .ok e => pure [("enabled", ToValue.toValue e)]
        | .error f => pure [("enabled", .obj [("fault", ToValue.toValue (Finding.fault f).toViolation)])]
      | _, _, _ => pure []
    let fields : List (String × Value) := [("service", .str service),
      ("lines", .arr (s.lines.toList.map fun l => lineValue l [] [])),
      ("violations", .arr ((reportedViolations s c none).map ToValue.toValue)),
      ("candidates", .arr (((w.services.lookup service).map fun st => candidates st s c none).getD [] |>.map
        fun ((i, j) : Nat × Nat) => .arr [.num i, .num j]))]
    pure (Value.obj (fields ++ enabled))).run acting
  pure (.obj [("type", .str "simulated"),
    ("services", .arr services),
    ("violations", .arr (w.violations.map Sim.InvalidScenario.toValue)),
    ("halted", (w.halted.map Sim.InvalidScenario.toValue).getD .null)])

/-- The JSON of a search, as TS writes it. -/
def searchValue (r : Searched) : Value :=
  .obj [("origin", ToValue.toValue r.origin), ("service", .str r.service),
    ("tried", .arr (r.search.tried.map fun t => .obj (("order", ToValue.toValue t.order) :: match t.verdict with
      | .refused => [("refused", .bool true)]
      | .decided found => [("found", (found.map (·.toValue)).getD .null)]))),
    ("found", .arr (r.search.found.map (·.toValue)))]

/--
The reply to request `stepOrderChanges`, which takes a structure and a scenario and returns stepOrderChanges of the
scenario executed, from its startup: every search, with each step order it ran and its verdict, and what it found.
-/
def stepOrderChangesRequest (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (sc : Scenario) : IO Value := do
  let executeWith (sc : Scenario) (stepOrders : List (Scenario.Origin × String × List StepName)) : IO Execution := do
    let start ← IO.ofExcept (Sim.World.start spec sc)
    let start := { start with stepOrders }
    let ran : ActingIO Sim.World := Sim.execute spec (← instrumentedOf stdin stdout start) start sc
    let (w, acting) ← ran.run {}
    pure { world := w, collect := acting.collect }
  let reads ← IO.mkRef {}
  let searched ← stepOrderChanges (fun service => compareOf spec service (askComparable stdin stdout reads))
    executeWith sc (← executeWith sc []) 0
  pure (.obj [("type", .str "stepOrderChanges"), ("searched", .arr (searched.map searchValue))])

/--
The reply to request `assignmentChanges`, which takes a structure and a scenario and returns assignmentSearch of the
scenario's handle groups: each assignment it ran, with the violation it found, and what it reports.
-/
def assignmentChangesRequest (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (sc : Scenario) : IO Value := do
  let start ← worldOf spec sc []
  let executeWith (assignments : List (Scenario.Fact × List Nat)) : IO Execution := do
    let start := { start with assignments }
    let ran : ActingIO Sim.World := Sim.execute spec (← instrumentedOf stdin stdout start) start sc
    let (w, acting) ← ran.run {}
    pure { world := w, collect := acting.collect }
  let base ← executeWith []
  let fsOf ← instrumentedOf stdin stdout start
  let sizeOf (g : HandleGroup) : IO Nat := do pure (← (groupSize fsOf base.world g).run {}).1
  let reads ← IO.mkRef {}
  let search ← assignmentSearch (fun service => compareOf spec service (askComparable stdin stdout reads)) sizeOf
    executeWith base (handleGroups sc)
  pure (.obj [("type", .str "assignmentChanges"),
    ("tried", .arr (search.tried.map fun t => .obj [("assigned", ToValue.toValue t.assigned),
      ("found", (t.found.map (·.toValue)).getD .null)])),
    ("found", .arr (search.found.map (·.toValue)))])

/-- The response to `request`. A snapshot line is none for a blank line. -/
def respond (stdin stdout : IO.FS.Stream) : DiffTest.Request → IO Value
  | .check s =>
    pure (.obj [("type", .str "checked"), ("findings", .arr ((Validation.check s).map Validation.Illegal.toValue))])
  | .verify s service snapshot trace => verify stdin stdout s service snapshot trace
  | .checkExternal s service trace =>
    pure (.obj [("type", .str "checkedExternal"),
      ("findings", .arr ((Verify.checkExternal s service trace).map Verify.Finding.toValue))])
  | .pair services scenarios others folders =>
    let found := Verify.pairTraces (services.map fun s => (s.name, s.external)) scenarios others folders
    pure (.obj [("type", .str "paired"), ("compare", refValues found.compare),
      ("contract", refValues found.contract), ("findings", pairingFindings found.violations)])
  | .pairSnapshots services scenarios folders =>
    let found := Verify.pairSnapshots services scenarios folders
    pure (.obj [("type", .str "pairedSnapshots"), ("compare", refValues found.compare),
      ("findings", pairingFindings found.violations)])
  | .compareSnapshot snapshot run =>
    pure (.obj [("type", .str "comparedSnapshot"),
      ("mismatch", ((Verify.compareSnapshot snapshot run).map Verify.Mismatch.toValue).getD .null)])
  | .afters snapshot =>
    let lines := snapshot.map (·.map fun l : TraceLine => ({ l with value := none } : Verify.Line))
    pure (.obj [("type", .str "afters"), ("findings", .arr ((Verify.unknownAfters lines).map (·.toValue)))])
  | .decodeLines values =>
    pure (.obj [("type", .str "decodedLines"), ("lines", .arr (values.map fun v =>
      match (FromValue.fromValue v : Except String TraceLine) with
      | .ok line => ToValue.toValue line
      | .error _ => .null))])
  | .simulate s sc execute stepOrders =>
    simulateRequest stdin stdout s sc (execute == some true) (stepOrders.getD [])
  | .stepOrderChanges s sc => stepOrderChangesRequest stdin stdout s sc
  | .assignmentChanges s sc => assignmentChangesRequest stdin stdout s sc

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let reply ← try
      respond stdin stdout (← IO.ofExcept (parse line >>= FromValue.fromValue))
    catch e => pure (.obj [("type", .str "error"), ("message", .str (toString e))])
  sendLine stdout reply
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
