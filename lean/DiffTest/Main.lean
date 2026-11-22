import Std.Data.HashMap
import DiffTest.Json
import DiffTest.Protocol
import Tazuna.Explore.StepOrders
import Tazuna.Ir.Overlay
import Tazuna.Sim.Run
import Tazuna.Data.Parse
import Tazuna.Validation.Canonical

/-!
tazuna-lean exchanges one JSON value per line with TS over stdio (precedents: leanprover-community/repl, the Lean LSP).
DiffTest/Protocol.lean defines the messages.

Service asks TS for a spec function's value whenever it needs one, unless the request's program holds the function as
IR, which Lean evaluates itself (Ir.Program.overlay). While computing it, TS sends `read` for each record a TS function
reads; Lean serves the value from its own records and remembers the parts read, which Instrument records in the
accesses of steps. Within one run tree, Lean reuses the reply that TS gave to the same question when the values
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
`service` when given, or else the request's service. A parse logs nothing into `reads`: Functions.sorting asks it
inside another answer, whose reads Instrument then reads.
-/
def functions (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool)
    (service : Option String := none) : Functions IO :=
  let asking (records : Records) (question : Question) (before : Records := []) :=
    ask stdin stdout reads memo reversed service records question before
  let answered {α : Type} (question : Question) (read : Reply → Option α) (records : Records := [])
      (before : Records := []) : IO (Except Issue α) := do
    answer question (← asking records question before) read
  { parse := fun schema value => do
      answer (.parse schema value) (← ask stdin stdout (← IO.mkRef {}) memo reversed service [] (.parse schema value)) fun
        | .parse v _ => some v | _ => none
    unordered := fun schema value => answered (.unordered schema value) fun | .unordered v => some v | _ => none
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
    resultEnsures := fun target c input output events =>
      answered (.resultEnsures target c input output events) fun | .resultEnsures e => some e | _ => none
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
    automationBinding := fun name b payload records now =>
      answered (.automationBinding name b payload now) (records := records) fun
        | .automationBinding b => some b | _ => none
    automationGuard := fun name c payload records now =>
      answered (.automationGuard name c payload now) (records := records) fun
        | .automationGuard h => some h | _ => none
    react := fun name payload records now keys =>
      answered (.react name payload now keys) (records := records) fun
        | .react input created => some (input, created) | _ => none
    comparable := fun name a => answered (.comparable name a) fun | .comparable v => some v | _ => none
    initialContext := fun name input =>
      answered (.initialContext name input) fun | .initialContext context => some context | _ => none
    guard := fun scope records t c extra =>
      answered (.guard scope t c extra) (records := records) fun | .guard holds => some holds | _ => none
    assign := fun scope records a extra keys =>
      answered (.assign scope a extra keys) (records := records) fun
        | .assign context copy created => some (context, copy, created) | _ => none
    input := fun scope records a keys =>
      answered (.input scope a keys) (records := records) fun
        | .input input created => some (input, created) | _ => none
    held := fun scope records n edge extra =>
      answered (.held scope n edge extra) (records := records) fun | .held v => some v | _ => none
    deadlineAt := fun scope records name =>
      answered (.deadlineAt scope name) (records := records) fun | .deadlineAt time => some time | _ => none
    offers := fun scope records control =>
      answered (.offers scope control) (records := records) fun | .offers payloads => some payloads | _ => none
    showInput := fun scope records a =>
      answered (.showInput scope a) (records := records) fun | .showInput input => some input | _ => none
    items := fun scope records =>
      answered (.items scope) (records := records) fun
        | .items keys => some keys | _ => none
    defaults := fun schema => answered (.defaults schema) fun | .defaults v => some v | _ => none
    close := fun scope records => answered (.close scope) (records := records) fun | .close o => some o | _ => none
    closeEnsures := fun screen input output =>
      answered (.closeEnsures screen input output) fun | .closeEnsures f => some f | _ => none }

/-- The comparable value that verify reads, which TS computes. -/
def askComparable (stdin stdout : IO.FS.Stream) (reads : Reads) (d : Spec.Definition) (part : Verify.Part)
    (value : Value) : IO CValue := do
  let question := Question.comparableValue d.kind { service := d.service, name := d.name } part value
  let { replied, .. } ← exchange stdin stdout reads [] [] { question }
  match replied.reply with
  | .comparableValue v => IO.ofExcept (CValue.decode v)
  | reply => throw (IO.userError s!"TS answered comparableValue with {reply.type}")

/-- The comparison violations of `trace` against `snapshot`, and the pairs of each binding that it ends with. -/
def verify (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (service : String)
    (snapshot : List (Option TraceLine)) (trace : List (FileLine TraceLine)) : IO Response := do
  let compared ← Verify.verifyLines spec service (askComparable stdin stdout (← IO.mkRef {})) snapshot trace id
  pure (.verified compared.findings (compared.bindings.map (·.strings)))

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

/-- The notes of a run outside a simulation, of which tazuna-lean hears only a bug, and stops on it. -/
instance : MonadNote IO where
  note
    | .bug message => throw (IO.userError message)
    | _ => pure ()

/-- The text of an answer, for the message of a mismatch. -/
def describe {ε α : Type} [Repr ε] [Repr α] : Except ε α → String
  | .ok a => s!"{repr a}"
  | .error e => s!"the Issue {repr e}"

def sameAnswer {ε α : Type} [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

/--
The answer that Lean evaluated, with what it read, after checking it against `beneath`, TS's answer to the same
question: both answer alike, read the same record parts in the same order, and read and assign the same chart values,
or tazuna-lean stops. The read log then holds what the evaluation read, and no enumeration of a Bag: no IR operation
can tell the order in which a Bag visits its values, so orderAudit has nothing to find.
-/
def shadowed (reads : Reads) : Ir.Answered IO := fun callback (answer, trace) beneath => do
  let ts ← beneath
  let log ← reads.get
  let access := (log.replied.bind (·.access)).getD {}
  unless sameAnswer answer ts && trace.parts == log.parts && trace.access == access do
    throw (IO.userError
      s!"IR answers {callback} with {describe answer} reading {repr trace.parts} {repr trace.access}, TS with {describe ts} reading {repr log.parts} {repr access}")
  reads.set { parts := trace.parts, replied := log.replied.map fun r => { r with enumerated := none } }
  pure answer

instance : BEq (Except (List Value) Value) := ⟨sameAnswer⟩

/-- `lean`, after checking that TS answered `question` alike, or tazuna-lean stops. -/
def checkedAgainst {α : Type} [BEq α] [Repr α] (question : String) (lean ts : Except Issue α) : IO (Except Issue α) := do
  unless sameAnswer lean ts do
    throw (IO.userError s!"Lean answers {question} with {describe lean}, TS with {describe ts}")
  pure lean

/--
`fs` with the structural questions that Lean answers by Data.Parse wherever the schema says all that Zod checks, each
after checking it against TS's answer, Zod's issues included, or tazuna-lean stops; elsewhere TS's.
-/
def structural (stdin stdout : IO.FS.Stream) (memo : Memo) (service : String) (st : Service) (fs : Functions IO) :
    Functions IO :=
  let schemaFor (schema : Schema) : Option Value :=
    (st.schemaOf schema).map rootSchema |>.filter supported
  let thrownBy (schema : Schema) {α : Type} : ParseM α → Except Issue α
    | .ok a => .ok a
    | .error () => .error (.thrown (some schema))
  { fs with
    parse := fun schema value => do
      let some parsed := (st.schemaOf schema).bind (Data.parse · value) | fs.parse schema value
      let lean := thrownBy schema parsed
      let ts : Except Issue (Except (List Value) Value) ←
        match ← ask stdin stdout (← IO.mkRef {}) memo false service [] (.parse schema value) with
        | .issue issue => pure (.error issue)
        | .parse (some v) _ => pure (.ok (.ok v))
        | .parse none issues => pure (.ok (.error (issues.getD [])))
        | reply => throw (IO.userError s!"TS answered parse with {reply.type}")
      let checked ← checkedAgainst s!"parse of {(ToValue.toValue value).canonical}" lean ts
      pure (checked.map (·.toOption))
    unordered := fun schema value => do
      let some json := schemaFor schema | fs.unordered schema value
      checkedAgainst "unordered" (thrownBy schema (unorderedBy json value)) (← fs.unordered schema value)
    comparable := fun query answer => do
      let output := .output (st.ref query)
      let json := (st.schemaOf output).map rootSchema
      if !(json.all supported) then return ← fs.comparable query answer
      checkedAgainst "comparable" (thrownBy output (comparableText json (ToValue.toValue answer)))
        (← fs.comparable query answer)
    defaults := fun schema => do
      let some json := schemaFor schema | fs.defaults schema
      checkedAgainst "defaults" (.ok (defaultsOf json)) (← fs.defaults schema) }

/--
The functions of each running service of `start`, instrumented as Instrument does, which collect into that service's
Collect. Each question to TS names its service. The run asks only running services.
-/
def instrumentedOf (stdin stdout : IO.FS.Stream) (program : Ir.Program) (start : Sim.World) :
    IO (String → Functions ActingIO) := do
  let reads ← IO.mkRef {}
  let memo ← IO.mkRef {}
  pure fun service =>
    let fs := functions stdin stdout reads memo false (some service)
    match start.services.lookup service with
    | none => fs.hoist fun _ => throw (IO.userError s!"the run asked {service}, which does not run")
    | some st =>
      let overlaid (fs : Functions IO) := structural stdin stdout memo service st (program.overlay st (shadowed reads) fs)
      let ifs : InstrumentFunctions IO := {
        lastReads := do pure (← reads.get).parts
        lastAccess := do pure (((← reads.get).replied.bind (·.access)).getD {})
        lastEnumerated := do pure (((← reads.get).replied.bind (·.enumerated)) == some true)
        reversed := overlaid (functions stdin stdout reads memo true (some service)) }
      (instrument st (overlaid fs) ifs).hoist (focus service)

/-- The start of the world of `sc`, with the step orders that the request names. -/
def worldOf (spec : Spec.Structure) (sc : Scenario) (stepOrders : List StepOrder) : IO Sim.World := do
  let start ← Sim.World.start spec sc
  pure { start with stepOrders := stepOrders.map fun o => (o.origin, o.service, o.order) }

/--
The reply to request `simulate`, which takes a structure, a scenario, and step orders, and returns each running
service's trace lines, violations (its own, then those Instrument collected, then its halt), and candidates, and the
simulation's violations and halting violation. With `execute` true, the lines take place as explore runs them (Sim.execute), and
each running service that did not halt also returns what it enables next and its state as ChoiceDependent compares it.
-/
def simulateRequest (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (sc : Scenario) (executing : Bool)
    (stepOrders : List StepOrder) (exploring : Bool) (program : Ir.Program) : IO Response := do
  let start ← worldOf spec sc stepOrders
  let fsOf ← instrumentedOf stdin stdout program start
  let path : Explore.Explored := { sc, lines := sc.lines, domains := [] }
  let ran : ActingIO Sim.World :=
    if executing then path.world spec fsOf start else Sim.simulate spec fsOf start sc
  let (w, acting) ← ran.run {}
  let reachedAll := w.states.foldl (fun acc (service, _) =>
    (acting.collect service).reached.foldl (fun acc u => if acc.contains u then acc else acc ++ [u]) acc) []
  let (services, _) ← (w.states.mapM fun ((service, s) : String × State) => do
    let c := acting.collect service
    let running := match executing, s.halted, w.services.lookup service with
      | true, none, some st => some st
      | _, _, _ => none
    let next : Option (Except Fault (Explore.Enabled × Option (List Explore.Move))) ← match running with
      | some st => do
        match ← Explore.enabled st (fsOf service) s with
        | .error f => pure (some (.error f))
        | .ok e =>
          if !exploring || service != sc.service then pure (some (.ok (e, none))) else
          let explore ← Explore.exploreOf spec sc.service
          pure (some (.ok (e, some (← Explore.moves spec st { path with domains := explore.domains } w e))))
      | none => pure none
    pure ({ service
            lines := s.lines.toList.map (Sim.traceLineOf service · [] [])
            violations := reportedViolations s c none
            candidates := if (w.services.lookup service).isSome then candidates s c none else []
            enabled := next.bind fun r => r.toOption.map Prod.fst
            moves := next.bind fun r => r.toOption.bind Prod.snd
            fault := next.bind fun
              | .error f => some (Finding.fault f).toViolation
              | .ok _ => none
            state := running.map fun st => (Explore.stateValue st s).flatten
            reached := if executing then
                some (c.reached.mergeSort fun a b => decide ((ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical))
              else none
            uncovered := if executing && exploring && service == sc.service then
                some (Explore.uncovered spec reachedAll)
              else none } : SimulatedService)).run acting
  let fingerprint ← if executing && exploring then some <$> Explore.worldFingerprint w else pure none
  pure (.simulated services w.violations w.halted fingerprint)

/-- A search, as TS writes it. -/
def searchedOf (r : Searched) : SearchedProcessing :=
  { origin := r.origin, service := r.service, found := r.search.found
    tried := r.search.tried.map fun t => match t.verdict with
      | .refused => { order := t.order, refused := some true, found := none }
      | .decided found => { order := t.order, refused := none, found := some found } }

/--
The reply to request `stepOrderChanges`, which takes a structure and a scenario and returns stepOrderChanges of the
scenario executed, from its startup: every search, with each step order it ran and its verdict, and what it found.
-/
def stepOrderChangesRequest (stdin stdout : IO.FS.Stream) (spec : Spec.Structure) (sc : Scenario)
    (program : Ir.Program) : IO Response := do
  let executeWith (sc : Scenario) (stepOrders : List (Scenario.Origin × String × List StepName)) : IO Execution := do
    let start ← Sim.World.start spec sc
    let start := { start with stepOrders }
    let ran : ActingIO Sim.World := Sim.execute spec (← instrumentedOf stdin stdout program start) start sc
    let (w, acting) ← ran.run {}
    pure { world := w, collect := acting.collect }
  let reads ← IO.mkRef {}
  let compare service renamed expected actual := do
    pure ((← Verify.compareTraces spec service (askComparable stdin stdout reads) renamed expected actual).mapError fun
      | .mismatch m => Explore.Difference.outputs m.toViolation
      | .uncomparable u => .outputs u.toViolation
      | .after line subject snapshot trace => .after line subject snapshot trace)
  let searched ← stepOrderChanges compare
    executeWith sc (← executeWith sc []) 0
  pure (.stepOrderChanges (searched.map searchedOf))

/-- The response to `request`. A snapshot line is none for a blank line. -/
def respond (stdin stdout : IO.FS.Stream) : DiffTest.Request → IO Response
  | .check s => pure (.checked (Validation.check s))
  | .checkCanonical s => pure (.checkedCanonical (Validation.Canonical.check s))
  | .verify s service snapshot trace => verify stdin stdout s service snapshot trace
  | .checkExternal s service trace => pure (.checkedExternal (Verify.checkExternal s service trace))
  | .pair services expected others folders =>
    let found := Verify.pairTraces (services.map fun s => (s.name, s.external)) expected others folders
    pure (.paired found.compare found.contract (unpaired found.violations))
  | .pairSnapshots services expected folders =>
    let found := Verify.pairSnapshots services expected folders
    pure (.pairedSnapshots found.compare (unpaired found.violations))
  | .compareSnapshot snapshot run => pure (.comparedSnapshot (Verify.compareSnapshot snapshot run))
  | .afters snapshot =>
    let lines := snapshot.map (·.map fun l : TraceLine => ({ l with value := none } : Verify.Line))
    pure (.afters (Verify.unknownAfters lines))
  | .decodeLines values =>
    pure (.decodedLines (values.map fun v => (FromValue.fromValue v : Except String TraceLine).toOption))
  | .simulate s sc execute stepOrders explore program =>
    simulateRequest stdin stdout s sc (execute == some true) (stepOrders.getD []) (explore == some true)
      (program.getD {})
  | .stepOrderChanges s sc program => stepOrderChangesRequest stdin stdout s sc (program.getD {})
  | .sort schema value => pure (.sorted (sortCollections schema value))
  | .keyOrdered schema value => pure (.keyOrdered (keyOrdered schema value))
  | .schemaOf s service schema => do pure (.schemaOf ((← Service.ofStructure s service).schemaOf schema))
  | .evaluate body input records keys =>
    let env : Ir.Env := { args := Ir.argsOf [(.input, .json input)], records := records.map Stored.row, keys }
    let (answer, trace) := (do Ir.encode env (← Ir.eval env [] body)).run'
    let reads := trace.parts.map ReadPart.of
    let created := trace.created
    pure (match answer with
      | .ok value => .evaluated { value, issue := none, reads, created }
      | .error issue => .evaluated { value := none, issue, reads, created })
  | .parse schema value => pure (match Data.parse schema value with
    | none => .parsed false none none false
    | some (.error ()) => .parsed true none none true
    | some (.ok (.ok v)) => .parsed true (some v) none false
    | some (.ok (.error issues)) => .parsed true none (some issues) false)
where
  unpaired (l : List (Verify.At × Verify.Uncomparable)) : List Unpaired := l.map fun (place, violation) => { «at» := place, violation }

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let reply ← try
      respond stdin stdout (← IO.ofExcept (parse line >>= FromValue.fromValue))
    catch e => pure (.error (toString e))
  sendLine stdout reply
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
