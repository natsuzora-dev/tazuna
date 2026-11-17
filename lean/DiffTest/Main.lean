import Std.Data.HashMap
import DiffTest.Json
import DiffTest.Names
import Tazuna.Explore.Assignments
import Tazuna.Sim.Run

/-!
tazuna-lean exchanges one JSON value per line with TS over stdio (precedents: leanprover-community/repl, the Lean LSP).

Semantics asks TS for a spec function's value whenever it needs one. While computing it, TS sends `read` for each record
a TS function reads; Lean serves the value from its own records and remembers the parts read, which Instrument records
in the accesses of steps. Within one run tree, Lean reuses the reply that TS gave to the same question when the values
that Lean serves for the reads that TS made then are the same now: a TS reply depends only on the question and those
values.
-/

open Tazuna Tazuna.Data Tazuna.Semantics Tazuna.Observe Tazuna.Explore Tazuna.Json

structure Log where
  parts : List RecordPart := []
  reply : Value := .null

abbrev Reads := IO.Ref Log

def send (stdout : IO.FS.Stream) (message : Value) : IO Unit := do
  stdout.putStrLn (render message)
  stdout.flush

def Log.add (l : Log) (part : RecordPart) : Log :=
  { l with parts := if part ∈ l.parts then l.parts else l.parts ++ [part] }

def serve (records : Records) (read : Value) : Except String (Option Value × RecordPart) := do
  let entity ← stringField read "entity"
  let rows := records.filter (·.entity == entity)
  match ← optionalString read "key", ← optionalString read "field" with
  | none, none => pure (some (.arr ((records.keys entity).map .str)), .keys entity)
  | some key, none => pure (some (.bool (rows.any (·.key == some key))), .record entity key)
  | key, some name => pure ((rows.find? (·.key == key)).bind (·.value.field? name), .field entity key name)

/--
The value that a `read` asks for, and the part read, from `records`, or from `before` when `beforeEventWrite` is set.
-/
def serveRead (records before : Records) (read : Value) : Except String (Option Value × RecordPart) :=
  serve (if read.field? "beforeEventWrite" == some (.bool true) then before else records) read

/-- A reply that TS gave, with each `read` that TS sent while replying and the value that Lean served for it. -/
structure Answered where
  reads : Array (Value × Option Value)
  reply : Value

/-- The replies that TS gave in one run tree, by the question's line. -/
abbrev Memo := IO.Ref (Std.HashMap String Answered)

/-- The reply that TS gives to `request`. While it waits, it serves each `read` and adds the part read to `reads`. -/
partial def exchange (stdin stdout : IO.FS.Stream) (reads : Reads) (records before : Records) (request : Value) :
    IO Answered := do
  reads.set {}
  send stdout request
  let rec wait (served : Array (Value × Option Value)) : IO Answered := do
    let line ← stdin.getLine
    -- getLine returns "" once TS closes stdin.
    if line.isEmpty then IO.Process.exit 0
    let message ← IO.ofExcept (parse line)
    if (message.field? "type") == some (.str "read") then
      let (value, part) ← IO.ofExcept (serveRead records before message)
      reads.modify (·.add part)
      send stdout (obj [("type", some (.str "served")), ("value", value)])
      wait (served.push (message, value))
    else
      reads.modify fun l => { l with reply := message }
      pure { reads := served, reply := message }
  wait #[]

/--
The reply to `request`, with the parts read in `reads`: the one in `memo` when Lean serves every read recorded with it
the same value now, otherwise the one TS gives, which `memo` then records.
-/
def ask (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool) (service : Option String)
    (records : Records) (request : Value) (before : Records := []) : IO Value := do
  let request := if reversed then request.merge (.obj [("reversed", .bool true)]) else request
  let request := match service with
    | some s => request.merge (.obj [("service", .str s)])
    | none => request
  let line := render request
  if let some answered := (← memo.get)[line]? then
    let served ← answered.reads.mapM fun (read, value) => do
      let (now, part) ← IO.ofExcept (serveRead records before read)
      pure (now == value, part)
    if served.all (·.1) then
      reads.set { served.foldl (fun (l : Log) (_, part) => l.add part) {} with reply := answered.reply }
      return answered.reply
  let answered ← exchange stdin stdout reads records before request
  memo.modify (·.insert line answered)
  pure answered.reply

def nextKeys (keys : Keys) : Value :=
  .obj ((keys.owner.map fun o => ("owner", .str o)).toList ++
    [("next", .obj (keys.next.map fun (e, k) => (e, .obj [("count", .num k.count)])))])

def schemaRequest (type : String) (schema : Schema) (value : Value) : Value :=
  .obj [("type", .str type), ("schema", Schema.toValue schema), ("value", value)]

/--
The reply that `read` decodes, or, when the reply has `issue`, the issue that tells why the question has no answer.
-/
def issueOr {α : Type} (reply : Value) (read : Value → Except String α) : Except String (Except Issue α) :=
  match reply.field? "issue" with
  | some v => return .error (← Issue.decode v)
  | none => return .ok (← read reply)

/--
The functions that ask TS, which answers with every Bag in reverse order when `reversed` is set, about the service
`service` when given, or else the request's service.
-/
def functions (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool)
    (service : Option String := none) : Functions IO where
  parse schema value := do
    let reply ← ask stdin stdout reads memo reversed service [] (schemaRequest "parse" schema value)
    IO.ofExcept (issueOr reply fun r => pure (optional r "value"))
  canonical schema value := do
    let reply ← ask stdin stdout reads memo reversed service [] (schemaRequest "canonical" schema value)
    IO.ofExcept (issueOr reply (field · "value"))
  unordered schema value := do
    let reply ← ask stdin stdout reads memo reversed service [] (schemaRequest "unordered" schema value)
    IO.ofExcept (issueOr reply (field · "value"))
  normalize schema value := do
    let reply ← ask stdin stdout reads memo reversed service [] (schemaRequest "normalize" schema value)
    IO.ofExcept (issueOr reply fun r => pure (optional r "value"))
  binding name binding input records now := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "binding"), ("command", .str name), ("binding", .str binding), ("input", input),
             ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "bound"))
  requirement name condition input records now := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "requirement"), ("command", .str name), ("condition", .str condition), ("input", input),
             ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "holds"))
  inputRequirement name condition input := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "inputRequirement"), ("target", .str name), ("condition", .str condition), ("input", input)])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "holds"))
  ensures name input before after now := do
    let reply ← ask stdin stdout reads memo reversed service after
      (.obj [("type", .str "ensures"), ("command", .str name), ("input", input), ("now", .str (renderTime now))])
      before
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  queryEnsures name input output records := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "queryEnsures"), ("query", .str name), ("input", input), ("output", output)])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  resultEnsures target input output events := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "resultEnsures"), ("target", .str target), ("input", input), ("output", output.getD .null),
             ("events", .arr (events.map fun e => .obj [("event", .str e.event), ("payload", e.payload)]))])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  invariant entity row := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "invariant"), ("entity", .str entity), ("record", row)])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  serviceInvariant records := do
    let reply ← ask stdin stdout reads memo reversed service records (.obj [("type", .str "serviceInvariant")])
    match ← IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue) with
    | .ok failed => pure (.ok failed)
    | .error (.thrown schema) => pure (.error schema)
    | .error issue => throw (IO.userError s!"serviceInvariant answered {repr issue}, which is no throw")
  chartInvariant scope records := do
    let reply ← ask stdin stdout reads memo reversed service records (.obj [("type", .str "chartInvariant"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  decide name input records now := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "decide"), ("command", .str name), ("input", input), ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply fun r => do
      (← asList (← field r "groups")).mapM fun g => do (← asList g).mapM Emit.decode)
  resolve name input records now := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "resolve"), ("query", .str name), ("input", input), ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply (field · "output"))
  react name payload records now keys := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "react"), ("automation", .str name), ("payload", payload), ("now", .str (renderTime now)),
             ("keys", nextKeys keys)])
    IO.ofExcept (issueOr reply fun r => do
      pure (optional r "input", ← (← asList (← field r "created")).mapM FromValue.fromValue))
  comparable name answer := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "comparable"), ("query", .str name), ("answer", ToValue.toValue answer)])
    IO.ofExcept (issueOr reply (field · "value"))
  initialContext name input := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "initialContext"), ("machine", .str name), ("input", input)])
    IO.ofExcept (issueOr reply (field · "context"))
  guard scope records t extra := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "guard"), ("scope", Scope.toValue scope), ("transition", Transition.toValue t), ("extra", Extra.toValue extra)])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "passes"))
  assign scope records a extra keys := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "assign"), ("scope", Scope.toValue scope), ("at", Assignment.toValue a), ("extra", Extra.toValue extra),
             ("keys", nextKeys keys)])
    IO.ofExcept (issueOr reply fun r => do
      pure (← field r "context", optional r "copy", ← (← asList (← field r "created")).mapM FromValue.fromValue))
  input scope records a keys := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "input"), ("scope", Scope.toValue scope), ("activity", Activity.toValue a), ("keys", nextKeys keys)])
    IO.ofExcept (issueOr reply fun r => do
      pure (← field r "input", ← (← asList (← field r "created")).mapM FromValue.fromValue))
  holds scope records := do
    let reply ← ask stdin stdout reads memo reversed service records (.obj [("type", .str "holds"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun _ => pure ())
  deadlines machine state := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "deadlines"), ("machine", .str machine), ("state", .str state)])
    IO.ofExcept do
      (← asList (← field reply "deadlines")).mapM fun d => do
        let deadline ← match optional d "delay" with
          | some (.num ⟨n, 0⟩) => pure (DeadlineTime.delay n)
          | none => pure DeadlineTime.atExpression
          | some other => throw s!"expected a whole number of milliseconds, got {render other}"
        pure (← stringField d "name", deadline)
  deadlineAt scope records name := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "deadlineAt"), ("scope", Scope.toValue scope), ("name", .str name)])
    IO.ofExcept (issueOr reply fun r => do parseTime (← stringField r "time"))
  offers scope records control := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "offers"), ("scope", Scope.toValue scope), ("control", .str control)])
    IO.ofExcept (issueOr reply fun r => do asList (← field r "payloads"))
  showInput scope records a := do
    let reply ← ask stdin stdout reads memo reversed service records
      (.obj [("type", .str "showInput"), ("scope", Scope.toValue scope), ("activity", Activity.toValue a)])
    IO.ofExcept (issueOr reply (field · "input"))
  items scope records := do
    let reply ← ask stdin stdout reads memo reversed service records (.obj [("type", .str "items"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun r => do
      (← asList (← field r "keys")).mapM fun k => do pure (← field k "key", ← stringField k "encodedKey"))
  copyContext chart map := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "copyContext"), ("machine", .str chart), ("map", .str map)])
    IO.ofExcept (field reply "context")
  singleRecord entity := do
    let reply ← ask stdin stdout reads memo reversed service [] (.obj [("type", .str "singleRecord"), ("entity", .str entity)])
    IO.ofExcept (field reply "record")
  copyKey chart map payload := do
    let reply ← ask stdin stdout reads memo reversed service []
      (.obj [("type", .str "copyKey"), ("machine", .str chart), ("map", .str map), ("payload", payload)])
    IO.ofExcept (issueOr reply fun r => do
      match r.field? "key" with
      | none => pure none
      | some .null => pure (some none)
      | some k => pure (some (some (← FromValue.fromValue k))))
  close scope records := do
    let reply ← ask stdin stdout reads memo reversed service records (.obj [("type", .str "close"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun r => do
      pure (← field r "output", ← (optional r "failed").mapM FromValue.fromValue))

/-- The comparable value that verify reads, which TS computes. -/
def askComparable (stdin stdout : IO.FS.Stream) (reads : Reads) (d : Syntax.Definition) (part : Verify.Part)
    (value : Value) : IO CValue := do
  let { reply, .. } ← exchange stdin stdout reads [] []
    (.obj ([("type", .str "comparableValue"),
      ("definition", .obj [("kind", .str d.kind), ("service", .str d.service), ("name", .str d.name)])] ++
      part.toValue ++ [("value", value)]))
  IO.ofExcept (CValue.decode (← IO.ofExcept (field reply "value")))

/--
The first violation, by line, that verify finds in `actual` with `expected` as the snapshot, as TS `compareTrace`
returns.
-/
def compareOf (spec : Syntax.Structure) (service : String)
    (ask : Syntax.Definition → Verify.Part → Value → IO CValue) : Compare IO := fun expected actual => do
  let compared ← Verify.verifyLines spec service ask (expected.map some) (actual.map .line)
  let numbered := compared.findings.map fun f =>
    let v : Violation := match f with
      | .mismatch m => { kind := m.kind, definition := m.definition, data := m.data }
      | .uncomparable u => { kind := u.kind, definition := u.definition, data := u.data }
    (f.line, v)
  pure (match (numbered.mergeSort fun a b => decide (a.1 ≤ b.1)).head? with
    | some (_, v) => .error v
    | none => .ok compared.bindings)

/-- The reply to request `check`, which takes a structure and returns the Illegal violations. -/
def check (request : Value) : Except String Value := do
  let s : Syntax.Structure ← FromValue.fromValue (← field request "structure")
  pure (.obj [("type", .str "checked"), ("findings", .arr ((Validation.check s).map Validation.Illegal.toValue))])

/--
The reply to request `verify`, which takes a structure, a service, the snapshot lines (null for a blank line), and the
implementation lines (as `FileLine.decode` reads them), and returns the comparison violations and the pairs of each
binding of the set that it ends with. TS computes
`comparableValue` for each value.
-/
def verify (stdin stdout : IO.FS.Stream) (request : Value) : IO Value := do
  let spec : Syntax.Structure ← IO.ofExcept (FromValue.fromValue (← IO.ofExcept (field request "structure")))
  let service ← IO.ofExcept (stringField request "service")
  let snapshot ← IO.ofExcept do
    (← asList (← field request "snapshot")).mapM fun l =>
      if l == .null then pure none else some <$> FromValue.fromValue l
  let trace ← IO.ofExcept do (← asList (← field request "trace")).mapM FileLine.decode
  let compared ← Verify.verifyLines spec service (askComparable stdin stdout (← IO.mkRef {})) snapshot trace
  pure (.obj [("type", .str "verified"), ("findings", .arr (compared.findings.map Verify.Finding.toValue)),
    ("bindings", .arr (compared.bindings.map fun b => .arr (b.strings.map fun (s, t) => .arr [.str s, .str t])))])

/--
The reply to request `afters`, which takes the snapshot lines (null for a blank line) and returns the `unknownAfter`
violations of reading the snapshot.
-/
def afters (request : Value) : Except String Value := do
  let snapshot ← (← asList (← field request "snapshot")).mapM fun l =>
    if l == .null then pure none else some <$> FromValue.fromValue l
  let lines := snapshot.map (·.map fun l : TraceLine => ({ l with value := none } : Verify.Line))
  pure (.obj [("type", .str "afters"), ("findings", .arr ((Verify.unknownAfters lines).map (·.toValue)))])

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
        lastAccess := do IO.ofExcept (Access.decode (((← reads.get).reply.field? "access").getD (.obj [])))
        lastEnumerated := do pure ((← reads.get).reply.field? "enumerated" == some (.bool true))
        reversed := functions stdin stdout reads memo true (some service) }
      (instrument st fs ifs).hoist (focus service)

/-- The scenario of a request, with the start of its world and the step orders that it names. -/
def worldOf (request : Value) : IO (Syntax.Structure × Scenario × Sim.World) := do
  let spec : Syntax.Structure ← IO.ofExcept (FromValue.fromValue (← IO.ofExcept (field request "structure")))
  let sc : Scenario ← IO.ofExcept (FromValue.fromValue (← IO.ofExcept (field request "scenario")))
  let stepOrders ← match request.field? "stepOrders" with
    | none => pure []
    | some v => IO.ofExcept do
      (← asList v).mapM fun e => do
        pure ((← FromValue.fromValue (← field e "origin") : Scenario.Origin), ← stringField e "service",
          (← FromValue.fromValue (← field e "order") : List StepName))
  let start ← IO.ofExcept (Sim.World.start spec sc)
  pure (spec, sc, { start with stepOrders })

/--
The reply to request `simulate`, which takes a structure, a scenario, and step orders, and returns each running
service's trace lines, violations (its own, then those Instrument collected, then its halt), and candidates, and the
simulation's reports and halting report. With `walk` true, the lines take place as explore runs them (Sim.walk), and
each running service that did not halt also returns what it enables next.
-/
def simulateRequest (stdin stdout : IO.FS.Stream) (request : Value) : IO Value := do
  let (spec, sc, start) ← worldOf request
  let walking := request.field? "walk" == some (.bool true)
  let fsOf ← instrumentedOf stdin stdout start
  let ran : ActingIO Sim.World :=
    if walking then Sim.walk spec fsOf start sc else Sim.simulate spec fsOf start sc
  let (w, acting) ← ran.run {}
  let (participants, _) ← (w.states.mapM fun ((service, s) : String × State) => do
    let c := acting.collect service
    let enabled ← match walking, s.halted, w.services.lookup service with
      | true, none, some st => do
        match ← Observe.enabled st (fsOf service) s with
        | .ok e => pure [("enabled", Tazuna.Json.Enabled.toValue e)]
        | .error f => pure [("enabled", .obj [("fault", ToValue.toValue (Finding.fault f).toViolation)])]
      | _, _, _ => pure []
    let fields : List (String × Value) := [("service", .str service),
      ("lines", .arr (s.lines.toList.map fun l => lineValue l [] [])),
      ("violations", .arr ((reportedViolations s c none).map ToValue.toValue)),
      ("candidates", .arr ((candidates s c none).map fun ((i, j) : Nat × Nat) => .arr [.num i, .num j]))]
    pure (Value.obj (fields ++ enabled))).run acting
  pure (.obj [("type", .str "simulated"),
    ("participants", .arr participants),
    ("reports", .arr (w.reports.map Sim.Report.toValue)),
    ("halted", (w.halted.map Sim.Report.toValue).getD .null)])

/-- The JSON of a search, as TS writes it. -/
def searchValue (r : Searched) : Value :=
  .obj [("origin", ToValue.toValue r.origin), ("service", .str r.service),
    ("tried", .arr (r.search.tried.map fun t => .obj (("order", ToValue.toValue t.order) :: match t.verdict with
      | .refused => [("refused", .bool true)]
      | .decided found => [("found", (found.map (·.toValue)).getD .null)]))),
    ("found", .arr (r.search.found.map (·.toValue)))]

/--
The reply to request `stepOrderChanges`, which takes a structure and a scenario and returns stepOrderChanges of the
scenario walked, from its begin: every search, with each step order it ran and its verdict, and what it found.
-/
def stepOrderChangesRequest (stdin stdout : IO.FS.Stream) (request : Value) : IO Value := do
  let (spec, sc, _) ← worldOf request
  let walkWith (sc : Scenario) (stepOrders : List (Scenario.Origin × String × List StepName)) : IO Walk := do
    let start ← IO.ofExcept (Sim.World.start spec sc)
    let start := { start with stepOrders }
    let ran : ActingIO Sim.World := Sim.walk spec (← instrumentedOf stdin stdout start) start sc
    let (w, acting) ← ran.run {}
    pure { world := w, collect := acting.collect }
  let reads ← IO.mkRef {}
  let searched ← stepOrderChanges (fun service => compareOf spec service (askComparable stdin stdout reads))
    walkWith sc (← walkWith sc []) 0
  pure (.obj [("type", .str "stepOrderChanges"), ("searched", .arr (searched.map searchValue))])

/--
The reply to request `assignmentChanges`, which takes a structure and a scenario and returns assignmentSearch of the
scenario's handle groups: each assignment it ran, with the violation it found, and what it reports.
-/
def assignmentChangesRequest (stdin stdout : IO.FS.Stream) (request : Value) : IO Value := do
  let (spec, sc, start) ← worldOf request
  let walkWith (assignments : List (Scenario.Fact × List Nat)) : IO Walk := do
    let start := { start with assignments }
    let ran : ActingIO Sim.World := Sim.walk spec (← instrumentedOf stdin stdout start) start sc
    let (w, acting) ← ran.run {}
    pure { world := w, collect := acting.collect }
  let base ← walkWith []
  let fsOf ← instrumentedOf stdin stdout start
  let sizeOf (g : HandleGroup) : IO Nat := do pure (← (groupSize fsOf base.world g).run {}).1
  let reads ← IO.mkRef {}
  let search ← assignmentSearch (fun service => compareOf spec service (askComparable stdin stdout reads)) sizeOf
    walkWith base (handleGroups sc)
  pure (.obj [("type", .str "assignmentChanges"),
    ("tried", .arr (search.tried.map fun t => .obj [("assigned", ToValue.toValue t.assigned),
      ("found", (t.found.map (·.toValue)).getD .null)])),
    ("found", .arr (search.found.map (·.toValue)))])

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let reply ← try
      let request ← IO.ofExcept (parse line)
      match request.field? "type" with
      | some (.str "check") => IO.ofExcept (check request)
      | some (.str "verify") => verify stdin stdout request
      | some (.str "checkExternal") => IO.ofExcept (checkExternal request)
      | some (.str "pair") => IO.ofExcept (pair request)
      | some (.str "pairSnapshots") => IO.ofExcept (pairSnapshots request)
      | some (.str "compareSnapshot") => IO.ofExcept (compareSnapshot request)
      | some (.str "afters") => IO.ofExcept (afters request)
      | some (.str "decodeLines") => IO.ofExcept (decodeLines request)
      | some (.str "simulate") => simulateRequest stdin stdout request
      | some (.str "stepOrderChanges") => stepOrderChangesRequest stdin stdout request
      | some (.str "assignmentChanges") => assignmentChangesRequest stdin stdout request
      | some (.str "names") =>
        pure (.obj [("type", .str "names"),
          ("byCaller", .obj (rejectionKinds.filterMap fun k =>
            match ToValue.toValue k with
            | .str s => some (s, .bool (RejectionKind.byCaller k))
            | _ => none)),
          ("limits", .obj (limits.map fun l => (l.name, .num (.fromInt l.max)))),
          ("stepOrderLimit", .num stepOrderLimit), ("assignmentLimit", .num assignmentLimit)])
      | _ => throw (IO.userError s!"unknown request {line.trimAscii}")
    catch e => pure (.obj [("type", .str "error"), ("message", .str (toString e))])
  send stdout reply
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
