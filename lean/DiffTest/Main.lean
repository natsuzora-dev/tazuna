import Std.Data.HashMap
import DiffTest.Json
import DiffTest.Names
import Tazuna.Observe.ChoiceDependent
import Tazuna.Semantics.System.Peer

/-!
tazuna-lean exchanges one JSON value per line with TS over stdio (precedents: leanprover-community/repl, the Lean LSP).

Semantics asks TS for a spec function's value whenever it needs one. While computing it, TS sends `read` for each record
a TS function reads; Lean serves the value from its own records and remembers the parts read, which Instrument records
in the accesses of steps. Within one run tree, Lean reuses the reply that TS gave to the same question when the values
that Lean serves for the reads that TS made then are the same now: a TS reply depends only on the question and those
values.
-/

open Tazuna Tazuna.Data Tazuna.Semantics Tazuna.Observe Tazuna.Json

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
def ask (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool) (records : Records)
    (request : Value) (before : Records := []) : IO Value := do
  let request := if reversed then request.merge (.obj [("reversed", .bool true)]) else request
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

def keyCounts (keys : List (String × Nat)) : Value := .obj (keys.map fun (e, n) => (e, .num n))

def schemaRequest (type : String) (schema : Schema) (value : Value) : Value :=
  .obj [("type", .str type), ("schema", Schema.toValue schema), ("value", value)]

/--
The reply that `read` decodes, or, when the reply has `issue`, the issue that tells why the question has no answer.
-/
def issueOr {α : Type} (reply : Value) (read : Value → Except String α) : Except String (Except Issue α) :=
  match reply.field? "issue" with
  | some v => return .error (← Issue.decode v)
  | none => return .ok (← read reply)

/-- The functions that ask TS, which answers with every Bag in reverse order when `reversed` is set. -/
def functions (stdin stdout : IO.FS.Stream) (reads : Reads) (memo : Memo) (reversed : Bool) : Functions IO where
  parse schema value := do
    let reply ← ask stdin stdout reads memo reversed [] (schemaRequest "parse" schema value)
    IO.ofExcept (issueOr reply fun r => pure (optional r "value"))
  canonical schema value := do
    let reply ← ask stdin stdout reads memo reversed [] (schemaRequest "canonical" schema value)
    IO.ofExcept (issueOr reply (field · "value"))
  normalize schema value := do
    let reply ← ask stdin stdout reads memo reversed [] (schemaRequest "normalize" schema value)
    IO.ofExcept (issueOr reply fun r => pure (optional r "value"))
  binding name binding input records now := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "binding"), ("command", .str name), ("binding", .str binding), ("input", input),
             ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "bound"))
  requirement name condition input records now := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "requirement"), ("command", .str name), ("condition", .str condition), ("input", input),
             ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "holds"))
  inputRequirement name condition input := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "inputRequirement"), ("target", .str name), ("condition", .str condition), ("input", input)])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "holds"))
  ensures name input before after now := do
    let reply ← ask stdin stdout reads memo reversed after
      (.obj [("type", .str "ensures"), ("command", .str name), ("input", input), ("now", .str (renderTime now))])
      before
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  queryEnsures name input output records := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "queryEnsures"), ("query", .str name), ("input", input), ("output", output)])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  resultEnsures target input output events := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "resultEnsures"), ("target", .str target), ("input", input), ("output", output.getD .null),
             ("events", .arr (events.map fun e => .obj [("event", .str e.event), ("payload", e.payload)]))])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  invariant entity row := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "invariant"), ("entity", .str entity), ("record", row)])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  serviceInvariant records := do
    let reply ← ask stdin stdout reads memo reversed records (.obj [("type", .str "serviceInvariant")])
    match ← IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue) with
    | .ok failed => pure (.ok failed)
    | .error (.thrown schema) => pure (.error schema)
    | .error issue => throw (IO.userError s!"serviceInvariant answered {repr issue}, which is no throw")
  chartInvariant scope records := do
    let reply ← ask stdin stdout reads memo reversed records (.obj [("type", .str "chartInvariant"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun r => (optional r "failed").mapM FromValue.fromValue)
  decide name input records now := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "decide"), ("command", .str name), ("input", input), ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply fun r => do
      (← asList (← field r "groups")).mapM fun g => do (← asList g).mapM Emit.decode)
  resolve name input records now := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "resolve"), ("query", .str name), ("input", input), ("now", .str (renderTime now))])
    IO.ofExcept (issueOr reply (field · "output"))
  react name payload records now keys := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "react"), ("automation", .str name), ("payload", payload), ("now", .str (renderTime now)),
             ("keys", keyCounts keys)])
    IO.ofExcept (issueOr reply fun r => do
      pure (optional r "input", ← (← asList (← field r "created")).mapM FromValue.fromValue))
  comparable name answer := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "comparable"), ("query", .str name), ("answer", ToValue.toValue answer)])
    IO.ofExcept (issueOr reply (field · "value"))
  initialContext name input := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "initialContext"), ("machine", .str name), ("input", input)])
    IO.ofExcept (issueOr reply (field · "context"))
  guard scope records t extra := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "guard"), ("scope", Scope.toValue scope), ("transition", Transition.toValue t), ("extra", Extra.toValue extra)])
    IO.ofExcept (issueOr reply fun r => do FromValue.fromValue (← field r "passes"))
  assign scope records a extra keys := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "assign"), ("scope", Scope.toValue scope), ("at", Assignment.toValue a), ("extra", Extra.toValue extra),
             ("keys", keyCounts keys)])
    IO.ofExcept (issueOr reply fun r => do
      pure (← field r "context", optional r "copy", ← (← asList (← field r "created")).mapM FromValue.fromValue))
  input scope records a keys := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "input"), ("scope", Scope.toValue scope), ("activity", Activity.toValue a), ("keys", keyCounts keys)])
    IO.ofExcept (issueOr reply fun r => do
      pure (← field r "input", ← (← asList (← field r "created")).mapM FromValue.fromValue))
  holds scope records := do
    let reply ← ask stdin stdout reads memo reversed records (.obj [("type", .str "holds"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun _ => pure ())
  deadlines machine state := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "deadlines"), ("machine", .str machine), ("state", .str state)])
    IO.ofExcept do
      (← asList (← field reply "deadlines")).mapM fun d => do
        let deadline ← match optional d "delay" with
          | some (.num ⟨n, 0⟩) => pure (DeadlineTime.delay n)
          | none => pure DeadlineTime.atExpression
          | some other => throw s!"expected a whole number of milliseconds, got {render other}"
        pure (← stringField d "name", deadline)
  deadlineAt scope records name := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "deadlineAt"), ("scope", Scope.toValue scope), ("name", .str name)])
    IO.ofExcept (issueOr reply fun r => do parseTime (← stringField r "time"))
  offers scope records control := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "offers"), ("scope", Scope.toValue scope), ("control", .str control)])
    IO.ofExcept (issueOr reply fun r => do asList (← field r "payloads"))
  showInput scope records a := do
    let reply ← ask stdin stdout reads memo reversed records
      (.obj [("type", .str "showInput"), ("scope", Scope.toValue scope), ("activity", Activity.toValue a)])
    IO.ofExcept (issueOr reply (field · "input"))
  items scope records := do
    let reply ← ask stdin stdout reads memo reversed records (.obj [("type", .str "items"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun r => do
      (← asList (← field r "keys")).mapM fun k => do pure (← field k "key", ← stringField k "encodedKey"))
  copyContext chart map := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "copyContext"), ("machine", .str chart), ("map", .str map)])
    IO.ofExcept (field reply "context")
  singleRecord entity := do
    let reply ← ask stdin stdout reads memo reversed [] (.obj [("type", .str "singleRecord"), ("entity", .str entity)])
    IO.ofExcept (field reply "record")
  copyKey chart map payload := do
    let reply ← ask stdin stdout reads memo reversed []
      (.obj [("type", .str "copyKey"), ("machine", .str chart), ("map", .str map), ("payload", payload)])
    IO.ofExcept (issueOr reply fun r => do
      match r.field? "key" with
      | none => pure none
      | some .null => pure (some none)
      | some k => pure (some (some (← FromValue.fromValue k))))
  close scope records := do
    let reply ← ask stdin stdout reads memo reversed records (.obj [("type", .str "close"), ("scope", Scope.toValue scope)])
    IO.ofExcept (issueOr reply fun r => do
      pure (← field r "output", ← (optional r "failed").mapM FromValue.fromValue))

/-- The semantic state with what Instrument collected and the enabled log. -/
abbrev Checkpoint := State × Collect × EnabledLog

abbrev EnabledCollectIO := StateT EnabledLog (StateT Collect IO)

/--
The saved states (`Checkpoint`) of the paths of the latest `run`, which `extend` continues, indexed by handle, and the
replies that TS gave along them.
-/
structure Tree where
  st : Service
  checkpoints : Array Checkpoint
  memo : Memo

def stepperOf (stdin stdout : IO.FS.Stream) (st : Service) (memo : Memo) : IO (Stepper EnabledCollectIO) := do
  let reads ← IO.mkRef {}
  let fs := functions stdin stdout reads memo false
  let ifs : InstrumentFunctions IO := {
    lastReads := do pure (← reads.get).parts
    lastAccess := do IO.ofExcept (Access.decode (((← reads.get).reply.field? "access").getD (.obj [])))
    lastEnumerated := do pure ((← reads.get).reply.field? "enumerated" == some (.bool true))
    reversed := functions stdin stdout reads memo true }
  pure (enabledStep st (step st (instrument st fs ifs)) (instrument st fs ifs))

def checkpointOf (stepper : Stepper EnabledCollectIO) (inputs : List Step) : IO Checkpoint := do
  let ((s, log), collected) ← ((runFrom stepper {} inputs).run {}).run {}
  pure (s, collected, log)

def stepOnce (stepper : Stepper EnabledCollectIO) : Checkpoint → Step → IO Checkpoint
  | (s, collected, log), input => do
    let ((s, log), collected) ← ((stepper s input).run log).run collected
    pure (s, collected, log)

def resultValue (handle : Nat) : Checkpoint → Value
  | (s, collected, log) =>
    .obj [("type", .str "result"), ("handle", .num handle),
      ("lines", .arr ((trace s collected.causes).map fun (line, after, created) => lineValue line after created)),
      ("violations", .arr ((reportedViolations s collected log.stopped).map ToValue.toValue)),
      ("candidates", .arr ((candidates s collected log.stopped).map fun (i, j) => .arr [.num i, .num j])),
      ("enabled", .arr (log.enabled.map Enabled.toValue))]

/--
The reply to request `run`, which takes a structure, a service, and steps, and returns the trace lines, the
violations, the pairs of steps whose other order test runs, the `Enabled` value of each step, and the path's handle.
It drops the handles and TS replies of earlier runs.
-/
def run (stdin stdout : IO.FS.Stream) (tree : IO.Ref (Option Tree)) (request : Value) : IO Value := do
  let spec : Syntax.Structure ← IO.ofExcept (FromValue.fromValue (← IO.ofExcept (field request "structure")))
  let service ← IO.ofExcept (stringField request "service")
  let st ← IO.ofExcept (spec.service service)
  let inputs : List Step ← IO.ofExcept do FromValue.fromValue (← field request "steps")
  let memo ← IO.mkRef {}
  let checkpoint ← checkpointOf (← stepperOf stdin stdout st memo) inputs
  tree.set (some { st, checkpoints := #[checkpoint], memo })
  pure (resultValue 0 checkpoint)

/--
The reply to request `extend`, which takes a handle and one step, and returns the result of the handle's path
followed by the step, and its handle. A halted path takes no more inputs, as in `runFrom`, so it returns the halted
path's result and handle unchanged.
-/
def extend (stdin stdout : IO.FS.Stream) (tree : IO.Ref (Option Tree)) (request : Value) : IO Value := do
  let some t ← tree.get | throw (IO.userError "extend before run")
  let handle : Nat ← IO.ofExcept (do FromValue.fromValue (← field request "handle"))
  let some checkpoint := t.checkpoints[handle]? | throw (IO.userError s!"no handle {handle}")
  let (s, _, log) := checkpoint
  if s.halted.isSome || log.stopped.isSome then return resultValue handle checkpoint
  let input : Step ← IO.ofExcept do FromValue.fromValue (← field request "step")
  let next ← stepOnce (← stepperOf stdin stdout t.st t.memo) checkpoint input
  tree.set (some { t with checkpoints := t.checkpoints.push next })
  pure (resultValue t.checkpoints.size next)

/-- The comparable value that verify reads, which TS computes. -/
def askComparable (stdin stdout : IO.FS.Stream) (reads : Reads) (d : Syntax.Definition) (part : Verify.Part)
    (value : Value) : IO Verify.CValue := do
  let { reply, .. } ← exchange stdin stdout reads [] []
    (.obj ([("type", .str "comparableValue"),
      ("definition", .obj [("kind", .str d.kind), ("service", .str d.service), ("name", .str d.name)])] ++
      part.toValue ++ [("value", value)]))
  IO.ofExcept (CValue.decode (← IO.ofExcept (field reply "value")))

/-- The index of the first step where the two lists differ. -/
def firstDifference (xs ys : List Step) : Option Nat :=
  (List.range (max xs.length ys.length)).find? fun i =>
    (xs[i]?.map fun x => (ToValue.toValue x).canonical) != (ys[i]?.map fun y => (ToValue.toValue y).canonical)

/-- The request id that an answer step chooses, with the trace name of the answer's sender. -/
def chosen (step : Step) : Except String (String × String) :=
  match step.body with
  | .answer sender _ _ (some (.search to)) => pure (to, sender)
  | _ => throw "expected an answer step that chooses a request"

/-- The trace name of the command or query that a step requests. -/
def requested (step : Step) : Except String String :=
  match step.body with
  | .command _ name _ | .query _ name _ => pure name
  | _ => throw "expected a command or query step"

/-- The saved state after the steps, run one at a time, and the number of lines after each prefix. -/
def runCounting (stepper : Stepper EnabledCollectIO) (steps : List Step) : IO (Checkpoint × List Nat) := do
  let start ← checkpointOf stepper []
  steps.foldlM (init := (start, [start.1.lines.size])) fun (checkpoint, counts) step => do
    let next ← stepOnce stepper checkpoint step
    pure (next, counts ++ [next.1.lines.size])

/-- The line of the input that arrives after `count` lines: the first `in` line from there. -/
def inputLineAfter (lines : List TraceLine) (count : Nat) : Option Nat :=
  ((lines.zipIdx.drop count).find? fun (l, _) => l.body.dir == .in).map (·.2)

/--
The first violation, by line, that verify finds in `actual` with `expected` as the snapshot, as TS `compareTrace`
returns.
-/
def compareOf (spec : Syntax.Structure) (service : String)
    (ask : Syntax.Definition → Verify.Part → Value → IO Verify.CValue) : Compare IO := fun expected actual => do
  let compared ← Verify.verifyLines spec service ask (expected.map some) (actual.map .line)
  let numbered := compared.findings.map fun f =>
    let v : Violation := match f with
      | .mismatch m => { kind := m.kind, definition := m.definition, data := m.data }
      | .uncomparable u => { kind := u.kind, definition := u.definition, data := u.data }
    (f.line, v)
  pure (match (numbered.mergeSort fun a b => decide (a.1 ≤ b.1)).head? with
    | some (_, v) => .error v
    | none => .ok compared.bindings)

/--
The reply to request `choice`, which takes a structure, a service, the kind of choice, and the steps of the two runs in
the order that the relation takes them, and returns the ChoiceDependent violation or null. The choice is at the first
step where the runs differ: the deadlines at the first place where the orders of that step differ, the requests that two
answers choose, the last two entries of the second run's `stepOrder` at that step, which take the second step of the
pair and then the first, or, for two swapped inputs, that step and the next of the first run. TS computes the functions
of both runs and the values that verify compares.
-/
def choice (stdin stdout : IO.FS.Stream) (request : Value) : IO Value := do
  let spec : Syntax.Structure ← IO.ofExcept (FromValue.fromValue (← IO.ofExcept (field request "structure")))
  let service ← IO.ofExcept (stringField request "service")
  let st ← IO.ofExcept (spec.service service)
  let stepsOf (key : String) : IO (List Step) := IO.ofExcept do FromValue.fromValue (← field request key)
  let (first, second) := (← stepsOf "first", ← stepsOf "second")
  let some k := firstDifference first second | throw (IO.userError "the two runs have the same steps")
  let stepper ← stepperOf stdin stdout st (← IO.mkRef {})
  let runOf (steps : List Step) : IO (Checkpoint × List TraceLine × List Nat) := do
    let (checkpoint, counts) ← runCounting stepper steps
    let (s, collected, _) := checkpoint
    pure (checkpoint, (trace s collected.causes).map (fun (line, after, created) => traceLineOf line after created), counts)
  let (a, b) := (← runOf first, ← runOf second)
  let outcome (run : Checkpoint × List TraceLine × List Nat) (swapped : Option (List Nat)) : Observe.Outcome :=
    let ((s, _, log), lines, _) := run
    Outcome.of st (s.halted <|> log.stopped) lines s.records swapped
  -- Two swapped inputs: each run lists the line of the first run's input k first.
  let swapped (run : Checkpoint × List TraceLine × List Nat) (reversed : Bool) : List Nat :=
    let (_, lines, counts) := run
    let positions := [k, k + 1].filterMap fun i => (counts[i]?).bind (inputLineAfter lines)
    if reversed then positions.reverse else positions
  let compare := compareOf spec service (askComparable stdin stdout (← IO.mkRef {}))
  let step (steps : List Step) (i : Nat) : IO Step := match steps[i]? with
    | some s => pure s
    | none => throw (IO.userError s!"no step {i}")
  let found ← match ← IO.ofExcept (stringField request "kind") with
    | "deadlineOrder" =>
      let (orderA, orderB) := ((← step first k).deadlineOrder.getD [], (← step second k).deadlineOrder.getD [])
      let some (y, j) := orderB.zipIdx.find? (fun (d, i) => orderA[i]? != some d)
        | throw (IO.userError "the orders of the step do not differ")
      let some x := orderA[j]? | throw (IO.userError "the first order ends early")
      let ((s, _, _), _, _) := a
      let chart (d : DeadlineId) := (s.machine? d.instance).map (st.ref ·.chart.name)
      deadlineOrder compare chart x y (outcome a none) (outcome b none)
    | "answerChoice" =>
      let (request, sender) ← IO.ofExcept (chosen (← step first k))
      answerChoice compare (st.refOf sender) request (← IO.ofExcept (chosen (← step second k))).1
        (outcome a none) (outcome b none)
    | "answerOrder" =>
      let (x, xSender) ← IO.ofExcept (chosen (← step first k))
      let (y, ySender) ← IO.ofExcept (chosen (← step first (k + 1)))
      answerOrder compare x y (st.refOf xSender) (st.refOf ySender)
        (outcome a (some (swapped a false))) (outcome b (some (swapped b true)))
    | "requestOrder" =>
      requestOrder compare (st.refOf (← IO.ofExcept (requested (← step first k))))
        (st.refOf (← IO.ofExcept (requested (← step first (k + 1))))) (outcome a (some (swapped a false)))
        (outcome b (some (swapped b true)))
    | "stepOrder" =>
      let entries := (← step second k).stepOrder.getD []
      let [y, x] := entries.drop (entries.length - 2) | throw (IO.userError "the stepOrder has no two entries")
      stepOrder compare x y (outcome a none) (outcome b none)
    | other => throw (IO.userError s!"unknown choice {other}")
  pure (.obj [("type", .str "decided"), ("found", (found.map (·.toValue)).getD .null)])

/-- The reply to request `check`, which takes a structure and returns the Illegal violations. -/
def check (request : Value) : Except String Value := do
  let s : Syntax.Structure ← FromValue.fromValue (← field request "structure")
  pure (.obj [("type", .str "checked"), ("findings", .arr ((Validation.check s).map Validation.Illegal.toValue))])

/--
The reply to request `verify`, which takes a structure, a service, the snapshot lines (null for a blank line), and the
implementation lines (as `FileLine.decode` reads them), and returns the comparison violations. TS computes
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
  pure (.obj [("type", .str "verified"), ("findings", .arr (compared.findings.map Verify.Finding.toValue))])

/--
The reply to request `afters`, which takes the snapshot lines (null for a blank line) and returns the `unknownAfter`
violations of reading the snapshot.
-/
def afters (request : Value) : Except String Value := do
  let snapshot ← (← asList (← field request "snapshot")).mapM fun l =>
    if l == .null then pure none else some <$> FromValue.fromValue l
  let lines := snapshot.map (·.map fun l : TraceLine => ({ l with value := none } : Verify.Line))
  pure (.obj [("type", .str "afters"), ("findings", .arr ((Verify.unknownAfters lines).map (·.toValue)))])

/--
The reply to request `peer`, which takes the scenario's service, the peer, the steps of the given state, the elsewhere
inputs with the line counts before them, the lines of the scenario's run and of the peer's run, the halt of the peer's
run, and the forms of `normal` that TS computed as `[name, value, form]`, and returns peerInputs and peerFindings. A
value without a form stays as it is.
-/
def peer (request : Value) : Except String Value := do
  let service ← stringField request "service"
  let peer ← stringField request "peer"
  let state : List Step ← FromValue.fromValue (← field request "state")
  let elsewhere ← (← asList (← field request "elsewhere")).mapM fun
    | .arr [n, s] => do pure ((← FromValue.fromValue n : Nat), (← FromValue.fromValue s : Step))
    | _ => throw "expected [count, step]"
  let lines : List TraceLine ← FromValue.fromValue (← field request "lines")
  let peerLines : List TraceLine ← FromValue.fromValue (← field request "peerLines")
  let halted ← match ← field request "halted" with
    | .null => pure none
    | .arr [o, .str kind] => pure (some ((← FromValue.fromValue o : Origin), kind))
    | _ => throw "expected null or [origin, kind]"
  let normals ← (← asList (← field request "normals")).mapM fun
    | .arr [.str name, v, form] => pure (name, v, form)
    | _ => throw "expected [name, value, form]"
  let normal (name : String) (v : Value) : Value :=
    ((normals.find? fun (n, w, _) => n == name && w.canonical == v.canonical).map (·.2.2)).getD v
  pure (.obj [("type", .str "peer"),
    ("inputs", .arr ((peerInputs service peer state elsewhere lines).map fun (s, o) =>
      .obj [("step", ToValue.toValue s), ("origin", ToValue.toValue o)])),
    ("findings", .arr ((peerFindings normal service peer lines peerLines halted).map fun (o, f) =>
      .obj [("origin", ToValue.toValue o), ("violation", f.toValue)]))])

partial def loop (stdin stdout : IO.FS.Stream) (tree : IO.Ref (Option Tree)) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let reply ← try
      let request ← IO.ofExcept (parse line)
      match request.field? "type" with
      | some (.str "run") => run stdin stdout tree request
      | some (.str "extend") => extend stdin stdout tree request
      | some (.str "check") => IO.ofExcept (check request)
      | some (.str "verify") => verify stdin stdout request
      | some (.str "choice") => choice stdin stdout request
      | some (.str "checkExternal") => IO.ofExcept (checkExternal request)
      | some (.str "pair") => IO.ofExcept (pair request)
      | some (.str "pairSnapshots") => IO.ofExcept (pairSnapshots request)
      | some (.str "compareSnapshot") => IO.ofExcept (compareSnapshot request)
      | some (.str "afters") => IO.ofExcept (afters request)
      | some (.str "decodeLines") => IO.ofExcept (decodeLines request)
      | some (.str "peer") => IO.ofExcept (peer request)
      | some (.str "names") =>
        pure (.obj [("type", .str "names"),
          ("byCaller", .obj (rejectionKinds.filterMap fun k =>
            match ToValue.toValue k with
            | .str s => some (s, .bool (RejectionKind.byCaller k))
            | _ => none)),
          ("limits", .obj (limits.map fun l => (l.name, .num (.fromInt l.max))))])
      | _ => throw (IO.userError s!"unknown request {line.trimAscii}")
    catch e => pure (.obj [("type", .str "error"), ("message", .str (toString e))])
  send stdout reply
  loop stdin stdout tree

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout) (← IO.mkRef none)
