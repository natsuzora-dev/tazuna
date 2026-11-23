import Engine.Run
import Tazuna.Verify.External
import Tazuna.Explore.Coverage

/-!
What the CLI's verify command asks of the engine: the replay of an implementation's log, whose `in` lines the spec
service takes and whose `out` lines are compared with the spec's, and an external service's trace checked against its
contract, with the values read by their schemas and the contract's conditions evaluated as IR.
-/

namespace Tazuna.Engine

open Tazuna.Data Tazuna.Service Tazuna.Verify Tazuna.Explore

/-- A finding as a report writes it: a violation with its line, or an `after`, which only test compares. -/
instance : ToValue Verify.Finding := ⟨fun
  | .mismatch m => ToValue.toValue m
  | .uncomparable u => ToValue.toValue u
  | .after line subject snapshot trace =>
    .obj [("after", .obj [("line", ToValue.toValue line), ("subject", ToValue.toValue subject),
      ("snapshot", ToValue.toValue snapshot), ("trace", ToValue.toValue trace)])]⟩

/-- Whether a finding is a violation of verify, which compares no `after`. -/
def _root_.Tazuna.Verify.Finding.isViolation : Verify.Finding → Bool
  | .after .. => false
  | _ => true

/-- The records that an implementation starts from, which a log states on its first line. -/
structure Start where
  time : Time
  records : List Scenario.GivenRecord
  /-- The user that operates the service's screens, or none when no user signed in. -/
  user : Option Caller := none

derive_wire Start skip_serializing_none

/-- A log's first line as it stands, with its line number, when it is a start line. -/
structure StartLine where
  line : Nat
  value : Value

derive_wire StartLine

/--
A log of an implementation of the spec service `service`: its start line, if any, and its lines, the start line blank
among them.
-/
structure Log where
  service : String
  start : Option StartLine
  lines : List (FileLine TraceLine)

derive_wire Log skip_serializing_none

/--
What verify finds of one log: the violations of comparing its lines with the spec's (Finding), those that the spec
reports while it takes the log's inputs, and the pairs of each binding that the comparison ends with.
-/
structure Replayed where
  findings : List Verify.Finding
  violations : List Violation
  bindings : List (List (String × String))

derive_wire Replayed serialize_only

/-- A replay: the spec service's run, which collects what its instrumented functions find and reach. -/
abbrev ReplayM := StateT Collect IO

/-- The spec value that `b` binds to the implementation value `t`, or `t` itself. -/
def inverse (b : Bindings) (t : String) : String := ((b.find? (·.2 == t)).map (·.1)).getD t

/-- The id of the service's line whose id reads `text`: the service's own request that an answer or resultOf names. -/
def lineIdOf (s : State) (text : String) : LineId :=
  ((s.lines.toList.find? (·.id.text == text)).map (·.id)).getD (.own text)

/-- The value with each key reference renamed by `f`. -/
partial def renameRefs (f : String → String) : CValue → CValue
  | .ref e v => .ref e (f v)
  | .leaf v => .leaf v
  | .arr xs => .arr (xs.map (renameRefs f))
  | .bag xs => .bag (xs.map (renameRefs f))
  | .runs rs => .runs (rs.map (renameRefs f))
  | .obj fs => .obj (fs.map fun (k, x) => (k, renameRefs f x))

/-- The caller with an entity record's key renamed by `f`, as renameRefs renames a key reference. -/
def renameCaller (f : String → String) : Caller → Caller
  | .entity e (.str k) => .entity e (.str (f k))
  | .entity e k => .entity e k
  | .service s => .service s

/-- The spec service's trace lines so far, as a snapshot holds them. -/
def specLines (service : String) (s : State) : List (Option TraceLine) :=
  (Sim.trace s).map fun (l, after, created) => some (Sim.traceLineOf service l after created)

/--
The state after the clock moves to `time` with no line of its own: the deadlines due by then fire, and the subscription
answers that the new time changes are sent.
-/
def advance (st : Service) (fs : Functions ReplayM) (time : Time) (s : State) : ReplayM State := do
  let s ← fireDue st fs time Limit.dueDeadlines.max none s
  let s := { s with now := max s.now time }
  if s.halted.isSome then pure s else publish st fs s

/--
The state after the spec service takes the log's `in` line `l`, whose values verify reads as `read`: the clock moves to
the line's time first, and the values that the implementation stands for in its own way (its keys, its request ids)
are the spec's that the binding `b` gives them, as drive substitutes them the other way.
-/
def takeIn (spec : Spec.Structure) (st : Service) (fs : Functions ReplayM) (b : Bindings) (s : State) (l : TraceLine)
    (read : Verify.Line) : ReplayM State := do
  let value := read.value.map fun v => (renameRefs (inverse b) v).flatten
  let ref (name : String) (kinds : List String) : Spec.Ref :=
    ((spec.named st.service (some name) kinds).map (·.ref)).getD { service := st.service, name }
  let s ← match l.body with
    | .time .. => pure s
    | _ => if s.now < l.time then advance st fs l.time s else pure s
  match l.body with
  | .command _ id name input caller =>
    send st fs s (ref name ["command"]) (some (.own id)) (value.getD input) (renameCaller (inverse b) caller)
  | .query _ id name input caller =>
    call st fs s (ref name ["query"]) (some (.own id)) (value.getD input) (renameCaller (inverse b) caller)
  | .subscribe _ id name input caller =>
    subscribe st fs s (ref name ["query"]) (some (.own id)) (value.getD input) (renameCaller (inverse b) caller)
  | .answer _ id to a =>
    let a := match a, value with
      | .accepted (some _), some o => .accepted (some o)
      | .fulfilled _, some o => .fulfilled o
      | a, _ => a
    answerIn st fs s (.own id) (lineIdOf s (inverse b to)) a
  | .unsubscribe _ _ to => endSubscription st fs s (.own to)
  | .event _ id name payload resultOf =>
    receive st fs s (ref name ["event"]) (.own id) (value.getD payload) (resultOf.map (lineIdOf s ∘ inverse b))
  | .operation _ _ name nth payload =>
    let (screen, control) := operationParts name
    let r := ref screen ["screen"]
    match (s.stack.filter (·.chart == r.name))[nth.getD 0]? with
    | some resource => operate st fs s resource control ((value <|> payload).getD (.obj []))
    | none => pure (s.report (.invalidInput (.unopenedScreen r control)))
  | .time .. => Sim.fireTo l.time st fs s
  | .restart .. => restart st fs s

/--
The replay of `log`: the spec service starts at the log's start from its records, or from none at the time of the
log's first line, and takes the log's `in` lines one by one, each under the first binding that comparing the lines so
far keeps; then its lines are compared with the log's (Verify.verifyLines). The replay stops at the first `in` line that
the spec does not take: after the spec halts, once the comparison so far finds the log uncomparable, or when the spec
rejects the line as an input that no sender could give. No line from there on compares.
-/
def replay (spec : Spec.Structure) (log : Log) : ReplayM Replayed := do
  let ask (d : Spec.Definition) (part : Verify.Part) (v : Value) : ReplayM CValue := pure (Verify.readValueOf spec d part v)
  let start ← match log.start with
    | none => pure (some none)
    | some s => pure ((FromValue.fromValue s.value : Except String Start).toOption.map some)
  let some start := start
    | return { findings := [.uncomparable (.lineSchema ((log.start.map (·.line)).getD 1))], violations := [],
               bindings := [] }
  let st ← Service.ofStructure spec log.service
  let last ← IO.mkRef {}
  let fs := instrument st (Ir.functionsOf st last) (Ir.instrumentOf last)
  let (lines, _) := comparedLines .out log.lines
  let time := match start with
    | some s => s.time
    | none => ((lines.findSome? id).map (·.time : TraceLine → Time)).getD 0
  let records := ((start.map (·.records)).getD []).mergeSort Sim.recordBefore
  let (rows, invalid) ← Sim.givenRows st fs (fun _ => none) log.service records
  let broken ← if invalid.isEmpty then Sim.givenInvariants fs log.service rows time else pure []
  let user := start.bind (·.user)
  let mut s ← begin st fs { now := time, service := log.service, records := rows, user }
  let inputs (s : State) := s.lines.toList.countP (·.dir == .in)
  let mut taken := log.lines.length
  -- A resend and the answer to it stand for the request that they repeat (withoutResends), so the spec takes neither.
  for (l, k) in (withoutResends lines).zipIdx do
    let some l := l | continue
    if l.body.dir == .out then continue
    if s.halted.isSome || !(invalid ++ broken).isEmpty then
      taken := k
      break
    let compared ← Verify.verifyLines spec log.service ask (specLines log.service s) (log.lines.take k) id
    -- Whether a route is ambiguous depends on the spec's later lines too, so only the final comparison tells.
    if compared.findings.any fun f => f matches .uncomparable _ && !(f matches .uncomparable (.ambiguous ..)) then
      taken := k
      break
    let b := (compared.bindings.head?.map (·.strings)).getD []
    let (read, _) ← Verify.readLines spec log.service ask (lines.take (k + 1)) []
    let some (some line) := read[k]? | continue
    let before := inputs s
    s ← takeIn spec st fs b s l line
    if inputs s == before then
      taken := k
      break
  if s.halted.isNone then s ← checkExchanges st fs s
  -- What the spec reports where it stops taking lines tells why, and no later line compares.
  let final ← Verify.verifyLines spec log.service ask (specLines log.service s) (log.lines.take taken) id
  let byLine := final.findings.mergeSort fun a b => decide (a.line ≤ b.line)
  pure { findings := byLine.filter (·.isViolation)
         violations := (invalid ++ broken).map (·.toViolation) ++ reportedViolations s (← get) none
         bindings := final.bindings.map (·.strings) }

/-- What verify finds of each log, and the parts of the spec that no log reached (Uncovered). -/
def verify (spec : Spec.Structure) (logs : List Log) : IO (List Replayed × List Violation) := do
  let (replayed, reached) ← logs.foldlM (init := ([], [])) fun (done, reached) log => do
    let (r, c) ← (replay spec log).run {}
    pure (done ++ [r], c.reached.foldl (fun acc u => if acc.contains u then acc else acc ++ [u]) reached)
  pure (replayed, (Explore.uncovered spec reached).map (·.toViolation))

/-- The value of an Except that stops the engine on an Issue, as a spec function's throw stopped TS. -/
def orStop {α : Type} (what : String) : Except Issue α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what} stopped on {repr e}")

/--
checkExternal, and on the lines that it finds nothing on, the checks that read schemas and the contract's conditions:
each event's payload, and each answer that answers a send of its request: the request's input, which only a rejection
may answer when it fails the schema, the requires on the input, the output, and a command's ensures with all its
result events, which may come before or after the answer.
-/
def verifyExternal (spec : Spec.Structure) (service : String) (trace : List (FileLine TraceLine)) :
    IO (List Verify.Finding) := do
  let st ← Service.ofStructure spec service
  let last ← IO.mkRef {}
  let fs := Ir.functionsOf st last
  let (lines, cut) := comparedLines .in trace
  let structural := checkLines spec service lines 1 [] ++ (exchanges spec service lines).flatMap (checkExchange spec service)
  let found := structural ++ (cut.map .uncomparable).toList
  let flagged := found.map (·.line)
  let numbered := (lines.zipIdx 1).filterMap fun (l, i) => l.map (i, ·)
  let mut more : List Verify.Finding := []
  let mut emitted : List (Nat × Emit) := []
  for (i, l) in numbered do
    let .event .out _ name payload _ := l.body | continue
    let some event := spec.named service (some name) ["event"] | continue
    if flagged.contains i then continue
    match ← orStop "the payload check" (← fs.parseOutside st (.payload event.ref) payload) with
    | some p => emitted := emitted ++ [(i, { event := event.ref, payload := p })]
    | none => more := more ++ [.mismatch (.eventPayloadSchema i event.ref)]
  for x in exchanges spec service lines do
    let target := x.definition.ref
    let input := match (numbered.lookup x.line).map (·.body) with
      | some (.command _ _ _ v _) | some (.query _ _ _ v _) => v
      | _ => .null
    let parsedInput ← orStop "the input check" (← fs.parseOutside st (.input target) input)
    let (requires, ensures) := (spec.conditionsOf? target).getD ([], [])
    let sentBefore (line : Nat) := 1 + (x.resends.filter (· < line)).length
    let mut answered := 0
    for (line, answer) in x.answers do
      if answered >= sentBefore line then continue
      answered := answered + 1
      if flagged.contains line then continue
      -- An answer without the output that its target declares fails the output schema.
      let output : Option (Option Value) := match answer with
        | .rejected _ => none
        | .accepted o => if spec.hasOutput target then some o else none
        | .fulfilled o => if spec.hasOutput target then some (some o) else none
      let parsedOutput ← match output with
        | some (some o) => some <$> orStop "the output check" (← fs.parseOutside st (.output target) o)
        | some none => pure (some none)
        | none => pure none
      let rejected := answer matches .rejected _
      if parsedInput.isNone && !rejected then more := more ++ [.mismatch (.requestInputSchema line x.id target)]
      if let some decodedInput := parsedInput then
        let failedRequires ← orStop "the requires" (← firstFalse (fs.inputRequirement target · decodedInput) requires)
        let outputFails := parsedOutput matches some none
        let results := x.events.filterMap fun (j, _) => emitted.lookup j
        let failedEnsures ←
          if rejected || failedRequires.isSome || outputFails then pure none
          else orStop "the ensures" (← firstFalse (fun n => do
            pure ((← fs.resultEnsures target n decodedInput (parsedOutput.join) results).map Ensured.passes)) ensures)
        if let some broken := Spec.assumptionMismatch answer failedRequires failedEnsures then
          more := more ++ [.mismatch (.assumption line x.id target broken)]
      if parsedOutput matches some none then
        more := more ++ [.mismatch (.assumption line x.id target .answerOutputSchema)]
  let all := (found ++ more).mergeSort fun a b => decide (a.line ≤ b.line)
  pure (all.filter (·.isViolation))

end Tazuna.Engine
