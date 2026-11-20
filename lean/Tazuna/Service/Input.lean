import Tazuna.Service.Queue
import Tazuna.Service.Screen.Operable

/-! Each input is one message, which the service processes to completion. -/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def send [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (target : Spec.Ref)
    (givenId : Option LineId) (raw : Value) : m State := do
  if target.service = st.service ∧ target.name ∈ st.commands then
    let (s, id) := s.write .in givenId (.command target raw)
    let (s, step) := s.newMessage.newStep .root
    let request : Request := { name := target.name, input := raw }
    match s.commandAnswers.find? id with
    | some known => message st fs (s.answer (some id) target (answerAgain known request)) {}
    | none =>
      let pc ← processCommand st fs s target.name raw (some id) step
      message st fs { pc.1 with commandAnswers := pc.1.commandAnswers.keep id request pc.2.1 }
        { tasks := commandWork st pc.1 pc.2.2 step }
  else pure (s.report (.invalidInput (.unownedTarget target)))

def call [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (target : Spec.Ref)
    (givenId : Option LineId) (raw : Value) : m State := do
  if target.service = st.service ∧ target.name ∈ st.queries then
    let (s, id) := s.write .in givenId (.query target raw)
    let s := s.newMessage
    match ← resolveChecked st fs s target.name raw with
    | .answered answer violations => message st fs ((s.reportAll violations).answer (some id) target answer) {}
    | .halted fault => pure (s.report (.fault fault))
  else pure (s.report (.invalidInput (.unownedTarget target)))

/-- The state after a subscribe input. The first answer is sent when the message finishes. -/
def subscribe [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (target : Spec.Ref)
    (givenId : Option LineId) (raw : Value) : m State := do
  if target.service = st.service ∧ target.name ∈ st.queries then
    let (s, id) := s.write .in givenId (.subscribe target raw)
    let s := if s.subscriptions.any (·.id == id) then
        s.report (.invalidInput (.reusedSubscriptionId id.text))
      else { s with subscriptions := s.subscriptions ++ [{ id, query := target.name, input := raw }] }
    message st fs s.newMessage {}
  else pure (s.report (.invalidInput (.unownedTarget target)))

/-- The state after an unsubscribe input that ends the subscription `id`. -/
def endSubscription [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (id : LineId) : m State :=
  let s := (s.write .in none (.unsubscribe id)).1
  let s := if s.subscriptions.any (·.id == id) then { s with subscriptions := s.subscriptions.filter (·.id != id) }
    else s.report (.invalidInput (.unopenedSubscription id.text))
  message st fs s.newMessage {}

/-- The state after the event that arrived as `raw` and parsed as `payload` is delivered. -/
def deliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (event : Spec.Ref)
    (id : LineId) (raw payload : Value) (resultOf : Option LineId) : m State := do
  let (s, _) := s.write .in (some id) (.event event raw resultOf)
  let s := { s with deliveries := s.deliveries ++ [id] }
  let (s, step) := s.newMessage.newStep .root
  message st fs s { tasks := reactions st s [[{ event, payload }]] false step }

/--
The state after an event with an already processed id. As in the EIP Idempotent Receiver, the event is not processed
again. The message itself is processed, so due deadlines and changed subscription answers are still sent. A
simulation redelivers a message as it was, so the name and payload are those of the first delivery.
-/
def redeliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (event : Spec.Ref)
    (id : LineId) (raw : Value) (resultOf : Option LineId) : m State :=
  message st fs (s.write .in (some id) (.event event raw resultOf)).1.newMessage {}

/--
The state after an event arrives. Its resultOf is only written: the end of the run checks it against the request
(checkExchanges), since the event may arrive before or after the answer, as a Stripe webhook may arrive before the API
response.
-/
def receive [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (event : Spec.Ref)
    (id : LineId) (raw : Value) (resultOf : Option LineId) : m State := do
  if s.deliveries.contains id then
    redeliver st fs s event id raw resultOf
  else
    match ← fs.parse (.payload event) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation event e)))
    | .ok none => pure (s.report (.invalidInput (.eventPayloadSchema event)))
    | .ok (some payload) => deliver st fs s event id raw payload resultOf

/-- The assumption that an answer to the request `requestId` to `target` breaks (Spec.assumptionMismatch). -/
def brokenAssumption (requestId : LineId) (target : Spec.Ref) (answer : Answer)
    (failedRequires failedEnsures : Option String) : Option Finding :=
  (Spec.assumptionMismatch answer failedRequires failedEnsures).map
    (.invalidInput ∘ .assumption requestId.text target)

/-- The answer with its output decoded, or none when the output does not match the output schema of `target`. -/
def decodedOutput [Monad m] (st : Service) (fs : Functions m) (target : Spec.Ref) (answer : Answer) :
    m (Except Issue (Option Answer)) := do
  if !st.«structure».hasOutput target then return .ok (some answer)
  match answer with
  | .rejected _ => return .ok (some answer)
  | .accepted none => return .ok none
  | .accepted (some output) => return (← fs.parse (.output target) output).map (·.map (.accepted ∘ some))
  | .fulfilled output => return (← fs.parse (.output target) output).map (·.map .fulfilled)

/-- The answer to the request `id` to `target` decoded, or why its rejection kind or output does not match `target`. -/
def decodedAnswer [Monad m] (st : Service) (fs : Functions m) (id : LineId) (target : Spec.Ref) (answer : Answer) :
    m (Except Issue (Except Finding Answer)) := do
  let j := st.«structure»
  match answer with
  | .rejected r =>
    if !(j.rejectionKinds st.service target).contains r.kind then
      return .ok (.error (.invalidInput (.assumption id.text target (.unlistedRejectionKind r))))
    if r.kind == .requires && !(j.rejectionReasons target).contains (r.reason.getD "") then
      return .ok (.error (.invalidInput (.unlistedRejectionReason id.text target r)))
    return .ok (.ok answer)
  | _ =>
    match ← decodedOutput st fs target answer with
    | .error e => return .error e
    | .ok none => return .ok (.error (.invalidInput (.assumption id.text target .answerOutputSchema)))
    | .ok (some decoded) => return .ok (.ok decoded)

/--
The answer to the request `p` decoded for its requester, or why it cannot be delivered. A spec service parsed the input
itself, so its rejection as invalid is the requester's fault. What an assumed peer's answer assumes is checked at the
end of the run (checkExchanges).
-/
def checkAnswer [Monad m] (st : Service) (fs : Functions m) (p : Pending) (answer : Answer) :
    m (Except Issue (Except Finding Answer)) :=
  let target := p.activity.ref
  match (if st.«structure».isAssumed target then none else rejectedInput? st p.requester.sender target answer) with
  | some fault => pure (.ok (.error (.fault fault)))
  | none => decodedAnswer st fs p.id target answer

/--
The state after an answer input with id `givenId` answers the request `p`, as checkAnswer checks the answer. The line
holds the answer as it arrived, and the requester gets it decoded.
-/
def answerRequest [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (givenId : Option LineId)
    (p : Pending) (answer : Answer) : m State := do
  match ← checkAnswer st fs p answer with
  | .error e =>
    pure (s.report (.fault (issueViolation p.activity.ref e)))
  | .ok (.error f) => pure (s.report f)
  | .ok (.ok decoded) =>
    let started := (s.write .in givenId (.answer p.id answer)).1.newMessage.newStep .root
    let r ← settled fs st started.2 p.requester.machine? (deliverAnswer fs st started.2 p decoded) ⟨started.1, {}⟩
    message st fs r.state r.queue

/--
The state after the answer `a` to the request `to` arrives with the id `id`. An answer to a request that no longer
waits, as after a restart, is a message with no effect; its line keeps it for the end of the run (checkExchanges). As
in the EIP Idempotent Receiver, an answer that arrives again is not processed again.
-/
def answerIn [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (id to : LineId) (a : Answer) :
    m State :=
  if s.deliveries.contains id then message st fs (s.write .in (some id) (.answer to a)).1.newMessage {} else
  let s := { s with deliveries := s.deliveries ++ [id] }
  match s.pending.find? (·.id == to) with
  | some p => answerRequest st fs s (some id) p a
  | none => message st fs (s.write .in (some id) (.answer to a)).1.newMessage {}

/--
A request that the service sent, as its lines record it: its input as sent, and the answers and the events naming it as
their resultOf that arrived, in arrival order. A message that arrived again has the id of its first arrival and counts
once.
-/
structure Exchange where
  id : LineId
  target : Spec.Ref
  sender : String
  input : Value
  answers : List Answer
  events : List (Spec.Ref × Value)

/-- The requests that the service sent, in sending order, each with what arrived of it. -/
def State.exchanges (s : State) : List Exchange :=
  let arrived := s.lines.toList.foldl (init := []) fun (acc : List Line) l =>
    if l.dir == .in && !acc.any (·.id == l.id) then acc ++ [l] else acc
  let sent (id : LineId) (target : Spec.Ref) (input : Value) (sender : String) : Exchange :=
    { id, target, sender, input
      answers := arrived.filterMap fun a => match a.body with
        | .answer to x => if to == id then some x else none
        | _ => none
      events := arrived.filterMap fun a => match a.body with
        | .event e p (some r) => if r == id then some (e, p) else none
        | _ => none }
  s.lines.toList.filterMap fun
    | ⟨_, .out, id, .command r input, _, sender, _⟩ | ⟨_, .out, id, .query r input, _, sender, _⟩
    | ⟨_, .out, id, .subscribe r input, _, sender, _⟩ => some (sent id r input sender)
    | _ => none

/--
The result events of `x` decoded. Each was decoded when it arrived, so an event that does not decode now is left out.
-/
def decodedEvents [Monad m] (fs : Functions m) (x : Exchange) : m (Except Issue (List Emit)) :=
  x.events.foldlM (init := .ok []) fun acc (event, raw) => do
    match acc with
    | .error e => pure (.error e)
    | .ok emits =>
      match ← fs.parse (.payload event) raw with
      | .error e => pure (.error e)
      | .ok none => pure (.ok emits)
      | .ok (some payload) => pure (.ok (emits ++ [{ event, payload }]))

/--
The finding of a result event of `x` that cannot be the result of its request (Structure.resultOfMismatch), as verify
checks an external service's trace.
-/
def resultOfFinding (st : Service) (x : Exchange) : Option Finding :=
  x.events.findSome? fun (event, _) =>
    (st.«structure».resultOfMismatch x.target x.answers event).map
      (.invalidInput ∘ .resultOf event x.id.text x.target)

/--
The state after the answer `a` of the request `x` to an assumed peer, whose input decoded as `input`, is checked: its
rejection kind or output, the target's requires over the input alone, and its ensures, a command's with all the result
events `events`.
-/
def checkAssumedAnswer [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (x : Exchange) (input : Value) (events : List Emit)
    (s : State) (a : Answer) : m State := do
  if s.halted.isSome then return s
  let target := x.target
  match ← decodedAnswer st fs x.id target a with
  | .error e => return s.report (.fault (issueViolation target e))
  | .ok (.error f) => return s.report f
  | .ok (.ok decoded) =>
  let (requires, ensures) ← expectFound s!"conditions of {target.name}" (st.«structure».conditionsOf? target)
  match ← firstFalse (fs.inputRequirement target · input) requires with
  | .error e => return s.report (.fault (issueViolation target e))
  | .ok failedRequires =>
  let ensured : Except Issue (Option String) ←
    if decoded matches .rejected _ || failedRequires.isSome then pure (.ok none) else
      firstFalse (fun n => (·.map Ensured.passes) <$> fs.resultEnsures target n input decoded.output? events) ensures
  match ensured with
  | .error e => return s.report (.fault (issueViolation target e))
  | .ok failedEnsures =>
    match brokenAssumption x.id target a failedRequires failedEnsures with
    | some f => return s.report f
    | none => return s

/--
The state after the request `x` is checked: its result events against its target, a spec peer's rejection of its input
as invalid, and, for an assumed peer, its input against the target's input schema, which stands for the peer's parse,
also when no answer arrived, and each answer (checkAssumedAnswer). Each answer counts, also one that arrived when the
request no longer waited.
-/
def checkExchange [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (x : Exchange) : m State := do
  if s.halted.isSome then return s
  if !st.«structure».isAssumed x.target then
    if let some f := x.answers.findSome? (rejectedInput? st x.sender x.target) then return s.report (.fault f)
    return (resultOfFinding st x).elim s s.report
  match ← fs.parse (.input x.target) x.input with
  | .error e => return s.report (.fault (issueViolation x.target e))
  | .ok none => return s.report (.fault (.inputSchema (st.ref x.sender) x.target))
  | .ok (some input) =>
  if let some f := resultOfFinding st x then return s.report f
  match ← decodedEvents fs x with
  | .error e => return s.report (.fault (issueViolation x.target e))
  | .ok events => x.answers.foldlM (checkAssumedAnswer st fs x input events) s

/--
The state after the run ends: each request that the service sent is checked once against what its lines record of it
(checkExchange), as a Pact provider verification replays the recorded interactions.
-/
def checkExchanges [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State :=
  s.exchanges.foldlM (checkExchange st fs) s

def startInstance [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (c : Chart) : m State := do
  if s.halted.isSome then pure s else
  match ← initialContextOf fs st c.name (.obj []) with
  | .error fault => pure (s.report (.fault fault))
  | .ok context =>
    pure { s with machines := s.machines ++ [{ chart := c, id := .top c.name, context, input := .obj [],
                                                shown := c.slots.map (·, .null) }],
                  stack := if c.screen then s.stack ++ [.top c.name] else s.stack }

/-- The charts that start when the service begins. A screen that another screen opens does not. -/
def starting (st : Service) : List Chart := st.charts.filter (!·.opened)

def startInstances [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State :=
  st.starting.foldlM (startInstance st fs) s

/--
Writes the record of each single entity that Given left out, as the defaults of its fields, which load checks
(Malformed.defaultSchema).
-/
def startRecords [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State :=
  st.singles.foldlM (fun s e => do
    if s.records.any (·.entity == e) then pure s else
    let schema := .record (st.ref e)
    let value ← st.sorted schema (← expectFound s!"defaults of the single entity {e}" (← fs.defaults schema).toOption)
    pure { s with records := s.records ++ [{ entity := e, key := none, value }] }) s

def begin [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  if s.started then pure s else
  let s ← startInstances st fs (← startRecords st fs { s with started := true }.newMessage)
  message st fs s { tasks := st.starting.map (fun c => .start (.top c.name) none) }

/--
Which of the open instances of the screen of `resource`, in opening order, it is, when more than one is open: an
operation line names its instance only then, as Playwright's strict locator needs `nth` only for several matches.
-/
def State.nthOpen (s : State) (resource : InstanceId) : Option Nat :=
  let open_ := s.stack.filter (·.chart == resource.chart)
  if open_.length > 1 then open_.idxOf? resource else none

/--
The state after an operate input on the screen instance `resource`. As Playwright's click fails on a covered or missing
element, operate reports an operation that the instance does not accept.
-/
def operate [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (resource : InstanceId)
    (control : String) (payload : Value) : m State := do
  let screen := resource.chart
  match st.chart? screen with
  | none => pure (s.report (.invalidInput (.unownedTarget (st.ref screen))))
  | some c =>
  match c.controls.find? (·.name == control) with
  | none => pure (s.report (.invalidInput (.unknownControl (st.ref screen) control)))
  | some ctl =>
    let s := (s.write .in none
      (.operation (st.ref screen) control (s.nthOpen resource) (if ctl.hasPayload then some payload else none))).1
    match ← fs.parse (.control (st.ref screen) control) payload with
    | .error e =>
      pure (s.report (.fault (issueViolation (st.ref screen) e)))
    | .ok none => pure (s.report (.invalidInput (.controlPayloadSchema (st.ref screen) control)))
    | .ok (some decoded) =>
      match ← acceptsOperation fs st s resource control decoded with
      | .error fault => pure (s.report (.fault fault))
      | .ok (.ok i) =>
        let (s, step) := s.newMessage.newStep .root
        let r ← settled fs st step (some i.id) (dispatch fs st step i.id control decoded) ⟨s, {}⟩
        message st fs r.state r.queue
      | .ok (.error r) => pure (s.report (r.finding st screen control decoded))

end Tazuna.Service
