import Tazuna.Service.Queue
import Tazuna.Service.Screen.Operable

/-! Each input is one message, which the service processes to completion. -/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def send [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (target : Spec.Ref)
    (givenId : Option String) (raw : Value) : m State := do
  if target.service = st.service ∧ target.name ∈ st.commands then
    let (s, id) := s.write .in givenId (.command target raw)
    let (s, step) := s.newMessage.newStep none
    let request : Request := { name := target.name, input := raw }
    match s.commandAnswers.find? id with
    | some known => message st fs (s.answer (some id) (answerAgain known request)) {}
    | none =>
      let pc ← processCommand st fs s target.name raw (some id) step
      message st fs { pc.1 with commandAnswers := pc.1.commandAnswers.keep id request pc.2.1 }
        { tasks := commandWork st pc.1 pc.2.2 step }
  else pure (s.report (.invalidInput (.unownedTarget target)))

def call [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (target : Spec.Ref)
    (givenId : Option String) (raw : Value) : m State := do
  if target.service = st.service ∧ target.name ∈ st.queries then
    let (s, id) := s.write .in givenId (.query target raw)
    let s := s.newMessage
    match ← resolveChecked st fs s target.name raw with
    | .answered answer violations => message st fs ((s.reportAll violations).answer (some id) answer) {}
    | .halted fault => pure (s.report (.fault fault))
  else pure (s.report (.invalidInput (.unownedTarget target)))

/-- The state after a subscribe input. The first answer is sent when the message finishes. -/
def subscribe [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (target : Spec.Ref)
    (givenId : Option String) (raw : Value) : m State := do
  if target.service = st.service ∧ target.name ∈ st.queries then
    let (s, id) := s.write .in givenId (.subscribe target raw)
    let s := if s.subscriptions.any (·.id == id) then
        s.report (.invalidInput (.reusedSubscriptionId id))
      else { s with subscriptions := s.subscriptions ++ [{ id, query := target.name, input := raw }] }
    message st fs s.newMessage {}
  else pure (s.report (.invalidInput (.unownedTarget target)))

/-- The state after an unsubscribe input that ends the subscription `id`. -/
def endSubscription [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (id : String) : m State :=
  let s := (s.write .in none (.unsubscribe id)).1
  let s := if s.subscriptions.any (·.id == id) then { s with subscriptions := s.subscriptions.filter (·.id != id) }
    else s.report (.invalidInput (.unopenedSubscription id))
  message st fs s.newMessage {}

/--
The request `handle` whose answer arrived (State.answerTo?), which an event names as its resultOf. It is none after
reporting that no answer to it arrived, or that the request cannot have the event as its result (resultOfMismatch).
-/
def resultRequest (st : Service) (s : State) (event : Spec.Ref) (handle : String) : State × Option String :=
  match s.answerTo? handle with
  | some (target, answer) =>
    match st.«structure».resultOfMismatch target (answer matches .accepted _) event with
    | some mismatch => (s.report (.invalidInput (.resultOf event handle target mismatch)), none)
    | none => (s, some handle)
  | none => (s.report (.invalidInput (.resultOfUnansweredRequest event handle)), none)

/-- The state after the result event `e` of the request `id`, an assumed peer's accepted command, arrives. -/
def State.addResult (s : State) (id : String) (e : Emit) : State :=
  { s with outgoing := s.outgoing.map fun (o : Outgoing) => if o.id == id then
      { o with accepted := o.accepted.map fun a => { a with events := a.events ++ [e] } } else o }

/--
The state after the run ends: the ensures of each command that an assumed peer accepted is checked with all its result
events that arrived, as a Pact provider verification checks a consumer's expectation against the whole interaction.
-/
def checkResults [Monad m] (fs : Functions m) (s : State) : m State :=
  s.outgoing.foldlM (init := s) fun s o => do
    if s.halted.isSome then return s
    match o.accepted with
    | none => return s
    | some a =>
    match ← fs.resultEnsures o.activity.ref a.input a.output a.events with
    | .error issue => return s.report (.fault (issueViolation o.activity.ref issue))
    | .ok (some c) => return s.report (.invalidInput (.assumption o.id o.activity.ref (.failedAssumedEnsures c)))
    | .ok none => return s

/-- The state after the event that arrived as `raw` and parsed as `payload` is delivered. -/
def deliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (event : Spec.Ref)
    (givenId : Option String) (raw payload : Value) (request : Option String) : m State := do
  let (s, id) := s.write .in givenId (.event event raw request)
  let s := { s with deliveries := s.deliveries ++ [id] }
  let s := match request with
    | some r => s.addResult r { event, payload }
    | none => s
  let (s, step) := s.newMessage.newStep none
  message st fs s { tasks := reactions st s [[{ event, payload }]] false step }

def withResultOf (st : Service) (s : State) (event : Spec.Ref) : Option String → State × Option String
  | some handle => resultRequest st s event handle
  | none => (s, none)

/--
The state after an event with an already processed id. As in the EIP Idempotent Receiver, the event is not processed
again. The message itself is processed, so due deadlines and changed subscription answers are still sent. A
simulation redelivers a message as it was, so the name and payload are those of the first delivery.
-/
def redeliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (event : Spec.Ref)
    (givenId : Option String) (raw : Value) (resultOf : Option String) : m State := do
  let (s, request) := withResultOf st s event resultOf
  if s.halted.isSome then pure s else
  let (s, _) := s.write .in givenId (.event event raw request)
  message st fs s.newMessage {}

def receive [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (event : Spec.Ref)
    (givenId : Option String) (raw : Value) (resultOf : Option String) : m State := do
  if s.deliveries.contains (s.lineId givenId (event.traceName s.service)) then
    redeliver st fs s event givenId raw resultOf
  else
    match ← fs.parse (.payload event) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation event e)))
    | .ok none => pure (s.report (.invalidInput (.eventPayloadSchema event)))
    | .ok (some payload) =>
      let (s, request) := withResultOf st s event resultOf
      if s.halted.isSome then pure s else deliver st fs s event givenId raw payload request

/-- The assumption that an answer to the request `requestId` to `target` breaks (Spec.assumptionMismatch). -/
def brokenAssumption (requestId : String) (target : Spec.Ref) (answer : Answer)
    (failedRequires failedEnsures : Option String) : Option Finding :=
  (Spec.assumptionMismatch answer failedRequires failedEnsures).map (.invalidInput ∘ .assumption requestId target)

/--
The check of an answer to a request of the service. `assumption` is the assumption that the answer breaks, reported
without halting. `decoded` is the answer to deliver, or why it is malformed or the sender's fault. `accepted` is an
assumed peer's acceptance of a command, whose ensures the end of the run checks with its result events.
-/
structure AnswerCheck where
  assumption : Option Finding := none
  decoded : Except Finding Answer
  accepted : Option Accepted := none

/-- The answer with its output decoded, or none when the output does not match the target's output schema. -/
def decodedOutput [Monad m] (st : Service) (fs : Functions m) (a : Activity) (answer : Answer) :
    m (Except Issue (Option Answer)) := do
  if !st.«structure».hasOutput a.ref then return .ok (some answer)
  match answer with
  | .rejected _ => return .ok (some answer)
  | .accepted none => return .ok none
  | .accepted (some output) => return (← fs.parse (.output a.ref) output).map (·.map (.accepted ∘ some))
  | .fulfilled output => return (← fs.parse (.output a.ref) output).map (·.map .fulfilled)

/-- The answer to the request `p` decoded, or why its rejection kind or output does not match the target. -/
def decodedAnswer [Monad m] (st : Service) (fs : Functions m) (p : Pending) (answer : Answer) :
    m (Except Issue (Except Finding Answer)) := do
  let target := p.activity.ref
  let j := st.«structure»
  match answer with
  | .rejected r =>
    if !(j.rejectionKinds st.service target).contains r.kind then
      return .ok (.error (.invalidInput (.assumption p.id target (.unlistedRejectionKind r))))
    if r.kind == .requires && !(j.rejectionReasons target).contains (r.reason.getD "") then
      return .ok (.error (.invalidInput (.unlistedRejectionReason p.id target r)))
    return .ok (.ok answer)
  | _ =>
    match ← decodedOutput st fs p.activity answer with
    | .error e => return .error e
    | .ok none => return .ok (.error (.invalidInput (.assumption p.id target .answerOutputSchema)))
    | .ok (some decoded) => return .ok (.ok decoded)

/-- The check of an answer to the request `p` from a spec service, which parsed the input itself. -/
def specAnswer [Monad m] (st : Service) (fs : Functions m) (p : Pending) (answer : Answer) :
    m (Except Issue AnswerCheck) := do
  match p.requester.rejectedInput? st p.activity.ref answer with
  | some fault => return .ok { decoded := .error (.fault fault) }
  | none =>
    match ← decodedAnswer st fs p answer with
    | .error e => return .error e
    | .ok decoded => return .ok { decoded }

/--
The check of an answer to the request `p` from an assumed peer. Its input schema stands for the peer's parse, and the
answer is also checked against its requires over the input alone and, for a query, its ensures that read no records; a
command's ensures waits for the end of the run, when all its result events arrived.
-/
def assumedAnswer [Monad m] (st : Service) (fs : Functions m) (p : Pending) (answer : Answer) :
    m (Except Issue AnswerCheck) := do
  let target := p.activity.ref
  match ← fs.parse (.input target) p.input with
  | .error e => return .error e
  | .ok none => return .ok { decoded := .error (.fault (p.requester.inputFault st target)) }
  | .ok (some input) =>
  match ← firstFalse (fs.inputRequirement target · input) (st.«structure».requiresOf target) with
  | .error e => return .error e
  | .ok failedRequires =>
  let broken := brokenAssumption p.id target answer failedRequires
  match ← decodedAnswer st fs p answer with
  | .error e => return .error e
  | .ok (.error f) => return .ok { assumption := broken none, decoded := .error f }
  | .ok (.ok decoded) =>
    if decoded matches .rejected _ || failedRequires.isSome then
      return .ok { assumption := broken none, decoded := .ok decoded }
    if p.activity matches .sends .. then
      return .ok { assumption := broken none, decoded := .ok decoded,
                   accepted := some { input, output := decoded.output? } }
    match ← fs.resultEnsures target input decoded.output? [] with
    | .error e => return .error e
    | .ok failedEnsures => return .ok { assumption := broken failedEnsures, decoded := .ok decoded }

def checkAnswer [Monad m] (st : Service) (fs : Functions m) (p : Pending) (answer : Answer) :
    m (Except Issue AnswerCheck) :=
  if st.«structure».isAssumed p.activity.ref then assumedAnswer st fs p answer else specAnswer st fs p answer

/--
The state after an answer input with id `givenId` answers the request `p`, as checkAnswer checks the answer. The line
holds the answer as it arrived, and the requester gets it decoded.
-/
def answerRequest [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (givenId : Option String)
    (p : Pending) (answer : Answer) : m State := do
  match ← checkAnswer st fs p answer with
  | .error e =>
    pure (s.report (.fault (issueViolation p.activity.ref e)))
  | .ok checked =>
  let s := match checked.assumption with
    | some f => s.report f
    | none => s
  match checked.decoded with
  | .error f => pure (s.report f)
  | .ok decoded =>
    let s := match checked.accepted with
      | some a => { s with outgoing := s.outgoing.map fun (o : Outgoing) => if o.id == p.id then { o with accepted := some a } else o }
      | none => s
    let started := (s.write .in givenId (.answer p.id answer)).1.newMessage.newStep none
    let r ← settled fs st started.2 p.requester.machine? (deliverAnswer fs st started.2 p decoded) ⟨started.1, {}⟩
    message st fs r.state r.queue

/--
The state after the answer `a` to the request `to` arrives with the id `id`. A later event's resultOf names the request,
so the answer is kept with it, also when the request no longer waits, as after a restart; such an answer is a message
with no effect. As in the EIP Idempotent Receiver, an answer that arrives again is not processed again.
-/
def answerIn [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (id to : String) (a : Answer) :
    m State :=
  if s.deliveries.contains id then message st fs (s.write .in (some id) (.answer to a)).1.newMessage {} else
  let s := { s with deliveries := s.deliveries ++ [id],
                    outgoing := s.outgoing.map fun (o : Outgoing) => if o.id == to then { o with answer := some a } else o }
  match s.pending.find? (·.id == to) with
  | some p => answerRequest st fs s (some id) p a
  | none => message st fs (s.write .in (some id) (.answer to a)).1.newMessage {}

def startInstance [Monad m] (st : Service) (fs : Functions m) (s : State) (c : Chart) : m State := do
  if s.halted.isSome then pure s else
  match ← initialContextOf fs st c.name (.obj []) with
  | .error fault => pure (s.report (.fault fault))
  | .ok context =>
    pure { s with machines := s.machines ++ [{ chart := c, id := .top c.name 0, context, input := .obj [],
                                                shown := c.slots.map (·, .null) }],
                  stack := if c.screen then s.stack ++ [.top c.name 0] else s.stack }

/-- The charts that start when the service begins. A screen that another screen opens does not. -/
def starting (st : Service) : List Chart := st.charts.filter (!·.opened)

def startInstances [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  st.starting.foldlM (startInstance st fs) s

def startRecords [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  st.singles.foldlM (fun s e => do
    if s.records.any (·.entity == e) then pure s else
    let value ← fs.singleRecord e
    pure { s with records := s.records ++ [{ entity := e, key := none, value }] }) s

def begin [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : m State := do
  if s.started then pure s else
  let s ← startInstances st fs (← startRecords st fs { s with started := true }.newMessage)
  message st fs s { tasks := st.starting.map (fun c => .start (.top c.name 0) none) }

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
        let (s, step) := s.newMessage.newStep none
        let r ← settled fs st step (some i.id) (dispatch fs st step i.id control decoded) ⟨s, {}⟩
        message st fs r.state r.queue
      | .ok (.error r) => pure (s.report (r.finding st screen control decoded))

end Tazuna.Service
