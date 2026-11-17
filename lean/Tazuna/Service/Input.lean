import Tazuna.Service.Queue
import Tazuna.Service.Screen.Operable

/-! Each input is one message, which the service processes to completion. -/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def send [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) : m State := do
  if name ∈ st.commands then
    match ← fs.canonical (.input name) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref name) e)))
    | .ok input =>
    let (s, id) := s.write .in givenId (.command name input)
    let (s, step) := s.newMessage.newStep none
    let request : Request := { name, input }
    match s.commandAnswers.find? id with
    | some known => message st fs (s.answer (some id) (answerAgain known request)) {}
    | none =>
      let pc ← processCommand st fs s name raw (some id) step
      message st fs { pc.1 with commandAnswers := pc.1.commandAnswers.keep id request pc.2.1 }
        { tasks := commandWork st pc.1 pc.2.2 step }
  else pure (s.report (.invalidInput (.unownedTarget (st.refOf name))))

def call [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) : m State := do
  if name ∈ st.queries then
    match ← fs.canonical (.input name) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref name) e)))
    | .ok input =>
    let (s, id) := s.write .in givenId (.query name input)
    let s := s.newMessage
    match ← resolveChecked st fs s name raw with
    | .answered answer violations => message st fs ((s.reportAll violations).answer (some id) answer) {}
    | .halted fault => pure (s.report (.fault fault))
  else pure (s.report (.invalidInput (.unownedTarget (st.refOf name))))

/-- The state after a subscribe input. The first answer is sent when the message finishes. -/
def subscribe [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) : m State := do
  if name ∈ st.queries then
    match ← fs.canonical (.input name) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref name) e)))
    | .ok input =>
    let (s, id) := s.write .in givenId (.subscribe name input)
    let s := if s.subscriptions.any (·.id == id) then
        s.report (.invalidInput (.reusedSubscriptionId id))
      else { s with subscriptions := s.subscriptions ++ [{ id, query := name, input := raw }] }
    message st fs s.newMessage {}
  else pure (s.report (.invalidInput (.unownedTarget (st.refOf name))))

/-- The state after an unsubscribe input that ends the subscription `id`. -/
def endSubscription [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (id : String) : m State :=
  let s := (s.write .in none (.unsubscribe id)).1
  let s := if s.subscriptions.any (·.id == id) then { s with subscriptions := s.subscriptions.filter (·.id != id) }
    else s.report (.invalidInput (.unopenedSubscription id))
  message st fs s.newMessage {}

def resultOfFinding (event : Spec.Ref) (requestId : String) (target : Spec.Ref) : Spec.ResultOfMismatch → Finding
  | .resultOfNonCommand => .invalidInput (.resultOfNonCommand event requestId target)
  | .resultOfUnacceptedRequest => .invalidInput (.resultOfUnacceptedRequest event requestId target)
  | .resultOfUnlistedEvent => .invalidInput (.resultOfUnlistedEvent event requestId target)

/--
The request `handle` whose answer the service took (State.takenAnswers), which an event names as its resultOf. It is none
after reporting that the service took no answer to it, or that the request cannot have the event as its result
(resultOfMismatch).
-/
def resultRequest (st : Service) (s : State) (name handle : String) : State × Option Pending :=
  match s.takenAnswers.lookup handle with
  | some (p, answer) =>
    match st.«structure».resultOfMismatch p.activity.ref (answer matches .accepted _) (st.refOf name) with
    | some mismatch => (s.report (resultOfFinding (st.refOf name) p.id p.activity.ref mismatch), none)
    | none => (s, some p)
  | none => (s.report (.invalidInput (.resultOfUnansweredRequest (st.refOf name) handle)), none)

def addResult [Monad m] (st : Service) (fs : Functions m) (s : State) (id : String) (e : Emit) : m State := do
  match s.results.find? (·.id == id) with
  | none => pure s
  | some a =>
    let events := a.events ++ [e]
    let s := { s with results := s.results.map fun b => if b.id == id then { b with events } else b }
    match ← fs.resultEnsures a.activity.target a.input a.output events with
    | .error issue =>
      pure (s.report (.fault (issueViolation st a.activity.ref issue)))
    | .ok (some c) => pure (s.report (.invalidInput (.failedAssumedEnsures id a.activity.ref c)))
    | .ok none => pure s

def deliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (payload : Value) (request : Option Pending) : m State := do
  let (s, id) := s.write .in givenId (.event name payload (request.map (·.id)))
  let s := { s with eventDeliveries := s.eventDeliveries ++ [id] }
  let s ← match request with
    | some p => addResult st fs s p.id { event := name, payload }
    | none => pure s
  let (s, step) := s.newMessage.newStep none
  message st fs s { tasks := reactions st s [{ event := name, payload }] false step }

def withResultOf (st : Service) (s : State) (name : String) : Option String → State × Option Pending
  | some handle => resultRequest st s name handle
  | none => (s, none)

/--
The state after an event with an already processed id. As in the EIP Idempotent Receiver, the event is not processed
again. The message itself is processed, so due deadlines and changed subscription answers are still sent. A
simulation redelivers a message as it was, so the name and payload are those of the first delivery.
-/
def redeliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) (resultOf : Option String) : m State := do
  match ← fs.canonical (.payload name) raw with
  | .error e =>
    pure (s.report (.fault (issueViolation st (st.refOf name) e)))
  | .ok payload =>
  let (s, request) := withResultOf st s name resultOf
  if s.halted.isSome then pure s else
  let (s, _) := s.write .in givenId (.event name payload (request.map (·.id)))
  message st fs s.newMessage {}

def receive [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) (resultOf : Option String) : m State := do
  if s.eventDeliveries.contains (s.lineId givenId name) then redeliver st fs s name givenId raw resultOf
  else
    match ← fs.parse (.payload name) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.refOf name) e)))
    | .ok none => pure (s.report (.invalidInput (.eventPayloadSchema (st.refOf name))))
    | .ok (some payload) =>
      let (s, request) := withResultOf st s name resultOf
      if s.halted.isSome then pure s else deliver st fs s name givenId payload request

def assumptionFinding (requestId : String) (target : Spec.Ref) : Spec.AssumptionMismatch → Finding
  | .rejectedAssumedRequires => .invalidInput (.rejectedAssumedRequires requestId target)
  | .failedAssumedRequires c => .invalidInput (.failedAssumedRequires requestId target c)
  | .failedAssumedEnsures c => .invalidInput (.failedAssumedEnsures requestId target c)

/-- The assumption that an answer to the request `requestId` to `target` breaks (Spec.assumptionMismatch). -/
def brokenAssumption (requestId : String) (target : Spec.Ref) (answer : Answer)
    (failedRequires failedEnsures : Option String) : Option Finding :=
  (Spec.assumptionMismatch answer failedRequires failedEnsures).map (assumptionFinding requestId target)

/--
The check of an answer to a request of the service. `assumption` is the assumption that the answer breaks, reported without halting.
`written` is the answer to write, or why it is malformed. `recorded` is whether the answer is an external command's
acceptance, recorded to check its result events later.
-/
structure AnswerCheck where
  assumption : Option Finding
  written : Except Finding Answer
  recorded : Bool := false

/--
The answer as written, with its output canonical, or none when the output does not match the target's output schema.
-/
def writtenAnswer [Monad m] (st : Service) (fs : Functions m) (a : Activity) (answer : Answer) :
    m (Except Issue (Option Answer)) := do
  if !st.«structure».hasOutput a.ref then return .ok (some answer)
  match answer with
  | .rejected _ => return .ok (some answer)
  | .accepted none => return .ok none
  | .accepted (some output) => return (← fs.parse (.output a.target) output).map (·.map (.accepted ∘ some))
  | .fulfilled output => return (← fs.parse (.output a.target) output).map (·.map .fulfilled)

/--
The check of an answer to the request `p`. When the target is assumed, the answer is also checked against the
target's requires over the input alone and its ensures that read no records.
-/
def checkAnswer [Monad m] (st : Service) (fs : Functions m) (p : Pending) (answer : Answer) :
    m (Except Issue AnswerCheck) := do
  let target := p.activity.ref
  let s := st.«structure»
  let assumed := s.isAssumed target
  let required ←
    if assumed then firstFalse (fs.inputRequirement p.activity.target · p.input) (s.requiresOf target)
    else pure (.ok none)
  match required with
  | .error e => return .error e
  | .ok failedRequires =>
  let broken (failedEnsures : Option String) : Option Finding :=
    if assumed then brokenAssumption p.id target answer failedRequires failedEnsures else none
  match answer with
  | .rejected r =>
    let written :=
      if !(s.rejectionKinds st.service target).contains r.kind then
        .error (.invalidInput (.unlistedRejectionKind p.id target r))
      else if r.kind == .requires && !(s.rejectionReasons target).contains (r.reason.getD "") then
        .error (.invalidInput (.unlistedRejectionReason p.id target r))
      else .ok answer
    return .ok { assumption := broken none, written }
  | _ =>
    match ← writtenAnswer st fs p.activity answer with
    | .error e => return .error e
    | .ok none =>
      return .ok { assumption := broken none, written := .error (.invalidInput (.answerOutputSchema p.id target)) }
    | .ok (some written) =>
      if !assumed || failedRequires.isSome then return .ok { assumption := broken none, written := .ok written }
      match ← fs.resultEnsures p.activity.target p.input written.output? [] with
      | .error e => return .error e
      | .ok failedEnsures =>
        return .ok { assumption := broken failedEnsures, written := .ok written,
                     recorded := p.activity.keyword == "sends" }

/-- The state after an answer input answers the request `p`, as checkAnswer checks the answer. -/
def answerRequest [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (p : Pending) (answer : Answer) :
    m State := do
  match ← checkAnswer st fs p answer with
  | .error e =>
    pure (s.report (.fault (issueViolation st p.activity.ref e)))
  | .ok checked =>
  let s := match checked.assumption with
    | some f => s.report f
    | none => s
  match checked.written with
  | .error f => pure (s.report f)
  | .ok written =>
    let s := if checked.recorded then
        { s with results := s.results ++ [{ id := p.id, activity := p.activity, input := p.input,
                                             output := written.output? }] }
      else s
    let started := (s.write .in none (.answer p.id written)).1.newMessage.newStep none
    let r ← settled fs st started.2 p.requester.machine? (deliverAnswer fs st started.2 p written) ⟨started.1, {}⟩
    message st fs r.state r.queue

def startInstance [Monad m] (st : Service) (fs : Functions m) (s : State) (c : Chart) : m State := do
  if s.halted.isSome then pure s else
  match ← initialContextOf fs st c.name (.obj []) with
  | .error fault => pure (s.report (.fault fault))
  | .ok context =>
    pure { s with machines := s.machines ++ [{ chart := c, resource := c.name, context, input := .obj [],
                                                shown := c.slots.map (·, .null) }],
                  stack := if c.screen then s.stack ++ [c.name] else s.stack }

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
  message st fs s { tasks := st.starting.map (.start ·.name none) }

/--
The state after an operate input. As Playwright's click fails on a covered or missing element, operate reports an
operation that the screen does not accept.
-/
def operate [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (screen control : String) (payload : Value) :
    m State := do
  let name := s!"{screen}.{control}"
  match st.chart? screen with
  | none => pure (s.report (.invalidInput (.unownedTarget (st.refOf screen))))
  | some c =>
  match c.controls.find? (·.name == control) with
  | none => pure (s.report (.invalidInput (.unknownControl (st.ref screen) control)))
  | some ctl =>
    let s := (s.write .in none (.operation name (if ctl.hasPayload then some payload else none))).1
    match ← fs.parse (.control screen control) payload with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref screen) e)))
    | .ok none => pure (s.report (.invalidInput (.controlPayloadSchema (st.ref screen) control)))
    | .ok (some decoded) =>
      match ← acceptsOperation fs st s screen control decoded with
      | .error fault => pure (s.report (.fault fault))
      | .ok (.ok i) =>
        let (s, step) := s.newMessage.newStep none
        let r ← settled fs st step (some i.resource) (dispatch fs st step i.resource control decoded) ⟨s, {}⟩
        message st fs r.state r.queue
      | .ok (.error r) => pure (s.report (r.finding st screen control decoded))

end Tazuna.Service
