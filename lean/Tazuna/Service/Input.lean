import Tazuna.Service.Queue
import Tazuna.Service.Screen.Operable
import Tazuna.Service.Step

/-! Each input is one message, which the service processes to completion. -/

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

def send [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) : m State := do
  if name ∈ st.commands then
    match ← fs.canonical (.input name) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref name) e)))
    | .ok input =>
    let (s, id) := s.writeInput givenId (.command name input)
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
    let (s, id) := s.writeInput givenId (.query name input)
    let s := s.newMessage
    match ← resolveChecked st fs s name raw with
    | .answered answer violations => message st fs ((s.reportAll violations).answer (some id) answer) {}
    | .halted fault => pure (s.report (.fault fault))
  else pure (s.report (.invalidInput (.unownedTarget (st.refOf name))))

/-- The state after a subscribe input. The first answer is sent when the message finishes. -/
def subscribe [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) (handle : Option String) : m State := do
  if name ∈ st.queries then
    match ← fs.canonical (.input name) raw with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref name) e)))
    | .ok input =>
    let (s, id) := s.writeInput givenId (.subscribe name input)
    let s := { s with subscribed := (handle.map (·, id)).toList ++ s.subscribed }
    let s := if s.subscriptions.any (·.id == id) then
        s.report (.invalidInput (.reusedSubscriptionId id))
      else { s with subscriptions := s.subscriptions ++ [{ id, query := name, input := raw }] }
    message st fs s.newMessage {}
  else pure (s.report (.invalidInput (.unownedTarget (st.refOf name))))

def endOpened [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (id : String) : m State :=
  let s := (s.writeInput none (.unsubscribe id)).1
  let s := if s.subscriptions.any (·.id == id) then { s with subscriptions := s.subscriptions.filter (·.id != id) }
    else s.report (.invalidInput (.unopenedSubscription id))
  message st fs s.newMessage {}

/--
The state after an unsubscribe input. A checked scenario names by handle only a subscribe input before it
(Illegal.namedInputUnplaced), so the handle names a subscription that the input opened.
-/
def endSubscription [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) : Ended → m State
  | .id id => endOpened st fs s id
  | .handle h => match s.subscribed.lookup h with
    | some id => endOpened st fs s id
    | none => pure s

def resultOfFinding (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref) : Syntax.ResultOfMismatch → Finding
  | .resultOfNonCommand => .invalidInput (.resultOfNonCommand event requestId target)
  | .resultOfUnacceptedRequest => .invalidInput (.resultOfUnacceptedRequest event requestId target)
  | .resultOfUnlistedEvent => .invalidInput (.resultOfUnlistedEvent event requestId target)

/--
The request whose answer the latest mock input with handle `handle` gave. A checked scenario names only a mock input before
the event (Illegal.namedInputUnplaced), so the mock has been processed. It is none when that mock answered no request
(ambiguousMock, missingWaitingRequest, missingStaleRequest), and after reporting that the request cannot have the event
as its result (resultOfMismatch).
-/
def resultRequest (st : Service) (s : State) (name handle : String) : State × Option Pending :=
  match s.mocks.lookup handle with
  | some (p, answer) =>
    match st.«structure».resultOfMismatch p.activity.ref (answer matches .accepted _) (st.refOf name) with
    | some mismatch => (s.report (resultOfFinding (st.refOf name) p.id p.activity.ref mismatch), none)
    | none => (s, some p)
  | _ => (s, none)

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
  let (s, id) := s.writeInput givenId (.event name payload (request.map (·.id)))
  let s := { s with eventDeliveries := s.eventDeliveries ++ [(id, { event := st.refOf name, payload })] }
  let s ← match request with
    | some p => addResult st fs s p.id { event := name, payload }
    | none => pure s
  let (s, step) := s.newMessage.newStep none
  message st fs s { tasks := reactions st s [{ event := name, payload }] false step }

def withResultOf (st : Service) (s : State) (name : String) : Option String → State × Option Pending
  | some handle => resultRequest st s name handle
  | none => (s, none)

/--
The state after an event with an already processed id. As in the EIP Idempotent Receiver, the id is checked before the
payload and the event is not processed; a different name or payload is reported as a reused id. The message itself is
processed, so due deadlines and changed subscription answers are still sent.
-/
def redeliver [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) (resultOf : Option String) (first : Delivery) : m State := do
  match ← fs.canonical (.payload name) raw with
  | .error e =>
    pure (s.report (.fault (issueViolation st (st.refOf name) e)))
  | .ok payload =>
  let (s, request) := withResultOf st s name resultOf
  let (s, id) := s.writeInput givenId (.event name payload (request.map (·.id)))
  let delivered : Delivery := { event := st.refOf name, payload }
  let s := if first = delivered then s else s.report (.invalidInput (malformedRedelivery id first delivered))
  message st fs s.newMessage {}

def receive [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (name : String) (givenId : Option String)
    (raw : Value) (resultOf : Option String) : m State := do
  if name ∈ st.received then
    match s.eventDeliveries.find? (s.lineId givenId name) with
    | some first => redeliver st fs s name givenId raw resultOf first
    | none =>
      match ← fs.parse (.payload name) raw with
      | .error e =>
        pure (s.report (.fault (issueViolation st (st.refOf name) e)))
      | .ok none => pure (s.report (.invalidInput (.eventPayloadSchema (st.refOf name))))
      | .ok (some payload) =>
        let (s, request) := withResultOf st s name resultOf
        deliver st fs s name givenId payload request
  else pure (s.report (.invalidInput (.unlistedEvent (st.refOf name))))

def earliestTurn (ps : List Pending) : Option Pending :=
  ps.foldl (fun best p => match best with
    | some b => if p.turn < b.turn then some p else some b
    | none => some p) none

/-- The requests from `sender` to `name` that wait, stale exactly when `stale` is true, in sending order. -/
def State.waiting (s : State) (sender name : String) (stale : Bool) : List Pending :=
  s.pending.filter fun p => p.stale == stale && p.activity.target == name && s.senderOf p.requester == sender

/--
The requests of `ps` that the mock input `input` chooses: those whose input is the canonical form of their input
overlaid with `input` (Value.overlay), so that `input` gives fields, at any depth, an array or any other value as a
whole, that the request's input has.
-/
def chosen [Monad m] (st : Service) (fs : Functions m) (name : String) (input : Value) :
    List Pending → m (Except Fault (List Pending))
  | [] => pure (.ok [])
  | p :: ps => do
    match ← fs.canonical (.input name) (p.input.overlay input) with
    | .error e => pure (.error (issueViolation st (st.refOf name) e))
    | .ok v =>
      match ← chosen st fs name input ps with
      | .error f => pure (.error f)
      | .ok rest => pure (.ok (if v == p.input then p :: rest else rest))

def choosesStale : Option Choice → Bool
  | some (.mock _ stale) => stale == some true
  | _ => false

/-- The requests from `sender` to `name` that the answer input may answer by its choice. -/
def State.answerable [Monad m] (st : Service) (fs : Functions m) (s : State) (sender name : String) :
    Option Choice → m (Except Fault (List Pending))
  | some (.id to) =>
    pure (.ok (s.pending.filter fun p => p.id == to && p.activity.target == name && s.senderOf p.requester == sender))
  | some (.mock (some input) stale) => chosen st fs name input (s.waiting sender name (stale == some true))
  | some (.mock none stale) => pure (.ok (s.waiting sender name (stale == some true)))
  | none => pure (.ok (s.waiting sender name false))

def assumptionFinding (requestId : String) (target : Syntax.Ref) : Syntax.AssumptionMismatch → Finding
  | .rejectedAssumedRequires => .invalidInput (.rejectedAssumedRequires requestId target)
  | .failedAssumedRequires c => .invalidInput (.failedAssumedRequires requestId target c)
  | .failedAssumedEnsures c => .invalidInput (.failedAssumedEnsures requestId target c)

/-- The assumption that a mock's answer to the request `requestId` to `target` breaks (Syntax.assumptionMismatch). -/
def brokenAssumption (requestId : String) (target : Syntax.Ref) (answer : Answer)
    (failedRequires failedEnsures : Option String) : Option Finding :=
  (Syntax.assumptionMismatch answer failedRequires failedEnsures).map (assumptionFinding requestId target)

/--
The check of a mock's answer. `assumption` is the assumption that the answer breaks, reported without halting.
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
The check of a mock's answer to the request `p`. When the target is assumed, the answer is also checked against the
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

/--
The request that the answer input answers: the longest-waiting of those that it may answer, unless their inputs differ,
which no order that the scenario wrote decides (ambiguousMock).
-/
def State.answering [Monad m] (st : Service) (fs : Functions m) (s : State) (sender name : String)
    (choice : Option Choice) : m (Except Finding Pending) := do
  match ← s.answerable st fs sender name choice with
  | .error fault => pure (.error (.fault fault))
  | .ok ps =>
  let inputs := (ps.map (·.input)).eraseDups
  if 1 < inputs.length then pure (.error (.invalidInput (.ambiguousMock (st.refOf sender) (st.refOf name) inputs)))
  else
  match earliestTurn ps with
  | none => pure (.error (.invalidInput
      ((if choosesStale choice then InvalidInput.missingStaleRequest else .missingWaitingRequest) (st.refOf sender)
        (st.refOf name))))
  | some p => pure (.ok p)

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
    let started := (s.writeInput none (.answer p.id written)).1.newMessage.newStep none
    let r ← settled fs st started.2 p.requester.machine? (deliverAnswer fs st started.2 p written) ⟨started.1, {}⟩
    message st fs r.state r.queue

def mock [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (sender name : String) (answer : Answer)
    (choice : Option Choice) (handle : Option String) : m State := do
  match ← s.answering st fs sender name choice with
  | .error f => pure (s.report f)
  | .ok p => answerRequest st fs { s with mocks := (handle.map (·, p, answer)).toList ++ s.mocks } p answer

/-- The state after an answer input answers the request to `target` whose trace line has id `to`. -/
def answerById [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (to target : String)
    (answer : Answer) : m State :=
  match s.pending.find? fun p => p.id == to && p.activity.target == target with
  | some p => answerRequest st fs s p answer
  | none => pure (s.report (.invalidInput (.unwaitedRequest to (st.refOf target))))

def startInstance [Monad m] (st : Service) (fs : Functions m) (s : State) (c : Chart) : m State := do
  if s.halted.isSome then pure s else
  match ← initialContextOf fs st c.name (.obj []) with
  | .error fault => pure (s.report (.fault fault))
  | .ok context =>
    pure { s with machines := s.machines ++ [{ chart := c, resource := c.name, context, input := .obj [],
                                                shown := c.slots.map (·, .null) }],
                  stack := if c.screen then s.stack ++ [c.name] else s.stack }

/-- The charts that start when the service begins. A screen that another screen opens does not. -/
def Service.starting (st : Service) : List Chart := st.charts.filter (!·.opened)

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

/-- The state with the names `keys` in place of the current ones, of which it reports the first entity's names left. -/
def State.takeKeys (s : State) (keys : List (String × List String)) : State :=
  let t := { s with keyNames := keys }
  match s.halted, s.keyNames.find? (!·.2.isEmpty) with
  | none, some (entity, names) => t.report (.invalidInput (.unusedKeys entity names))
  | _, _ => t

/--
The state at the end of an input, with the entries of its `deadlineOrder` that no tie used reported, or else the
entries of its `stepOrder` left unused, or else the first entity's names of its `keys` that no createKey returned.
-/
def State.checkOrderUsed (s : State) : State :=
  let t := { s with inputDeadlineOrder := [] }
  match s.halted, s.deadlineOrder, s.stepOrder with
  | none, _ :: _, _ => { t with keyNames := [] }.report (.invalidInput (.unusedDeadlineOrder s.deadlineOrder))
  | none, [], _ :: _ => { t with keyNames := [] }.report (.invalidInput (.unusedStepOrder s.stepOrder))
  | _, _, _ => t.takeKeys []

/--
The first string of the values of `body` that has the form of a createKey value of an own entity that createKey has
not given yet, with the entity.
-/
def State.uncreatedKey (s : State) (st : Service) (body : Step.Body) : Option (String × String) :=
  (body.values.flatMap Value.strings).findSome? fun v =>
    if s.created.any (·.2 == v) then none
    else (st.entities.find? fun e => !st.singles.contains e && Syntax.isKeyOf e v).map (v, ·)

/--
The state in which `input` arrives. Every input first advances the time to its own, firing the deadlines due by then;
then every input but a restart, which begins the service itself, begins the service if it has not begun.
-/
def advance [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (input : Step) : m State := do
  let time := input.time.time
  if time < s.now then
    pure (s.report (.invalidInput (.earlierAt time s.now)))
  else
    let s ← fireDue st fs time Limit.dueDeadlines.max none s
    if s.halted.isSome then pure s else
    let s := { s with now := max s.now time }
    match input.body with
    | .restart => pure s
    | _ => begin st fs s

/--
The state after an operate or cannotOperate input. As Playwright's click fails on a covered or missing element and
toBeDisabled and toBeHidden assert that it cannot be used, operate and cannotOperate check the expectation of whether
the screen accepts the operation.
-/
def operate [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (screen control : String) (payload : Value)
    (accepted : Bool) : m State := do
  let name := s!"{screen}.{control}"
  match st.chart? screen with
  | none => pure (s.report (.invalidInput (.unownedTarget (st.refOf screen))))
  | some c =>
  match c.controls.find? (·.name == control) with
  | none => pure (s.report (.invalidInput (.unknownControl (st.ref screen) control)))
  | some ctl =>
    let s := (s.writeInput none (.operation name (if ctl.hasPayload then some payload else none) accepted)).1
    match ← fs.parse (.control screen control) payload with
    | .error e =>
      pure (s.report (.fault (issueViolation st (st.ref screen) e)))
    | .ok none => pure (s.report (.invalidInput (.controlPayloadSchema (st.ref screen) control)))
    | .ok (some decoded) =>
      match ← acceptsOperation fs st s screen control decoded with
      | .error fault => pure (s.report (.fault fault))
      | .ok top =>
        match accepted, top with
        | true, .ok i =>
          let (s, step) := s.newMessage.newStep none
          let r ← settled fs st step (some i.resource) (dispatch fs st step i.resource control decoded) ⟨s, {}⟩
          message st fs r.state r.queue
        | false, .error _ => message st fs s.newMessage {}
        | true, .error r => pure (s.report (r.finding st screen control decoded))
        | false, .ok _ => pure (s.report (.invalidInput (.unexpectedlyAccepted (st.ref screen) control)))

end Tazuna.Semantics
