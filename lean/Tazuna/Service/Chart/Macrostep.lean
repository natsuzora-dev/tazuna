import Tazuna.Service.Chart.Always
import Tazuna.Service.Screen.Subscription
import Tazuna.Service.Automation
import Tazuna.Service.Command

/-!
As in an SCXML microstep, all chosen transitions run before always transitions are evaluated (settle). As in the SCXML
main loop, an instance handles events, operations, answers, onDone and deadlines in the configuration left after
always transitions (settled). The order within one message (run-to-completion) follows W3C SCXML Appendix D: the
internal queue first processes work caused by steps; whenever work runs out, commands sent to its own service in the
meantime (a round) are appended to the command queue in sender-definition order and processed one by one. When both
are empty (end of macrostep), the activities of entered states are sent (sendEntered) and the work and commands that
they cause are processed. No cause orders the work and commands waiting at one time, so the input's `stepOrder` may take
any of them first (Queue.take).
-/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

def handlingStateReads (i : Instance) (key : String) (leaves : List (InstanceId × Option String)) : List (InstanceId × String) :=
  let handling := (i.chart.states.filter fun cs => !(i.chart.transitionsAt (some cs.spec.name) (.on key)).isEmpty).map
    (·.spec.name)
  let holders := i.id :: dedupe ((leaves.map (·.1)).filter (· != i.id))
  holders.flatMap fun h => handling.map (h, ·)

def mapStateReads (i : Instance) : List (InstanceId × String) :=
  let tree := i.chart.tree
  (i.active.filter (tree.kindOf · == some .map)).map (i.id, ·)

def Work.name : Work → StepName
  | .reaction a ((e :: _) :: _) d _ => .reaction a.name a.receives e.payload (d.map (·.map (·.payload)))
  | .reaction a _ d _ => .reaction a.name a.receives .null (d.map (·.map (·.payload)))
  | .answered c answer _ => .answer c.activity c.requester c.input (ToValue.toValue answer)
  | .start name _ => .start name
  | .receive name ((e :: _) :: _) d _ => .receive name e d
  | .receive name _ _ _ => .always name
  | .onDone name _ => .onDone name
  | .opensDone name state key _ _ _ => .opensDone name state key

def Ready.name : Ready → StepName
  | .work w => w.name
  | .command c => .command c.activity c.requester c.input

def Work.origin : Work → StepOrigin
  | .reaction _ _ _ cause | .answered _ _ cause | .receive _ _ _ cause | .onDone _ cause | .opensDone _ _ _ _ _ cause =>
    .caused cause
  | .start _ (some cause) => .caused cause
  | .start _ none => .root

def Work.started : Work → Option InstanceId
  | .start name _ => some name
  | _ => none

/-- The transitions of `i` at `state` that take `answer` to activity `a`. -/
def Instance.answerTransitions (i : Instance) (state : String) (a : Activity) (answer : Answer) : List Transition :=
  ((a.answerTrigger? (answer matches .rejected _)).map (i.chart.transitionsAt (some state))).getD []

section

variable [Monad m] [MonadNote m] (fs : Functions m)

def applyCompletion (st : Service) (step : Nat) (name : InstanceId) (ts : List Transition) (extra : Extra) :
    Processing → m Processing :=
  withMachine name fun i r => do
    match ← choose fs st r.state i extra ts with
    | .error fault => pure (r.report (.fault fault))
    | .ok none => pure r
    | .ok (some t) => microstep fs st step name [(name, t)] extra r

def handle (st : Service) (step : Nat) (name : InstanceId) (state : String) (a : Activity) (answer : Answer) : Processing → m Processing :=
  withMachine name fun i r => do
    MonadNote.note (.readStates [(name, state)])
    if i.closed || !i.isIn state then pure r else
    let ts := i.answerTransitions state a answer
    match answer with
    | .rejected rejection => applyCompletion fs st step name ts (.rejection rejection) r
    | .accepted output =>
      applyCompletion fs st step name ts (match output with | some o => .output o | none => .none) r
    | .fulfilled output => applyCompletion fs st step name ts (.output output) r

def dispatch (st : Service) (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) : m Processing :=
  match r.state.machine? name with
  | none => pure r
  | some i =>
    if r.halted || i.closed then pure r else do
    match ← eventLeaves fs st r.state i payload with
    | .error fault => pure (r.report (.fault fault))
    | .ok leaves =>
    let reads := handlingStateReads i key leaves ++ mapStateReads i
    MonadNote.note (.readStates reads)
    match ← select fs st r.state i (.on key) (.payload payload) leaves with
    | .error fault => pure (r.report (.fault fault))
    -- An event that no transition takes is discarded, as in SCXML.
    | .ok [] => pure r
    | .ok chosen => microstep fs st step name chosen (.payload payload) r

/-- The processing of the first event of the receive work `groups` of `name`; none only settles. -/
def receiveWork (st : Service) (step : Nat) (name : InstanceId) (groups : List (List Received))
    (r : Processing) : m Processing :=
  match groups with
  | (e :: _) :: _ => do dispatch fs st step name e.key e.payload (← settle fs st step name r)
  | _ => pure r

def done (st : Service) (step : Nat) (name : InstanceId) (n : String) : Processing → m Processing :=
  withMachine name fun i r => do
    MonadNote.note (.readStates [(name, n)])
    if i.closed || !i.isIn n then pure r
    else applyCompletion fs st step name (i.chart.transitionsAt (some n) .onDone) .none r

/--
The processing of the onDone selections of instance `name`. States that finish during the work are handled by the same
work.
-/
def doneWork (st : Service) (step : Nat) (name : InstanceId) : Nat → Processing → m Processing
  | 0, r =>
    match r.state.machine? name with
    | some i =>
      match i.awaitingOnDone with
      | some (_ :: _) =>
        pure (r.report (.fault (.exceededOnDoneSelections (st.ref i.chart.name) Limit.onDoneSelections.max)))
      | _ => pure ⟨r.state.setMachine name fun i => { i with awaitingOnDone := none }, r.queue⟩
    | none => pure r
  | fuel + 1, r =>
    if r.halted then pure r else
    match r.state.machine? name with
    | none => pure r
    | some i =>
      match i.awaitingOnDone with
      | some (n :: rest) => do
        let r ← settle fs st step name ⟨r.state.setMachine name fun i => { i with awaitingOnDone := some rest }, r.queue⟩
        doneWork st step name fuel (← done fs st step name n r)
      | _ => pure ⟨r.state.setMachine name fun i => { i with awaitingOnDone := none }, r.queue⟩

def startWork (st : Service) (step : Nat) (name : InstanceId) : Processing → m Processing :=
  withMachine name fun i r => do
    let r ← enter fs st step name [i.chart.initial] ⟨r.state.setMachine name ({ · with startStep := some step }), r.queue⟩
    let r ← checkChart fs st name r
    unlessHalted (settle fs st step name) r

/--
The processing after an answer to the subscription of shows slot `slot`. A rejection that blames the caller is the
screen's fault (Fault.rejectedShows). Any other rejection, such as unavailable, keeps the shown value, as HTTP's
stale-if-error (RFC 5861) serves the last good response while the origin fails. A shows writes no `onRejected` for it,
unlike `sends` and automations, because a slot has no transition to choose, so keeping the value is the only behavior
that an `onRejected` could name.
-/
def showAnswer (st : Service) (name : InstanceId) (slot : String) (answer : Answer) (r : Processing) : Processing :=
  let s := match answer with
    | .rejected rejection =>
      if RejectionKind.byCaller rejection.kind then
        r.state.report (.fault (.rejectedShows (st.ref name.chart) slot rejection))
      else r.state
    | _ => r.state
  let s := match answer with
    | .fulfilled output => s.setShown name slot output
    | _ => s
  ⟨s, r.queue⟩

def answerTo (st : Service) (step : Nat) (activity : Activity) (answer : Answer) : Requester → Processing → m Processing
  | .state name state => handle fs st step name state activity answer
  | .slot name slot => fun r => do
    if answer matches .fulfilled _ && (r.state.machine? name).isSome then
      MonadNote.note (.wroteShown name slot)
    pure (showAnswer st name slot answer r)
  | .automation a => fun r => pure ⟨automationAnswer st a answer r.state, r.queue⟩

def deliverAnswer (st : Service) (step : Nat) (p : Pending) (answer : Answer) (r : Processing) : m Processing :=
  let (s, live) := r.state.answered p
  let r : Processing := ⟨s, r.queue⟩
  if live then answerTo fs st step p.activity answer p.requester r else pure r

end

def Work.settledMachine? : Work → Option InstanceId
  | .receive name _ _ _ | .onDone name _ | .opensDone name _ _ _ _ _ => some name
  | .answered c _ _ => c.requester.machine?
  | .start _ _ | .reaction .. => none

def workBody [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (step : Nat) : Work → Processing → m Processing
  | .reaction _ [] _ _, r | .reaction _ ([] :: _) _ _, r => pure r
  | .reaction a ((e :: _) :: _) _ _, ⟨s, q⟩ => do
    let faulted (issue : Issue) : Processing :=
      ⟨s.report (.fault (issueViolation (st.ref a.name) issue fun _ => .inputSchema (st.ref a.name) a.sends.ref)), q⟩
    let definition := st.ref a.name
    MonadNote.note (.reached (.automation definition))
    let bound (b : String) := do
      let r ← fs.automationBinding a.name b e.payload s.records s.now
      if let .ok v := r then
        MonadNote.note (.reached (if v then .automationBindingValue definition b else .automationBindingNull definition b))
      pure r
    let met (c : String) := do
      let r ← fs.automationGuard a.name c e.payload s.records s.now
      if let .ok v := r then MonadNote.note (.reached (.automationGuard definition c v))
      pure r
    match ← firstFalse bound a.binds with
    | .error issue => pure (faulted issue)
    | .ok (some _) => pure ⟨s, q⟩
    | .ok none =>
    match ← firstFalse met a.guard with
    | .error issue => pure (faulted issue)
    | .ok (some _) => pure ⟨s, q⟩
    | .ok none =>
    match ← fs.react a.name e.payload s.records s.now s.nextKeys with
    | .error issue => pure (faulted issue)
    | .ok (input, keys) =>
      let s := s.createKeys keys
      if a.sends.isOwn st.service then
        pure ⟨s, { q with round := q.round ++ [{ order := a.order, requester := .automation a.name, activity := a.sends,
                                                  serial := none, input, cause := step }] }⟩
      else do
        MonadNote.note (.reached (.request a.sends.ref))
        pure ⟨s.await (.command a.sends.ref input) (.automation a.name) a.sends input, q⟩
  | .answered c answer _, ⟨s, q⟩ => do
    -- Whether the Queued is stale depends on whether the machine left the sending state, which matters only when the
    -- answer has a transition to take.
    if let .state name state := c.requester then
      if (s.machine? name).any fun i => !(i.answerTransitions state c.activity answer).isEmpty then
        MonadNote.note (.readStates [(name, state)])
    let (s, live) := match c.serial with
      | some serial => s.takeQueued serial
      | none => (s, true)
    match rejectedInput? st c.requester.sender c.activity.ref answer with
    | some fault => pure ⟨s.report (.fault fault), q⟩
    | none => if live then answerTo fs st step c.activity answer c.requester ⟨s, q⟩ else pure ⟨s, q⟩
  | .start name _, r => startWork fs st step name r
  | .receive name received _ _, r => receiveWork fs st step name received r
  | .onDone name _, r => doneWork fs st step name Limit.onDoneSelections.max r
  | .opensDone name state key output serial _, ⟨s, q⟩ => do
    let (s, live) := s.takeQueued serial
    MonadNote.note (.readStates [(name, state)])
    if !live then pure ⟨s, q⟩ else
    withMachine name (fun i r =>
      applyCompletion fs st step name (i.chart.transitionsAt (some state) (.opens key)) (.output output) r)
      ⟨s, q⟩

def runWork [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (s : State) (q : Queue) (step : Nat) (w : Work) :
    m Processing :=
  settled fs st step w.settledMachine? (workBody st fs step w) ⟨s, q⟩

def shownChanged (before after : State) : List InstanceId :=
  (after.machines.filter fun i => (before.machine? i.id).any (·.shown != i.shown)).map (·.id)

/--
The processing after a step that settles screen `name` once its `shown` changed. The step only evaluates always
transitions, like the step after a record change, and is a barrier, like the step that sends activities. Reconciling
subscriptions that change `shown` is not a step, so the step has no cause.
-/
def settleScreen [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (name : InstanceId) (r : Processing) :
    m Processing :=
  if r.halted then pure r else do
  let (s, step) := r.state.newStep .root (barrier := true)
  MonadNote.note (.stepBegins step (.always name) none)
  let r ← settle fs st step name ⟨s, r.queue⟩
  MonadNote.note .stepEnds
  pure r

def drain [Monad m] [MonadNote m] (st : Service) (fs : Functions m) (fuel : Nat) (s : State) (q : Queue) : m State :=
  if s.halted.isSome then pure s else
  match fuel with
  | 0 =>
    if !q.isEmpty then pure (s.report (.fault (.exceededMessageWork Limit.messageWork.max))) else do
    let refreshed ← refreshScreens st fs s
    pure (if refreshed.halted.isNone && !(shownChanged s refreshed).isEmpty then
      refreshed.report (.fault (.exceededMessageWork Limit.messageWork.max)) else refreshed)
  | fuel + 1 =>
    match q.take Ready.name s.stepOrder with
    | .error invalid => pure (s.report (.invalidInput invalid))
    | .ok (some (.work w, i, rest, stepOrder)) => do
      let (s, step) := { s with stepOrder }.newStep w.origin
      MonadNote.note (.stepBegins step w.name w.started)
      let r ← runWork st fs s (rest.putBack i (w.rest step)) step w
      MonadNote.note .stepEnds
      drain st fs fuel r.state r.queue
    | .ok (some (.command c, _, rest, stepOrder)) => do
      let ((s, step), runaway) := { s with stepOrder }.newCommandStep c.cause (st.ref c.requester.sender)
      match runaway with
      | some exceeded => pure (s.report (.fault exceeded))
      | none =>
        MonadNote.note (.stepBegins step (Ready.command c).name none)
        let pc ← processCommand st fs s c.activity.ref.name c.input none step
        MonadNote.note .stepEnds
        drain st fs fuel pc.1
          { rest with tasks := rest.tasks ++ commandWork st pc.1 pc.2.2 step ++ [.answered c pc.2.1 step] }
    | .ok none =>
      if !q.entered.isEmpty then do
        let r ← sendEntered fs st ⟨s, q⟩
        drain st fs fuel r.state r.queue
      else do
        let refreshed ← refreshScreens st fs s
        let screens := shownChanged s refreshed
        if screens.isEmpty then pure refreshed else do
        let r ← screens.foldlM (fun r name => settleScreen st fs name r) ⟨refreshed, q⟩
        drain st fs fuel r.state r.queue

end Tazuna.Service
