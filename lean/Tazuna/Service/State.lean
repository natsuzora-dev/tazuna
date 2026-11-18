import Tazuna.Service.Functions
import Tazuna.Service.Idempotency
import Tazuna.Service.Chart.Config
import Tazuna.Service.Note
import Tazuna.Service.Instance

namespace Tazuna.Service

open Tazuna.Data

/-- The opener of a screen: the instance `parent` that opened it. -/
structure Opener where
  parent : InstanceId
  state : String
  key : String
  modal : Bool
deriving DecidableEq, Repr, Inhabited

/--
An instance of a machine or screen. A machine, or a screen that no other screen opens, has one instance per definition;
`opens` creates an instance each time it opens.
-/
structure Instance where
  chart : Chart
  id : InstanceId
  context : Value
  input : Value := .obj []
  /-- The active states and their entry times, in entry order. -/
  entered : List (String × Time) := []
  /-- The children of each parent that were active when the parent was last exited. -/
  lastChildren : List (String × List String) := []
  /-- Whether the instance entered a root final state and stopped. -/
  closed : Bool := false
  /-- The finished states awaiting onDone, in finishing order; `some` from queuing the onDone work until it finishes. -/
  awaitingOnDone : Option (List String) := none
  /-- The output of the last fulfilled answer of each shows slot, or null before any. -/
  shown : List (String × Value) := []
  opener : Option Opener := none
  /-- The decoded item key of a copy; the map state and the canonical key are in `id`. -/
  itemKey : Option Value := none
  copyKeys : List (String × List Value) := []
deriving Repr, Inhabited

/--
An `after` deadline of an active state. `order` is the creation order. An `at` deadline has no time until computed.
-/
structure Deadline where
  time : Option Time
  fromAt : Bool := false
  order : Nat
  machine : InstanceId
  state : String
  name : String
  /-- The step that entered `state`, which armed the deadline. -/
  armedBy : Nat
  /-- The last message after which rearm changed `time` by reading what steps write, or none when it read nothing. -/
  timedIn : Option Nat := none
deriving DecidableEq, Repr, Inhabited

/--
A request with a request line, awaiting an answer. `stale` is whether the sending state was exited or the
subscription ended. A stale request still awaits an answer, but its sender ignores it, as SCXML ignores events from a
cancelled invoke.
-/
structure Pending where
  id : LineId
  activity : Activity
  requester : Requester
  input : Value
  stale : Bool := false
  /-- The order in which waiting began; a subscription waits again after each answer. -/
  turn : Nat
deriving DecidableEq, Repr, Inhabited

/--
Work that a state began and that awaits the internal queue: the answer to an own-service command that a machine sent,
or the opens onDone after the opened screen closed. `serial` is the start order. `stale`, as in Pending, is whether the
starting state was exited.
-/
structure Queued where
  serial : Nat
  machine : InstanceId
  state : String
  stale : Bool := false
deriving DecidableEq, Repr, Inhabited

/--
A tie of steps that no cause orders, which test's search takes in every order: the deadlines of a service due at one
time, or the messages that one line delivers to the service, the first of which arrived in step `first`.
-/
inductive Tie where
  | deadlines (time : Time)
  | arrivals (first : Nat)
deriving DecidableEq, Repr, Inhabited

/--
A step of a run. `cause` is the step that caused this one, or none for input and deadline steps. `armedBy` is, for a
deadline step, the step that armed the deadline, which caused it as `cause` does but in an earlier message, and
`timedIn` the message whose end last changed the deadline's time by reading what steps write (see `Sim.causes`). `message`
is the message number, inherited from the cause. `command` is whether the step processes an own-service command. `barrier` is
whether the step comes after every earlier step of the same message and before every later one. `nested` is whether
the step began while its cause was running (a copy start), so that it ends before its cause does. `tie` is, for a
deadline step or the step in which a message of a tie arrives, its tie.
-/
structure StepInfo where
  cause : Option Nat
  armedBy : Option Nat := none
  timedIn : Option Nat := none
  message : Nat
  command : Bool := false
  barrier : Bool := false
  nested : Bool := false
  tie : Option Tie := none
deriving DecidableEq, Repr, Inhabited

/--
An open subscription. `input` is as the scenario gave it, and `last` is the comparable value of the last answer sent.
-/
structure Subscription where
  id : LineId
  query : String
  input : Value
  last : Option Value := none
deriving DecidableEq, Repr, Inhabited

/-- The part of the state that the service persists; a restart keeps it, as in the Raft TLA+ spec's Restart. -/
structure Durable where
  records : Records := []
  commandAnswers : CommandAnswers := []
  /-- The ids of the events and answers that arrived; one that arrives again is not processed again. -/
  deliveries : List LineId := []
  /-- The entities that createKey was called for, in call order; State.created derives the values from them. -/
  createdEntities : List String := []
  /-- The service whose state this is, which qualifies its createKey values (Keys) and names its line ids. -/
  service : String
deriving Repr, Inhabited

/-- The part of the state that lives in the service process's memory; a restart drops it. -/
structure Process where
  /-- Whether service processing started, which it does at the first input and at each restart. -/
  started : Bool := false
  /-- The machine and screen instances in creation order. -/
  machines : List Instance := []
  copies : List Instance := []
  /-- The open screens in opening order. -/
  stack : List InstanceId := []
  deadlines : List Deadline := []
  /-- The pending requests in sending order. -/
  pending : List Pending := []
  queued : List Queued := []
  /-- The subscriptions that other services opened, in opening order. -/
  subscriptions : List Subscription := []
deriving Repr, Inhabited

/-- The state of a run between messages, when the internal queue is empty. -/
structure State extends Durable, Process where
  now : Time := 0
  deadlineCount : Nat := 0
  /-- The entries of the current input's `stepOrder` that the internal queue has not used yet. -/
  stepOrder : List StepName := []
  serial : Nat := 0
  /-- The number of the next request to start waiting. -/
  turn : Nat := 0
  lines : Array Line := #[]
  steps : Array StepInfo := #[]
  /-- The number of messages begun; messages are numbered from 1. -/
  messageCount : Nat := 0
  violations : List Finding := []
  /-- The halting finding; after it, no input changes the state. -/
  halted : Option Finding := none
deriving Repr, Inhabited

def namedCount (service : String) (lines : Array Line) (name : String) : Nat :=
  lines.countP (·.body.idName service == name)

def State.lineId (s : State) (givenId : Option LineId) (name : String) : LineId :=
  givenId.getD (.own s!"{name}#{namedCount s.service s.lines name + 1}")

def State.write (s : State) (dir : Dir) (givenId : Option LineId) (body : LineBody) (emitted : Option EmittedBy := none)
    (sender : SenderOf dir body := by exact ()) (request : RequestOf dir body := by exact ()) : State × LineId :=
  let id := s.lineId givenId (body.idName s.service)
  ({ s with lines := s.lines.push { time := s.now, dir, id, body, emitted, sender, request } }, id)

/-- The state after the request `body`, which `requester` sends, is written and awaits its answer. -/
def State.await (s : State) (body : LineBody) (requester : Requester) (activity : Activity) (input : Value) : State :=
  let (s, id) := s.write .out none body none (.given requester.sender .out body) (.given activity.ref .out body)
  { s with turn := s.turn + 1, pending := s.pending ++ [{ id, activity, requester, input, turn := s.turn }] }

/--
The createKey values with their entity, in creation order: the `n`-th value of an entity is `<entity>-<n>`, qualified by
the service. Deriving them from the entities alone keeps any two of them apart.
-/
def State.created (s : State) : List (String × String) := givenKeys { owner := some s.service } s.createdEntities

def State.keyCount (s : State) (entity : String) : Nat := (s.createdEntities.filter (· == entity)).length

/-- What createKey returns next for each entity that has a createKey value: its value after the entity's last one. -/
def State.nextKeys (s : State) : Keys :=
  { owner := some s.service, next := s.createdEntities.eraseDups.map fun e => (e, { count := s.keyCount e }) }

def State.createKeys (s : State) (entities : List String) : State :=
  { s with createdEntities := s.createdEntities ++ entities }

def State.newMessage (s : State) : State := { s with messageCount := s.messageCount + 1 }

def State.newStep (s : State) (cause : Option Nat) (barrier := false) (nested := false) (tie : Option Tie := none)
    (armedBy : Option Nat := none) (timedIn : Option Nat := none) (message : Option Nat := none) : State × Nat :=
  let message := message.getD (match cause.bind (s.steps[·]?) with
    | some c => c.message
    | none => s.messageCount)
  let step := s.steps.size
  ({ s with steps := s.steps.push { cause, armedBy, timedIn, message, barrier, nested, tie } }, step)

/-- The number of command steps in the cause chain of `step`, including `step`. -/
def State.commandDepth (s : State) (step : Nat) : Nat :=
  match s.steps[step]? with
  | some { cause, command, .. } =>
    (if command then 1 else 0) + match cause with
      | some c => if c < step then s.commandDepth c else 0
      | none => 0
  | none => 0
termination_by step

/--
The state with a new command step, and the fault of the exceeded limit, if any; `sender` is the definition of the
command's sender.
-/
def State.newCommandStep (s : State) (cause : Nat) (sender : Spec.Ref) : (State × Nat) × Option Fault :=
  let (s, step) := s.newStep (some cause)
  let info := s.steps[step]?
  let message := (info.map (·.message)).getD s.messageCount
  let s := { s with steps := s.steps.setIfInBounds step { (info.getD default) with command := true } }
  let depth := s.commandDepth step
  let count := s.steps.countP fun i => i.command && i.message == message
  ((s, step),
    if depth > Limit.commandDepth.max then some (.exceededCommandDepth sender Limit.commandDepth.max)
    else if count > Limit.messageCommands.max then some (.exceededMessageCommands sender Limit.messageCommands.max)
    else none)

def failedEnsures (st : Service) (name c : String) : Fault := .failedEnsures (st.ref name) c

def State.violate (s : State) (f : Finding) : State :=
  { s with violations := s.violations ++ [f] }

def State.halt (s : State) (f : Finding) : State :=
  { s with halted := some f }

def State.report (s : State) (f : Finding) : State :=
  if f.halts then s.halt f else s.violate f

def State.reportAll (s : State) (faults : List Fault) : State :=
  faults.foldl (fun s fault => if s.halted.isSome then s else s.report (.fault fault)) s

/--
The state with the answer line to the request `to` of `definition` written. An own-service command has no id and writes
no answer line.
-/
def State.answer (s : State) (to : Option LineId) (definition : Spec.Ref) (answer : Answer) : State :=
  match to with
  | some to => (s.write .out none (.answer to answer) none () definition).1
  | none => s

/-- Each event of `groups`, which step `step` decided, with the step and the place of its group. -/
def emittedBy (step : Nat) (groups : List (List Emit)) : List (Emit × EmittedBy) :=
  groups.zipIdx.flatMap fun (g, group) => g.map (·, { step, group })

/-- The state with the event lines of `emits` written, each the result of the request `resultOf`. -/
def State.emitAll (s : State) (resultOf : Option LineId) (emits : List (Emit × EmittedBy)) : State :=
  emits.foldl (fun s (e, w) => (s.write .out none (.event e.event e.payload resultOf) (some w)).1) s

def State.machine? (s : State) (id : InstanceId) : Option Instance :=
  (s.machines ++ s.copies).find? (·.id == id)

/--
The fault of `sender` when the receiver rejected its input to `target` as invalid. Only the receiver parses a message,
so the sender wrote an input that the receiver's schema does not take.
-/
def rejectedInput? (st : Service) (sender : String) (target : Spec.Ref) : Answer → Option Fault
  | .rejected { kind := .invalidInput, .. } => some (.inputSchema (st.ref sender) target)
  | _ => none

def State.setMachine (s : State) (id : InstanceId) (f : Instance → Instance) : State :=
  { s with machines := s.machines.map (fun i => if i.id == id then f i else i),
           copies := s.copies.map (fun i => if i.id == id then f i else i) }

def Instance.isIn (i : Instance) (n : String) : Bool := i.entered.any (·.1 == n)

def Instance.active (i : Instance) : List String := i.entered.map (·.1)

/-- The depth of the states that a copy enters and exits: the length of the map state's path, or 0 for a non-copy. -/
def Instance.depth (i : Instance) : Nat :=
  match i.id.map? with
  | some m => (i.chart.tree.pathOf m).length
  | none => 0

def Instance.copyKeysOf (i : Instance) (map : String) : List Value := (i.copyKeys.lookup map).getD []

def Instance.copyIds (i : Instance) : List InstanceId := i.copyKeys.flatMap fun c => c.2.map (.copy i.id c.1)

def Instance.documentOrder (i : Instance) : List (InstanceId × String) :=
  let tree := i.chart.tree
  i.chart.states.flatMap fun cs =>
    (i.id, cs.name) :: (i.copyKeysOf cs.name).flatMap fun k => (tree.descendants cs.name).map (.copy i.id cs.name k, ·)

/-- The scope of instance `i` at `state`. A copy's expressions also read the owner's context, shown, and input. -/
def State.scopeOf (s : State) (i : Instance) (state : Option String) : Scope :=
  match i.itemKey.bind fun k => (s.machine? i.id.owner).map (k, ·) with
  | some (key, o) =>
    { id := i.id, state, context := o.context, copy := some { key, context := i.context },
      active := i.active ++ o.active, shown := o.shown, input := o.input, now := s.now }
  | none =>
    { id := i.id, state, context := i.context, active := i.active, shown := i.shown, input := i.input, now := s.now }

def State.running (s : State) : List Instance :=
  s.machines.flatMap fun i => i :: i.copyIds.filterMap fun c => s.copies.find? (·.id == c)

/--
The state with slot `slot` of `owner` shown as `value`. Copies read the owner's `shown`, so it is written to the owner.
-/
def State.setShown (s : State) (owner : InstanceId) (slot : String) (value : Value) : State :=
  s.setMachine owner fun i => { i with shown := i.shown.map fun (k, v) => if k == slot then (k, value) else (k, v) }

def State.removeFromStack (s : State) (id : InstanceId) : State := { s with stack := s.stack.filter (· != id) }

def State.startQueued (s : State) (machine : InstanceId) (state : String) : State × Nat :=
  ({ s with serial := s.serial + 1, queued := s.queued ++ [{ serial := s.serial, machine, state }] }, s.serial)

/-- The state without the Queued `serial`, and whether it is not stale. -/
def State.takeQueued (s : State) (serial : Nat) : State × Bool :=
  ({ s with queued := s.queued.filter (·.serial != serial) }, (s.queued.find? (·.serial == serial)).any (!·.stale))

/-- The state after request `p` is answered, and whether the request is not stale. -/
def State.answered (s : State) (p : Pending) : State × Bool :=
  (if p.requester.slot?.isSome then
    { s with pending := s.pending.map (fun q => if q.id == p.id then { q with turn := s.turn } else q),
             turn := s.turn + 1 }
  else { s with pending := s.pending.filter (·.id != p.id) },
  (s.pending.find? (·.id == p.id)).any (!·.stale))

end Tazuna.Service
