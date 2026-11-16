import Tazuna.Service.Functions
import Tazuna.Service.Idempotency
import Tazuna.Service.Chart.Config
import Tazuna.Service.Note

namespace Tazuna.Semantics

open Tazuna.Data

/-- The opener of a screen. `parent` is the resource of the instance that opened the screen. -/
structure Opener where
  parent : String
  state : String
  key : String
  modal : Bool
deriving DecidableEq, Repr, Inhabited

/--
The origin of a copy. `owner` is the resource of the owner instance, and `encodedKey` is the canonicalJson of `key`.
-/
structure CopyOf where
  owner : String
  map : String
  key : Value
  encodedKey : String
deriving DecidableEq, Repr, Inhabited

def copyName (owner map key : String) : String := s!"{owner}@{map}[{key}]"

/--
An instance of a machine or screen. A machine, or a screen that no other screen opens, has one instance per definition;
`opens` creates an instance each time it opens.
-/
structure Instance where
  chart : Chart
  resource : String
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
  copyOf : Option CopyOf := none
  copyKeys : List (String × List String) := []
deriving Repr, Inhabited

/--
An `after` deadline of an active state. `order` is the creation order. An `at` deadline has no time until computed.
-/
structure Deadline where
  time : Option Time
  fromAt : Bool := false
  order : Nat
  machine : String
  state : String
  name : String
deriving DecidableEq, Repr, Inhabited

def Deadline.id (t : Deadline) : DeadlineId := { «instance» := t.machine, state := t.state, name := t.name }

inductive Requester where
  /-- The machine `machine`, which sent the request on entering `state`. -/
  | state (machine state : String)
  /-- The screen `machine`, which subscribed the query of shows slot `slot`; answers keep coming until it ends. -/
  | slot (machine slot : String)
  | automation (name : String)
deriving DecidableEq, Repr, Inhabited

/-- The instance or automation that sent the request. -/
def Requester.sender : Requester → String
  | .state m _ | .slot m _ => m
  | .automation a => a

def Requester.machine? : Requester → Option String
  | .state m _ | .slot m _ => some m
  | .automation _ => none

def Requester.slot? : Requester → Option String
  | .slot _ k => some k
  | _ => none

/--
A request with a request line, awaiting an answer. `stale` is whether the sending state was exited or the
subscription ended. A stale request still awaits an answer, but its sender ignores it, as SCXML ignores events from a
cancelled invoke.
-/
structure Pending where
  id : String
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
  machine : String
  state : String
  stale : Bool := false
deriving DecidableEq, Repr, Inhabited

/--
A step of a run. `cause` is the step that caused this one, or none for input and deadline steps. `message` is the
message number, inherited from the cause. `command` is whether the step processes an own-service command. `barrier` is
whether the step comes after every earlier step of the same message and before every later one. `nested` is whether
the step began while its cause was running (a copy start), so that it ends before its cause does.
-/
structure StepInfo where
  cause : Option Nat
  message : Nat
  command : Bool := false
  barrier : Bool := false
  nested : Bool := false
deriving DecidableEq, Repr, Inhabited

/--
An open subscription. `input` is as the scenario gave it, and `last` is the comparable value of the last answer sent.
-/
structure Subscription where
  id : String
  query : String
  input : Value
  last : Option Value := none
deriving DecidableEq, Repr, Inhabited

/-- A recorded acceptance of an external command, and the result events received so far. -/
structure Accepted where
  id : String
  activity : Activity
  input : Value
  output : Option Value
  events : List Emit := []
deriving DecidableEq, Repr, Inhabited

/-- The state of a run between messages, when the internal queue is empty. -/
structure State where
  now : Time := 0
  /-- Whether service processing started, which it does at the first input and at each restart. -/
  started : Bool := false
  records : Records := []
  commandAnswers : CommandAnswers := []
  eventDeliveries : EventDeliveries := []
  /-- The machine and screen instances in creation order. -/
  machines : List Instance := []
  copies : List Instance := []
  /-- The open screen resources in opening order. -/
  stack : List String := []
  deadlines : List Deadline := []
  deadlineCount : Nat := 0
  /-- The current input's `deadlineOrder`, which its `in` line carries. -/
  inputDeadlineOrder : List DeadlineId := []
  /-- The entries of the current input's `deadlineOrder` that no tie has used yet. -/
  deadlineOrder : List DeadlineId := []
  /-- The entries of the current input's `stepOrder` that the internal queue has not used yet. -/
  stepOrder : List StepName := []
  /-- The pending requests in sending order. -/
  pending : List Pending := []
  queued : List Queued := []
  serial : Nat := 0
  /-- The number of the next request to start waiting. -/
  turn : Nat := 0
  lines : Array Line := #[]
  steps : Array StepInfo := #[]
  /-- The number of messages begun; messages are numbered from 1. -/
  messageCount : Nat := 0
  /-- The createKey values with their entity, in creation order. -/
  created : List (String × String) := []
  /-- The names of the current input's `keys` that createKey has not returned yet, by entity. -/
  keyNames : List (String × List String) := []
  /-- The subscriptions that other services opened, in opening order. -/
  subscriptions : List Subscription := []
  results : List Accepted := []
  /-- The processed mocks that have a handle, latest first: the handle, the request answered, and the answer. -/
  mocks : List (String × Pending × Answer) := []
  /-- The processed subscribe inputs that have a handle, latest first: the handle and the subscription's id. -/
  subscribed : List (String × String) := []
  violations : List Violation := []
  /-- The halting violation; after it, no input changes the state. -/
  halted : Option Violation := none
deriving Repr, Inhabited

def namedCount (lines : Array Line) (name : String) : Nat := lines.countP (·.body.idName == name)

def State.lineId (s : State) (givenId : Option String) (name : String) : String :=
  givenId.getD s!"{name}#{namedCount s.lines name + 1}"

def State.write (s : State) (dir : Dir) (givenId : Option String) (body : LineBody) : State × String :=
  let id := s.lineId givenId body.idName
  ({ s with lines := s.lines.push { time := s.now, dir, id, body } }, id)

/-- The state with the `in` line of the current input written, with the input's `deadlineOrder`, and the line's id. -/
def State.writeInput (s : State) (givenId : Option String) (body : LineBody) : State × String :=
  let id := s.lineId givenId body.idName
  ({ s with lines := s.lines.push { time := s.now, dir := .in, id, body, deadlineOrder := s.inputDeadlineOrder } }, id)

def State.await (s : State) (body : LineBody) (requester : Requester) (activity : Activity) (input : Value) : State :=
  let (s, id) := s.write .out none body
  { s with turn := s.turn + 1, pending := s.pending ++ [{ id, activity, requester, input, turn := s.turn }] }

def State.keyCount (s : State) (entity : String) : Nat := (s.created.filter (·.1 == entity)).length

/--
What createKey returns next for each entity that has a createKey value or a name left: the names left, in order, and
after them `<entity>-<n>` for the entity's `n`-th createKey value.
-/
def State.nextKeys (s : State) : List (String × NextKeys) :=
  (s.created.map (·.1) ++ s.keyNames.map (·.1)).eraseDups.map fun e =>
    (e, { count := s.keyCount e, names := (s.keyNames.lookup e).getD [] })

def State.createKeys (s : State) (entities : List String) : State :=
  { s with created := s.created ++ givenKeys s.nextKeys entities,
           keyNames := s.keyNames.map fun (e, names) => (e, names.drop (entities.count e)) }

def State.newMessage (s : State) : State := { s with messageCount := s.messageCount + 1 }

def State.newStep (s : State) (cause : Option Nat) (barrier := false) (nested := false) : State × Nat :=
  let message := match cause.bind (s.steps[·]?) with
    | some c => c.message
    | none => s.messageCount
  let step := s.steps.size
  ({ s with steps := s.steps.push { cause, message, barrier, nested } }, step)

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
def State.newCommandStep (s : State) (cause : Nat) (sender : Syntax.Ref) : (State × Nat) × Option Fault :=
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

def Service.failedEnsures (st : Service) (name c : String) : Fault := .failedEnsures (st.ref name) c

def State.violate (s : State) (v : Violation) : State :=
  { s with violations := s.violations ++ [v] }

def State.halt (s : State) (v : Violation) : State :=
  { s with halted := some v }

def State.report (s : State) (f : Finding) : State :=
  if f.halts then s.halt f.toViolation else s.violate f.toViolation

def State.reportAll (s : State) (reports : List Fault) : State :=
  reports.foldl (fun s fault => if s.halted.isSome then s else s.report (.fault fault)) s

/-- The state with the answer line to `to` written. An own-service command has no id and writes no answer line. -/
def State.answer (s : State) (to : Option String) (answer : Answer) : State :=
  match to with
  | some to => (s.write .out none (.answer to answer)).1
  | none => s

/-- The state with the event lines of `emits` written, each the result of the request `resultOf`. -/
def State.emitAll (s : State) (resultOf : Option String) (emits : List Emit) : State :=
  emits.foldl (fun s e => (s.write .out none (.event e.event e.payload resultOf)).1) s

def State.machine? (s : State) (name : String) : Option Instance :=
  (s.machines ++ s.copies).find? (·.resource == name)

def State.chartName (s : State) (name : String) : String := ((s.machine? name).map (·.chart.name)).getD name

/-- The chart or automation that a mock's `sender` names. -/
def State.senderOf (s : State) : Requester → String
  | .state m _ | .slot m _ => s.chartName m
  | .automation a => a

def State.setMachine (s : State) (name : String) (f : Instance → Instance) : State :=
  { s with machines := s.machines.map (fun i => if i.resource == name then f i else i),
           copies := s.copies.map (fun i => if i.resource == name then f i else i) }

def Instance.isIn (i : Instance) (n : String) : Bool := i.entered.any (·.1 == n)

def Instance.active (i : Instance) : List String := i.entered.map (·.1)

/-- The depth of the states that a copy enters and exits: the length of the map state's path, or 0 for a non-copy. -/
def Instance.depth (i : Instance) : Nat :=
  match i.copyOf with
  | some c => (i.chart.tree.pathOf c.map).length
  | none => 0

def Instance.copyKeysOf (i : Instance) (map : String) : List String := (i.copyKeys.lookup map).getD []

def Instance.copyResources (i : Instance) : List String := i.copyKeys.flatMap fun c => c.2.map (copyName i.resource c.1)

def Instance.documentOrder (i : Instance) : List (String × String) :=
  let tree := i.chart.tree
  i.chart.states.flatMap fun cs =>
    (i.resource, cs.name) :: (i.copyKeysOf cs.name).flatMap fun k => (tree.descendants cs.name).map (copyName i.resource cs.name k, ·)

def Instance.who (i : Instance) (st : Service) : Who :=
  { chart := st.ref i.chart.name, copy := i.copyOf.map fun c => { map := c.map, itemKey := c.key } }

def State.who (s : State) (st : Service) (resource : String) : Who :=
  match s.machine? resource with
  | some i => i.who st
  | none => { chart := st.ref resource }

/-- The scope of instance `i` at `state`. A copy's expressions also read the owner's context, shown, and input. -/
def State.scopeOf (s : State) (i : Instance) (state : Option String) : Scope :=
  match i.copyOf.bind fun c => (s.machine? c.owner).map (c, ·) with
  | some (c, o) =>
    { machine := i.chart.name, resource := i.resource, owner := o.resource, state, context := o.context,
      copy := some { map := c.map, key := c.key, context := i.context }, active := i.active ++ o.active,
      shown := o.shown, input := o.input, now := s.now }
  | none =>
    { machine := i.chart.name, resource := i.resource, owner := i.resource, state, context := i.context, active := i.active,
      shown := i.shown, input := i.input, now := s.now }

def State.ownerOf (s : State) (name : String) : String :=
  match (s.machine? name).bind (·.copyOf) with
  | some c => c.owner
  | none => name

def State.running (s : State) : List Instance :=
  s.machines.flatMap fun i => i :: i.copyResources.filterMap fun c => s.copies.find? (·.resource == c)

/--
The state with slot `slot` of `owner` shown as `value`. Copies read the owner's `shown`, so it is written to the owner.
-/
def State.setShown (s : State) (owner slot : String) (value : Value) : State :=
  s.setMachine owner fun i => { i with shown := i.shown.map fun (k, v) => if k == slot then (k, value) else (k, v) }

def State.removeFromStack (s : State) (name : String) : State := { s with stack := s.stack.filter (· != name) }

def State.startQueued (s : State) (machine state : String) : State × Nat :=
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

end Tazuna.Semantics
