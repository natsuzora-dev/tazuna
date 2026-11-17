import Tazuna.Service.State

/-! The internal queue of one message: work caused by steps, and commands sent to its own service. -/

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/--
A command that a service sends to itself. `order` is the rank of the sender definition, `cause` is the sending step,
and `serial` is the serial of the `Queued` that awaits the answer when a machine sent the command.
-/
structure Sent where
  order : Nat
  requester : Requester
  activity : Activity
  serial : Option Nat
  input : Value
  cause : Nat
deriving Repr, Inhabited

/-- Work that the step `cause` caused. -/
inductive Work where
  | reaction (automation : Automation) (event : Emit) (cause : Nat)
  | answered (sent : Sent) (answer : Answer) (cause : Nat)
  /--
  The start of a machine or screen in its initial state. A screen that `opens` opened has the opening step as `cause`.
  -/
  | start (machine : InstanceId) (cause : Option Nat)
  /--
  An evaluation of a machine. `received` holds the key and payload of each matching `receives`, and is empty when only
  records changed.
  -/
  | receive (machine : InstanceId) (received : List (String × Value)) (cause : Nat)
  | onDone (machine : InstanceId) (cause : Nat)
  /-- The close in a final state of a screen that `opens` opened; the opener takes the `onDone` of its `opens`. -/
  | opensDone (machine : InstanceId) (state key : String) (output : Value) (serial : Nat) (cause : Nat)
deriving Repr, Inhabited

/--
The pending work of one message. `entered` holds each state with calls, sends, shows, or opens that the message entered,
as instance, state, and entering step.
-/
structure Queue where
  tasks : List Work := []
  round : List Sent := []
  commands : List Sent := []
  entered : List (InstanceId × String × Nat) := []
deriving Repr, Inhabited

def Queue.isEmpty (q : Queue) : Bool :=
  q.tasks.isEmpty && q.round.isEmpty && q.commands.isEmpty && q.entered.isEmpty

def Queue.enter (q : Queue) (name : InstanceId) (n : String) (step : Nat) : Queue :=
  { q with entered := q.entered.filter (fun e => !(e.1 == name && e.2.1 == n)) ++ [(name, n, step)] }

/-- The commands sorted by the rank of their sender definition; commands of equal rank keep their sending order. -/
def sortSent : List Sent → List Sent
  | [] => []
  | c :: cs => insert c (sortSent cs)
where
  insert (c : Sent) : List Sent → List Sent
    | [] => [c]
    | d :: ds => if c.order ≤ d.order then c :: d :: ds else d :: insert c ds

/-- Work or an own-service command that the internal queue can take next. -/
inductive Ready where
  | work (w : Work)
  | command (c : Sent)
deriving Repr, Inhabited

/--
What the queue can take next, in queue order: the tasks in arrival order, then the commands, with the round joined to
them in sender-definition order.
-/
def Queue.ready (q : Queue) : List Ready := q.tasks.map .work ++ (q.commands ++ sortSent q.round).map .command

/-- The queue without the entry at position `i` of `ready`. Taking a command joins the round to the commands. -/
def Queue.without (q : Queue) (i : Nat) : Queue :=
  if i < q.tasks.length then { q with tasks := q.tasks.eraseIdx i }
  else { q with commands := (q.commands ++ sortSent q.round).eraseIdx (i - q.tasks.length), round := [] }

/--
The entry that the queue takes next, the queue without it, and the entries of `stepOrder` left; none when nothing is
ready. While entries remain, it is the first ready one that the next entry names (`name` names each); otherwise it is
the first in queue order. An entry that names a deadline is for a tie of deadlines after the message (chooseDeadline),
so until then the queue takes the first in queue order and keeps the entry.
-/
def Queue.take (q : Queue) (name : Ready → StepName) : List StepName →
    Except InvalidInput (Option (Ready × Queue × List StepName))
  | [] =>
    match q.tasks with
    | w :: ws => .ok (some (.work w, { q with tasks := ws }, []))
    | [] =>
      match q.commands ++ sortSent q.round with
      | c :: cs => .ok (some (.command c, { q with commands := cs, round := [] }, []))
      | [] => .ok none
  | named :: rest =>
    match q.ready with
    | [] => .ok none
    | first :: others =>
      match (first :: others).zipIdx.find? (name ·.1 == named) with
      | some (r, i) => .ok (some (r, q.without i, rest))
      | none =>
        if named.isDeadline then .ok (some (first, q.without 0, named :: rest))
        else .error (.unreadyStep named ((first :: others).map name))

structure Processing where
  state : State
  queue : Queue
deriving Repr, Inhabited

def Processing.halted (r : Processing) : Bool := r.state.halted.isSome

def Processing.report (r : Processing) (f : Finding) : Processing :=
  ⟨r.state.report f, r.queue⟩

def unlessHalted [Monad m] (f : Processing → m Processing) (r : Processing) : m Processing :=
  if r.halted then pure r else f r

def withMachine [Monad m] (name : InstanceId) (f : Instance → Processing → m Processing) (r : Processing) : m Processing :=
  if r.halted then pure r else
  match r.state.machine? name with
  | some i => f i r
  | none => pure r

/-- The evaluation work of instance `i`. A record change alone also causes it, since always guards may read records. -/
def machineWork (emits : List Emit) (recordsChanged : Bool) (cause : Nat) (i : Instance) : Option Work :=
  let received := emits.flatMap fun e => (i.chart.receives.filter (·.2 == e.event)).map fun r => (r.1, e.payload)
  if i.closed || (received.isEmpty && !recordsChanged) then none else some (.receive i.id received cause)

/--
The work that the events `emits` cause. Copies get no work, since they move with their owner's evaluation.
-/
def reactions (st : Service) (s : State) (emits : List Emit) (recordsChanged : Bool) (cause : Nat) : List Work :=
  s.machines.filterMap (machineWork emits recordsChanged cause) ++
  emits.flatMap fun e => (st.automations.filter (·.receives == e.event)).map (.reaction · e cause)

/-- The work that a command's events cause. Writing an event counts as a record change. -/
def commandWork (st : Service) (s : State) (emits : List Emit) (cause : Nat) : List Work :=
  if emits.isEmpty then [] else reactions st s emits true cause

end Tazuna.Service
