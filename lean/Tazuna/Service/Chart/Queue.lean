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
  An evaluation of a machine. `groups` holds the key and payload of each matching `receives`, in the groups of the
  events, and is empty when only records changed. One step takes one event; the next group waits for the current one.
  -/
  | receive (machine : InstanceId) (groups : List (List (String × Value))) (cause : Nat)
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
The ways to take work `w`: a receive work takes any event of its first group first, since a group has no order. The
first way is `w` itself.
-/
def Work.choices : Work → List Work
  | .receive machine ((e :: g) :: gs) cause =>
    .receive machine ((e :: g) :: gs) cause :: (List.range g.length).filterMap fun k =>
      g[k]?.map fun x => .receive machine ((x :: e :: g.eraseIdx k) :: gs) cause
  | w => [w]

/--
The work left after the step `step` took the first event of `w`: the rest of its group with the same cause, or else the
next group, which the step causes. None for other work.
-/
def Work.rest (step : Nat) : Work → Option Work
  | .receive machine ((_ :: e :: g) :: gs) cause => some (.receive machine ((e :: g) :: gs) cause)
  | .receive machine ([_] :: g :: gs) _ => some (.receive machine (g :: gs) step)
  | _ => none

/--
What the queue can take next, in queue order, each with the position of its task or command: the ways to take the
tasks in arrival order, then the commands, with the round joined to them in sender-definition order.
-/
def Queue.entries (q : Queue) : List (Ready × Nat) :=
  (q.tasks.zipIdx.flatMap fun (w, i) => w.choices.map (.work ·, i)) ++
    (q.commands ++ sortSent q.round).zipIdx.map fun (c, j) => (.command c, q.tasks.length + j)

def Queue.ready (q : Queue) : List Ready := q.entries.map (·.1)

/-- The queue without the task or command at position `i`. Taking a command joins the round to the commands. -/
def Queue.without (q : Queue) (i : Nat) : Queue :=
  if i < q.tasks.length then { q with tasks := q.tasks.eraseIdx i }
  else { q with commands := (q.commands ++ sortSent q.round).eraseIdx (i - q.tasks.length), round := [] }

/-- The queue with the work left `w` back at task position `i`. -/
def Queue.putBack (q : Queue) (i : Nat) : Option Work → Queue
  | some w => { q with tasks := q.tasks.insertIdx i w }
  | none => q

/--
The entry that the queue takes next, its position, the queue without it, and the entries of `stepOrder` left; none when
nothing is ready. While entries remain, it is the first ready one that the next entry names (`name` names each);
otherwise it is the first in queue order. An entry that names a deadline is for a tie of deadlines after the message
(chooseDeadline), so until then the queue takes the first in queue order and keeps the entry.
-/
def Queue.take (q : Queue) (name : Ready → StepName) : List StepName →
    Except InvalidInput (Option (Ready × Nat × Queue × List StepName))
  | [] =>
    match q.entries with
    | (r, i) :: _ => .ok (some (r, i, q.without i, []))
    | [] => .ok none
  | named :: rest =>
    match q.entries with
    | [] => .ok none
    | (first, p) :: others =>
      match ((first, p) :: others).find? (name ·.1 == named) with
      | some (r, i) => .ok (some (r, i, q.without i, rest))
      | none =>
        if named.isDeadline then .ok (some (first, p, q.without p, named :: rest))
        else .error (.unreadyStep named (((first, p) :: others).map (name ·.1)))

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
def machineWork (groups : List (List Emit)) (recordsChanged : Bool) (cause : Nat) (i : Instance) : Option Work :=
  let received := (groups.map fun g => g.flatMap fun e =>
    (i.chart.receives.filter (·.2 == e.event)).map fun r => (r.1, e.payload)).filter (!·.isEmpty)
  if i.closed || (received.isEmpty && !recordsChanged) then none else some (.receive i.id received cause)

/--
The work that the groups of events `groups` cause. Copies get no work, since they move with their owner's evaluation.
-/
def reactions (st : Service) (s : State) (groups : List (List Emit)) (recordsChanged : Bool) (cause : Nat) :
    List Work :=
  s.machines.filterMap (machineWork groups recordsChanged cause) ++
  groups.flatten.flatMap fun e => (st.automations.filter (·.receives == e.event)).map (.reaction · e cause)

/-- The work that a command's groups of events cause. Writing an event counts as a record change. -/
def commandWork (st : Service) (s : State) (groups : List (List Emit)) (cause : Nat) : List Work :=
  if groups.flatten.isEmpty then [] else reactions st s groups true cause

end Tazuna.Service
