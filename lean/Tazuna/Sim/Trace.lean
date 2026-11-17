import Tazuna.Service.Note
import Tazuna.Service.State
import Tazuna.Data.Trace

/-!
This module computes a snapshot line's `after`: every order that must hold among the lines of one window (between two
input lines).
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Service

/--
Whether step `earlier` leads to step `later`. Nested steps are spans of their outer step, so only steps that write
event lines are compared. Reachability between them follows the cause chain and barriers.
-/
def leadsTo (s : State) (earlier later : Nat) : Bool :=
  later == earlier ||
    (earlier < later && (s.steps[earlier]?.any (·.barrier)) &&
      (s.steps[earlier]?.map (·.message)) == (s.steps[later]?.map (·.message))) ||
    match s.steps[later]? with
    | some { cause, message, barrier, .. } =>
      (barrier && earlier < later && (s.steps[earlier]?.map (·.message)) == some message) ||
        match cause with
        | some cause => if cause < later then leadsTo s earlier cause else false
        | none => false
    | none => false
termination_by later

/--
The channel that an `out` line travels on, seen from its sender (Sim's Message.sameChannel, whose receiver a trace line
does not name): a request and its end travel to the request's receiver on the request's own channel, the answers to a
received request travel back to its sender, and events travel to their receivers on the channel of their `resultOf`,
or on the sender's channel when they name none. A line that no sender writes `out` travels on none.
-/
inductive Channel where
  | request (id : String)
  | answers (request : String)
  | events (resultOf : Option String)
deriving DecidableEq, Repr

def Channel.key : Channel → String
  | .request id => s!"request {id}"
  | .answers to => s!"answers {to}"
  | .events (some resultOf) => s!"events {resultOf}"
  | .events none => "events"

def channelOf (l : Line) : Option Channel :=
  match l.body with
  | .command .. | .query .. | .subscribe .. => some (.request l.id)
  | .unsubscribe to => some (.request to)
  | .answer to _ => some (.answers to)
  | .event _ _ resultOf => some (.events resultOf)
  | .time | .restart | .operation .. => none

/--
The causes that the notes record: the step, first line and line count of each group of event lines that a step wrote.
-/
structure Causes where
  events : Array (Nat × Nat × Nat) := #[]
deriving Repr, Inhabited

def Causes.notice (c : Causes) : Note → Causes
  | .events step start groups =>
    { c with events := (groups.foldl (fun (events, start) n => (events.push (step, start, n), start + n))
        (c.events, start)).1 }
  | .read .. | .transitionPart _ | .microstepEnds _ | .stepBegins .. | .stepEnds | .settlesAround _ | .readStates _ | .wroteState ..
  | .wroteCopies .. | .wroteShown .. | .afterMessageBegins _ | .afterMessageEnds => c

/-- For each line, the step that wrote it and the number of its group if it is an event line. -/
def lineSteps (s : State) (c : Causes) : Array (Option (Nat × Nat)) :=
  c.events.zipIdx.foldl (init := Array.replicate s.lines.size none) fun steps ((step, start, count), group) =>
    (List.range' start count).foldl (fun steps i => steps.setIfInBounds i (some (step, group))) steps

/--
Whether line `a` must precede line `b`: they travel on one channel, whose messages keep their order, and are not two
lines of one group of events, because decide gives those no order. Lines on different channels keep no order, as
messages on different connections do not. Precedents: Kafka (order within a partition), HTTP/2 (independent streams),
and Mazurkiewicz traces (independent actions commute).
-/
def ordered (s : State) (lineSteps : Array (Option (Nat × Nat))) (a b : Nat) : Bool :=
  match s.lines[a]?, s.lines[b]? with
  | some la, some lb =>
    (channelOf la).isSome && channelOf la == channelOf lb &&
      match lineSteps[a]?, lineSteps[b]? with
      | some (some (_, ga)), some (some (_, gb)) => ga != gb
      | _, _ => true
  | _, _ => false

/-- The `out` lines of the window that contains line `i`. -/
def window (s : State) (i : Nat) : List Nat :=
  let indexed := s.lines.toList.zipIdx
  let before := (indexed.take i).reverse.takeWhile (·.1.dir == .out)
  let after := (indexed.drop i).takeWhile (·.1.dir == .out)
  (before.reverse ++ after).map (·.2)

/-- The ids of the earlier lines in the same window that must precede line `i` (ordered). -/
def after (s : State) (lineSteps : Array (Option (Nat × Nat))) (i : Nat) : List String :=
  match s.lines[i]? with
  | none => []
  | some line =>
    if line.dir == .in then [] else
    ((window s i).filter fun a => a < i && ordered s lineSteps a i).filterMap fun a => s.lines[a]?.map (·.id)

/--
The strings of a line body in which createKey values are searched. Rejection kinds are excluded, since they can never
be createKey values.
-/
def bodyStrings : LineBody → List String
  | .command _ input | .query _ input | .subscribe _ input => input.strings
  | .event _ payload _ => payload.strings
  | .answer _ a => match a with
    | .accepted none => ["accepted"]
    | .accepted (some o) => "accepted" :: o.strings
    | .fulfilled o => "fulfilled" :: o.strings
    | .rejected r => "rejected" :: r.reason.toList
  | .unsubscribe _ | .time | .restart => []
  | .operation _ payload => (payload.map Value.strings).getD []

/-- The first `out` line where createKey value `v` appears. -/
def firstOut (s : State) (v : String) : Option Nat :=
  (s.lines.toList.zipIdx.find? fun (l, _) => l.dir == .out && v ∈ bodyStrings l.body).map (·.2)

/-- The createKey values whose first `out` line is `i`, in createKey order. -/
def createdAt (s : State) (i : Nat) : List String :=
  (s.created.map (·.2)).filter (firstOut s · == some i)

def trace (s : State) (c : Causes) : List (Line × List String × List String) :=
  let lineSteps := lineSteps s c
  s.lines.toList.zipIdx.map fun (line, i) => (line, after s lineSteps i, createdAt s i)

/-- The trace line of `line` as a snapshot holds it, with its `after` and `created`. -/
def traceLineOf (line : Line) (after created : List String) : TraceLine :=
  let (dir, id) := (line.dir, line.id)
  let body : TraceLine.Body := match line.body with
    | .command name input => .command dir id name input
    | .query name input => .query dir id name input
    | .subscribe name input => .subscribe dir id name input
    | .event name payload resultOf => .event dir id name payload resultOf
    | .answer to answer => .answer dir id to answer
    | .unsubscribe to => .unsubscribe dir id to
    | .time => .time .in id
    | .restart => .restart .in id
    | .operation name payload => .operation dir id name payload
  { time := { text := renderTime line.time, time := line.time }
    body
    after := if after.isEmpty then none else some after
    created := if created.isEmpty then none else some created }

end Tazuna.Sim
