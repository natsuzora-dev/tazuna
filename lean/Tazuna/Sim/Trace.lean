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
event lines are compared. Reachability between them follows the cause chain and barriers, which the search of step
orders keeps fixed.
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

/-- Whether step `later` is step `earlier` or one that it caused, following the cause chain only. -/
def causedBy (s : State) (earlier later : Nat) : Bool :=
  later == earlier ||
    match s.steps[later]?.bind (·.cause) with
    | some cause => if cause < later then causedBy s earlier cause else false
    | none => false
termination_by later

def channelOf (l : Line) : Option Channel :=
  match l.body with
  | .command .. | .query .. | .subscribe .. => some (.request l.id)
  | .unsubscribe to => some (.request to)
  | .answer to _ => some (.answers to)
  | .event _ _ resultOf => some (.events resultOf)
  | .time | .restart | .operation .. => none

/--
Whether line `a` must precede line `b` among the lines of one window: they travel on one channel, and `b` is caused by
`a`. The lines of one request's channel all are. Of two event lines, `b` is when its step is `a`'s and its group a
different one, since decide orders its groups and not the events of one group, or when its step is one that `a`'s step
caused. Events of steps that no cause chain links keep no order, even on one channel, as two senders' messages do not;
lines on different channels keep none either. Precedents: Lamport's happens-before, Kafka (order within a partition),
HTTP/2 (independent streams), and Mazurkiewicz traces (independent actions commute).
-/
def ordered (s : State) (a b : Nat) : Bool :=
  match s.lines[a]?, s.lines[b]? with
  | some la, some lb =>
    (channelOf la).isSome && channelOf la == channelOf lb &&
      match la.emitted, lb.emitted with
      | some ea, some eb => if ea.step == eb.step then ea.group != eb.group else causedBy s ea.step eb.step
      | _, _ => true
  | _, _ => false

/--
Whether line `a` reaches a receiver before line `b` (`a < b`): an `in` line lies between them, since every line caused
by an input comes before the next input, or they are ordered.
-/
def sentBefore (s : State) (a b : Nat) : Bool :=
  a < b && ((s.lines.extract (a + 1) b).any (·.dir == .in) || ordered s a b)

/-- The `out` lines of the window that contains line `i`. -/
def window (s : State) (i : Nat) : List Nat :=
  let indexed := s.lines.toList.zipIdx
  let before := (indexed.take i).reverse.takeWhile (·.1.dir == .out)
  let after := (indexed.drop i).takeWhile (·.1.dir == .out)
  (before.reverse ++ after).map (·.2)

/-- The ids of the earlier lines in the same window that must precede line `i` (ordered). -/
def after (s : State) (i : Nat) : List LineId :=
  match s.lines[i]? with
  | none => []
  | some line =>
    if line.dir == .in then [] else
    ((window s i).filter fun a => a < i && ordered s a i).filterMap fun a => s.lines[a]?.map (·.id)

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
  | .operation _ _ _ payload => (payload.map Value.strings).getD []

/-- The first `out` line where createKey value `v` appears. -/
def firstOut (s : State) (v : String) : Option Nat :=
  (s.lines.toList.zipIdx.find? fun (l, _) => l.dir == .out && v ∈ bodyStrings l.body).map (·.2)

/-- The createKey values whose first `out` line is `i`, in createKey order. -/
def createdAt (s : State) (i : Nat) : List String :=
  (s.created.map (·.2)).filter (firstOut s · == some i)

def trace (s : State) : List (Line × List LineId × List String) :=
  s.lines.toList.zipIdx.map fun (line, i) => (line, after s i, createdAt s i)

/--
The trace line of `line` of the trace of `service` as a snapshot holds it, with its `after` and `created`. This is where
a definition gets its trace name and a line id its text.
-/
def traceLineOf (service : String) (line : Line) (after : List LineId) (created : List String) : TraceLine :=
  let (dir, id) := (line.dir, line.id.text)
  let name (r : Spec.Ref) := r.traceName service
  let body : TraceLine.Body := match line.body with
    | .command r input => .command dir id (name r) input
    | .query r input => .query dir id (name r) input
    | .subscribe r input => .subscribe dir id (name r) input
    | .event r payload resultOf => .event dir id (name r) payload (resultOf.map (·.text))
    | .answer to answer => .answer dir id to.text answer
    | .unsubscribe to => .unsubscribe dir id to.text
    | .time => .time .in id
    | .restart => .restart .in id
    | .operation screen control nth payload => .operation dir id (operationName (name screen) control) nth payload
  { time := { text := renderTime line.time, time := line.time }
    body
    after := if after.isEmpty then none else some (after.map (·.text))
    created := if created.isEmpty then none else some created }

end Tazuna.Sim
