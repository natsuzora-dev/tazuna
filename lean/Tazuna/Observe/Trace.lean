import Tazuna.Semantics.Note
import Tazuna.Semantics.State

/-!
This module computes a snapshot line's `after`: every order that must hold among the lines of one window (between two
input lines).
-/

namespace Tazuna.Observe

open Tazuna.Data Tazuna.Semantics

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

def isEvent (l : Line) : Bool :=
  match l.body with
  | .event _ _ _ => true
  | _ => false

/--
The causes that the notes record. `events` holds the step, first line and line count of each step that wrote event
lines. `deadlines` holds the message number and time of each deadline message.
-/
structure Causes where
  events : Array (Nat × Nat × Nat) := #[]
  deadlines : Array (Nat × Time) := #[]
deriving Repr, Inhabited

def Causes.notice (c : Causes) : Note → Causes
  | .events step start count => { c with events := c.events.push (step, start, count) }
  | .deadline message time => { c with deadlines := c.deadlines.push (message, time) }
  | .read .. | .transitionPart _ | .microstepEnds _ | .stepBegins .. | .stepEnds | .settlesAround _ | .readStates _ | .wroteState ..
  | .wroteCopies .. | .wroteShown .. => c

/-- For each line, the step that wrote it if it is an event line. -/
def lineSteps (s : State) (c : Causes) : Array (Option Nat) :=
  c.events.foldl (init := Array.replicate s.lines.size none) fun steps (step, start, count) =>
    (List.range' start count).foldl (fun steps i => steps.setIfInBounds i (some step)) steps

/-- For each message, numbered from 1, the deadline time if it is a deadline message. -/
def messages (s : State) (c : Causes) : List (Option Time) :=
  (List.range s.messageCount).map fun k => (c.deadlines.find? (·.1 == k + 1)).map (·.2)

/-- The raceScope of message `k`. Consecutive deadline messages at the same time share a raceScope. -/
def raceScopeOf (messages : List (Option Time)) (k : Nat) : Nat :=
  ((messages.take k).foldl (fun (acc : Nat × Option Time) d =>
    (if d.isSome && d == acc.2 then acc.1 else acc.1 + 1, d)) (0, none)).1

/-- Whether line `a` must precede line `b`. Only event lines are ordered, because an implementation keeps order only
within the events that a service emits. Precedents: Kafka (order within a partition) and HTTP/2 (independent streams).
-/
def ordered (s : State) (lineSteps : Array (Option Nat)) (messages : List (Option Time)) (a b : Nat) : Bool :=
  match s.lines[a]?, s.lines[b]?, lineSteps[a]?, lineSteps[b]? with
  | some la, some lb, some (some sa), some (some sb) =>
    isEvent la && isEvent lb &&
      match s.steps[sa]?, s.steps[sb]? with
      | some ia, some ib =>
        if raceScopeOf messages ia.message != raceScopeOf messages ib.message then ia.message < ib.message
        else leadsTo s sa sb
      | _, _ => false
  | _, _, _, _ => false

/-- The `out` lines of the window that contains line `i`. -/
def window (s : State) (i : Nat) : List Nat :=
  let indexed := s.lines.toList.zipIdx
  let before := (indexed.take i).reverse.takeWhile (·.1.dir == .out)
  let after := (indexed.drop i).takeWhile (·.1.dir == .out)
  (before.reverse ++ after).map (·.2)

/--
The ids of the earlier lines in the same window that must precede line `i`: event lines ordered before it, and lines
at a different time.
-/
def after (s : State) (lineSteps : Array (Option Nat)) (messages : List (Option Time)) (i : Nat) : List String :=
  match s.lines[i]? with
  | none => []
  | some line =>
    if line.dir == .in then [] else
    ((window s i).filter fun a =>
      a < i && (ordered s lineSteps messages a i || (s.lines[a]?.map (·.time != line.time)).getD false)).filterMap
      fun a => s.lines[a]?.map (·.id)

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
  | .operation _ payload _ => (payload.map Value.strings).getD []

/-- The first `out` line where createKey value `v` appears. -/
def firstOut (s : State) (v : String) : Option Nat :=
  (s.lines.toList.zipIdx.find? fun (l, _) => l.dir == .out && v ∈ bodyStrings l.body).map (·.2)

/-- The createKey values whose first `out` line is `i`, in createKey order. -/
def createdAt (s : State) (i : Nat) : List String :=
  (s.created.map (·.2)).filter (firstOut s · == some i)

def trace (s : State) (c : Causes) : List (Line × List String × List String) :=
  let lineSteps := lineSteps s c
  let messages := messages s c
  s.lines.toList.zipIdx.map fun (line, i) => (line, after s lineSteps messages i, createdAt s i)

end Tazuna.Observe
