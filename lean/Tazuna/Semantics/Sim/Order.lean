import Tazuna.Semantics.Service.State

/-!
The causal order of a running service's lines: which earlier line of one window (between two input lines) each line
must follow, which a snapshot line's `after` records and the network keeps.
-/

namespace Tazuna.Semantics.Sim

open Tazuna.Ir Tazuna.Semantics.Service

/--
The channel that an `out` line travels on, seen from its sender (Sim's Message.sameChannel, whose receiver a trace line
does not name): a request and its end travel to the request's receiver on the request's own channel, the answers to a
received request travel back to its sender, and events travel to their receivers on the channel of their `resultOf`,
or on the sender's channel when they name none. A line that no sender writes `out` travels on none.
-/
inductive Channel where
  | request (id : LineId)
  | answers (request : LineId)
  | events (resultOf : Option LineId)
deriving DecidableEq, Repr

/--
Whether step `later` is step `earlier` or one that it caused, following the cause chain, in which a deadline step's
cause is the step that armed it.
-/
def causedBy (s : Service.State) (earlier later : Nat) : Bool :=
  later == earlier ||
    match s.steps[later]?.map (·.origin) with
    | some (StepOrigin.caused c) | some (StepOrigin.deadline c _) => if c < later then causedBy s earlier c else false
    | _ => false
termination_by later

/-- The channel of the line with id `id` and body `body`. -/
def _root_.Tazuna.Semantics.Service.LineBody.channel (id : LineId) : LineBody → Option Channel
  | .command .. | .query .. | .subscribe .. => some (.request id)
  | .unsubscribe to => some (.request to)
  | .answer to _ => some (.answers to)
  | .event _ _ resultOf => some (.events resultOf)
  | .time | .restart | .operation .. => none

def channelOf (l : Line) : Option Channel := l.body.channel l.id

/--
Whether line `a` must precede line `b` among the lines of one window: they travel on one channel, and `b` is caused by
`a`. The lines of one request's channel all are. Of two event lines, `b` is when its step is `a`'s and its group a
different one, since decide orders its groups and not the events of one group, when its step is one that `a`'s step
caused, or when it is later than `a`: within one window only the clock line moves time, and it fires its deadlines
before its own line, so `b` is an output of that clock line and `a` was sent before it. Events of steps that no cause
chain links keep no order, even on one channel, as two senders' messages do not; lines on different channels keep none
either. Precedents: Lamport's happens-before (order along a cause chain), Kafka (send order within a partition),
HTTP/2 (independent streams), and Mazurkiewicz traces (independent actions commute).
-/
def ordered (s : Service.State) (a b : Nat) : Bool :=
  match s.lines[a]?, s.lines[b]? with
  | some la, some lb =>
    (channelOf la).isSome && channelOf la == channelOf lb &&
      match la, lb with
      | ⟨ta, .out, _, .event .., ea, _, _⟩, ⟨tb, .out, _, .event .., eb, _, _⟩ =>
        ta < tb || if ea.step == eb.step then ea.group != eb.group else causedBy s ea.step eb.step
      | _, _ => true
  | _, _ => false

/--
Whether line `a` reaches a receiver before line `b` (`a < b`): an `in` line lies between them, since every line caused
by an input comes before the next input, or they are ordered.
-/
def sentBefore (s : Service.State) (a b : Nat) : Bool :=
  a < b && ((s.lines.extract (a + 1) b).any (·.dir == .in) || ordered s a b)

/-- The `out` lines of the window that contains line `i`. -/
def window (s : Service.State) (i : Nat) : List Nat :=
  let indexed := s.lines.toList.zipIdx
  let before := (indexed.take i).reverse.takeWhile (·.1.dir == .out)
  let after := (indexed.drop i).takeWhile (·.1.dir == .out)
  (before.reverse ++ after).map (·.2)

/-- The ids of the earlier lines in the same window that must precede line `i` (ordered). -/
def after (s : Service.State) (i : Nat) : List LineId :=
  match s.lines[i]? with
  | none => []
  | some line =>
    if line.dir == .in then [] else
    ((window s i).filter fun a => a < i && ordered s a i).filterMap fun a => s.lines[a]?.map (·.id)

end Tazuna.Semantics.Sim
