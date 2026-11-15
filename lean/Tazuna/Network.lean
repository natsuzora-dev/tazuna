import Tazuna.Semantics.System.Peer

/-!
This module models services that run together on a network: an execution gives each member service its trace, and
each line that a member receives from another member the line that the other member sent.
-/

namespace Tazuna.Network

open Tazuna.Data Tazuna.Semantics

/-- A line of an execution: the member, from 0, and the line of its trace, from 0. -/
abbrev Place := Nat × Nat

/-- Services that run together: each member's name and trace, and where each line that a member received was sent. -/
structure Execution where
  members : List (String × List TraceLine)
  /-- The line that another member sent as the received line at the place, or none for a line from outside. -/
  source : Place → Option Place

def Execution.name (e : Execution) (m : Nat) : String := (e.members[m]?.map (·.1)).getD ""

def Execution.lines (e : Execution) (m : Nat) : List TraceLine := (e.members[m]?.map (·.2)).getD []

def Execution.line? (e : Execution) (p : Place) : Option TraceLine := (e.lines p.1)[p.2]?

/--
Whether value `y` that member `r` receives stands for value `x` that member `s` sent, of the definition that `r` names
`name` in its trace. In an execution of implementations it is equality; between spec runs, it is equality up to the
keys that each run chooses.
-/
abbrev Agree := (s r : Nat) → (name : String) → (x y : Value) → Prop

/-- Whether the received answer `a` carries the sent answer `b`, values compared by `agree`, rejections by kind. -/
def AnswerCarries (agree : Value → Value → Prop) : Answer → Answer → Prop
  | .accepted (some x), .accepted (some y) => agree x y
  | .accepted none, .accepted none => True
  | .fulfilled x, .fulfilled y => agree x y
  | .rejected r, .rejected q => r.kind = q.kind
  | _, _ => False

/--
Whether the line `recv` that member `r` received carries the line `sent` that member `s` sent: a request to `r` with
the same id, an end of a subscription, an answer to a request of `r` to `s`, or an event of `s`. A name of the other
service has its name before a dot, as in a trace.
-/
def Carries (agree : Agree) (e : Execution) (s r : Nat) (sent recv : TraceLine) : Prop :=
  match sent.body, recv.body with
  | .command .out (some i) name x, .command .in (some j) n y
  | .query .out (some i) name x, .query .in (some j) n y
  | .subscribe .out (some i) name x, .subscribe .in (some j) n y =>
    j = i ∧ peerName? (e.name r) name = some n ∧ agree s r n x y
  | .unsubscribe .out _ to, .unsubscribe .in _ to' => to' = to
  | .answer .out _ to b, .answer .in _ to' a =>
    to' = to ∧ ∃ m, requestName? (e.lines r) to = some m ∧ (peerName? (e.name s) m).isSome ∧
      AnswerCarries (agree s r m) b a
  | .event .out _ n x _, .event .in _ name y _ => peerName? (e.name s) name = some n ∧ agree s r name x y
  | _, _ => False

def isEventLine (l : TraceLine) : Bool :=
  match l.body with
  | .event .. => true
  | _ => false

/--
Whether line `l` of the trace `lines` is a message that the network must deliver to the service named `to`: a request
to it with an id, or an end of a subscription to it, that no answer in `lines` rejects as unavailable.
-/
def Sends (to : String) (lines : List TraceLine) (l : TraceLine) : Prop := (peerBody? to lines [] l).isSome

/--
The network that an execution runs on. Each received line that another member sent carries it, at or after the time
it was sent; a request or an answer arrives at most once, and the answers to one request arrive in the order they were
sent; an answer `unavailable` comes from no member, since its request reached no one. Every answer to a request to a
member that no answer rejects as unavailable, and every event of a member, that a member receives was sent; every
request to a member that no answer rejects as unavailable arrives, with the end of its subscription. A member sends a
line that another member receives before it receives a line that the other member sends at or after receiving it. An
event may be delayed, lost, delivered more than once, or overtaken, and an answer may be lost.
-/
structure WellFormed (agree : Agree) (e : Execution) : Prop where
  delivered : ∀ r i s j, e.source (r, i) = some (s, j) → s ≠ r ∧
    ∃ sent recv, e.line? (s, j) = some sent ∧ e.line? (r, i) = some recv ∧ sent.body.dir = .out ∧
      recv.body.dir = .in ∧ sent.time.time ≤ recv.time.time ∧ Carries agree e s r sent recv
  once : ∀ p q x sent, e.source p = some x → e.source q = some x → e.line? x = some sent → isEventLine sent = false →
    p = q
  ordered : ∀ r i i' s j j' l l' id id' to a a', i < i' → e.source (r, i) = some (s, j) →
    e.source (r, i') = some (s, j') → e.line? (r, i) = some l → e.line? (r, i') = some l' →
    l.body = .answer .in id to a → l'.body = .answer .in id' to a' → j < j'
  unavailable : ∀ r i l id to rejection, e.line? (r, i) = some l → l.body = .answer .in id to (.rejected rejection) →
    rejection.kind = .unavailable → e.source (r, i) = none
  answered : ∀ r s i l id to a, s ≠ r → s < e.members.length → e.line? (r, i) = some l →
    l.body = .answer .in id to a → (peerTarget? (e.name s) (e.lines r) to).isSome → unreached (e.lines r) to = false →
    ∃ j, e.source (r, i) = some (s, j)
  emitted : ∀ r s i l id name n payload resultOf, s ≠ r → s < e.members.length → e.line? (r, i) = some l →
    l.body = .event .in id name payload resultOf → peerName? (e.name s) name = some n →
    ∃ j, e.source (r, i) = some (s, j)
  arrives : ∀ r s i l, s ≠ r → s < e.members.length → e.line? (r, i) = some l → Sends (e.name s) (e.lines r) l →
    ∃ j, e.source (s, j) = some (r, i)
  causal : ∀ r i s j i' j', e.source (r, i) = some (s, j) → j' ≤ j → e.source (s, j') = some (r, i') → i' < i

/--
Whether `l` is the `in` line that a run writes for input `s`, as far as the network needs: at the input's time; for a
request or an event the same one with its value in the form `canon` that the run writes for the definition, keeping a
given id, and an event without resultOf has none; for an end of a subscription the same end; and no event otherwise.
-/
def Writes (canon : String → Value → Value) (s : Step) (l : TraceLine) : Prop :=
  l.time = s.time ∧ l.body.dir = .in ∧
  match s.body with
  | .command id name x => ∃ id', l.body = .command .in id' name (canon name x) ∧ ∀ i, id = some i → id' = some i
  | .query id name x => ∃ id', l.body = .query .in id' name (canon name x) ∧ ∀ i, id = some i → id' = some i
  | .subscribe id name x => ∃ id', l.body = .subscribe .in id' name (canon name x) ∧ ∀ i, id = some i → id' = some i
  | .unsubscribe to => ∃ id', l.body = .unsubscribe .in id' to
  | .event id name x resultOf =>
    ∃ id' r, l.body = .event .in id' name (canon name x) r ∧ (∀ i, id = some i → id' = some i) ∧
      (resultOf = none → r = none)
  | _ => isEventLine l = false

/-- Whether the `in` lines of `lines` are the lines that a run writes for `inputs`, one for each, in order. -/
def RunOf (canon : String → Value → Value) (inputs : List Step) (lines : List TraceLine) : Prop :=
  inputs.length = (inLines lines).length ∧
    ∀ (k : Nat) s (p : TraceLine × Nat), inputs[k]? = some s → (inLines lines)[k]? = some p → Writes canon s p.1

end Tazuna.Network
