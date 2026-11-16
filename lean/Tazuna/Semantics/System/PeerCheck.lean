import Tazuna.Data.Unify
import Tazuna.Semantics.InvalidInput
import Tazuna.Semantics.System.Peer

/-!
This module checks the mocks that a scenario takes from a peer against the peer's run of the inputs that the
scenario's run gives it (System.Peer): a mocked answer, a received event, and a request that the scenario takes from
the peer must come from the peer's run, up to the strings that the peer gives its createKey values and request ids
(unify). The check's bindings rename the strings of the inputs that the peer takes later (peerForward), so peerInputs
is defined here.
-/

namespace Tazuna.Semantics

open Tazuna.Data

/-- The answers in direction `dir` to the request `id`, in order, with their times. -/
def answersTo (lines : List TraceLine) (dir : Dir) (id : String) : List (DateTime × Answer) :=
  lines.filterMap fun l =>
    match l.body with
    | .answer d _ to a => if d == dir && to == id then some (l.time, a) else none
    | _ => none

/--
The number of the peer's lines that it writes before it takes an input that arrives after the run's line `i`, the
input of its `k`-th `in` line arriving before the run's line `arrivals[k]` (peerArrivals). A line of the scenario's run
can come only from these lines of the peer, which do not depend on the scenario's later lines.
-/
def peerBefore (arrivals : List Nat) (peerLines : List TraceLine) (i : Nat) : Nat :=
  match arrivals.findIdx? (i < ·) with
  | some k => ((inLines peerLines)[k]?.map (·.2)).getD peerLines.length
  | none => peerLines.length

/--
Whether the peer's line `b` can send the scenario's from line `l`, with the bindings `bs`: none when `b` is not an `out`
line of the same request to the scenario's service `service`, or of the end of the subscription bound to the one that
`l` ends, by `l`'s time and with an id that no string is bound to yet. Otherwise `bs` with `b`'s id bound to `l`'s and,
for a request, extended so that its input is `l`'s (unify), the peer's in the form `seen` and the scenario's in the form
`form` of the definition by the scenario's own name.
-/
def sentAs? (created : List String) (seen form : NamedForm) (service : String) (bs : Bindings)
    (l b : TraceLine) : Option (Except Unequal Bindings) :=
  if l.time.time < b.time.time then none else
  match l.body, b.body with
  | .unsubscribe .in id to, .unsubscribe .out id' to' =>
    if bs.lookup to' == some to then (bs.bindNew id' id).map .ok else none
  | lb, bb =>
    match requestOf? .in lb, requestOf? .out bb with
    | some (t, id, name, x), some (t', id', m, y) =>
      if t' == t && peerName? service m == some name then
        (bs.bindNew id' id).map (unify created (seen name y) (form name x))
      else none
    | _, _ => none

/--
The first of the lines `before` of the peer that sends the scenario's from line `l` (sentAs?), by its place, with the
bindings extended, or why none does.
-/
def peerSent (created : List String) (seen form : NamedForm) (service : String) (bs : Bindings)
    (before : List TraceLine) (l : TraceLine) : Except Unequal (Nat × Bindings) :=
  let tries := before.zipIdx.filterMap fun (b, j) => (sentAs? created seen form service bs l b).map (j, ·)
  match tries.findSome? fun (j, r) => r.toOption.map (j, ·) with
  | some p => .ok p
  | none => .error (if tries.any (·.2 matches .error .searchLimit) then .searchLimit else .differ)

/--
The check of the run's line `l`, the line `i` of the run, with the bindings `bs` of the peer's createKey values to the
strings that the scenario has in their place: its violation, or `bs` extended. A mocked answer to a request to the peer
that reached it must be the peer's answer at the same place, by its time; a received event of the peer must be one that
the peer emits by its time, with the `resultOf` that the event names, if any; a from line must be a request that the
peer sends by its time (peerSent). Each must come from the peer's lines before its inputs that arrive after `l`
(peerBefore). The peer's values have its peer keys turned back into the run's createKey values, and both sides take the
forms of PeerDerivation. A comparison that does not finish within its tries gives peerSearchLimit.
-/
def peerLine (service : String) (d : PeerDerivation) (arrivals : List Nat) (lines peerLines : List TraceLine)
    (bs : Bindings) (i : Nat) (l : TraceLine) : Except InvalidInput Bindings :=
  let created := peerLines.flatMap (·.created.getD [])
  let back : Bindings := (peerKeys service lines).map fun (k, v) => (v, k)
  let seen (n : String) (v : Value) : CValue := d.peerForm n (back.rename v)
  let before := peerLines.take (peerBefore arrivals peerLines i)
  match l.body with
  | .answer .in id to a =>
    match peerTarget? d.peer lines to with
    | none => .ok bs
    | some target =>
      if unreached lines to then .ok bs else
      let k := (answersTo (lines.take i) .in to).length
      if (answersTo peerLines .out to)[k]?.isNone then .error (.unansweredRequest to ⟨d.peer, target⟩) else
      match (answersTo before .out to)[k]? with
      | none => .error (.unproducibleAnswer to ⟨d.peer, target⟩)
      | some (t, b) =>
        match if t.time ≤ l.time.time then unifyAnswer created (seen target) (d.peerForm target) bs b a
          else .error .differ with
        | .ok bs => .ok bs
        | .error .differ => .error (.unproducibleAnswer to ⟨d.peer, target⟩)
        | .error .searchLimit => .error (.peerSearchLimit id d.peer)
  | .event .in id name payload resultOf =>
    match peerName? d.peer name with
    | none => .ok bs
    | some n =>
      let tries := before.filterMap fun b =>
        match b.body with
        | .event .out _ m p r =>
          if m == n && b.time.time ≤ l.time.time && resultOf.all (r == some ·) then
            some (unify created (seen n p) (d.peerForm n payload) bs)
          else none
        | _ => none
      match tries.findSome? (·.toOption) with
      | some bs => .ok bs
      | none =>
        .error (if tries.any (· matches .error .searchLimit) then .peerSearchLimit id d.peer
          else .unproducibleEvent id ⟨d.peer, n⟩)
  | .command .in .. | .query .in .. | .subscribe .in .. | .unsubscribe .in .. =>
    if d.fromLines.contains i then
      match peerSent created (fun n v => d.ownInputForm n (back.rename v)) d.ownInputForm service bs before l with
      | .ok (_, bs) => .ok bs
      | .error .differ => .error (.unproducibleRequest l.body.id d.peer)
      | .error .searchLimit => .error (.peerSearchLimit l.body.id d.peer)
    else .ok bs
  | _ => .ok bs

/-- The bindings after the run's first `n` lines (peerLine): a line with a violation keeps them. -/
def peerBindings (service : String) (d : PeerDerivation) (arrivals : List Nat) (lines peerLines : List TraceLine)
    (n : Nat) : Bindings :=
  (lines.zipIdx.take n).foldl (init := []) fun bs (l, i) =>
    (peerLine service d arrivals lines peerLines bs i l).toOption.getD bs

/--
The strings that the peer takes in place of the scenario's strings before the run's line `n`: each createKey value of
the run as its peer key, and each string bound by then (peerBindings) as the peer's createKey value or request id
bound to it.
-/
def peerForward (service : String) (d : PeerDerivation) (arrivals : List Nat) (lines peerLines : List TraceLine)
    (n : Nat) : Bindings :=
  peerKeys service lines ++ (peerBindings service d arrivals lines peerLines n).map fun (k, v) => (v, k)

/--
The peer's inputs, each with its origin: those of the given state, then those of peerPlaced. The run's lines and the
elsewhere inputs take the peer's strings (peerForward) of the place where they arrive. `peerLines` is the peer's run
of these inputs.
-/
def peerInputs (service : String) (d : PeerDerivation) (lines peerLines : List TraceLine) : List (Step × PeerOrigin) :=
  let forward := peerForward service d (peerArrivals service d lines) lines peerLines
  let placed := peerPlaced service d lines forward
  d.state.map (·, PeerOrigin.given) ++ placed.map fun (s, o) =>
    match o with
    | .elsewhere _ => ({ s with body := s.body.forPeer (forward (o.arrival d.elsewhere)) }, o)
    | _ => (s, o)

/--
The violations of the scenario's mocks of the peer, each with the origin of its cause. `peerLines` is the peer's run of
`peerInputs`, `arrivals` their peerArrivals, and `halted` the origin of the input that halted it, with the halting
violation's kind. A halted run gives only haltedPeer.
-/
def peerFindings (service : String) (d : PeerDerivation) (arrivals : List Nat) (lines peerLines : List TraceLine)
    (halted : Option (PeerOrigin × String)) : List (PeerOrigin × InvalidInput) :=
  match halted with
  | some (o, kind) => [(o, .haltedPeer d.peer kind)]
  | none =>
    lines.zipIdx.filterMap fun (l, i) =>
      match peerLine service d arrivals lines peerLines (peerBindings service d arrivals lines peerLines i) i l with
      | .error v => some (PeerOrigin.line i, v)
      | .ok _ => none

end Tazuna.Semantics
