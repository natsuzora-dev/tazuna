import Tazuna.Data.Canonical
import Tazuna.Semantics.Step

/-!
This module derives the inputs of a peer, another spec service, from a scenario's run: the requests that the run sends
to the peer, the events of the run that the peer receives, and the answers to the peer's requests that the scenario
takes from it (from lines), each placed where it arrives among the scenario's elsewhere inputs to the peer. The peer
check (System.PeerCheck) compares the scenario's mocks with the peer's run of these inputs.
-/

namespace Tazuna.Semantics

open Tazuna.Data

/-- The string that the peer takes in place of the createKey value `key` of the scenario's service `service`. -/
def peerKey (service key : String) : String := s!"{service}.{key}"

/--
Each createKey value of the scenario's run with the string that the peer takes in its place: the peer halts on a value
of the form of its own createKey value that it has not given (uncreatedKey).
-/
def peerKeys (service : String) (lines : List TraceLine) : Bindings :=
  (lines.flatMap (·.created.getD [])).map fun k => (k, peerKey service k)

/-- The peer's own name of the trace name `name`, when `name` names a definition of the peer. -/
def peerName? (peer name : String) : Option String :=
  if name.startsWith (peer ++ ".") then some (name.drop (peer.length + 1)).toString else none

/-- Whether a mock answered the request `id` as unavailable: such a request never reached the peer. -/
def unreached (lines : List TraceLine) (id : String) : Bool :=
  lines.any fun l =>
    match l.body with
    | .answer .in _ to (.rejected r) => to == id && r.kind == .unavailable
    | _ => false

/-- The trace name of the target of the request `id` that the run sent. -/
def requestName? (lines : List TraceLine) (id : String) : Option String :=
  lines.findSome? fun l =>
    match l.body with
    | .command .out i name _ | .query .out i name _ | .subscribe .out i name _ =>
      if i == id then some name else none
    | _ => none

/-- The peer's own name of the target of the request `id` of the run, when the request went to the peer. -/
def peerTarget? (peer : String) (lines : List TraceLine) (id : String) : Option String :=
  (requestName? lines id).bind (peerName? peer)

/--
The peer's input of the run's line `l`: a request to the peer that reached it, with the request's id, or the end of a
subscription to the peer. `keys` renames the strings of the request (peerForward).
-/
def peerBody? (peer : String) (lines : List TraceLine) (keys : Bindings) (l : TraceLine) : Option Step.Body :=
  let reached (id name : String) : Option String := if unreached lines id then none else peerName? peer name
  match l.body with
  | .command .out id name input => (reached id name).map (.command (some id) · (keys.rename input))
  | .query .out id name input => (reached id name).map (.query (some id) · (keys.rename input))
  | .subscribe .out id name input => (reached id name).map (.subscribe (some id) · (keys.rename input) none)
  | .unsubscribe .out _ to =>
    if (peerTarget? peer lines to).isSome && !unreached lines to then some (.unsubscribe (.id to)) else none
  | _ => none

/--
The peer's input of the run's line `l`: an event that the scenario's service `service` emits and that the peer
receives, by the peer's trace name of it among `received`, with the event's id and no resultOf. `keys` renames the
strings of the payload (peerForward).
-/
def peerEvent? (service : String) (received : List String) (keys : Bindings) (l : TraceLine) : Option Step.Body :=
  match l.body with
  | .event .out id name payload _ =>
    (received.find? (peerName? service · == some name)).map (.event id · (keys.rename payload) none)
  | _ => none

/-- The type, id, trace name and input of a command, query, or subscribe line in direction `dir`. -/
def requestOf? (dir : Dir) (b : TraceLine.Body) : Option (String × String × String × Value) :=
  match b with
  | .command d id name x | .query d id name x | .subscribe d id name x =>
    if d == dir then some (b.type, id, name, x) else none
  | _ => none

/--
The peer's input of the run's line `l`: an answer of the scenario's service `service`, other than unavailable, to a
request of the run's from lines `fromLines`, which the peer sent. It answers the peer's request whose id `keys` binds
to the request's (peerForward), with the strings of its output renamed.
-/
def peerAnswer? (service : String) (lines : List TraceLine) (fromLines : List Nat) (keys : Bindings) (l : TraceLine) :
    Option Step.Body :=
  match l.body with
  | .answer .out _ to a =>
    if a.unavailable then none else
    (fromLines.findSome? fun k => (lines[k]?.bind (requestOf? .in ·.body)).bind fun (_, id, name, _) =>
      if id == to then some name else none).map fun name =>
      .answerById ((keys.lookup to).getD to) s!"{service}.{name}" (a.mapOutput keys.rename)
  | _ => none

/--
The peer's input of the run's line `l` (peerBody?, peerEvent?, peerAnswer?), the strings of the run renamed by `keys`.
-/
def peerInput? (service peer : String) (received : List String) (fromLines : List Nat) (lines : List TraceLine)
    (keys : Bindings) (l : TraceLine) : Option Step.Body :=
  ((peerBody? peer lines keys l).orElse fun _ => peerEvent? service received keys l).orElse fun _ =>
    peerAnswer? service lines fromLines keys l

/-- The trace name of the definition of another service whose message the input gives: an event, or an answer's target. -/
def Step.Body.received? : Step.Body → Option String
  | .event _ name _ _ | .answer _ name _ _ _ | .answerById _ name _ => some name
  | _ => none

/-- The body with each string of its values that `keys` binds replaced. -/
def Step.Body.forPeer (keys : Bindings) : Step.Body → Step.Body
  | .command id name input => .command id name (keys.rename input)
  | .query id name input => .query id name (keys.rename input)
  | .subscribe id name input handle => .subscribe id name (keys.rename input) handle
  | .event id name payload resultOf => .event id name (keys.rename payload) resultOf
  | .operation screen control payload => .operation screen control (keys.rename payload)
  | .unacceptedOperation screen control payload => .unacceptedOperation screen control (keys.rename payload)
  | .answer sender target a choice handle =>
    .answer sender target (a.mapOutput keys.rename) (choice.map fun
      | .mock input stale => .mock (input.map keys.rename) stale
      | c => c) handle
  | .answerById to target a => .answerById to target (a.mapOutput keys.rename)
  | b => b

/-- Where an input of the peer comes from. -/
inductive PeerOrigin where
  /-- The given state of the peer. -/
  | given
  /-- The line `line`, from 0, of the scenario's run. -/
  | line (line : Nat)
  /-- The elsewhere input `index`, from 0, of the scenario. -/
  | elsewhere (index : Nat)
deriving DecidableEq, Repr, Inhabited

derive_wire PeerOrigin tag "type"

/-- The lines of `lines` that are `in` lines, each with its place in `lines`. -/
def inLines (lines : List TraceLine) : List (TraceLine × Nat) := lines.zipIdx.filter (·.1.body.dir == .in)

/-- The form of a value of a definition, by the definition's trace name, that verify compares. -/
abbrev NamedForm := String → Value → CValue

/--
What a peer's inputs derive from, besides the scenario's run: the peer `peer`, the trace names `received` of the
events that it receives, the scenario's from lines `fromLines` of the peer, the inputs `state` of its given state, and
the scenario's elsewhere inputs `elsewhere` to it, each with the number of the run's lines before which it arrives. The
peer check compares the peer's outputs and payloads in the form `peerForm`, by the peer's own names, and the inputs of
the requests that the scenario takes from the peer in the form `ownInputForm`, by the scenario's own names.
-/
structure PeerDerivation where
  peer : String
  received : List String
  fromLines : List Nat
  state : List Step
  elsewhere : List (Nat × Step)
  peerForm : NamedForm
  ownInputForm : NamedForm

/--
The run's inputs to the peer and the scenario's elsewhere inputs to it, each with its origin, in the order that they
arrive: the run's requests to the peer, ends of subscriptions to it, events that the peer receives, and answers to the
peer's requests of the from lines at their lines, taking the strings `keys n` at the line `n`, and each elsewhere input
before the number of the run's lines that it holds, unchanged.
-/
def peerPlaced (service : String) (d : PeerDerivation) (lines : List TraceLine) (keys : Nat → Bindings) :
    List (Step × PeerOrigin) :=
  (List.range (lines.length + 1)).flatMap fun n =>
    ((d.elsewhere.zipIdx.filter fun e => e.1.1 == n || (n == lines.length && n < e.1.1)).map fun e =>
      (e.1.2, PeerOrigin.elsewhere e.2)) ++
    match lines[n]? with
    | some l =>
      ((peerInput? service d.peer d.received d.fromLines lines (keys n) l).map fun b =>
        (⟨l.time, b, none, none, none⟩, PeerOrigin.line n)).toList
    | none => []

/-- The number of the run's lines before which the input of origin `o` arrives, `elsewhere` as in PeerDerivation. -/
def PeerOrigin.arrival (elsewhere : List (Nat × Step)) : PeerOrigin → Nat
  | .given => 0
  | .line n => n
  | .elsewhere k => (elsewhere[k]?.map (·.1)).getD 0

/--
The arrival of each input of the peer (PeerOrigin.arrival), in the order of peerInputs, the given state first. The
origins do not depend on the strings that the inputs take.
-/
def peerArrivals (service : String) (d : PeerDerivation) (lines : List TraceLine) : List Nat :=
  d.state.map (fun _ => 0) ++ (peerPlaced service d lines fun _ => []).map (·.2.arrival d.elsewhere)

end Tazuna.Semantics
