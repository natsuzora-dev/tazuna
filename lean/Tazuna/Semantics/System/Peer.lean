import Tazuna.Semantics.InvalidInput
import Tazuna.Semantics.Step

/-!
This module checks the mocks that a scenario takes from a peer, another spec service, against the peer's spec: it
derives the peer's inputs from the scenario's run, and compares the mocks with the peer's run of those inputs.
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

/-- The peer's own name of the target of the request `id` of the run, when the request went to the peer. -/
def peerTarget? (peer : String) (lines : List TraceLine) (id : String) : Option String :=
  lines.findSome? fun l =>
    match l.body with
    | .command .out (some i) name _ | .query .out (some i) name _ | .subscribe .out (some i) name _ =>
      if i == id then peerName? peer name else none
    | _ => none

/--
The peer's input of the run's line `l`: a request to the peer that reached it, with the request's id, or the end of a
subscription to the peer. `keys` renames the createKey values of the run (peerKeys).
-/
def peerBody? (peer : String) (lines : List TraceLine) (keys : Bindings) (l : TraceLine) : Option Step.Body :=
  let reached (id name : String) : Option String := if unreached lines id then none else peerName? peer name
  match l.body with
  | .command .out (some id) name input => (reached id name).map (.command (some id) · (keys.rename input))
  | .query .out (some id) name input => (reached id name).map (.query (some id) · (keys.rename input))
  | .subscribe .out (some id) name input => (reached id name).map (.subscribe (some id) · (keys.rename input))
  | .unsubscribe .out _ to =>
    if (peerTarget? peer lines to).isSome && !unreached lines to then some (.unsubscribe to) else none
  | _ => none

def _root_.Tazuna.Data.Answer.mapOutput (f : Value → Value) : Answer → Answer
  | .accepted output => .accepted (output.map f)
  | .fulfilled output => .fulfilled (f output)
  | .rejected r => .rejected r

/-- The body with each string of its values that `keys` binds replaced, and each resultOf moved by `index`. -/
def Step.Body.forPeer (keys : Bindings) (index : Nat → Nat) : Step.Body → Step.Body
  | .command id name input => .command id name (keys.rename input)
  | .query id name input => .query id name (keys.rename input)
  | .subscribe id name input => .subscribe id name (keys.rename input)
  | .event id name payload resultOf => .event id name (keys.rename payload) (resultOf.map index)
  | .operation screen control payload => .operation screen control (keys.rename payload)
  | .unacceptedOperation screen control payload => .unacceptedOperation screen control (keys.rename payload)
  | .answer sender target a choice =>
    .answer sender target (a.mapOutput keys.rename) (choice.map fun
      | .mock input stale => .mock (input.map keys.rename) stale
      | c => c)
  | b => b

/-- Where an input of the peer comes from. -/
inductive Origin where
  /-- The given state of the peer. -/
  | given
  /-- The line `line`, from 0, of the scenario's run. -/
  | line (line : Nat)
  /-- The elsewhere input `index`, from 0, of the scenario. -/
  | elsewhere (index : Nat)
deriving DecidableEq, Repr, Inhabited

derive_wire Origin tag "type"

/--
The peer's inputs, each with its origin: those of the given state `state`, then the run's requests to the peer and
ends of subscriptions to it at their times, with the scenario's elsewhere inputs among them. `elsewhere` holds each
elsewhere input with the number of the run's lines before it, and its resultOf indexes `state ++ elsewhere`. The
createKey values of the run take the peer's form (peerKeys) in the run's requests and in the elsewhere inputs.
-/
def peerInputs (service peer : String) (state : List Step) (elsewhere : List (Nat × Step)) (lines : List TraceLine) :
    List (Step × Origin) :=
  let keys := peerKeys service lines
  let placedAt (n : Nat) : List (Step × Origin) :=
    ((elsewhere.zipIdx.filter fun e => e.1.1 == n || (n == lines.length && n < e.1.1)).map fun e =>
      (e.1.2, Origin.elsewhere e.2)) ++
    match lines[n]? with
    | some l => ((peerBody? peer lines keys l).map fun b => (⟨l.time, b, none, none⟩, Origin.line n)).toList
    | none => []
  let placed := (List.range (lines.length + 1)).flatMap placedAt
  let index (r : Nat) : Nat :=
    if r < state.length then r
    else state.length + (placed.findIdx? (·.2 == Origin.elsewhere (r - state.length))).getD 0
  state.map (·, Origin.given) ++ placed.map fun (s, o) =>
    match o with
    | .elsewhere _ => ({ s with body := s.body.forPeer keys index }, o)
    | _ => (s, o)

/-- The answers in direction `dir` to the request `id`, in order, with their times. -/
def answersTo (lines : List TraceLine) (dir : Dir) (id : String) : List (DateTime × Answer) :=
  lines.filterMap fun l =>
    match l.body with
    | .answer d _ to a => if d == dir && to == id then some (l.time, a) else none
    | _ => none

/--
Whether the mock's answer `a` is the peer's answer `b` as the scenario sees it through `seen`, both outputs in the
form `norm` that verify compares. Rejections compare by kind, as verify compares them.
-/
def sameAnswer (norm seen : Value → Value) : Answer → Answer → Bool
  | .rejected r, .rejected q => r.kind == q.kind
  | .accepted o, .accepted p => o.map (norm · |>.canonical) == p.map fun v => (norm (seen v)).canonical
  | .fulfilled o, .fulfilled p => (norm o).canonical == (norm (seen p)).canonical
  | _, _ => false

/--
Whether the peer's line `b` emits `event` with `payload` as the scenario sees it through `seen`, both in the form
`norm` that verify compares, at or before `time`.
-/
def emitted (norm seen : Value → Value) (event : String) (payload : Value) (time : DateTime) (b : TraceLine) : Bool :=
  match b.body with
  | .event .out _ name p _ =>
    name == event && (norm (seen p)).canonical == (norm payload).canonical && b.time.time ≤ time.time
  | _ => false

mutual

/--
`bs` extended so that `b`, with each string that `bs` binds replaced, equals `a`, or none. Only a string of `created`
that `bs` does not bind is bound, and only to a string that no string is bound to, so `bs` stays one-to-one.
-/
def unify (created : List String) (bs : Bindings) : Value → Value → Option Bindings
  | .str a, .str b =>
    match bs.lookup b with
    | some x => if x == a then some bs else none
    | none =>
      if created.contains b then if bs.any (·.2 == a) then none else some (bs ++ [(b, a)])
      else if a == b then some bs else none
  | .arr as, .arr bs' => unifyList created bs as bs'
  | .obj fs, .obj gs => if fs.length == gs.length then unifyFields created bs fs gs else none
  | a, b => if a == b then some bs else none

def unifyList (created : List String) (bs : Bindings) : List Value → List Value → Option Bindings
  | [], [] => some bs
  | a :: as, b :: bs' => (unify created bs a b).bind fun bs => unifyList created bs as bs'
  | _, _ => none

def unifyFields (created : List String) (bs : Bindings) :
    List (String × Value) → List (String × Value) → Option Bindings
  | [], _ => some bs
  | (k, a) :: fs, gs =>
    match gs.lookup k with
    | some b => (unify created bs a b).bind fun bs => unifyFields created bs fs gs
    | none => none

end

/--
The strings that the scenario has in place of the peer's createKey values, bound one-to-one in the run's order: at each
mocked answer, from the peer's answer at the same place, and at each received event, from the first event that the
peer emits by then that matches it. `back` turns the peer keys back into the run's createKey values, and `normal`
gives the form of a value of the peer's definition that verify compares.
-/
def peerBindings (normal : String → Value → Value) (peer : String) (back : Bindings)
    (aLines bLines : List TraceLine) : Bindings :=
  let created := bLines.flatMap (·.created.getD [])
  aLines.zipIdx.foldl (init := []) fun bs (l, i) =>
    match l.body with
    | .answer .in _ to a =>
      match peerTarget? peer aLines to with
      | none => bs
      | some target =>
        if unreached aLines to then bs else
        match (answersTo bLines .out to)[(answersTo (aLines.take i) .in to).length]? with
        | some (_, b) =>
          match a.output?, b.output? with
          | some x, some y => (unify created bs (normal target x) (normal target (back.rename y))).getD bs
          | _, _ => bs
        | none => bs
    | .event .in _ name payload _ =>
      match peerName? peer name with
      | none => bs
      | some n =>
        (bLines.findSome? fun b =>
          match b.body with
          | .event .out _ m p _ =>
            if m == n && b.time.time ≤ l.time.time then unify created bs (normal n payload) (normal n (back.rename p))
            else none
          | _ => none).getD bs
    | _ => bs

/--
How the scenario sees a value of the peer's run: each peer key as the run's createKey value, and each createKey value
of the peer as the string bound to it (peerBindings).
-/
def peerSeen (normal : String → Value → Value) (service peer : String) (aLines bLines : List TraceLine) :
    Value → Value :=
  let back := (peerKeys service aLines).map fun (k, v) => (v, k)
  Bindings.rename (back ++ peerBindings normal peer back aLines bLines)

/--
The violation of the run's line `l`, the line `i` of the run: a mocked answer to a request to the peer that reached it,
which must be the peer's answer at the same place, by its time; or a received event of the peer, which the peer must
emit with the same payload by its time.
-/
def peerFinding (normal : String → Value → Value) (peer : String) (seen : Value → Value)
    (aLines bLines : List TraceLine) (i : Nat) (l : TraceLine) : Option InvalidInput :=
  match l.body with
  | .answer .in _ to a =>
    match peerTarget? peer aLines to with
    | none => none
    | some target =>
      if unreached aLines to then none else
      match (answersTo bLines .out to)[(answersTo (aLines.take i) .in to).length]? with
      | none => some (.unansweredRequest to ⟨peer, target⟩)
      | some (t, b) =>
        if sameAnswer (normal target) seen a b && t.time ≤ l.time.time then none
        else some (.unproducibleAnswer to ⟨peer, target⟩)
  | .event .in id name payload _ =>
    match peerName? peer name with
    | none => none
    | some n =>
      if bLines.any (emitted (normal n) seen n payload l.time) then none
      else some (.unproducibleEvent (id.getD "") ⟨peer, n⟩)
  | _ => none

/--
The violations of the scenario's mocks of the peer, each with the origin of its cause. `bLines` is the peer's run of
`peerInputs`, and `halted` the origin of the input that halted it, with the halting violation's kind. A halted run
gives only haltedPeer. `normal` gives the form of an output or payload of the peer's definition, by the peer's own
name, that verify compares: bags and sets in canonical order.
-/
def peerFindings (normal : String → Value → Value) (service peer : String) (aLines bLines : List TraceLine)
    (halted : Option (Origin × String)) : List (Origin × InvalidInput) :=
  match halted with
  | some (o, kind) => [(o, .haltedPeer peer kind)]
  | none =>
    let seen := peerSeen normal service peer aLines bLines
    aLines.zipIdx.filterMap fun (l, i) => (peerFinding normal peer seen aLines bLines i l).map (Origin.line i, ·)

end Tazuna.Semantics
