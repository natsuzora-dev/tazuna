import Tazuna.Semantics.InvalidInput
import Tazuna.Semantics.Step
import Tazuna.Data.Canonical

/-!
This module checks the mocks that a scenario takes from a peer, another spec service, against the peer's spec: it
derives the peer's inputs from the scenario's run, and compares the mocks with the peer's run of those inputs. The
scenario may name a createKey value of the peer with any string, one-to-one, as verify compares createKey values.
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
    | .command .out (some i) name _ | .query .out (some i) name _ | .subscribe .out (some i) name _ =>
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
  | .command .out (some id) name input => (reached id name).map (.command (some id) · (keys.rename input))
  | .query .out (some id) name input => (reached id name).map (.query (some id) · (keys.rename input))
  | .subscribe .out (some id) name input => (reached id name).map (.subscribe (some id) · (keys.rename input))
  | .unsubscribe .out _ to =>
    if (peerTarget? peer lines to).isSome && !unreached lines to then some (.unsubscribe to) else none
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

/--
The id of the `in` line at or before the run's line `j`, from 0: an event that the run emits as the result of a request
follows the request's `in` line before the next input.
-/
def inputOf? (lines : List TraceLine) (j : Nat) : Option String :=
  ((lines.take (j + 1)).reverse.find? (·.body.dir == .in)).bind (·.body.id)

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

/-- The answers in direction `dir` to the request `id`, in order, with their times. -/
def answersTo (lines : List TraceLine) (dir : Dir) (id : String) : List (DateTime × Answer) :=
  lines.filterMap fun l =>
    match l.body with
    | .answer d _ to a => if d == dir && to == id then some (l.time, a) else none
    | _ => none

/-- `bs` with `v` bound to `w`, unless `v` is bound to another string or another string to `w`. -/
def _root_.Tazuna.Data.Bindings.bind (bs : Bindings) (v w : String) : Option Bindings :=
  match bs.lookup v with
  | some x => if x == w then some bs else none
  | none => if bs.any (·.2 == w) then none else some (bs ++ [(v, w)])

mutual

/--
Whether the peer's value `s` can equal the scenario's value `t` under some bindings: unify's comparison with each
string of `created` equal to any string, and bags compared by their sizes.
-/
def fits (created : List String) : CValue → CValue → Bool
  | .leaf (.str v), .leaf (.str w) => created.contains v || w == v
  | .leaf v, .leaf w => w == v
  | .arr xs, .arr ys | .runs xs, .runs ys => fitsList created xs ys
  | .bag xs, .bag ys => xs.length == ys.length
  | .obj fs, .obj gs => sameKeys fs gs && fitsFields created fs gs
  | _, _ => false

def fitsList (created : List String) : List CValue → List CValue → Bool
  | x :: xs, y :: ys => fits created x y && fitsList created xs ys
  | [], [] => true
  | _, _ => false

def fitsFields (created : List String) : List (String × CValue) → List (String × CValue) → Bool
  | [], _ => true
  | (k, v) :: fs, gs => (gs.lookup k).any (fits created v) && fitsFields created fs gs

end

/--
Whether the elements of `ss` can pair one to one with those of `ts` as far as fits tells: the elements of `ss` that
fit the same elements of `ts` are no more than those elements. unify fails at once otherwise, before it searches.
-/
def bagFits (created : List String) (ss ts : List CValue) : Bool :=
  let fitting (s : CValue) : List Nat := ts.zipIdx.filterMap fun (t, k) => if fits created s t then some k else none
  ss.all fun s => (ss.filter (fitting · == fitting s)).length ≤ (fitting s).length

mutual

/--
`bs` extended so that the peer's value `s` equals the scenario's value `t`, or none. A string of `created` equals the
string that it is bound to, and is bound when it is not (Bindings.bind); other strings equal themselves. Bags pair their
elements by backtracking, as verify's `free` does, after bagFits; a bag whose search takes more than `searchLimit`
tries does not equal (unifyBag).
-/
def unify (created : List String) (s t : CValue) (bs : Bindings) : Option Bindings :=
  match s, t with
  | .leaf (.str v), t =>
    match t with
    | .leaf (.str w) => if created.contains v then bs.bind v w else if w == v then some bs else none
    | _ => none
  | .leaf v, .leaf w => if w == v then some bs else none
  | .arr xs, .arr ys => if xs.length == ys.length then unifyList created xs ys bs else none
  | .runs xs, .runs ys => if xs.length == ys.length then unifyList created xs ys bs else none
  | .bag xs, .bag ys => if bagFits created xs ys then (unifyBag created xs ys bs searchLimit).toOption else none
  | .obj fs, .obj gs => if sameKeys fs gs then unifyFields created fs gs bs else none
  | _, _ => none
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

def unifyList (created : List String) (xs ys : List CValue) (bs : Bindings) : Option Bindings :=
  match xs, ys with
  | x :: xs, y :: ys => (unify created x y bs).bind (unifyList created xs ys)
  | _, _ => some bs
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

/-- The fields in the field order of `fs`. -/
def unifyFields (created : List String) (fs gs : List (String × CValue)) (bs : Bindings) : Option Bindings :=
  match fs with
  | [] => some bs
  | (k, v) :: fs => (gs.lookup k).bind fun w => (unify created v w bs).bind (unifyFields created fs gs)
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

/--
`bs` extended so that the elements of `ss` equal those of `ts` in some order, or, when no order is found within `left`
tries, the tries left. A try unifies an element of `ss` with an element of `ts`.
-/
def unifyBag (created : List String) (ss ts : List CValue) (bs : Bindings) (left : Nat) : Except Nat Bindings :=
  if ss.length != ts.length then .error left
  else
    match ss with
    | [] => .ok bs
    | first :: rest => unifyBagFrom created first rest ts [] bs left
termination_by (sizeOf ss, ts.length + 1)
decreasing_by all_goals lex_decreasing

/-- The search of unifyBag for `first`. `passed` holds the candidates tried. -/
def unifyBagFrom (created : List String) (first : CValue) (rest cands passed : List CValue) (bs : Bindings)
    (left : Nat) : Except Nat Bindings :=
  match cands, left with
  | [], left => .error left
  | _ :: _, 0 => .error 0
  | t :: more, left + 1 =>
    match unify created first t bs with
    | some bs' =>
      match unifyBag created rest (passed.reverse ++ more) bs' left with
      | .ok bs'' => .ok bs''
      | .error left' => unifyBagFrom created first rest more (t :: passed) bs left'
    | none => unifyBagFrom created first rest more (t :: passed) bs left
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

/--
`bs` extended so that the mock's answer `a` is the peer's answer `b`, the peer's values in the form `seen` and the
mock's in the form `form`, or none. Rejections compare by kind, as verify compares them.
-/
def unifyAnswer (created : List String) (seen form : Value → CValue) (bs : Bindings) : Answer → Answer → Option Bindings
  | .accepted (some x), .accepted (some y) => unify created (seen x) (form y) bs
  | .accepted none, .accepted none => some bs
  | .fulfilled x, .fulfilled y => unify created (seen x) (form y) bs
  | .rejected r, .rejected q => if r.kind == q.kind then some bs else none
  | _, _ => none

/--
The check of the run's line `l`, the line `i` of the run, with the bindings `bs` of the peer's createKey values to the
strings that the scenario has in their place: its violation, or `bs` extended. A mocked answer to a request to the peer
that reached it must be the peer's answer at the same place, by its time; a received event of the peer must be one that
the peer emits by its time, after the `in` line of the request that it names as its result (inputOf?). The peer's
values have its peer keys turned back into the run's createKey values, and `normal` gives the form of an output or
payload of the peer's definition, by the peer's own name, that verify compares.
-/
def peerLine (normal : String → Value → CValue) (service peer : String) (aLines bLines : List TraceLine)
    (bs : Bindings) (i : Nat) (l : TraceLine) : Except InvalidInput Bindings :=
  let created := bLines.flatMap (·.created.getD [])
  let back : Bindings := (peerKeys service aLines).map fun (k, v) => (v, k)
  let seen (n : String) (v : Value) : CValue := normal n (back.rename v)
  match l.body with
  | .answer .in _ to a =>
    match peerTarget? peer aLines to with
    | none => .ok bs
    | some target =>
      if unreached aLines to then .ok bs else
      match (answersTo bLines .out to)[(answersTo (aLines.take i) .in to).length]? with
      | none => .error (.unansweredRequest to ⟨peer, target⟩)
      | some (t, b) =>
        match if t.time ≤ l.time.time then unifyAnswer created (seen target) (normal target) bs b a else none with
        | some bs => .ok bs
        | none => .error (.unproducibleAnswer to ⟨peer, target⟩)
  | .event .in id name payload resultOf =>
    match peerName? peer name with
    | none => .ok bs
    | some n =>
      let found := bLines.zipIdx.findSome? fun (b, j) =>
        match b.body with
        | .event .out _ m p _ =>
          if m == n && b.time.time ≤ l.time.time && resultOf.all (inputOf? bLines j == some ·) then
            unify created (seen n p) (normal n payload) bs
          else none
        | _ => none
      match found with
      | some bs => .ok bs
      | none => .error (.unproducibleEvent (id.getD "") ⟨peer, n⟩)
  | _ => .ok bs

/-- The bindings after the run's first `n` lines (peerLine): a line with a violation keeps them. -/
def peerBindings (normal : String → Value → CValue) (service peer : String) (aLines bLines : List TraceLine)
    (n : Nat) : Bindings :=
  (aLines.zipIdx.take n).foldl (init := []) fun bs (l, i) =>
    (peerLine normal service peer aLines bLines bs i l).toOption.getD bs

/--
The strings that the peer takes in place of the scenario's strings before the run's line `n`: each createKey value of
the run as its peer key, and each string bound by then (peerBindings) as the peer's createKey value bound to it.
-/
def peerForward (normal : String → Value → CValue) (service peer : String) (aLines bLines : List TraceLine)
    (n : Nat) : Bindings :=
  peerKeys service aLines ++ (peerBindings normal service peer aLines bLines n).map fun (k, v) => (v, k)

/--
The peer's inputs, each with its origin: those of the given state `state`, then the run's requests to the peer, ends
of subscriptions to it, and events that the peer receives (`received`, by trace name) at their times, with the
scenario's elsewhere inputs among them. `elsewhere` holds each elsewhere input with the number of the run's lines
before it, and its resultOf indexes `state ++ elsewhere`. The run's lines and the elsewhere inputs take the peer's
strings (peerForward) of the place where they arrive. `bLines` is the peer's run of these inputs.
-/
def peerInputs (normal : String → Value → CValue) (service peer : String) (received : List String) (state : List Step)
    (elsewhere : List (Nat × Step)) (aLines bLines : List TraceLine) : List (Step × Origin) :=
  let forward := peerForward normal service peer aLines bLines
  let placedAt (n : Nat) : List (Step × Origin) :=
    ((elsewhere.zipIdx.filter fun e => e.1.1 == n || (n == aLines.length && n < e.1.1)).map fun e =>
      (e.1.2, Origin.elsewhere e.2)) ++
    match aLines[n]? with
    | some l =>
      (((peerBody? peer aLines (forward n) l).orElse fun _ => peerEvent? service received (forward n) l).map fun b =>
        (⟨l.time, b, none, none⟩, Origin.line n)).toList
    | none => []
  let placed := (List.range (aLines.length + 1)).flatMap placedAt
  let index (r : Nat) : Nat :=
    if r < state.length then r
    else state.length + (placed.findIdx? (·.2 == Origin.elsewhere (r - state.length))).getD 0
  state.map (·, Origin.given) ++ placed.map fun (s, o) =>
    match o with
    | .elsewhere k => ({ s with body := s.body.forPeer (forward ((elsewhere[k]?.map (·.1)).getD 0)) index }, o)
    | _ => (s, o)

/--
The violations of the scenario's mocks of the peer, each with the origin of its cause. `bLines` is the peer's run of
`peerInputs`, and `halted` the origin of the input that halted it, with the halting violation's kind. A halted run
gives only haltedPeer.
-/
def peerFindings (normal : String → Value → CValue) (service peer : String) (aLines bLines : List TraceLine)
    (halted : Option (Origin × String)) : List (Origin × InvalidInput) :=
  match halted with
  | some (o, kind) => [(o, .haltedPeer peer kind)]
  | none =>
    aLines.zipIdx.filterMap fun (l, i) =>
      match peerLine normal service peer aLines bLines (peerBindings normal service peer aLines bLines i) i l with
      | .error v => some (Origin.line i, v)
      | .ok _ => none

end Tazuna.Semantics
