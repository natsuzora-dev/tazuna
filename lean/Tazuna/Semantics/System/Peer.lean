import Tazuna.Semantics.InvalidInput
import Tazuna.Semantics.Step
import Tazuna.Data.Canonical

/-!
This module checks the mocks that a scenario takes from a peer, another spec service, against the peer's spec: it
derives the peer's inputs from the scenario's run, and compares the mocks, and the requests that the scenario takes from
the peer (from lines), with the peer's run of those inputs. The scenario may name a createKey value of the peer with
any string, and the peer's run may give a request its own id, one-to-one, as verify compares them.
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

/-- `bs` with `v` bound to `w`, when neither is bound yet. -/
def _root_.Tazuna.Data.Bindings.bindNew (bs : Bindings) (v w : String) : Option Bindings :=
  if (bs.lookup v).isNone && !bs.any (·.2 == w) then some (bs ++ [(v, w)]) else none

/-- Whether the answer rejects its request as unavailable. -/
def _root_.Tazuna.Data.Answer.unavailable : Answer → Bool
  | .rejected r => r.kind == .unavailable
  | _ => false

def _root_.Tazuna.Data.Answer.mapOutput (f : Value → Value) : Answer → Answer
  | .accepted output => .accepted (output.map f)
  | .fulfilled output => .fulfilled (f output)
  | .rejected r => .rejected r

/--
The peer's input of the run's line `l`: an answer of the scenario's service `service`, other than unavailable, to a
request of the run's from lines `fromLines`, which the peer sent. It answers the peer's request whose id `keys` binds
to the request's (peerForward), with the strings of its output renamed.
-/
def peerAnswer? (service : String) (aLines : List TraceLine) (fromLines : List Nat) (keys : Bindings) (l : TraceLine) :
    Option Step.Body :=
  match l.body with
  | .answer .out _ to a =>
    if a.unavailable then none else
    (fromLines.findSome? fun k => (aLines[k]?.bind (requestOf? .in ·.body)).bind fun (_, id, name, _) =>
      if id == to then some name else none).map fun name =>
      .answerTo ((keys.lookup to).getD to) s!"{service}.{name}" (a.mapOutput keys.rename)
  | _ => none

/--
The peer's input of the run's line `l` (peerBody?, peerEvent?, peerAnswer?), the strings of the run renamed by `keys`.
-/
def peerInput? (service peer : String) (received : List String) (fromLines : List Nat) (aLines : List TraceLine)
    (keys : Bindings) (l : TraceLine) : Option Step.Body :=
  ((peerBody? peer aLines keys l).orElse fun _ => peerEvent? service received keys l).orElse fun _ =>
    peerAnswer? service aLines fromLines keys l

/-- The trace name of the definition of another service whose message the input gives: an event, or an answer's target. -/
def Step.Body.received? : Step.Body → Option String
  | .event _ name _ _ | .answer _ name _ _ _ | .answerTo _ name _ => some name
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
  | .answerTo to target a => .answerTo to target (a.mapOutput keys.rename)
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

/-- Why unify gives no bindings. -/
inductive Unequal where
  /-- The values differ. -/
  | differ
  /-- A bag's search used up its tries before it found an order. -/
  | searchLimit
deriving DecidableEq, Repr, Inhabited

/-- The result of unifyBag with `searchLimit` tries: none left means that the search did not finish. -/
def searched : Except Nat Bindings → Except Unequal Bindings
  | .ok bs => .ok bs
  | .error 0 => .error .searchLimit
  | .error _ => .error .differ

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
`bs` extended so that the peer's value `s` equals the scenario's value `t`, or why not. A string of `created` equals the
string that it is bound to, and is bound when it is not (Bindings.bind); other strings equal themselves. Bags pair their
elements by backtracking, as verify's `free` does, after bagFits, with `searchLimit` tries each (unifyBag).
-/
def unify (created : List String) (s t : CValue) (bs : Bindings) : Except Unequal Bindings :=
  match s, t with
  | .leaf (.str v), t =>
    match t with
    | .leaf (.str w) =>
      if created.contains v then (bs.bind v w).elim (.error .differ) .ok
      else if w == v then .ok bs else .error .differ
    | _ => .error .differ
  | .leaf v, .leaf w => if w == v then .ok bs else .error .differ
  | .arr xs, .arr ys => if xs.length == ys.length then unifyList created xs ys bs else .error .differ
  | .runs xs, .runs ys => if xs.length == ys.length then unifyList created xs ys bs else .error .differ
  | .bag xs, .bag ys =>
    if bagFits created xs ys then searched (unifyBag created xs ys bs searchLimit) else .error .differ
  | .obj fs, .obj gs => if sameKeys fs gs then unifyFields created fs gs bs else .error .differ
  | _, _ => .error .differ
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

def unifyList (created : List String) (xs ys : List CValue) (bs : Bindings) : Except Unequal Bindings :=
  match xs, ys with
  | x :: xs, y :: ys => (unify created x y bs).bind (unifyList created xs ys)
  | _, _ => .ok bs
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

/-- The fields in the field order of `fs`. -/
def unifyFields (created : List String) (fs gs : List (String × CValue)) (bs : Bindings) : Except Unequal Bindings :=
  match fs with
  | [] => .ok bs
  | (k, v) :: fs =>
    (gs.lookup k).elim (.error .differ) fun w => (unify created v w bs).bind (unifyFields created fs gs)
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

/--
`bs` extended so that the elements of `ss` equal those of `ts` in some order, or, when no order is found within `left`
tries, the tries left. A try unifies an element of `ss` with an element of `ts`; a try whose own search did not finish
ends the search with none left.
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
    | .ok bs' =>
      match unifyBag created rest (passed.reverse ++ more) bs' left with
      | .ok bs'' => .ok bs''
      | .error left' => unifyBagFrom created first rest more (t :: passed) bs left'
    | .error .searchLimit => .error 0
    | .error .differ => unifyBagFrom created first rest more (t :: passed) bs left
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

/--
`bs` extended so that the mock's answer `a` is the peer's answer `b`, the peer's values in the form `seen` and the
mock's in the form `form`, or why not. Rejections compare by kind, as verify compares them.
-/
def unifyAnswer (created : List String) (seen form : Value → CValue) (bs : Bindings) :
    Answer → Answer → Except Unequal Bindings
  | .accepted (some x), .accepted (some y) => unify created (seen x) (form y) bs
  | .accepted none, .accepted none => .ok bs
  | .fulfilled x, .fulfilled y => unify created (seen x) (form y) bs
  | .rejected r, .rejected q => if r.kind == q.kind then .ok bs else .error .differ
  | _, _ => .error .differ

/-- The lines of `lines` that are `in` lines, each with its place in `lines`. -/
def inLines (lines : List TraceLine) : List (TraceLine × Nat) := lines.zipIdx.filter (·.1.body.dir == .in)

/--
The run's inputs to the peer and the scenario's elsewhere inputs to it, each with its origin, in the order that they
arrive: the run's requests to the peer, ends of subscriptions to it, events that the peer receives (`received`, by trace
name), and answers to the peer's requests of the from lines `fromLines` at their lines, taking the strings `keys n` at
the line `n`, and each elsewhere input before the number of the run's lines that `elsewhere` holds with it, unchanged.
-/
def peerPlaced (service peer : String) (received : List String) (fromLines : List Nat) (elsewhere : List (Nat × Step))
    (aLines : List TraceLine) (keys : Nat → Bindings) : List (Step × Origin) :=
  (List.range (aLines.length + 1)).flatMap fun n =>
    ((elsewhere.zipIdx.filter fun e => e.1.1 == n || (n == aLines.length && n < e.1.1)).map fun e =>
      (e.1.2, Origin.elsewhere e.2)) ++
    match aLines[n]? with
    | some l =>
      ((peerInput? service peer received fromLines aLines (keys n) l).map fun b =>
        (⟨l.time, b, none, none, none⟩, Origin.line n)).toList
    | none => []

/-- The number of the run's lines before which the input of origin `o` arrives, `elsewhere` as in peerPlaced. -/
def Origin.arrival (elsewhere : List (Nat × Step)) : Origin → Nat
  | .given => 0
  | .line n => n
  | .elsewhere k => (elsewhere[k]?.map (·.1)).getD 0

/--
The arrival of each input of the peer (Origin.arrival), in the order of peerInputs, the given state `state` first. The
origins do not depend on the strings that the inputs take.
-/
def peerArrivals (service peer : String) (received : List String) (fromLines : List Nat) (state : List Step)
    (elsewhere : List (Nat × Step)) (aLines : List TraceLine) : List Nat :=
  state.map (fun _ => 0) ++
    (peerPlaced service peer received fromLines elsewhere aLines fun _ => []).map (·.2.arrival elsewhere)

/--
The number of the peer's lines that it writes before it takes an input that arrives after the run's line `i`, the
input of its `k`-th `in` line arriving before the run's line `arrivals[k]` (peerArrivals). A line of the scenario's run
can come only from these lines of the peer, which do not depend on the scenario's later lines.
-/
def peerBefore (arrivals : List Nat) (bLines : List TraceLine) (i : Nat) : Nat :=
  match arrivals.findIdx? (i < ·) with
  | some k => ((inLines bLines)[k]?.map (·.2)).getD bLines.length
  | none => bLines.length

/--
Whether the peer's line `b` can send the scenario's from line `l`, with the bindings `bs`: none when `b` is not an `out`
line of the same request to the scenario's service `service`, or of the end of the subscription bound to the one that
`l` ends, by `l`'s time and with an id that no string is bound to yet. Otherwise `bs` with `b`'s id bound to `l`'s and,
for a request, extended so that its input is `l`'s (unify), the peer's in the form `seen` and the scenario's in the form
`form` of the definition by the scenario's own name.
-/
def sentAs? (created : List String) (seen form : String → Value → CValue) (service : String) (bs : Bindings)
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
def peerSent (created : List String) (seen form : String → Value → CValue) (service : String) (bs : Bindings)
    (before : List TraceLine) (l : TraceLine) : Except Unequal (Nat × Bindings) :=
  let tries := before.zipIdx.filterMap fun (b, j) => (sentAs? created seen form service bs l b).map (j, ·)
  match tries.findSome? fun (j, r) => r.toOption.map (j, ·) with
  | some p => .ok p
  | none => .error (if tries.any (·.2 matches .error .searchLimit) then .searchLimit else .differ)

/--
The check of the run's line `l`, the line `i` of the run, with the bindings `bs` of the peer's createKey values to the
strings that the scenario has in their place: its violation, or `bs` extended. A mocked answer to a request to the peer
that reached it must be the peer's answer at the same place, by its time; a received event of the peer must be one that
the peer emits by its time, with the `resultOf` that the event names, if any; a from line, one of `fromLines`, must be
a request that the peer sends by its time (peerSent). Each must come from the peer's lines before its inputs that arrive
after `l` (peerBefore). The peer's values have its peer keys turned back into the run's createKey values. `normal`
gives the form of an output or payload of the peer's definition, by the peer's own name, and `inputForm` the form of
an input of a request to the scenario's service, by its own name, that verify compares. A comparison that does not
finish within its tries gives peerSearchLimit.
-/
def peerLine (normal inputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (aLines bLines : List TraceLine) (bs : Bindings) (i : Nat) (l : TraceLine) : Except InvalidInput Bindings :=
  let created := bLines.flatMap (·.created.getD [])
  let back : Bindings := (peerKeys service aLines).map fun (k, v) => (v, k)
  let seen (n : String) (v : Value) : CValue := normal n (back.rename v)
  let before := bLines.take (peerBefore arrivals bLines i)
  match l.body with
  | .answer .in id to a =>
    match peerTarget? peer aLines to with
    | none => .ok bs
    | some target =>
      if unreached aLines to then .ok bs else
      let k := (answersTo (aLines.take i) .in to).length
      if (answersTo bLines .out to)[k]?.isNone then .error (.unansweredRequest to ⟨peer, target⟩) else
      match (answersTo before .out to)[k]? with
      | none => .error (.unproducibleAnswer to ⟨peer, target⟩)
      | some (t, b) =>
        match if t.time ≤ l.time.time then unifyAnswer created (seen target) (normal target) bs b a
          else .error .differ with
        | .ok bs => .ok bs
        | .error .differ => .error (.unproducibleAnswer to ⟨peer, target⟩)
        | .error .searchLimit => .error (.peerSearchLimit id peer)
  | .event .in id name payload resultOf =>
    match peerName? peer name with
    | none => .ok bs
    | some n =>
      let tries := before.filterMap fun b =>
        match b.body with
        | .event .out _ m p r =>
          if m == n && b.time.time ≤ l.time.time && resultOf.all (r == some ·) then
            some (unify created (seen n p) (normal n payload) bs)
          else none
        | _ => none
      match tries.findSome? (·.toOption) with
      | some bs => .ok bs
      | none =>
        .error (if tries.any (· matches .error .searchLimit) then .peerSearchLimit id peer
          else .unproducibleEvent id ⟨peer, n⟩)
  | .command .in .. | .query .in .. | .subscribe .in .. | .unsubscribe .in .. =>
    if fromLines.contains i then
      match peerSent created (fun n v => inputForm n (back.rename v)) inputForm service bs before l with
      | .ok (_, bs) => .ok bs
      | .error .differ => .error (.unproducibleRequest l.body.id peer)
      | .error .searchLimit => .error (.peerSearchLimit l.body.id peer)
    else .ok bs
  | _ => .ok bs

/-- The bindings after the run's first `n` lines (peerLine): a line with a violation keeps them. -/
def peerBindings (normal inputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (aLines bLines : List TraceLine) (n : Nat) : Bindings :=
  (aLines.zipIdx.take n).foldl (init := []) fun bs (l, i) =>
    (peerLine normal inputForm service peer fromLines arrivals aLines bLines bs i l).toOption.getD bs

/--
The strings that the peer takes in place of the scenario's strings before the run's line `n`: each createKey value of
the run as its peer key, and each string bound by then (peerBindings) as the peer's createKey value or request id
bound to it.
-/
def peerForward (normal inputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (aLines bLines : List TraceLine) (n : Nat) : Bindings :=
  peerKeys service aLines ++
    (peerBindings normal inputForm service peer fromLines arrivals aLines bLines n).map fun (k, v) => (v, k)

/--
The peer's inputs, each with its origin: those of the given state `state`, then those of peerPlaced. The run's lines and
the elsewhere inputs take the peer's strings (peerForward) of the place where they arrive. `bLines` is the peer's run of
these inputs.
-/
def peerInputs (normal inputForm : String → Value → CValue) (service peer : String) (received : List String)
    (fromLines : List Nat) (state : List Step) (elsewhere : List (Nat × Step)) (aLines bLines : List TraceLine) :
    List (Step × Origin) :=
  let forward := peerForward normal inputForm service peer fromLines
    (peerArrivals service peer received fromLines state elsewhere aLines) aLines bLines
  let placed := peerPlaced service peer received fromLines elsewhere aLines forward
  state.map (·, Origin.given) ++ placed.map fun (s, o) =>
    match o with
    | .elsewhere _ => ({ s with body := s.body.forPeer (forward (o.arrival elsewhere)) }, o)
    | _ => (s, o)

/--
The violations of the scenario's mocks of the peer, each with the origin of its cause. `bLines` is the peer's run of
`peerInputs`, `arrivals` their peerArrivals, and `halted` the origin of the input that halted it, with the halting
violation's kind. A halted run gives only haltedPeer.
-/
def peerFindings (normal inputForm : String → Value → CValue) (service peer : String) (fromLines arrivals : List Nat)
    (aLines bLines : List TraceLine) (halted : Option (Origin × String)) : List (Origin × InvalidInput) :=
  match halted with
  | some (o, kind) => [(o, .haltedPeer peer kind)]
  | none =>
    aLines.zipIdx.filterMap fun (l, i) =>
      match peerLine normal inputForm service peer fromLines arrivals aLines bLines
          (peerBindings normal inputForm service peer fromLines arrivals aLines bLines i) i l with
      | .error v => some (Origin.line i, v)
      | .ok _ => none

end Tazuna.Semantics
