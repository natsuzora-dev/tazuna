import Tazuna.Data.Trace
import Tazuna.Data.Canonical
import Tazuna.Spec.Structure
import Tazuna.Data.Binding
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable

/-!
This module compares an implementation trace with a snapshot. The harness gave the implementation the snapshot's `in`
lines one by one under one deterministic simulation, so the lines align without a search; only the bindings of the
values that the implementation chose in its own way are open.

- Values are read by their definition's schema (the `ask` parameter) and compare as CValue.
- A binding (Data/Binding) maps snapshot strings to implementation strings, one to one within each domain
  (valueDomains): request ids, the keys of each entity, and the other strings. A value that a snapshot line introduces
  (the id of an `out` request, a `created` key) is fresh until bound and binds to the implementation string at the same
  place of a compared line that holds it, maybe in a later group; a request id or key that is not fresh binds to itself;
  any other string compares equal to itself without entering the binding. A string that already stands for another
  value of its domain does not compare equal, so an implementation that reuses an existing request id or key for a new
  one differs, while using an input's string (a title, an idempotency key) as a new key does not.
- The comparison carries the set of every binding that agrees with the lines compared so far (forward state-set
  tracking, as ioco testers do). Each compared line keeps the bindings under which it compares equal, extended by the
  values that it binds; a bag or a group of lines that pairs in several ways keeps each way's binding. The set holds
  at most `bindingLimit` bindings, and a line that would make it hold more is reported as `bindingLimit`. A line that
  would leave no binding is reported, and the set stays as it was before it. Bindings that the lines cannot tell apart
  stay in the set to the end, and each of them is fine.
- `in` lines align by position and compare under each binding of the set. After the first `in` line that differs or is
  missing, nothing later is compared. The harness gives an `in` line by one binding of the set (the first); when the
  line names a value that the bindings give different implementation values (a route that the set does not decide),
  verify reports the line as ambiguous unless the snapshot's `in` lines use alike every value that may stand for those
  (sameUses), since then every route gives the implementation the same inputs.
- The `out` lines after an `in` line, or before the first, are that input's group. A group's snapshot lines, in file
  order, each pair with any unpaired trace line of the group that compares equal under a binding of the set, at the same
  time and after the lines that its `after` names, keeping every way. `after` names the earlier lines on the line's
  channel (Sim.ordered), so a group keeps each channel's order and no order across channels. test compares two
  orders of a processing alike (ChoiceDependent), so a spec without that report fixes each channel's order.
- A snapshot line that pairs in no way pairs by place (type and name, or the answered request under the first way) to
  report how it differs; a line with no place is missing, and the trace lines that the first way leaves unpaired are
  unexpected. The set keeps the ways that leave the same trace lines unpaired. Paired lines compare their time and the
  snapshot's `after` order.
- Verify reports the trace's first malformed line, and the first `out` request line with the id of an earlier one
  (duplicateId), and compares neither the group of the first of them nor anything later. Other lines' ids name no
  line, so the ids that the harness gives the lines that the implementation gives no id never meet them.
-/

namespace Tazuna.Verify

open Tazuna.Data
open Tazuna.Spec

/--
A trace line with its value read by its definition's schema, if any. `value` is the input, payload or answer output,
and `body` holds it as JSON.
-/
structure Line extends TraceLine where
  value : Option CValue
deriving Inhabited

/-- Where the schema comes from: a definition's input, output or payload, or a screen control's payload. -/
inductive Part where
  | input
  | output
  | payload
  | control (name : String)

derive_wire Part tag "kind"

/-- The value read by the definition's schema when the definition is known, and as a plain CValue otherwise. -/
def readValue {m : Type → Type} [Monad m] (ask : Definition → Part → Value → m CValue) (d : Option Definition)
    (part : Part) (v : Value) : m CValue :=
  match d with
  | some d => ask d part v
  | none => pure (CValue.ofValue v)

def comparableAnswer {m : Type → Type} [Monad m] (ask : Definition → Part → Value → m CValue)
    (shape : Option Definition) : Answer → m (Answer × Option CValue)
  | .rejected r => pure (.rejected { kind := r.kind }, none)
  | .accepted none => pure (.accepted none, none)
  | .accepted (some output) => do
    let compared ← readValue ask shape .output output
    pure (.accepted (some compared.flatten), some compared)
  | .fulfilled output => do
    let compared ← readValue ask shape .output output
    pure (.fulfilled compared.flatten, some compared)

/-- The list with `v` at key `k`, replaced in place if `k` exists and appended otherwise (JS `Map.set`). -/
def setAt {β : Type} : List (String × β) → String → β → List (String × β)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v => if k' == k then (k, v) :: rest else (k', v') :: setAt rest k v

/--
The comparable form of a trace line. An answer's output is read with the output schema of the definition that its
request line named. `outputByRequestId` carries over from the snapshot lines to the implementation lines.
-/
def readLine {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue)
    (outputByRequestId : List (String × Definition)) (l : TraceLine) : m (Line × List (String × Definition)) := do
  let read := readValue ask
  let line (body : TraceLine.Body) (value : Option CValue) : Line := { l with body, value }
  let request (d : Option Definition) (id : String) : List (String × Definition) :=
    match d with
    | some d => if d.hasOutput then setAt outputByRequestId id d else outputByRequestId
    | none => outputByRequestId
  let control (name : String) : Option Definition × Part :=
    let (screen, control) := operationParts name
    let d := s.named service (some screen) ["screen"]
    let hasPayload := (d.bind fun d => d.chart?.bind fun c => c.controls.lookup control).any (·.isSome)
    (if hasPayload then d else none, .control control)
  match l.body with
  | .operation dir id name nth payload =>
    let (d, part) := control name
    let value ← payload.mapM (read d part)
    pure (line (.operation dir id name nth (value.map (·.flatten))) value, outputByRequestId)
  | .answer dir id to answer =>
    let (answer, value) ← comparableAnswer ask (outputByRequestId.lookup to) answer
    pure (line (.answer dir id to answer) value, outputByRequestId)
  | .event dir id name payload resultOf =>
    let value ← read (s.named service (some name) ["event"]) .payload payload
    pure (line (.event dir id name value.flatten resultOf) (some value), outputByRequestId)
  | .command dir id name input =>
    let d := s.named service (some name) ["command"]
    let value ← read d .input input
    pure (line (.command dir id name value.flatten) (some value), request d id)
  | .query dir id name input =>
    let d := s.named service (some name) ["query"]
    let value ← read d .input input
    pure (line (.query dir id name value.flatten) (some value), request d id)
  | .subscribe dir id name input =>
    let d := s.named service (some name) ["query"]
    let value ← read d .input input
    pure (line (.subscribe dir id name value.flatten) (some value), request d id)
  | .unsubscribe .. | .time .. | .restart .. => pure (line l.body none, outputByRequestId)

def readLines {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue) :
    List (Option TraceLine) → List (String × Definition) → m (List (Option Line) × List (String × Definition))
  | [], outputByRequestId => pure ([], outputByRequestId)
  | none :: ls, outputByRequestId => do
    let (rest, outputByRequestId) ← readLines s service ask ls outputByRequestId
    pure (none :: rest, outputByRequestId)
  | some l :: ls, outputByRequestId => do
    let (line, outputByRequestId) ← readLine s service ask outputByRequestId l
    let (rest, outputByRequestId) ← readLines s service ask ls outputByRequestId
    pure (some line :: rest, outputByRequestId)

/-- The JSON form of `answer`, with the given output as its output. -/
def answerContent (answer : Answer) : Option CValue → CValue
  | some output => .obj [("result", .leaf (.str answer.result)), ("output", output)]
  | none => CValue.ofValue (ToValue.toValue answer)

def Line.content (l : Line) : Option CValue :=
  match l.body with
  | .answer _ _ _ answer => some (answerContent answer l.value)
  | _ => l.value

/--
The lines with each `out` answer to a subscription that equals the previous answer to it set to `none`. A
subscription is open from the `in` subscribe to the `in` unsubscribe or restart. Values compare ignoring bag order and
object field order.
-/
def withoutRepeatedAnswers (lines : List (Option Line)) : List (Option Line) :=
  go lines []
where
  go : List (Option Line) → List (String × Option String) → List (Option Line)
    | [], _ => []
    | none :: ls, o => none :: go ls o
    | some l :: ls, o =>
      match l.body with
      | .subscribe .in id _ _ => some l :: go ls (if (o.lookup id).isSome then o else o ++ [(id, none)])
      | .unsubscribe .in _ to => some l :: go ls (o.filter (·.1 != to))
      | .restart .in _ => some l :: go ls []
      | .answer .out _ to answer =>
        match o.lookup to with
        | some last =>
          let k := (answerContent answer l.value).key
          if last == some k then none :: go ls o else some l :: go ls (setAt o to (some k))
        | none => some l :: go ls o
      | _ => some l :: go ls o

/-- Whether `l` is an `out` event line whose definition exists and no contract lists. -/
def internalEvent (s : Structure) (service : String) (l : Line) : Bool :=
  match l.body with
  | .event .out _ name _ _ =>
    match s.named service (some name) ["event"] with
    | some d => (s.contractsListing d.ref).isEmpty
    | none => false
  | _ => false

/-- A line with its line number, counted from 1. -/
structure Numbered where
  line : Line
  index : Nat
deriving Inhabited

/-- An `in` line and the `out` lines after it up to the next `in` line. The first group may have no `in` line. -/
structure Group where
  input : Option Numbered
  outs : List Numbered

/-- The groups of `lines`. A `none` line is a blank line or a line that verify does not compare, and only takes a
number. -/
def groups (lines : List (Option Line)) : List Group :=
  go lines 1 none []
where
  go : List (Option Line) → Nat → Option Numbered → List Numbered → List Group
    | [], _, input, acc => [{ input, outs := acc.reverse }]
    | none :: ls, i, input, acc => go ls (i + 1) input acc
    | some l :: ls, i, input, acc =>
      if l.body.dir == .out then go ls (i + 1) input ({ line := l, index := i } :: acc)
      else { input, outs := acc.reverse } :: go ls (i + 1) (some { line := l, index := i }) []

inductive Finding where
  | mismatch (m : Mismatch)
  | uncomparable (u : Uncomparable)

/-- The violations of a comparison, and the bindings that agree with every compared line. -/
structure Compared where
  findings : List Finding
  bindings : List Binding

def Line.isOutRequest (l : Line) : Bool :=
  match l.body with
  | .command .out .. | .query .out .. | .subscribe .out .. => true
  | _ => false

/-- The values that the snapshot line introduces: the id of an `out` request and the line's `created` keys. -/
def Line.fresh (l : Line) : List String :=
  (if l.isOutRequest then [l.body.id] else []) ++ l.created.getD []

def Line.fields (l : Line) : Value :=
  match ToValue.toValue l.body with
  | .obj fs => .obj (fs.filter fun (k, _) => k == "type" || k == "dir" || k == "name" || k == "nth")
  | v => v

/--
The bindings under which snapshot line `s` compares equal with implementation line `t`, apart from their time: their
type, direction and name are equal; the id of an `out` request binds, and an `in` line's id compares, while other `out`
lines' ids are not compared; the answered request, `resultOf` and the content compare under the binding.
-/
def matchContent (v : Values) (b : Binding) (s t : Line) : Matches b :=
  if s.fields != t.fields then some []
  else
    let ids : Matches b :=
      if s.body.dir == .in || s.isOutRequest then v.bind b s.body.id t.body.id
      else some [⟨b, .refl b⟩]
    let opt (x y : Option String) (b : Binding) : Matches b :=
      match x, y with
      | none, none => some [⟨b, .refl b⟩]
      | some x, some y => v.bind b x y
      | _, _ => some []
    ids.andThen fun b =>
      (opt s.body.to? t.body.to? b).andThen fun b =>
        (opt s.body.resultOf? t.body.resultOf? b).andThen fun b => matchOption v b s.content t.content

/-- The bindings under which snapshot line `s` compares equal with implementation line `t`: at the same time, and by
matchContent. -/
def matchLine (v : Values) (b : Binding) (s t : Line) : Matches b :=
  if s.time.time == t.time.time then matchContent v b s t else some []

def json (v : Option CValue) : Value := (v.map (·.flatten)).getD .null

def lineValue (l : Line) : Value := ToValue.toValue l.toTraceLine

/-- Whether two unpaired lines stand at one place: the same type, direction and name, and for an answer or unsubscribe
the same request under the binding. -/
def samePlace (b : Bindings) (s t : Line) : Bool :=
  s.fields == t.fields && (s.body.to?.map fun to => (b.lookup to).getD to) == t.body.to?

/-- How the paired-by-place line `t` differs from snapshot line `s`. -/
def difference (s : Line) (t : Numbered) : Mismatch :=
  let subject := Subject.of t.line.toTraceLine
  match s.body, t.line.body with
  | .answer _ _ _ sa, .answer _ _ _ ta =>
    match sa, ta with
    | .rejected sr, .rejected tr => .rejection t.index subject sr.kind tr.kind
    | _, _ =>
      if sa.result != ta.result then .result t.index subject sa.result ta.result
      else .output t.index subject (json s.content) (json t.line.content)
  | .event _ _ _ _ sr, .event _ _ _ _ tr =>
    if (s.content.map (·.key)) == (t.line.content.map (·.key)) then .resultOf t.index subject sr tr
    else .event t.index subject (json s.content) (json t.line.content)
  | .operation .., _ => .operation t.index subject (json s.content) (json t.line.content)
  | _, _ => .request t.index subject (json s.content) (json t.line.content)

/-- The report of snapshot line `s` that the trace lacks, at trace line `place`. -/
def missing (s : Numbered) (place : Nat) : Mismatch :=
  let subject := Subject.of s.line.toTraceLine
  match s.line.body with
  | .answer .. => .missingAnswer place subject s.index
  | .subscribe .out .. => .unopenedSubscription place subject (json s.line.content) s.index
  | _ => .missingLine place subject (json s.line.content) s.index

def unexpected (t : Numbered) : Mismatch :=
  let subject := Subject.of t.line.toTraceLine
  match t.line.body with
  | .subscribe .out .. => .unexpectedSubscription t.index subject (json t.line.content)
  | _ => .unexpectedLine t.index subject

def earlierWithId (earlier : List Numbered) (id : String) : Option Numbered :=
  earlier.reverse.find? fun o => o.line.body.id == id

/-- Each `after` id of a snapshot `out` line that names no earlier `out` line of its group, at that snapshot line. -/
def unknownAfters (snapshot : List (Option Line)) : List Uncomparable :=
  (groups snapshot).flatMap fun g =>
    g.outs.zipIdx.flatMap fun (o, k) =>
      (o.line.after.getD []).filterMap fun id =>
        if (earlierWithId (g.outs.take k) id).isSome then none else some (.unknownAfter o.index id)

/-- The lines of the group, by number, that snapshot line `o` (its `k`th) must follow. -/
def mustFollow (outs : List Numbered) (o : Numbered) (k : Nat) : List Nat :=
  (o.line.after.getD []).filterMap fun id => (earlierWithId (outs.take k) id).map (·.index)

/-- Whether snapshot line `i` may pair with trace line `j` after `pairs`: each line it must follow that is paired is
paired with a trace line before `j`. -/
def followsPaired (snapshot : List Numbered) (pairs : List (Nat × Nat)) (i j : Nat) : Bool :=
  match snapshot.zipIdx.find? (·.1.index == i) with
  | none => true
  | some (s, k) =>
    (mustFollow snapshot s k).all fun n =>
      match pairs.find? (·.1 == n) with
      | some (_, before) => before < j
      | none => true

/-- The request ids that line `l` names: the id of a request line, the answered or unsubscribed request, and resultOf. -/
def Line.requestIds (l : Line) : List String :=
  (match l.body with
    | .command .. | .query .. | .subscribe .. => [l.body.id]
    | _ => []) ++ l.body.to?.toList ++ l.body.resultOf?.toList

/--
The domain of each snapshot value: `request` for a request id that a snapshot line names, else the entity of the first
key reference that holds it (CValue.ref), else "".
-/
def valueDomains (snapshot : List (Option Line)) : String → String :=
  let lines := snapshot.filterMap id
  let requests := lines.flatMap Line.requestIds
  let keys := lines.flatMap fun l => (l.content.map CValue.keyRefs).getD []
  fun s => if requests.contains s then "request" else (keys.lookup s).getD ""
/-- The line that orders a finding in a report. -/
def Finding.line : Finding → Nat
  | .mismatch m => m.line?.getD 0
  | .uncomparable u => u.line?.getD 0

def differentInput (b : Binding) (s t : Numbered) : Finding :=
  .uncomparable (.differentInput t.index s.index (Bindings.substitute b.strings (lineValue s.line)) (lineValue t.line))

/-- One way of pairing a group's lines so far: its binding, and the snapshot and trace lines paired, by number. -/
structure State (root : Binding) where
  binding : From root
  pairs : List (Nat × Nat)

def State.used {root : Binding} (st : State root) : List Nat := st.pairs.map (·.2)

/--
Whether two ways go on alike: the same binding, the same trace lines paired, and the same pairs of the snapshot lines
`named`, those that an `after` names.
-/
def State.same {root : Binding} (named : List Nat) (a b : State root) : Bool :=
  a.binding.same b.binding && sameSet a.used b.used &&
    sameSet (a.pairs.filter fun p => named.contains p.1) (b.pairs.filter fun p => named.contains p.1)

/-- The items, each once by `same`, in the order of their first appearance. -/
def distinctBy {α : Type} (same : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.any (same x) then acc else acc ++ [x]) []

/-- The ways that pair snapshot line `s` with trace line `t` under the bindings `cs` that extend the way's binding. -/
def State.paired {root : Binding} (st : State root) (s t : Numbered) (cs : List (From st.binding.val)) :
    List (State root) :=
  (lift st.binding.property cs).map fun c => { binding := c, pairs := st.pairs ++ [(s.index, t.index)] }

def overLimit (place : Nat) (s : Numbered) : Finding :=
  .uncomparable (.bindingLimit place (Subject.of s.line.toTraceLine) s.index bindingLimit)

/--
One snapshot line of the exact pass: each way pairs it with every unpaired trace line of the group that compares equal,
at the same time and after the lines it must follow. A line that pairs in no way goes to the failed lines.
-/
def pairExact {root : Binding} (v : Values) (snapshot trace : List Numbered) (place : Nat)
    (same : State root → State root → Bool) (acc : List (State root) × List Numbered) (s : Numbered) :
    Except Finding (List (State root) × List Numbered) :=
  let (states, failed) := acc
  let next (st : State root) : Option (List (State root)) := do
    let ways ← (trace.filter fun t => !st.used.contains t.index && followsPaired snapshot st.pairs s.index t.index).mapM
      fun t => (matchLine v st.binding.val s.line t.line).map (st.paired s t)
    pure ways.flatten
  match expand same states next with
  | none => .error (overLimit place s)
  | some [] => .ok (states, failed ++ [s])
  | some ways => .ok (ways, failed)

/--
One failed line of the place pass. It pairs, in snapshot order, with the first trace line at its place that the first
way leaves unpaired; `true` when its content compares equal, so that it differs only in its time or order, which
compareGroup reports. A line with no place stays unpaired.
-/
def pairPlace {root : Binding} (v : Values) (trace : List Numbered) (place : Nat) (same : State root → State root → Bool)
    (acc : List (State root) × List (Numbered × Option (Numbered × Bool))) (s : Numbered) :
    Except Finding (List (State root) × List (Numbered × Option (Numbered × Bool))) :=
  let (states, placed) := acc
  let first := states.head?
  let at? := first.bind fun w =>
    trace.find? fun t => !w.used.contains t.index && samePlace w.binding.val.strings s.line t.line
  match at? with
  | none => .ok (states, placed ++ [(s, none)])
  | some t =>
    let free := states.filter fun st => !st.used.contains t.index
    match expand same free fun st => (matchContent v st.binding.val s.line t.line).map (st.paired s t) with
    | none => .error (overLimit place s)
    | some (w :: ws) => .ok (w :: ws, placed ++ [(s, some (t, true))])
    | some [] =>
      let bound := free.map fun st =>
        let id := s.line.body.id
        let c : From root :=
          if s.line.isOutRequest then
            match st.binding.val.bindString (v.binds id t.line.body.id) (v.domain id, id) (v.domain id, t.line.body.id) with
            | some c => ⟨c.val, st.binding.property.trans c.property⟩
            | none => st.binding
          else st.binding
        { binding := c, pairs := st.pairs ++ [(s.index, t.index)] }
      .ok (bound, placed ++ [(s, some (t, false))])

/-- The snapshot lines that the group's snapshot line `s`, its `k`th, must follow, by number. -/
def namedLines (snapshot : List Numbered) : List Nat :=
  snapshot.zipIdx.flatMap fun (s, k) => mustFollow snapshot s k

/--
Pairs the `out` lines of one group under the set of bindings and reports their differences. `v.fresh` holds the values
that this and earlier groups introduced, also on lines that are not compared; one that is not bound yet binds where a
compared line first holds it. `place` is the trace line of the group's input. The last component tells that nothing
later is compared.
-/
def compareGroup {root : Binding} (set : List (From root)) (v : Values) (snapshot trace : List Numbered) (place : Nat) :
    List Finding × List (From root) × Bool :=
  let same := State.same (namedLines snapshot)
  let start : Except Finding (List (State root) × List Numbered) := .ok (set.map ({ binding := ·, pairs := [] }), [])
  match snapshot.foldl (fun acc s => acc.bind fun a => pairExact v snapshot trace place same a s) start with
  | .error f => ([f], set, true)
  | .ok (states, failed) =>
  let start : Except Finding (List (State root) × List (Numbered × Option (Numbered × Bool))) := .ok (states, [])
  match failed.foldl (fun acc s => acc.bind fun a => pairPlace v trace place same a s) start with
  | .error f => ([f], set, true)
  | .ok (states, placed) =>
  let first := states.head?
  let used := (first.map State.used).getD []
  let differences := placed.filterMap fun
    | (s, some (t, false)) => some (Finding.mismatch (difference s.line t))
    | (_, some (_, true)) => none
    | (s, none) => some (.mismatch (missing s place))
  let unexpectedLines := (trace.filter fun t => !used.contains t.index).map (.mismatch ∘ unexpected)
  let pairs := ((first.map (·.pairs)).getD []).filterMap fun (i, j) => do
    pure (← snapshot.find? (·.index == i), ← trace.find? (·.index == j))
  let times := pairs.filterMap fun (s, t) =>
    if s.line.time.time == t.line.time.time then none
    else some (Finding.mismatch (.time t.index (Subject.of t.line.toTraceLine) s.line.time.text t.line.time.text))
  let orders := snapshot.zipIdx.flatMap fun (s, k) =>
    match pairs.find? (·.1.index == s.index) with
    | none => []
    | some (_, t) =>
      (mustFollow snapshot s k).filterMap fun n => do
        let (_, before) ← pairs.find? (·.1.index == n)
        if before.index < t.index then none
        else some (Finding.mismatch
          (.lineOrder t.index (Subject.of t.line.toTraceLine) (Subject.of before.line.toTraceLine)))
  let kept := states.filter fun st => sameSet st.used used
  (differences ++ unexpectedLines ++ times ++ orders, distinctBy From.same (kept.map (·.binding)), false)

/-- The line without its own id, which names the line rather than what it gives. -/
def useValue (l : Line) : Value :=
  match lineValue l with
  | .obj fs => .obj (fs.filter (·.1 != "id"))
  | v => v

/-- How the snapshot `in` lines `inputs` use `σ`: those that name it, each with `σ` replaced by "" (useValue). -/
def usesOf (inputs : List Line) (σ : String) : List String :=
  (inputs.filter fun l => (useValue l).strings.contains σ).map fun l =>
    ((useValue l).mapStrings fun x => if x == σ then "" else x).canonical

/-- Whether the snapshot `in` lines `inputs` use the values `σs` alike, so that any choice among them does. -/
def sameUses (inputs : List Line) (σs : List String) : Bool :=
  match σs.map (usesOf inputs) with
  | u :: us => us.all (· == u)
  | [] => true

/--
The implementation values that the bindings give the value `σ` of `in` line `l`, when they are two or more and the
snapshot `in` lines `inputs` do not use alike (sameUses) the snapshot values that some binding gives one of them: the
harness had to choose a route that the set does not decide.
-/
def unrouted (set : List Binding) (v : Values) (inputs : List Line) (l : Line) : Option (List String) :=
  (useValue l).strings.findSome? fun σ =>
    let d := v.domain σ
    let images := distinctBy (· == ·) (set.map fun b => b.image (d, σ))
    let standing := distinctBy (· == ·) (σ :: set.flatMap fun b =>
      b.pairs.filterMap fun (s, t) => if s.1 == d && images.contains t.2 then some s.2 else none)
    if images.length < 2 || sameUses inputs standing then none else some images

/--
Compares the groups in order, carrying the set of bindings. When `cut`, the trace's last group ends at a malformed line,
and only its input is compared. `internal` selects the `out` lines that are not compared. `inputs` holds the snapshot's
`in` lines, and `outs` the trace's `out` lines.
-/
def compareGroups (lineCount : Nat) (internal : Line → Bool) (inputs : List Line) (outs : List Numbered)
    (expected actual : List Group) (cut : Bool) {root : Binding} :
    Nat → Values → List (From root) → List Finding × List (From root)
  | 0, _, set => ([], set)
  | fuel + 1, v, set =>
    match expected, actual with
    | [], [] => ([], set)
    | e :: es, a :: as =>
      let inputs' : Except Finding (List (From root)) :=
        match e.input, a.input with
        | none, none => .ok set
        | some s, some t =>
          let subject := Subject.of s.line.toTraceLine
          match expand From.same set fun b => (matchLine { v with fresh := [] } b.val s.line t.line).map
              (lift b.property) with
          | none => .error (.uncomparable (.bindingLimit t.index subject s.index bindingLimit))
          | some [] => .error (differentInput ((set.head?.map (·.val)).getD .empty) s t)
          | some set' =>
            match unrouted (set.map (·.val)) v inputs s.line with
            | some images =>
              .error (.uncomparable (.ambiguous t.index subject s.index
                ((outs.filter fun o => images.contains o.line.body.id).map (·.index))))
            | none => .ok set'
        | some s, none => .error (.uncomparable (.missingInput lineCount (lineValue s.line) s.index))
        | none, some t => .error (.uncomparable (.unexpectedInput t.index (lineValue t.line)))
      match inputs' with
      | .error f => ([f], set)
      | .ok set₁ =>
        if cut && as.isEmpty then ([], set₁)
        else
          let place := (a.input.map (·.index)).getD 1
          let compared (outs : List Numbered) := outs.filter fun o => !internal o.line
          let v := { v with fresh := v.fresh ++ e.outs.flatMap (·.line.fresh) }
          let (found, set₂, stop) := compareGroup set₁ v (compared e.outs) (compared a.outs) place
          if stop then (found, set₂)
          else
            let (rest, set₃) := compareGroups lineCount internal inputs outs es as cut fuel v set₂
            (found ++ rest, set₃)
    | e :: _, [] =>
      match e.input with
      | some s => ([.uncomparable (.missingInput lineCount (lineValue s.line) s.index)], set)
      | none => ([], set)
    | [], a :: _ =>
      match a.input with
      | some t => ([.uncomparable (.unexpectedInput t.index (lineValue t.line))], set)
      | none => ([], set)

/--
The violations of comparing a trace with a snapshot, and the bindings that agree with every compared line. In
`snapshot`, `none` is a blank line. `lines` holds the trace lines before the line that `cut` reports, if any, with `none`
for blank lines and repeated subscription answers. `internal` selects the event lines that verify does not compare. An
`unknownAfters` id orders no line, because reading the snapshot reports it before the comparison. `renamed` refines
what the comparison knows of the values (Explore's Outcome.renaming); verify passes `id`.
-/
def compare (snapshot lines : List (Option Line)) (cut : Option Uncomparable) (internal : Line → Bool)
    (renamed : Values → Values) : Compared :=
  let expected := groups snapshot
  let actual := groups lines
  let inputs := expected.filterMap fun g => g.input.map (·.line)
  let (found, set) :=
    compareGroups lines.length internal inputs (actual.flatMap (·.outs)) expected actual cut.isSome
      (expected.length + actual.length) (renamed { domain := valueDomains snapshot, fresh := [], image := fun _ _ => true })
      [⟨Binding.empty, .refl _⟩]
  { findings := found ++ (cut.map Finding.uncomparable).toList, bindings := set.map (·.val) }

def isOutRequestLine (l : TraceLine) : Bool :=
  match l.body with
  | .command .out .. | .query .out .. | .subscribe .out .. => true
  | _ => false

/--
The number of the first `out` request line with the id of an earlier `out` request line, and its report. An `in` line's
answer names an `out` request and an `out` answer an `in` one, so only `out` request ids must differ; a redelivered
`in` request keeps its id.
-/
def firstDuplicate (lines : List (Option TraceLine)) : Option (Nat × Uncomparable) :=
  go lines 1 []
where
  go : List (Option TraceLine) → Nat → List (String × Nat) → Option (Nat × Uncomparable)
    | [], _, _ => none
    | none :: ls, i, seen => go ls (i + 1) seen
    | some l :: ls, i, seen =>
      if !isOutRequestLine l then go ls (i + 1) seen
      else
        match seen.lookup l.body.id with
        | some first => some (i, .duplicateId i l.body.id first)
        | none => go ls (i + 1) (seen ++ [(l.body.id, i)])

/-- The trace lines that verify compares, and the report of the line that ends them, if any. -/
def comparedLines (trace : List (FileLine TraceLine)) : List (Option TraceLine) × Option Uncomparable :=
  let (lines, malformed) := untilMalformed trace
  match firstDuplicate lines with
  | some (i, u) => (lines.take (i - 1), some u)
  | none => (lines, malformed.map .lineSchema)

def verifyLines {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue)
    (snapshot : List (Option TraceLine)) (trace : List (FileLine TraceLine)) (renamed : Values → Values) : m Compared := do
  let (lines, cut) := comparedLines trace
  let (expected, outputByRequestId) ← readLines s service ask snapshot []
  let (actual, _) ← readLines s service ask lines outputByRequestId
  pure (compare expected (withoutRepeatedAnswers actual) cut (internalEvent s service) renamed)

end Tazuna.Verify
