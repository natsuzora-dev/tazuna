import Tazuna.Data.Trace
import Tazuna.Data.Canonical
import Tazuna.Syntax.Structure
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable

/-!
This module compares an implementation trace with a snapshot. The harness gave the implementation the snapshot's `in`
lines one by one under one deterministic simulation, so nothing is searched.

- Values are read by their definition's schema (the `ask` parameter) and compare as CValue.
- `in` lines align by position and compare exactly under the binding. After the first `in` line that differs or is
  missing, nothing later is compared.
- The `out` lines after an `in` line, or before the first, are that input's group. A group's lines pair by content in
  any order.
- The binding maps snapshot values to implementation values one-to-one. A value that a snapshot line introduces (the id
  of an `out` request, a `created` key) is fresh until bound: it binds to the implementation string at the same place
  of the first compared line that holds it, maybe in a later group. Every other string compares under the binding, or as itself.
- Pairing a group: again and again, the first unpaired snapshot line whose candidates (the unpaired implementation
  lines equal to it under the binding) are one line, or several lines that bind it the same way, pairs with its first
  candidate. A snapshot line left with two or more candidates is ambiguous: verify reports
  only the ambiguous lines of the group and compares nothing later. A bag pairs its elements by the same rule.
- Lines left unpaired pair by place (type and name, or the answered request) to report how they differ; the others are
  missing or unexpected. Paired lines compare their time and the snapshot's `after` order.
- Verify reports the trace's first malformed line, and compares neither the group of that line nor anything later.
-/

namespace Tazuna.Verify

open Tazuna.Data
open Tazuna.Syntax

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
    let (screen, control) := match name.splitOn "." with
      | first :: second :: _ => (first, second)
      | parts => (parts.headD "", "")
    let d := s.named service (some screen) ["screen"]
    let hasPayload := (d.bind fun d => d.chart?.bind fun c => c.controls.lookup control).any (·.isSome)
    (if hasPayload then d else none, .control control)
  match l.body with
  | .operation dir id name payload =>
    let (d, part) := control name
    let value ← payload.mapM (read d part)
    pure (line (.operation dir id name (value.map (·.flatten))) value, outputByRequestId)
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
subscription is open from the `in` subscribe to the `in` unsubscribe. Values compare ignoring bag order and object
field order.
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

/-- The violations of a comparison, and the bindings that it ends with. -/
structure Compared where
  findings : List Finding
  bindings : Bindings

/-- How a snapshot value or line compares with an implementation one under a binding. -/
inductive Match where
  | equal (bindings : Bindings)
  | differ
  | ambiguous
deriving Inhabited

/--
The binding with snapshot string `s` standing for implementation string `t`: a bound `s` must stand for its value, a
fresh `s` binds unless `t` stands for another value, and any other `s` stands for itself.
-/
def bindString (fresh : List String) (b : Bindings) (s t : String) : Option Bindings :=
  match b.lookup s with
  | some bound => if bound == t then some b else none
  | none =>
    if fresh.contains s then (if b.any (·.2 == t) then none else some (b ++ [(s, t)]))
    else if s == t then some b else none

def Match.ofOption : Option Bindings → Match
  | some b => .equal b
  | none => .differ

/-- What pairing two lists leaves: the pairs by index, the binding, and the left items left over. -/
structure Paired where
  pairs : List (Nat × Nat)
  bindings : Bindings
  /-- Left items with two or more candidates, or with a candidate that is ambiguous itself. -/
  ambiguous : List Nat
  /-- Left items with no candidate. -/
  unmatched : List Nat
  /-- Right items that pair with no left item. -/
  extra : List Nat

/--
Pairs the items of `left` with those of `right` (each with its index) by the rule of the module documentation: `test`
compares two items under a binding.
-/
def pairUp {α β : Type} (test : Bindings → α → β → Match) (b : Bindings)
    (left : List (Nat × α)) (right : List (Nat × β)) : Paired :=
  go left.length b left right []
where
  candidates (b : Bindings) (rs : List (Nat × β)) (s : α) : List (Nat × Bindings) × Bool :=
    rs.foldl (fun (cs, amb) (j, t) =>
      match test b s t with
      | .equal b' => (cs ++ [(j, b')], amb)
      | .differ => (cs, amb)
      | .ambiguous => (cs, true)) ([], false)
  step (b : Bindings) (ls : List (Nat × α)) (rs : List (Nat × β)) : Option (Nat × Nat × Bindings) :=
    ls.findSome? fun (i, s) =>
      match candidates b rs s with
      | ([(j, b')], false) => some (i, j, b')
      | ((j, b') :: rest, false) =>
        if rest.all fun (_, c) => c.length == b'.length && c.all b'.contains then some (i, j, b') else none
      | _ => none
  go : Nat → Bindings → List (Nat × α) → List (Nat × β) → List (Nat × Nat) → Paired
    | fuel + 1, b, ls, rs, pairs =>
      match step b ls rs with
      | some (i, j, b') => go fuel b' (ls.filter (·.1 != i)) (rs.filter (·.1 != j)) (pairs ++ [(i, j)])
      | none => go 0 b ls rs pairs
    | 0, b, ls, rs, pairs =>
      let left := ls.map fun (i, s) => (i, candidates b rs s)
      { pairs, bindings := b
        ambiguous := left.filterMap fun (i, cs, amb) => if amb || cs.length ≥ 2 then some i else none
        unmatched := left.filterMap fun (i, cs, amb) => if amb || cs.length ≥ 2 then none else some i
        extra := rs.map (·.1) }

mutual

/-- How snapshot value `s` compares with implementation value `t` under `b`, binding the fresh strings of `s`. -/
partial def matchValue (fresh : List String) (b : Bindings) : CValue → CValue → Match
  | .leaf (.str s), .leaf (.str t) => .ofOption (bindString fresh b s t)
  | .leaf v, .leaf w => if v == w then .equal b else .differ
  | .arr xs, .arr ys | .runs xs, .runs ys => matchList fresh b xs ys
  | .obj fs, .obj gs => if sameKeys fs gs then matchFields fresh b fs gs else .differ
  | .bag xs, .bag ys => if xs.length == ys.length then matchBag fresh b xs ys else .differ
  | _, _ => .differ

partial def matchList (fresh : List String) (b : Bindings) : List CValue → List CValue → Match
  | [], [] => .equal b
  | x :: xs, y :: ys =>
    match matchValue fresh b x y with
    | .equal b' => matchList fresh b' xs ys
    | m => m
  | _, _ => .differ

partial def matchFields (fresh : List String) (b : Bindings) (fs gs : List (String × CValue)) : Match :=
  fs.foldl (fun m (k, v) =>
    match m, gs.lookup k with
    | .equal b', some w => matchValue fresh b' v w
    | .equal _, none => .differ
    | m, _ => m) (.equal b)

partial def matchBag (fresh : List String) (b : Bindings) (xs ys : List CValue) : Match :=
  let p : Paired := pairUp (matchValue fresh) b
    (xs.zipIdx.map fun (x, i) => (i, x)) (ys.zipIdx.map fun (y, i) => (i, y))
  if !p.ambiguous.isEmpty then .ambiguous
  else if p.unmatched.isEmpty then .equal p.bindings
  else .differ

end

def matchOption (fresh : List String) (b : Bindings) : Option CValue → Option CValue → Match
  | none, none => .equal b
  | some s, some t => matchValue fresh b s t
  | _, _ => .differ

def Match.andThen : Match → (Bindings → Match) → Match
  | .equal b, f => f b
  | m, _ => m

def Line.isOutRequest (l : Line) : Bool :=
  match l.body with
  | .command .out .. | .query .out .. | .subscribe .out .. => true
  | _ => false

/-- The values that the snapshot line introduces: the id of an `out` request and the line's `created` keys. -/
def Line.fresh (l : Line) : List String :=
  (if l.isOutRequest then [l.body.id] else []) ++ l.created.getD []

def Line.fields (l : Line) : Value :=
  match ToValue.toValue l.body with
  | .obj fs => .obj (fs.filter fun (k, _) => k == "type" || k == "dir" || k == "name")
  | v => v

/--
How snapshot line `s` compares with implementation line `t`: their type, direction and name are equal; the id of an
`out` request binds, and an `in` line's id compares, while other `out` lines' ids are not compared; the answered
request, `resultOf` and the content compare under the binding.
-/
def matchLine (fresh : List String) (b : Bindings) (s t : Line) : Match :=
  if s.fields != t.fields then .differ
  else
    let ids : Match :=
      if s.body.dir == .in || s.isOutRequest then .ofOption (bindString fresh b s.body.id t.body.id) else .equal b
    let opt (x y : Option String) (b : Bindings) : Match :=
      match x, y with
      | none, none => .equal b
      | some x, some y => .ofOption (bindString fresh b x y)
      | _, _ => .differ
    ids.andThen fun b =>
      (opt s.body.to? t.body.to? b).andThen fun b =>
        (opt s.body.resultOf? t.body.resultOf? b).andThen fun b => matchOption fresh b s.content t.content

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

/-- The latest of the earlier lines with the id. -/
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

/--
Pairs the `out` lines of one group and reports their differences. `fresh` holds the values that this and earlier
groups introduced, also on lines that are not compared; one that is not bound yet binds where a compared line first
holds it. `place` is the trace line of the group's input. A group with an ambiguous line reports
only its ambiguous lines, and the last component tells that nothing later is compared.
-/
def compareGroup (b : Bindings) (fresh : List String) (snapshot trace : List Numbered) (place : Nat) :
    List Finding × Bindings × Bool :=
  let p := pairUp (fun b (s : Numbered) (t : Numbered) => matchLine fresh b s.line t.line)
    b
    (snapshot.map fun s => (s.index, s)) (trace.map fun t => (t.index, t))
  let byIndex {γ : Type} (xs : List Numbered) (i : Nat) (f : Numbered → γ) : List γ :=
    (xs.find? (·.index == i)).toList.map f
  let ambiguous := p.ambiguous.flatMap fun i => byIndex snapshot i fun s =>
    let cands := (trace.filter fun t => !p.pairs.any (·.2 == t.index)).filter fun t =>
      match matchLine fresh p.bindings s.line t.line with
      | .differ => false
      | _ => true
    Finding.uncomparable (.ambiguous ((cands.head?.map (·.index)).getD place) (Subject.of s.line.toTraceLine) s.index
      (cands.map (·.index)))
  if !ambiguous.isEmpty then (ambiguous, p.bindings, true) else
  -- Unpaired lines pair by place, in snapshot order, each with the first unpaired trace line at its place.
  let (placed, extra, b) := p.unmatched.foldl (fun (placed, extra, b) i =>
    match snapshot.find? (·.index == i) with
    | none => (placed, extra, b)
    | some s =>
      match (trace.filter fun t => extra.contains t.index).find? fun t => samePlace b s.line t.line with
      | some t =>
        let b := if s.line.isOutRequest then (bindString fresh b s.line.body.id t.line.body.id).getD b else b
        (placed ++ [(s, some t)], extra.filter (· != t.index), b)
      | none => (placed ++ [(s, none)], extra, b)) (([] : List (Numbered × Option Numbered)), p.extra, p.bindings)
  let differences := placed.map fun
    | (s, some t) => Finding.mismatch (difference s.line t)
    | (s, none) => .mismatch (missing s place)
  let unexpectedLines := (trace.filter fun t => extra.contains t.index).map (.mismatch ∘ unexpected)
  let pairs := (p.pairs.filterMap fun (i, j) => do
      pure (← snapshot.find? (·.index == i), ← trace.find? (·.index == j))) ++
    placed.filterMap fun (s, t) => t.map (s, ·)
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
  (differences ++ unexpectedLines ++ times ++ orders, b, false)

/-- The line that orders a finding in a report. -/
def Finding.line : Finding → Nat
  | .mismatch m =>
    match m.place.lookup "line" with
    | some (.num n) => n.mantissa.toNat
    | _ => 0
  | .uncomparable u =>
    match u.place.lookup "line" with
    | some (.num n) => n.mantissa.toNat
    | _ => 0

def differentInput (b : Bindings) (s t : Numbered) : Finding :=
  .uncomparable (.differentInput t.index s.index (b.rename (lineValue s.line)) (lineValue t.line))

/--
Compares the groups in order, carrying the binding. When `cut`, the trace's last group ends at a malformed line, and
only its input is compared. `internal` selects the `out` lines that are not compared.
-/
def compareGroups (lineCount : Nat) (internal : Line → Bool) (expected actual : List Group) (cut : Bool) :
    Nat → List String → Bindings → List Finding × Bindings
  | 0, _, b => ([], b)
  | fuel + 1, fresh, b =>
    match expected, actual with
    | [], [] => ([], b)
    | e :: es, a :: as =>
      let inputs : Except Finding Bindings :=
        match e.input, a.input with
        | none, none => .ok b
        | some s, some t =>
          match matchLine [] b s.line t.line with
          | .equal b' => if s.line.time.time == t.line.time.time then .ok b' else .error (differentInput b s t)
          | _ => .error (differentInput b s t)
        | some s, none => .error (.uncomparable (.missingInput lineCount (lineValue s.line) s.index))
        | none, some t => .error (.uncomparable (.unexpectedInput t.index (lineValue t.line)))
      match inputs with
      | .error f => ([f], b)
      | .ok b =>
        if cut && as.isEmpty then ([], b)
        else
          let place := (a.input.map (·.index)).getD 1
          let compared (outs : List Numbered) := outs.filter fun o => !internal o.line
          let fresh := fresh ++ e.outs.flatMap (·.line.fresh)
          let (found, b, stop) := compareGroup b fresh (compared e.outs) (compared a.outs) place
          if stop then (found, b)
          else
            let (rest, b) := compareGroups lineCount internal es as cut fuel fresh b
            (found ++ rest, b)
    | e :: _, [] =>
      match e.input with
      | some s => ([.uncomparable (.missingInput lineCount (lineValue s.line) s.index)], b)
      | none => ([], b)
    | [], a :: _ =>
      match a.input with
      | some t => ([.uncomparable (.unexpectedInput t.index (lineValue t.line))], b)
      | none => ([], b)

/--
The violations of comparing a trace with a snapshot, and the bindings. In `snapshot`, `none` is a blank line. `lines`
holds the trace lines before its first malformed line, with `none` for blank lines and repeated subscription answers,
and `malformed` is the number of that line. `internal` selects the event lines that verify does not compare. An
`unknownAfters` id orders no line, because reading the snapshot reports it before the comparison.
-/
def compare (snapshot lines : List (Option Line)) (malformed : Option Nat) (internal : Line → Bool) : Compared :=
  let expected := groups snapshot
  let actual := groups lines
  let (found, bindings) :=
    compareGroups lines.length internal expected actual malformed.isSome (expected.length + actual.length) [] []
  { findings := found ++ (malformed.map fun n => Finding.uncomparable (.lineSchema n)).toList, bindings }

def verifyLines {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue)
    (snapshot : List (Option TraceLine)) (trace : List (FileLine TraceLine)) : m Compared := do
  let (lines, malformed) := untilMalformed trace
  let (expected, outputByRequestId) ← readLines s service ask snapshot []
  let (actual, _) ← readLines s service ask lines outputByRequestId
  pure (compare expected (withoutRepeatedAnswers actual) malformed (internalEvent s service))

end Tazuna.Verify
