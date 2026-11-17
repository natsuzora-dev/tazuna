import Tazuna.Data.Trace
import Tazuna.Data.Canonical
import Tazuna.Syntax.Structure
import Tazuna.Verify.Binding
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable

/-!
This module compares an implementation trace with a snapshot. The harness gave the implementation the snapshot's `in`
lines one by one under one deterministic simulation, so nothing is searched.

- Values are read by their definition's schema (the `ask` parameter) and compare as CValue.
- `in` lines align by position and compare exactly under the binding. After the first `in` line that differs or is
  missing, nothing later is compared.
- The `out` lines after an `in` line, or before the first, are that input's group. A group's lines pair by content and
  time in any order that keeps the snapshot's `after` order.
- The binding (Verify/Binding) maps snapshot strings to implementation strings one-to-one over the whole comparison.
  Every string that compares equal enters it: a value that a snapshot line introduces (the id of an `out` request, a
  `created` key) is fresh until bound and binds to the implementation string at the same place of the first compared
  line that holds it, maybe in a later group; any other string binds to itself. A string that already stands for
  another value does not compare equal, so an implementation that reuses an existing value for a new one differs.
- Pairing a group: again and again, the first unpaired snapshot line whose candidates (the unpaired implementation
  lines equal to it under the binding) are one line, or several lines that bind it the same way, pairs with its first
  candidate. When no line is decided so, snapshot lines that each have the same candidates, as many as they are, and
  that each bind one value differently per candidate pair in order, and the binding keeps the choice open in a slot
  until a later line binds one of its values. A snapshot line left with two or more candidates is ambiguous: verify
  reports only the ambiguous lines of the group and compares nothing later. A bag pairs its elements by the same rule.
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

/-- The violations of a comparison, and the binding that it ends with. -/
structure Compared where
  findings : List Finding
  binding : Binding

/-- The pairs of the binding that the comparison ends with, choosing in each larger slot by position. -/
def Compared.bindings (c : Compared) : Bindings := c.binding.pairs

/-- How a snapshot value or line compares with an implementation one under binding `b`. -/
inductive Match (b : Binding) where
  | equal (b' : Binding) (h : b.Extends b')
  | differ
  | ambiguous

instance (b : Binding) : Inhabited (Match b) := ⟨.differ⟩

def Match.ofOption {b : Binding} : Option { b' : Binding // b.Extends b' } → Match b
  | some ⟨b', h⟩ => .equal b' h
  | none => .differ

def Match.andThen {b : Binding} (m : Match b) (f : (b' : Binding) → Match b') : Match b :=
  match m with
  | .equal b' h =>
    match f b' with
    | .equal c hc => .equal c (h.trans hc)
    | .differ => .differ
    | .ambiguous => .ambiguous
  | .differ => .differ
  | .ambiguous => .ambiguous

/-- What pairing two lists leaves: the pairs by index, the binding, and the left items left over. -/
structure Paired (start : Binding) where
  pairs : List (Nat × Nat)
  bindings : Binding
  ext : start.Extends bindings
  /-- Left items with two or more candidates, or with a candidate that is ambiguous itself. -/
  ambiguous : List Nat
  /-- Left items with no candidate. -/
  unmatched : List Nat
  /-- Right items that pair with no left item. -/
  extra : List Nat

/-- The slots that hold one value on each side, as pairs. -/
def singletons (slots : List Slot) : List (String × String) :=
  slots.filterMap fun
    | ([s], [t]) => some (s, t)
    | _ => none

/-- The slots with `s` standing for `t`, as Binding.bindString makes them for a string that may bind. -/
def bindSlots (slots : List Slot) (s t : String) : Option (List Slot) :=
  if s ∈ domainOf slots then resolveIn s t slots
  else if t ∈ imageOf slots then none
  else some (slots ++ [([s], [t])])

/--
The pair that `b'` binds beyond `b`, when `b'` is `b` with that pair bound. Binding one value of a slot of two also
binds the other, so the first new pair that gives `b'` is the one.
-/
def newPair (b b' : Binding) : Option (String × String) :=
  ((singletons b'.slots).filter fun p => !(singletons b.slots).contains p).find? fun (s, t) =>
    bindSlots b.slots s t == some b'.slots

/--
The slots with the snapshot values `σs` standing for the implementation values `τs` in some order: a new slot when no
value is in a slot yet, or a split of the one slot that holds them all.
-/
def refineSlots (slots : List Slot) (σs τs : List String) : Option (List Slot) :=
  if !(decide σs.Nodup && decide τs.Nodup) then none
  else if σs.all (· ∉ domainOf slots) && τs.all (· ∉ imageOf slots) then some (slots ++ [(σs, τs)])
  else
    match slots.find? fun k => σs.all (· ∈ k.1) && τs.all (· ∈ k.2) with
    | none => none
    | some k =>
      let rest : Slot := (k.1.filter (· ∉ σs), k.2.filter (· ∉ τs))
      some (slots.flatMap fun k' => if k' == k then (σs, τs) :: (if rest.1.isEmpty then [] else [rest]) else [k'])

/-- The one value of the list, when all its items are equal. -/
def allSame {α : Type} [BEq α] : List α → Option α
  | x :: xs => if xs.all (· == x) then some x else none
  | [] => none

/-- Whether two bindings have the same slots. -/
def sameSlots (a b : Binding) : Bool :=
  a.slots == b.slots || (a.slots.length == b.slots.length && a.slots.all b.slots.contains)

/--
Pairs the items of `left` with those of `right` (each with its index) by the rule of the module documentation: `test`
compares two items under a binding, and `allowed pairs i j` tells whether left item `i` may pair with right item `j`
after `pairs`.
-/
def pairUp {α β : Type} (test : (b : Binding) → α → β → Match b) (allowed : List (Nat × Nat) → Nat → Nat → Bool)
    (start : Binding) (left : List (Nat × α)) (right : List (Nat × β)) : Paired start :=
  go left.length start (.refl start) left right []
where
  candidates (b : Binding) (pairs : List (Nat × Nat)) (rs : List (Nat × β)) (i : Nat) (s : α) :
      List (Nat × { b' : Binding // b.Extends b' }) × Bool :=
    rs.foldl (fun (cs, amb) (j, t) =>
      if !allowed pairs i j then (cs, amb)
      else
        match test b s t with
        | .equal b' h => (cs ++ [(j, ⟨b', h⟩)], amb)
        | .differ => (cs, amb)
        | .ambiguous => (cs, true)) ([], false)
  /-- The first left item whose candidates all bind it the same way, with its first candidate. -/
  determined (b : Binding) (pairs : List (Nat × Nat)) (ls : List (Nat × α)) (rs : List (Nat × β)) :
      Option (List (Nat × Nat) × { b' : Binding // b.Extends b' }) :=
    ls.findSome? fun (i, s) =>
      match candidates b pairs rs i s with
      | ((j, c) :: rest, false) => if rest.all fun (_, d) => sameSlots d.val c.val then some ([(i, j)], c) else none
      | _ => none
  /--
  Left items that each have the same candidates, as many as they are, where pairing left item `k` with candidate `j`
  binds one more pair, `σ k ↦ τ j`. Every way of pairing them compares equal, so they pair in order and the binding
  gets the slot `(σs, τs)` instead of a choice.
  -/
  block (b : Binding) (pairs : List (Nat × Nat)) (ls : List (Nat × α)) (rs : List (Nat × β)) :
      Option (List (Nat × Nat) × { b' : Binding // b.Extends b' }) :=
    ls.findSome? fun (i, s) => do
      let (cs, amb) := candidates b pairs rs i s
      if amb || cs.length < 2 then none else
      let js := cs.map (·.1)
      let group := ls.filterMap fun (k, x) =>
        let (cx, ax) := candidates b pairs rs k x
        if !ax && cx.map (·.1) == js then some (k, cx) else none
      if group.length != js.length then none else
      let rows ← group.mapM fun (_, cx) => cx.mapM fun (_, c) => newPair b c.val
      let σs ← rows.mapM fun row => allSame (row.map (·.1))
      let τs ← (List.range js.length).mapM fun n => allSame (rows.map fun row => (row[n]?.map (·.2)).getD "")
      let slots ← refineSlots b.slots σs τs
      let b' ← b.refine slots
      pure ((group.map (·.1)).zip js, b')
  go : Nat → (b : Binding) → start.Extends b → List (Nat × α) → List (Nat × β) → List (Nat × Nat) → Paired start
    | fuel + 1, b, h, ls, rs, pairs =>
      match (determined b pairs ls rs).orElse fun _ => block b pairs ls rs with
      | some (new, ⟨b', h'⟩) =>
        go fuel b' (h.trans h') (ls.filter fun (i, _) => !new.any (·.1 == i))
          (rs.filter fun (j, _) => !new.any (·.2 == j)) (pairs ++ new)
      | none => go 0 b h ls rs pairs
    | 0, b, h, ls, rs, pairs =>
      let left := ls.map fun (i, s) => (i, candidates b pairs rs i s)
      { pairs, bindings := b, ext := h
        ambiguous := left.filterMap fun (i, cs, amb) => if amb || cs.length ≥ 2 then some i else none
        unmatched := left.filterMap fun (i, cs, amb) => if amb || cs.length ≥ 2 then none else some i
        extra := rs.map (·.1) }

mutual

/-- How snapshot value `s` compares with implementation value `t` under `b`, binding the strings of `s`. -/
partial def matchValue (fresh : List String) (b : Binding) : CValue → CValue → Match b
  | .leaf (.str s), .leaf (.str t) => .ofOption (b.bindString fresh s t)
  | .leaf v, .leaf w => if v == w then .equal b (.refl b) else .differ
  | .arr xs, .arr ys | .runs xs, .runs ys => matchList fresh b xs ys
  | .obj fs, .obj gs => if sameKeys fs gs then matchFields fresh b fs gs else .differ
  | .bag xs, .bag ys => if xs.length == ys.length then matchBag fresh b xs ys else .differ
  | _, _ => .differ

partial def matchList (fresh : List String) (b : Binding) : List CValue → List CValue → Match b
  | [], [] => .equal b (.refl b)
  | x :: xs, y :: ys => (matchValue fresh b x y).andThen fun b' => matchList fresh b' xs ys
  | _, _ => .differ

partial def matchFields (fresh : List String) (b : Binding) :
    List (String × CValue) → List (String × CValue) → Match b
  | [], _ => .equal b (.refl b)
  | (k, v) :: fs, gs =>
    match gs.lookup k with
    | some w => (matchValue fresh b v w).andThen fun b' => matchFields fresh b' fs gs
    | none => .differ

partial def matchBag (fresh : List String) (b : Binding) (xs ys : List CValue) : Match b :=
  let p := pairUp (matchValue fresh) (fun _ _ _ => true) b
    (xs.zipIdx.map fun (x, i) => (i, x)) (ys.zipIdx.map fun (y, i) => (i, y))
  if !p.ambiguous.isEmpty then .ambiguous
  else if p.unmatched.isEmpty then .equal p.bindings p.ext
  else .differ

end

def matchOption (fresh : List String) (b : Binding) : Option CValue → Option CValue → Match b
  | none, none => .equal b (.refl b)
  | some s, some t => matchValue fresh b s t
  | _, _ => .differ

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
How snapshot line `s` compares with implementation line `t`, apart from their time: their type, direction and name are
equal; the id of an `out` request binds, and an `in` line's id compares, while other `out` lines' ids are not compared;
the answered request, `resultOf` and the content compare under the binding.
-/
def matchContent (fresh : List String) (b : Binding) (s t : Line) : Match b :=
  if s.fields != t.fields then .differ
  else
    let ids : Match b :=
      if s.body.dir == .in || s.isOutRequest then .ofOption (b.bindString fresh s.body.id t.body.id)
      else .equal b (.refl b)
    let opt (x y : Option String) (b : Binding) : Match b :=
      match x, y with
      | none, none => .equal b (.refl b)
      | some x, some y => .ofOption (b.bindString fresh x y)
      | _, _ => .differ
    ids.andThen fun b =>
      (opt s.body.to? t.body.to? b).andThen fun b =>
        (opt s.body.resultOf? t.body.resultOf? b).andThen fun b => matchOption fresh b s.content t.content

/-- How snapshot line `s` compares with implementation line `t`: at the same time, and by matchContent. -/
def matchLine (fresh : List String) (b : Binding) (s t : Line) : Match b :=
  if s.time.time == t.time.time then matchContent fresh b s t else .differ

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

/--
Pairs the `out` lines of one group and reports their differences. `fresh` holds the values that this and earlier
groups introduced, also on lines that are not compared; one that is not bound yet binds where a compared line first
holds it. `place` is the trace line of the group's input. A group with an ambiguous line reports only its ambiguous
lines, and the last component tells that nothing later is compared.
-/
def compareGroup (b : Binding) (fresh : List String) (snapshot trace : List Numbered) (place : Nat) :
    List Finding × { b' : Binding // b.Extends b' } × Bool :=
  let p := pairUp (fun b (s : Numbered) (t : Numbered) => matchLine fresh b s.line t.line) (followsPaired snapshot)
    b (snapshot.map fun s => (s.index, s)) (trace.map fun t => (t.index, t))
  let byIndex {γ : Type} (xs : List Numbered) (i : Nat) (f : Numbered → γ) : List γ :=
    (xs.find? (·.index == i)).toList.map f
  let ambiguous := p.ambiguous.flatMap fun i => byIndex snapshot i fun s =>
    let cands := (trace.filter fun t => !p.pairs.any (·.2 == t.index)).filter fun t =>
      match matchLine fresh p.bindings s.line t.line with
      | .differ => false
      | _ => true
    Finding.uncomparable (.ambiguous ((cands.head?.map (·.index)).getD place) (Subject.of s.line.toTraceLine) s.index
      (cands.map (·.index)))
  if !ambiguous.isEmpty then (ambiguous, ⟨p.bindings, p.ext⟩, true) else
  -- Unpaired lines pair by place, in snapshot order, each with the first unpaired trace line at its place. A pair whose
  -- content compares equal differs only in its time or order, which the checks below report.
  let start : List (Numbered × Option (Numbered × Bool)) × List Nat × { b' : Binding // b.Extends b' } :=
    ([], p.extra, ⟨p.bindings, p.ext⟩)
  let (placed, extra, ⟨b', h'⟩) := p.unmatched.foldl (fun (placed, extra, ⟨b', h'⟩) i =>
    match snapshot.find? (·.index == i) with
    | none => (placed, extra, ⟨b', h'⟩)
    | some s =>
      match (trace.filter fun t => extra.contains t.index).find? fun t => samePlace b'.pairs s.line t.line with
      | some t =>
        let extra := extra.filter (· != t.index)
        match matchContent fresh b' s.line t.line with
        | .equal b'' h'' => (placed ++ [(s, some (t, true))], extra, ⟨b'', h'.trans h''⟩)
        | _ =>
          let bound : { c : Binding // b.Extends c } :=
            if s.line.isOutRequest then
              match b'.bindString fresh s.line.body.id t.line.body.id with
              | some ⟨c, hc⟩ => ⟨c, h'.trans hc⟩
              | none => ⟨b', h'⟩
            else ⟨b', h'⟩
          (placed ++ [(s, some (t, false))], extra, bound)
      | none => (placed ++ [(s, none)], extra, ⟨b', h'⟩)) start
  let differences := placed.filterMap fun
    | (s, some (t, false)) => some (Finding.mismatch (difference s.line t))
    | (_, some (_, true)) => none
    | (s, none) => some (.mismatch (missing s place))
  let unexpectedLines := (trace.filter fun t => extra.contains t.index).map (.mismatch ∘ unexpected)
  let pairs := (p.pairs.filterMap fun (i, j) => do
      pure (← snapshot.find? (·.index == i), ← trace.find? (·.index == j))) ++
    placed.filterMap fun (s, t) => t.map fun (t, _) => (s, t)
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
  (differences ++ unexpectedLines ++ times ++ orders, ⟨b', h'⟩, false)

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

def differentInput (b : Binding) (s t : Numbered) : Finding :=
  .uncomparable (.differentInput t.index s.index (Bindings.rename b.pairs (lineValue s.line)) (lineValue t.line))

/--
Compares the groups in order, carrying the binding. When `cut`, the trace's last group ends at a malformed line, and
only its input is compared. `internal` selects the `out` lines that are not compared.
-/
def compareGroups (lineCount : Nat) (internal : Line → Bool) (expected actual : List Group) (cut : Bool) :
    Nat → List String → (b : Binding) → List Finding × { b' : Binding // b.Extends b' }
  | 0, _, b => ([], ⟨b, .refl b⟩)
  | fuel + 1, fresh, b =>
    match expected, actual with
    | [], [] => ([], ⟨b, .refl b⟩)
    | e :: es, a :: as =>
      let inputs : Except Finding { b' : Binding // b.Extends b' } :=
        match e.input, a.input with
        | none, none => .ok ⟨b, .refl b⟩
        | some s, some t =>
          match matchLine [] b s.line t.line with
          | .equal b' h => .ok ⟨b', h⟩
          | _ => .error (differentInput b s t)
        | some s, none => .error (.uncomparable (.missingInput lineCount (lineValue s.line) s.index))
        | none, some t => .error (.uncomparable (.unexpectedInput t.index (lineValue t.line)))
      match inputs with
      | .error f => ([f], ⟨b, .refl b⟩)
      | .ok ⟨b₁, h₁⟩ =>
        if cut && as.isEmpty then ([], ⟨b₁, h₁⟩)
        else
          let place := (a.input.map (·.index)).getD 1
          let compared (outs : List Numbered) := outs.filter fun o => !internal o.line
          let fresh := fresh ++ e.outs.flatMap (·.line.fresh)
          let (found, ⟨b₂, h₂⟩, stop) := compareGroup b₁ fresh (compared e.outs) (compared a.outs) place
          if stop then (found, ⟨b₂, h₁.trans h₂⟩)
          else
            let (rest, ⟨b₃, h₃⟩) := compareGroups lineCount internal es as cut fuel fresh b₂
            (found ++ rest, ⟨b₃, h₁.trans (h₂.trans h₃)⟩)
    | e :: _, [] =>
      match e.input with
      | some s => ([.uncomparable (.missingInput lineCount (lineValue s.line) s.index)], ⟨b, .refl b⟩)
      | none => ([], ⟨b, .refl b⟩)
    | [], a :: _ =>
      match a.input with
      | some t => ([.uncomparable (.unexpectedInput t.index (lineValue t.line))], ⟨b, .refl b⟩)
      | none => ([], ⟨b, .refl b⟩)

/--
The violations of comparing a trace with a snapshot, and the binding. In `snapshot`, `none` is a blank line. `lines`
holds the trace lines before its first malformed line, with `none` for blank lines and repeated subscription answers,
and `malformed` is the number of that line. `internal` selects the event lines that verify does not compare. An
`unknownAfters` id orders no line, because reading the snapshot reports it before the comparison.
-/
def compare (snapshot lines : List (Option Line)) (malformed : Option Nat) (internal : Line → Bool) : Compared :=
  let expected := groups snapshot
  let actual := groups lines
  let (found, binding) :=
    compareGroups lines.length internal expected actual malformed.isSome (expected.length + actual.length) []
      Binding.empty
  { findings := found ++ (malformed.map fun n => Finding.uncomparable (.lineSchema n)).toList, binding := binding.val }

def verifyLines {m : Type → Type} [Monad m] (s : Structure) (service : String) (ask : Definition → Part → Value → m CValue)
    (snapshot : List (Option TraceLine)) (trace : List (FileLine TraceLine)) : m Compared := do
  let (lines, malformed) := untilMalformed trace
  let (expected, outputByRequestId) ← readLines s service ask snapshot []
  let (actual, _) ← readLines s service ask lines outputByRequestId
  pure (compare expected (withoutRepeatedAnswers actual) malformed (internalEvent s service))

end Tazuna.Verify
