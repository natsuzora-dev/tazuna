import Tazuna.Data.Trace
import Tazuna.Data.Canonical
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable

/-!
This module compares an implementation trace with a snapshot.

- `in` lines split `out` lines into windows. In each window, one search pairs each compared snapshot `out` line with an
  implementation `out` line, and each subscription open after the window with an open implementation subscription.
- Paired lines have equal type, place (the answered request for answer lines, and the name otherwise), time and value.
  Values compare as CValue. Subscriptions pair by name and input.
- Ids and createKey values (snapshot `created`) compare up to two one-to-one renamings that every line shares. A
  snapshot id or createKey value stands for one implementation value, and an implementation value for one snapshot
  value.
- Alike requests of one window bind their ids when a later line names one of them.
- The order of paired lines must follow the snapshot's `after` (mustFollow). Verify reports an `after` id that names no
  earlier `out` line of the same window, and compares nothing.
- Each `in` line is compared with the `in` line at the same position. After a difference, nothing later is compared.
- A window's search may pair a value in more than one way, and a later line decides which. So a search across windows
  first looks for a pairing of every window and `in` line, trying the other pairings of earlier ones when a later one
  has none (guideFor). The windows are then compared one by one, keeping to its renamings when it found one.
- When a window has no pairing, verify pairs the lines one by one to report the differences, and reports the uses of a
  value that stands for two values when no line differs. A search that takes more than `searchLimit` steps in one
  window or pair of `in` lines, over all its tries, is reported, and nothing later is compared.
- Verify reports the first malformed line of the trace, and compares neither its window nor any later line.
-/

namespace Tazuna.Verify

open Tazuna.Data

/--
A trace line with its value read by its definition's schema, if any. `value` is the input, payload or answer output,
and `body` holds it as JSON.
-/
structure Line extends TraceLine where
  value : Option CValue
deriving Inhabited

/-- The JSON form of `answer`, with the given output as its output. -/
def answerContent (answer : Answer) : Option CValue → CValue
  | some output => .obj [("result", .leaf (.str answer.result)), ("output", output)]
  | none => CValue.ofValue (ToValue.toValue answer)

def Line.content (l : Line) : Option CValue :=
  match l.body with
  | .answer _ _ _ answer => some (answerContent answer l.value)
  | _ => l.value

/-- An `out` line with its line number, counted from 1. -/
structure Out where
  line : Line
  index : Nat
deriving Inhabited

/-- The use of the id of the snapshot line `s` for the id of the implementation line `t`. -/
def Out.idUse (s t : Out) : Use :=
  { snapshot := s.line.body.id, trace := t.line.body.id, line := t.index, snapshotLine := s.index }

/-- The `out` lines before an `in` line, and that line. The last window has no `in` line. -/
structure Window where
  before : List Out
  input : Option Out

/-- The windows of `lines`. A `none` line is a blank line or a repeated subscription answer, and only takes a number. -/
def steps (lines : List (Option Line)) : List Window :=
  go lines 0 []
where
  go : List (Option Line) → Nat → List Out → List Window
    | [], _, acc => [{ before := acc.reverse, input := none }]
    | none :: ls, i, acc => go ls (i + 1) acc
    | some l :: ls, i, acc =>
      if l.body.dir == .out then go ls (i + 1) ({ line := l, index := i + 1 } :: acc)
      else { before := acc.reverse, input := some { line := l, index := i + 1 } } :: go ls (i + 1) []

inductive Finding where
  | mismatch (m : Mismatch)
  | uncomparable (u : Uncomparable)

/-- The list with `v` at key `k`, replaced in place if `k` exists and appended otherwise (JS `Map.set`). -/
def setAt {β : Type} : List (String × β) → String → β → List (String × β)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v => if k' == k then (k, v) :: rest else (k', v') :: setAt rest k v

/-- The violations of a comparison, and the bindings that it ends with. -/
structure Compared where
  findings : List Finding
  bindings : Bindings

/-- A one-to-one renaming of snapshot values to implementation values, with the lines that bound each value. -/
abbrev Renaming := List Use

def Renaming.traceOf? (r : Renaming) (s : String) : Option String := (r.find? (·.snapshot == s)).map (·.trace)

def Renaming.takes (r : Renaming) (t : String) : Bool := r.any (·.trace == t)

/-- The renaming with `u`, unless one of its values already stands for another value. -/
def Renaming.bind (r : Renaming) (u : Use) : Option Renaming :=
  match r.traceOf? u.snapshot with
  | some t => if t == u.trace then some r else none
  | none => if r.takes u.trace then none else some (r ++ [u])

/-- `v` with its renamed createKey values replaced by their implementation values, for reports. -/
def substitute (r : Renaming) (v : CValue) : CValue :=
  v.mapStrings fun s => (r.traceOf? s).getD s

/-- What a search still has to pair. Bag elements pair at trace line `line` and snapshot line `snapshotLine`. -/
inductive Goal where
  | out (s : Out)
  | subscription (id : String)
  | bag (line snapshotLine : Nat) (xs ys : List CValue)

mutual

/--
The renaming under which `s` equals `t` apart from the elements of bags, and the bags left to pair. A declared
createKey value equals the implementation string that it is renamed to, and other strings equal themselves.
-/
def walk (declared : List String) (line snapshotLine : Nat) (s t : CValue) (r : Renaming) :
    Option (Renaming × List Goal) :=
  match s, t with
  | .leaf (.str v), t =>
    match t with
    | .leaf (.str w) =>
      if declared.contains v then (r.bind { snapshot := v, trace := w, line, snapshotLine }).map (·, [])
      else if w == v then some (r, []) else none
    | _ => none
  | .leaf v, .leaf w => if w == v then some (r, []) else none
  | .arr xs, .arr ys => if xs.length == ys.length then walkList declared line snapshotLine xs ys r else none
  | .runs xs, .runs ys => if xs.length == ys.length then walkList declared line snapshotLine xs ys r else none
  | .bag xs, .bag ys => if xs.length == ys.length then some (r, [.bag line snapshotLine xs ys]) else none
  | .obj fs, .obj gs => if sameKeys fs gs then walkFields declared line snapshotLine fs gs r else none
  | _, _ => none
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

def walkList (declared : List String) (line snapshotLine : Nat) (xs ys : List CValue) (r : Renaming) :
    Option (Renaming × List Goal) :=
  match xs, ys with
  | x :: xs, y :: ys => do
    let (r, g) ← walk declared line snapshotLine x y r
    let (r, g') ← walkList declared line snapshotLine xs ys r
    pure (r, g ++ g')
  | _, _ => some (r, [])
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

/-- The fields in the field order of `fs`. -/
def walkFields (declared : List String) (line snapshotLine : Nat) (fs gs : List (String × CValue)) (r : Renaming) :
    Option (Renaming × List Goal) :=
  match fs with
  | [] => some (r, [])
  | (k, v) :: fs => do
    let w ← gs.lookup k
    let (r, g) ← walk declared line snapshotLine v w r
    let (r, g') ← walkFields declared line snapshotLine fs gs r
    pure (r, g ++ g')
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

end

/-- Two missing values (undefined) are equal, and one missing value is not. -/
def walkContent (declared : List String) (line snapshotLine : Nat) (s t : Option CValue) (r : Renaming) :
    Option (Renaming × List Goal) :=
  match s, t with
  | some s, some t => walk declared line snapshotLine s t r
  | none, none => some (r, [])
  | _, _ => none

mutual

/--
The uses under which `s` equals `t` when each declared createKey value may stand for any string, for reports. Bags pair
their elements by backtracking.
-/
def free (declared : List String) (line snapshotLine : Nat) (s t : CValue) : Option (List Use) :=
  match s, t with
  | .leaf (.str v), t =>
    match t with
    | .leaf (.str w) =>
      if declared.contains v then some [{ snapshot := v, trace := w, line, snapshotLine }]
      else if w == v then some [] else none
    | _ => none
  | .leaf v, .leaf w => if w == v then some [] else none
  | .arr xs, .arr ys => if xs.length == ys.length then freeList declared line snapshotLine xs ys else none
  | .runs xs, .runs ys => if xs.length == ys.length then freeList declared line snapshotLine xs ys else none
  | .bag xs, .bag ys => freeBag declared line snapshotLine xs ys
  | .obj fs, .obj gs => if sameKeys fs gs then freeFields declared line snapshotLine fs gs else none
  | _, _ => none
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

def freeList (declared : List String) (line snapshotLine : Nat) (xs ys : List CValue) : Option (List Use) :=
  match xs, ys with
  | x :: xs, y :: ys => do
    let u ← free declared line snapshotLine x y
    let u' ← freeList declared line snapshotLine xs ys
    pure (u ++ u')
  | _, _ => some []
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

def freeFields (declared : List String) (line snapshotLine : Nat) (fs gs : List (String × CValue)) :
    Option (List Use) :=
  match fs with
  | [] => some []
  | (k, v) :: fs => do
    let w ← gs.lookup k
    let u ← free declared line snapshotLine v w
    let u' ← freeFields declared line snapshotLine fs gs
    pure (u ++ u')
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

def freeBag (declared : List String) (line snapshotLine : Nat) (ss ts : List CValue) : Option (List Use) :=
  if ss.length != ts.length then none
  else
    match ss with
    | [] => some []
    | first :: rest => freeBagFrom declared line snapshotLine first rest ts []
termination_by (sizeOf ss, ts.length + 1)
decreasing_by all_goals lex_decreasing

/-- The search of freeBag for `first`. `passed` holds the candidates tried. -/
def freeBagFrom (declared : List String) (line snapshotLine : Nat) (first : CValue) (rest cands passed : List CValue) :
    Option (List Use) :=
  match cands with
  | [] => none
  | t :: more =>
    -- Each fallback calls the search again rather than through a `let`, which Lean evaluates first, so that the search
    -- stops at the first pairing as TS's does instead of trying every order of the bag.
    match free declared line snapshotLine first t with
    | some u =>
      match freeBag declared line snapshotLine rest (passed.reverse ++ more) with
      | some u' => some (u ++ u')
      | none => freeBagFrom declared line snapshotLine first rest more (t :: passed)
    | none => freeBagFrom declared line snapshotLine first rest more (t :: passed)
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

def freeContent (declared : List String) (line snapshotLine : Nat) : Option CValue → Option CValue → Option (List Use)
  | some s, some t => free declared line snapshotLine s t
  | none, none => some []
  | _, _ => none

/-- Whether two lines have the same type, name and value, ignoring `created`. -/
def alike (a b : Line) : Bool :=
  a.body.type == b.body.type && a.body.name? == b.body.name? && plainEqual a.content b.content

/--
Alike `out` requests of window `window`, paired by `uses`. Each snapshot id in `snapshot` stands for one of the
implementation ids in `trace`, and binds to it when a line names it.
-/
structure Block where
  line : Line
  window : Nat
  snapshot : List String
  trace : List String
  uses : List Use

/-- The renaming of request, subscription and input ids, and the blocks of alike requests. -/
structure Ids where
  bound : Renaming := []
  blocks : List Block := []

def Ids.known (ids : Ids) (s : String) : Bool :=
  (ids.bound.traceOf? s).isSome || ids.blocks.any (·.snapshot.contains s)

def Ids.reserved (ids : Ids) (t : String) : Bool := ids.bound.takes t || ids.blocks.any (·.trace.contains t)

/-- The ids with `u` bound. A snapshot id of a block binds only to an implementation id of the same block. -/
def Ids.use (ids : Ids) (u : Use) : Option Ids :=
  match ids.bound.traceOf? u.snapshot with
  | some t => if t == u.trace then some ids else none
  | none =>
    match ids.blocks.find? (·.snapshot.contains u.snapshot) with
    | some b =>
      if b.trace.contains u.trace then
        some { bound := ids.bound ++ [u]
               blocks := ids.blocks.map fun b =>
                 if b.snapshot.contains u.snapshot then
                   { b with snapshot := b.snapshot.erase u.snapshot, trace := b.trace.erase u.trace }
                 else b }
      else none
    | none => if ids.reserved u.trace then none else some { ids with bound := ids.bound ++ [u] }

/-- Two missing ids are the same, and one missing id is not. -/
def Ids.useIds (ids : Ids) (line snapshotLine : Nat) : Option String → Option String → Option Ids
  | some s, some t => ids.use { snapshot := s, trace := t, line, snapshotLine }
  | none, none => some ids
  | _, _ => none

/--
The ids with the ids `u` of a paired `out` request `l` in the block of its alike requests of window `window`. An id
that is already bound or in a block binds instead.
-/
def Ids.join (ids : Ids) (window : Nat) (l : Line) (u : Use) : Option Ids :=
  if ids.known u.snapshot || ids.reserved u.trace then ids.use u
  else
    match ids.blocks.findIdx? fun b => b.window == window && alike b.line l with
    | some i =>
      some { ids with blocks := ids.blocks.modify i fun b =>
        { b with snapshot := b.snapshot ++ [u.snapshot], trace := b.trace ++ [u.trace], uses := b.uses ++ [u] } }
    | none =>
      some { ids with blocks := ids.blocks ++ [{ line := l, window, snapshot := [u.snapshot], trace := [u.trace],
                                                  uses := [u] }] }

/-- The uses that bind an id: the bound ids, and the request of each block that has one request. -/
def Ids.uses (ids : Ids) : List Use :=
  ids.bound ++ ids.blocks.flatMap fun b => if b.uses.length == 1 then b.uses else []

/--
The renamings of a pairing of every window that the search across windows found (guideFor). A search that keeps to them
pairs no value that they pair with another value.
-/
structure Guide where
  ids : Renaming := []
  keys : Renaming := []

/-- Whether `u` pairs no value that `r` pairs with another value. -/
def Renaming.allows (r : Renaming) (u : Use) : Bool :=
  match r.traceOf? u.snapshot with
  | some t => t == u.trace
  | none => !r.takes u.trace

structure Ctx where
  /-- The line of each snapshot id. The later line wins (JS `new Map`). -/
  requests : List (String × Line)
  /-- The lines that must precede snapshot line `n`, counted from 0. -/
  follows : Nat → List Nat
  /-- The snapshot lines, by number, whose pairing can depend on where the implementation line stands (placedLines). -/
  placed : List Nat
  /-- Whether a line is an event that no contract lists, which verify does not compare. -/
  internal : Line → Bool
  /-- The renamings that each search keeps to. -/
  guide : Guide := {}

/-- An open subscription: its subscribe line and the subscribed query's name. -/
structure Subscription where
  out : Out
  name : String

def Line.isRequest (l : Line) : Bool :=
  match l.body with
  | .command .. | .query .. => true
  | _ => false

def Line.isSubscribing (l : Line) : Bool :=
  match l.body with
  | .subscribe .. | .unsubscribe .. => true
  | _ => false

def sameTime (a b : Line) : Bool := a.time.time == b.time.time

def Ctx.answersQuery (c : Ctx) (to : String) : Bool :=
  match c.requests.lookup to with
  | some r =>
    match r.body with
    | .query .. | .subscribe .. => true
    | _ => false
  | none => false

def Line.queryAnswer (l : Line) : Option CValue :=
  match l.body with
  | .answer _ _ _ (.fulfilled _) => l.value
  | .answer .. => l.content
  | _ => none

def Ctx.compared (c : Ctx) (s t : Line) : Option CValue × Option CValue :=
  match s.body with
  | .answer _ _ to _ => if c.answersQuery to then (s.queryAnswer, t.queryAnswer) else (s.content, t.content)
  | _ => (s.content, t.content)

def json (v : Option CValue) : Option Value := v.map (·.flatten)

def jsonOrNull (v : Option CValue) : Value := (json v).getD .null

/-- What a window's search compares in, besides the pairing. -/
structure Scope where
  ctx : Ctx
  declared : List String
  window : Nat
  traceOut : List Out
  openSnapshot : List (String × Subscription)
  openTrace : List (String × Subscription)

/-- A pairing that a search builds, with the renamings under which the paired lines are equal. -/
structure Pairing where
  ids : Ids
  keys : Renaming
  pairs : List (Out × Out) := []
  subscriptions : List (String × String) := []

/-- Whether the uses that pairing `q` adds to pairing `p` keep to the guide. -/
def Guide.allows (g : Guide) (p q : Pairing) : Bool :=
  (q.ids.bound.drop p.ids.bound.length).all g.ids.allows && (q.keys.drop p.keys.length).all g.keys.allows

/-- Whether pairing `s` with `t` keeps the snapshot's `after` order among the pairs. -/
def ordered (c : Ctx) (pairs : List (Out × Out)) (s t : Out) : Bool :=
  pairs.all fun (ps, pt) =>
    (!(c.follows (s.index - 1)).contains (ps.index - 1) || pt.index < t.index) &&
      (!(c.follows (ps.index - 1)).contains (s.index - 1) || t.index < pt.index)

/--
The ids of the pairing with `s` paired with `t`: the answered request's ids, a request's own ids, or the ids of the
request that an event results from.
-/
def pairIds (sc : Scope) (ids : Ids) (s t : Out) : Option Ids :=
  match s.line.body with
  | .answer _ _ to _ => ids.useIds t.index s.index (some to) t.line.body.to?
  | .event _ _ _ _ resultOf => ids.useIds t.index s.index resultOf t.line.body.resultOf?
  | .command .. | .query .. =>
    ids.join sc.window s.line (s.idUse t)
  | _ => some ids

/-- The pairing with `s` paired with `t`, and the bags left to pair, if `t` can stand for `s`. -/
def pairOut (sc : Scope) (p : Pairing) (s t : Out) : Option (Pairing × List Goal) := do
  if !ordered sc.ctx p.pairs s t then none
  let ids ← pairIds sc p.ids s t
  let (ev, av) := sc.ctx.compared s.line t.line
  let (keys, goals) ← walkContent sc.declared t.index s.index ev av p.keys
  pure ({ p with ids, keys, pairs := p.pairs ++ [(s, t)] }, goals)

/-- The pairing with open snapshot subscription `id` paired with open implementation subscription `tid`. -/
def pairSubscription (sc : Scope) (p : Pairing) (id tid : String) : Option (Pairing × List Goal) := do
  let s ← sc.openSnapshot.lookup id
  let t ← sc.openTrace.lookup tid
  if s.name != t.name then none
  let (keys, goals) ← walkContent sc.declared t.out.index s.out.index s.out.line.content t.out.line.content p.keys
  pure ({ p with keys, subscriptions := p.subscriptions ++ [(id, tid)] }, goals)

/-- The elements of `xs` whose key no earlier element has. -/
def distinct {α : Type} (key : α → Value) (xs : List α) : List α :=
  go xs []
where
  go : List α → List Value → List α
    | [], _ => []
    | x :: xs, seen => if seen.contains (key x) then go xs seen else x :: go xs (key x :: seen)

/-- The implementation `out` lines that are not paired yet and have the type, time and name of `s`. -/
def candidates (sc : Scope) (p : Pairing) (s : Out) : List Out :=
  sc.traceOut.filter fun t =>
    !p.pairs.any (·.2.index == t.index) && t.line.body.type == s.line.body.type && sameTime s.line t.line &&
      (match s.line.body with | .answer .. => true | _ => t.line.body.name? == s.line.body.name?)

/--
What pairing an implementation line with snapshot line `s` depends on: the request that it answers or results from, its
compared value, and its number when `s` is placed.
-/
def pairingKey (sc : Scope) (s t : Out) : Value :=
  let id (v : Option String) : Value := (v.map .str).getD .null
  .arr [id t.line.body.to?, id t.line.body.resultOf?, jsonOrNull (sc.ctx.compared s.line t.line).2,
    if sc.ctx.placed.contains s.index then .str (toString t.index) else .null]

/--
The ways to meet goal `g`, each with the goals left. Candidates with the same pairingKey give the same result in the
same pairing, so only the first of them is tried.
-/
def ways (sc : Scope) (g : Goal) (rest : List Goal) (p : Pairing) : List (List Goal × Pairing) :=
  match g with
  | .out s =>
    (distinct (pairingKey sc s) (candidates sc p s)).filterMap fun t =>
      (pairOut sc p s t).map fun (p, goals) => (goals ++ rest, p)
  | .subscription id =>
    let open_ := sc.openTrace.filter fun (tid, t) =>
      !p.subscriptions.any (·.2 == tid) && ((sc.openSnapshot.lookup id).map (·.name == t.name)).getD false
    (distinct (fun (_, t) => jsonOrNull t.out.line.content) open_).filterMap fun (tid, _) =>
      (pairSubscription sc p id tid).map fun (p, goals) => (goals ++ rest, p)
  | .bag line snapshotLine xs ys =>
    match xs with
    | [] => [(rest, p)]
    | x :: more =>
      (distinct (fun (y, _) => y.flatten) ys.zipIdx).filterMap fun (y, i) =>
        (walk sc.declared line snapshotLine x y p.keys).map fun (keys, goals) =>
          (goals ++ [.bag line snapshotLine more (ys.eraseIdx i)] ++ rest, { p with keys })

/-- The ways to meet goal `g` that keep to the guide. -/
def expand (sc : Scope) (g : Goal) (rest : List Goal) (p : Pairing) : List (List Goal × Pairing) :=
  (ways sc g rest p).filter fun (_, q) => sc.ctx.guide.allows p q

inductive Outcome where
  | paired (p : Pairing)
  | unpaired
  | limited

/-- Depth-first search over the frames of `stack`, each the goals left and the pairing so far, for `steps` steps. -/
def search (sc : Scope) : Nat → List (List Goal × Pairing) → Outcome
  | _, [] => .unpaired
  | _, ([], p) :: _ => .paired p
  | 0, _ => .limited
  | n + 1, (g :: rest, p) :: stack => search sc n (expand sc g rest p ++ stack)

/-- The order in which the search pairs lines: requests and lines that create keys, then answers, then the rest. -/
def rank (l : Line) : Nat :=
  if l.isRequest || !(l.created.getD []).isEmpty then 0
  else
    match l.body with
    | .answer .. => 1
    | _ => 2

def byRank (ss : List Out) : List Out :=
  [0, 1, 2].flatMap fun r => ss.filter (rank ·.line == r)

/-- Whether a search may pair all `goals`: the counts agree, and each goal has a way at the start. -/
def pairable (sc : Scope) (goals : List Goal) (start : Pairing) : Bool :=
  (goals.filter fun | .out _ => true | _ => false).length == sc.traceOut.length &&
    sc.openSnapshot.length == sc.openTrace.length && goals.all fun g => !(expand sc g [] start).isEmpty

/-- The pairing of all `goals`, unpaired at once unless they are pairable. -/
def pairAll (sc : Scope) (goals : List Goal) (start : Pairing) : Outcome :=
  if pairable sc goals start then search sc searchLimit [(goals, start)] else .unpaired

structure St where
  findings : List Mismatch := []
  keys : Renaming := []
  declared : List String := []
  ids : Ids := {}
  window : Nat := 0
  openSnapshot : List (String × Subscription) := []
  openTrace : List (String × Subscription) := []
  subscriptionIds : List (String × List String) := []
  reportedMissing : List String := []
  reportedUnexpected : List String := []

abbrev CompareM := ReaderT Ctx (StateM St)

def report (m : Mismatch) : CompareM Unit :=
  modify fun st => { st with findings := st.findings ++ [m] }

def valueMismatch (c : Ctx) (s : Line) (t : Out) (keys : Renaming) : Option Mismatch :=
  let a := t.line
  let got := jsonOrNull a.content
  let subject := Subject.of a.toTraceLine
  let sub (v : Option CValue) : Value := jsonOrNull (v.map (substitute keys))
  match s.body, a.body with
  | .command .., _ | .query .., _ => some (.request t.index subject (sub s.content) got)
  | .event .., _ => some (.event t.index subject (sub s.content) got)
  | .operation .., _ | .unacceptedOperation .., _ => some (.operation t.index subject (sub s.content) got)
  | .answer _ _ snapshotTo e, .answer _ _ _ g =>
    let output (x y : Option CValue) : Mismatch := .output t.index subject (sub x) (jsonOrNull y)
    if c.answersQuery snapshotTo then some (output s.queryAnswer a.queryAnswer)
    else if e.result != g.result then some (.result t.index subject e.result g.result)
    else
      match e, g with
      | .rejected er, .rejected gr => some (.rejection t.index subject er.kind gr.kind)
      | .accepted _, .accepted _ | .fulfilled _, .fulfilled _ => some (output s.value a.value)
      | _, _ => none
  | _, _ => none

def missing (s : Out) (line : Nat) : CompareM Unit := do
  let st ← get
  let l := s.line
  match l.body with
  | .answer _ _ to _ | .unsubscribe _ _ to =>
    report (.missingAnswer line (.reply l.body.type ((st.ids.bound.traceOf? to).getD to)) s.index)
  | _ =>
    let content := jsonOrNull (l.content.map (substitute st.keys))
    report (.missingLine line (Subject.of l.toTraceLine) content s.index)

/-- The renaming under which the values are equal, bags included, or `none`. -/
def contentKeys (sc : Scope) (line snapshotLine : Nat) (s t : Option CValue) (p : Pairing) : Option Renaming :=
  (walkContent sc.declared line snapshotLine s t p.keys).bind fun (keys, goals) =>
    match search sc searchLimit [(goals, { p with keys })] with
    | .paired p => some p.keys
    | _ => none

/--
The groups of connected uses in which a value stands for two values, each in the order of the uses. A snapshot value and
an implementation value connect when a use pairs them.
-/
def conflicts (uses : List Use) : List (List Use) :=
  let groups := uses.eraseDups.foldl (init := ([] : List (List Use))) fun groups u =>
    let touches (g : List Use) : Bool := g.any fun v => v.snapshot == u.snapshot || v.trace == u.trace
    match groups.findIdx? touches with
    | none => groups ++ [[u]]
    | some i =>
      let rest := groups.filter (!touches ·)
      rest.take i ++ [(groups.filter touches).flatten ++ [u]] ++ rest.drop i
  groups.filter fun g =>
    g.any fun u => g.any fun v => (u.snapshot == v.snapshot && u.trace != v.trace) ||
      (u.trace == v.trace && u.snapshot != v.snapshot)

/--
Pairs the lines one by one, preferring equal lines, and reports the differences. When no line differs, including the
subscriptions reported in an earlier window, it reports the uses of each value that stands for two values.
-/
def explain (sc : Scope) (specOut : List Out) (missingAt : Nat) : CompareM Unit := do
  let c ← read
  let before ← get
  let mut pairs : List (Out × Out) := []
  let mut idUses : List Use := []
  let mut keyUses : List Use := []
  let mut repeated := false
  for s in byRank specOut do
    let st ← get
    let p : Pairing := { ids := st.ids, keys := st.keys }
    let cands := sc.traceOut.filter fun t =>
      !pairs.any (·.2.index == t.index) && t.line.body.type == s.line.body.type &&
        match s.line.body with
        | .answer _ _ to _ => (st.ids.useIds t.index s.index (some to) t.line.body.to?).isSome
        | _ => t.line.body.name? == s.line.body.name?
    let keysOf (t : Out) : Option Renaming :=
      let (ev, av) := c.compared s.line t.line
      contentKeys sc t.index s.index ev av p
    let equal (t : Out) : Bool := (pairIds sc st.ids s t).isSome && (keysOf t).isSome
    let renamed (t : Out) : Bool :=
      let (ev, av) := c.compared s.line t.line
      (freeContent st.declared t.index s.index ev av).isSome
    match (cands.find? fun t => equal t && sameTime s.line t.line) <|> cands.find? equal <|> cands.find? renamed <|>
        cands.head? with
    | none => missing s missingAt
    | some t =>
      pairs := pairs ++ [(s, t)]
      if !sameTime s.line t.line then
        report (.time t.index (Subject.of t.line.toTraceLine) s.line.time.text t.line.time.text)
      match pairIds sc st.ids s t, s.line.body with
      | some ids, _ => modify fun st => { st with ids }
      | none, .event _ _ _ _ resultOf =>
        report (.resultOf t.index (Subject.of t.line.toTraceLine) resultOf t.line.body.resultOf?)
      | none, _ => idUses := idUses ++ [s.idUse t]
      let (ev, av) := c.compared s.line t.line
      match keysOf t, freeContent st.declared t.index s.index ev av with
      | some keys, _ => modify fun st => { st with keys }
      | none, some uses => keyUses := keyUses ++ uses
      | none, none => if let some m := valueMismatch c s.line t st.keys then report m
  let mut subscriptions : List (String × String) := []
  for (id, s) in sc.openSnapshot do
    let st ← get
    let p : Pairing := { ids := st.ids, keys := st.keys }
    let cands := sc.openTrace.filter fun (tid, t) => !subscriptions.any (·.2 == tid) && t.name == s.name
    let keysOf (t : Subscription) : Option Renaming :=
      contentKeys sc t.out.index s.out.index s.out.line.content t.out.line.content p
    let renamed (t : Subscription) : Bool :=
      (freeContent st.declared t.out.index s.out.index s.out.line.content t.out.line.content).isSome
    match (cands.find? fun (_, t) => (keysOf t).isSome) <|> cands.find? (renamed ·.2) with
    | some (tid, t) =>
      subscriptions := subscriptions ++ [(id, tid)]
      match keysOf t, freeContent st.declared t.out.index s.out.index s.out.line.content t.out.line.content with
      | some keys, _ => modify fun st => { st with keys }
      | none, uses => keyUses := keyUses ++ uses.getD []
    | none =>
      if st.reportedMissing.contains id then repeated := true
      else
        set { st with reportedMissing := st.reportedMissing ++ [id] }
        report (.unopenedSubscription missingAt (Subject.of s.out.line.toTraceLine)
          (jsonOrNull (s.out.line.content.map (substitute st.keys))) s.out.index)
  for (tid, t) in sc.openTrace do
    let st ← get
    if !subscriptions.any (·.2 == tid) then
      if st.reportedUnexpected.contains tid then repeated := true
      else
        set { st with reportedUnexpected := st.reportedUnexpected ++ [tid] }
        report (.unexpectedSubscription t.out.index (Subject.of t.out.line.toTraceLine) (jsonOrNull t.out.line.content))
  modify fun st => { st with subscriptionIds := subscribed sc st.subscriptionIds subscriptions }
  for (s, t) in pairs do
    let before := pairs.find? fun (ps, pt) => pt.index > t.index && (c.follows (s.index - 1)).contains (ps.index - 1)
    if let some (_, bt) := before then
      report (.lineOrder t.index (Subject.of t.line.toTraceLine) (Subject.of bt.line.toTraceLine))
  for t in sc.traceOut do
    if !pairs.any (·.2.index == t.index) then report (.unexpectedLine t.index (Subject.of t.line.toTraceLine))
  let st ← get
  if !repeated && st.findings.length == before.findings.length then
    let found := conflicts (st.ids.uses ++ idUses) ++ conflicts (st.keys ++ keyUses)
    if found.isEmpty then report (.renaming (keyUses ++ idUses ++ st.keys.drop before.keys.length))
    else for uses in found do report (.renaming uses)
where
  /-- Each paired snapshot subscription with the implementation subscriptions paired with alike subscriptions. -/
  subscribed (sc : Scope) (known : List (String × List String)) (pairs : List (String × String)) :
      List (String × List String) :=
    let lineOf (s : String) : Option Line := (sc.openSnapshot.lookup s).map (·.out.line)
    pairs.foldl (init := known) fun all (s, _) =>
      let ids := pairs.foldl (init := (all.lookup s).getD []) fun ids (other, t) =>
        match lineOf s, lineOf other with
        | some a, some b => if alike a b && !ids.contains t then ids ++ [t] else ids
        | _, _ => ids
      setAt all s ids

/-- The open subscriptions after the subscribe and unsubscribe lines of `lines`. -/
def follow (open_ : List (String × Subscription)) (lines : List Out) : List (String × Subscription) :=
  lines.foldl (init := open_) fun o l =>
    match l.line.body with
    | .subscribe _ id name _ => if (o.lookup id).isSome then o else o ++ [(id, { out := l, name })]
    | .unsubscribe _ _ to => o.filter (·.1 != to)
    | _ => o

/-- The state in which the search of a window with `out` lines `specOut` and `traceOut` starts. -/
def enter (st : St) (specOut traceOut : List Out) : St :=
  { st with findings := []
            declared := specOut.foldl (fun d s => d ++ s.line.created.getD []) st.declared
            window := st.window + 1
            openSnapshot := follow st.openSnapshot (specOut.filter (·.line.isSubscribing))
            openTrace := follow st.openTrace (traceOut.filter (·.line.isSubscribing)) }

/-- The scope of a window's search, with the window's implementation `out` lines `traceOut`. -/
def scopeOf (c : Ctx) (st : St) (traceOut : List Out) : Scope :=
  { ctx := c, declared := st.declared, window := st.window,
    traceOut := traceOut.filter fun t => !t.line.isSubscribing && !c.internal t.line,
    openSnapshot := st.openSnapshot, openTrace := st.openTrace }

/-- The snapshot `out` lines that a window's search pairs. -/
def comparedOut (c : Ctx) (specOut : List Out) : List Out :=
  specOut.filter fun s => !s.line.isSubscribing && !c.internal s.line

def goalsOf (c : Ctx) (st : St) (specOut : List Out) : List Goal :=
  (byRank (comparedOut c specOut)).map .out ++ st.openSnapshot.map (.subscription ·.1)

/-- The state after a window whose search in scope `sc` found `p`. -/
def St.paired (st : St) (sc : Scope) (p : Pairing) : St :=
  { st with ids := p.ids, keys := p.keys, subscriptionIds := explain.subscribed sc st.subscriptionIds p.subscriptions }

/--
Compares the `out` lines between two `in` lines, which follow the `in` lines `missingAt` and `snapshotAt`. It returns
the violation when the search stops at `searchLimit`.
-/
def compareWindow (allSpecOut allTraceOut : List Out) (missingAt snapshotAt : Nat) :
    CompareM (Option Uncomparable) := do
  let c ← read
  modify (enter · allSpecOut allTraceOut)
  let st ← get
  let sc := scopeOf c st allTraceOut
  match pairAll sc (goalsOf c st allSpecOut) { ids := st.ids, keys := st.keys } with
  | .paired p =>
    set (st.paired sc p)
    pure none
  | .limited => pure (some (.searchLimit missingAt snapshotAt))
  | .unpaired =>
    explain sc (comparedOut c allSpecOut) missingAt
    pure none

/-- Whether answer `t` answers the request that answer `s` answers, through a like subscription or the ids. -/
def answersPlaced (st : St) (s t : Out) : Option Ids :=
  match s.line.body, t.line.body with
  | .answer _ _ snapshotTo _, .answer _ _ to _ =>
    match st.subscriptionIds.lookup snapshotTo with
    | some ids => if ids.contains to then some st.ids else none
    | none => st.ids.useIds t.index s.index (some snapshotTo) (some to)
  | _, _ => none

/-- The pairing of two `in` lines apart from the elements of bags, and the bags left to pair. -/
def inputStart (st : St) (s t : Out) : Option (List Goal × Pairing) :=
  let (sl, tl) := (s.line, t.line)
  if sl.body.type != tl.body.type || sl.body.name? != tl.body.name? || !sameTime sl tl then none
  else
    match st.ids.use (s.idUse t) with
    | none => none
    | some ids =>
      let st := { st with ids }
      let placed : Option Ids :=
        match sl.body with
        | .time .. | .restart .. => some ids
        | .unsubscribe _ _ to => ids.useIds t.index s.index (some to) tl.body.to?
        | .answer .. => answersPlaced st s t
        | _ => ids.useIds t.index s.index sl.body.resultOf? tl.body.resultOf?
      match placed with
      | none => none
      | some ids =>
        match sl.body with
        | .time .. | .restart .. | .unsubscribe .. => some ([], { ids, keys := st.keys })
        | _ =>
          (walkContent st.declared t.index s.index sl.content tl.content st.keys).map fun (keys, goals) =>
            (goals, { ids, keys })

/-- The comparison of two `in` lines: the renamings under which they are the same. -/
def sameInput (sc : Scope) (st : St) (s t : Out) : Outcome :=
  match inputStart st s t with
  | none => .unpaired
  | some (goals, p) => search sc searchLimit [(goals, p)]

def runWindow (c : Ctx) (st : St) (specOut traceOut : List Out) (missingAt snapshotAt : Nat) :
    List Mismatch × Option Uncomparable × St :=
  let (limited, st) := ((compareWindow specOut traceOut missingAt snapshotAt).run c).run { st with findings := [] }
  (st.findings, limited, st)

def differentInput (st : St) (s t : Out) : Uncomparable :=
  let mismatch : Uncomparable := .differentInput t.index s.index
    (substitute st.keys (.ofValue (ToValue.toValue s.line.toTraceLine))).flatten (ToValue.toValue t.line.toTraceLine)
  match s.line.body, t.line.body with
  | .answer .., .answer .. =>
    if (answersPlaced st s t).isSome then mismatch else .differentRequest t.index (Subject.of t.line.toTraceLine) s.index
  | _, _ => mismatch

def bindings (st : St) : Bindings := st.keys.map fun u => (u.snapshot, u.trace)

def inputScope (c : Ctx) (st : St) : Scope :=
  { ctx := c, declared := st.declared, window := st.window, traceOut := [], openSnapshot := [], openTrace := [] }

mutual

/--
The violations from the windows. Each element holds a snapshot window, an implementation window and the previous `in`
lines of the implementation and of the snapshot. The `out` lines are compared before the `in` line, and `malformed` is
reported after the last element.
-/
def compareFrom (c : Ctx) (lineCount : Nat) (malformed : Option Nat) :
    List (Option Window × Option Window × Option Out × Option Out) → St → Compared
  | [], st => { findings := (malformed.map fun n => .uncomparable (.lineSchema n)).toList, bindings := bindings st }
  | (expected, actual, previous, previousSnapshot) :: rest, st =>
    let (found, limited, st) := runWindow c st ((expected.map (·.before)).getD []) ((actual.map (·.before)).getD [])
      ((previous.map (·.index)).getD 1) ((previousSnapshot.map (·.index)).getD 1)
    match limited with
    | some u => { findings := found.map .mismatch ++ [.uncomparable u], bindings := bindings st }
    | none =>
      let later := compareInputs c lineCount malformed (expected.bind (·.input)) (actual.bind (·.input)) rest st
      { later with findings := found.map .mismatch ++ later.findings }
termination_by L => 2 * L.length

/--
The violations from the `in` lines and the rest. The comparison reports and stops when only one side has a line or the
lines differ, and it stops when neither side has one.
-/
def compareInputs (c : Ctx) (lineCount : Nat) (malformed : Option Nat) (expected actual : Option Out)
    (rest : List (Option Window × Option Window × Option Out × Option Out)) (st : St) : Compared :=
  match expected, actual with
  | none, none => { findings := [], bindings := bindings st }
  | none, some t =>
    { findings := [.uncomparable (.unexpectedInput t.index (ToValue.toValue t.line.toTraceLine))],
      bindings := bindings st }
  | some s, none =>
    { findings := [.uncomparable (.missingInput lineCount (ToValue.toValue s.line.toTraceLine) s.index)],
      bindings := bindings st }
  | some s, some t =>
    match sameInput (inputScope c st) st s t with
    | .unpaired => { findings := [.uncomparable (differentInput st s t)], bindings := bindings st }
    | .limited => { findings := [.uncomparable (.searchLimit t.index s.index)], bindings := bindings st }
    | .paired p => compareFrom c lineCount malformed rest { st with ids := p.ids, keys := p.keys }
termination_by 2 * rest.length + 1

end

/-- A part of the comparison that one search pairs: the `out` lines of a window, or two `in` lines. -/
inductive Stage where
  /-- The `out` lines of a window that follows the `in` lines `missingAt` and `snapshotAt`. -/
  | outs (specOut traceOut : List Out) (missingAt snapshotAt : Nat)
  | input (s t : Out)

/-- The violation when the search of the stage takes more than `searchLimit` steps. -/
def Stage.limited : Stage → Uncomparable
  | .outs _ _ missingAt snapshotAt => .searchLimit missingAt snapshotAt
  | .input s t => .searchLimit t.index s.index

/-- The stages of compareFrom's windows, up to an `in` line that only one side has. -/
def stagesOf : List (Option Window × Option Window × Option Out × Option Out) → List Stage
  | [] => []
  | (expected, actual, previous, previousSnapshot) :: rest =>
    .outs ((expected.map (·.before)).getD []) ((actual.map (·.before)).getD []) ((previous.map (·.index)).getD 1)
        ((previousSnapshot.map (·.index)).getD 1) ::
      match expected.bind (·.input), actual.bind (·.input) with
      | some s, some t => .input s t :: stagesOf rest
      | _, _ => []

/-- A frame of the search across stages: the goals left of stage number `stage`, and the pairing so far. -/
structure Frame where
  goals : List Goal
  pairing : Pairing
  scope : Scope
  /-- The state before the stage. -/
  st : St
  stage : Nat

/-- The frame that starts the stage, number `k`, in state `st`, unless the stage has no pairing at once. -/
def Stage.start (c : Ctx) (k : Nat) (st : St) : Stage → Option Frame
  | .outs specOut traceOut _ _ =>
    let st := enter st specOut traceOut
    let scope := scopeOf c st traceOut
    let goals := goalsOf c st specOut
    let pairing : Pairing := { ids := st.ids, keys := st.keys }
    if pairable scope goals pairing then some { goals, pairing, scope, st, stage := k } else none
  | .input s t =>
    (inputStart st s t).map fun (goals, pairing) => { goals, pairing, scope := inputScope c st, st, stage := k }

/-- The state after the stage of `f`, whose goals are met. -/
def Frame.commit (f : Frame) : Stage → St
  | .outs .. => f.st.paired f.scope f.pairing
  | .input .. => { f.st with ids := f.pairing.ids, keys := f.pairing.keys }

/--
Depth-first search over the frames of `stack` for a pairing of every stage, with the steps left of each stage in
`left`. A step expands a goal or starts a stage, so `fuel` covers every step. It returns the renamings of the pairing,
or no guide when there is no pairing.
-/
def searchAcross (c : Ctx) (stages : List Stage) : Nat → List Nat → List Frame → Except Uncomparable Guide
  | 0, _, _ | _, _, [] => .ok {}
  | fuel + 1, left, f :: stack =>
    match f.goals, stages[f.stage]? with
    | _, none => .ok {}
    | g :: rest, some stage =>
      match left[f.stage]? with
      | some (n + 1) =>
        searchAcross c stages fuel (left.set f.stage n)
          ((expand f.scope g rest f.pairing).map (fun (goals, pairing) => { f with goals, pairing }) ++ stack)
      | _ => .error stage.limited
    | [], some stage =>
      let st := f.commit stage
      let k := f.stage + 1
      match stages[k]?, left[k]? with
      | none, _ => .ok { ids := st.ids.bound, keys := st.keys }
      | some next, some (n + 1) => searchAcross c stages fuel (left.set k n) ((next.start c k st).toList ++ stack)
      | some next, _ => .error next.limited

/--
The guide of the comparison of the windows: the renamings of a pairing of every window and `in` line, found by trying
the other pairings of earlier stages when a later stage has none, or no guide when there is no such pairing. Each stage
has `searchLimit` steps, its start included, over all the times that the search returns to it; the violation names the
stage that runs out.
-/
def guideFor (c : Ctx) (windows : List (Option Window × Option Window × Option Out × Option Out)) :
    Except Uncomparable Guide :=
  let stages := stagesOf windows
  match stages with
  | [] => .ok {}
  | first :: _ =>
    searchAcross c stages (stages.length * (searchLimit + 1))
      ((stages.map fun _ => searchLimit + 1).set 0 searchLimit) (first.start c 0 {}).toList

/-- The latest of the earlier lines with the id, as an index counted from 0. -/
def earlierWithId (earlier : List Out) (id : String) : Option Nat :=
  (earlier.reverse.find? fun o => o.line.body.id == id).map (·.index - 1)

/-- Each `after` id of a snapshot `out` line that names no earlier `out` line of its window, at that snapshot line. -/
def unknownAfters (snapshot : List (Option Line)) : List Uncomparable :=
  (steps snapshot).flatMap fun w =>
    w.before.zipIdx.flatMap fun (o, k) =>
      (o.line.after.getD []).filterMap fun id =>
        if (earlierWithId (w.before.take k) id).isSome then none else some (.unknownAfter o.index id)

/-- The lines that line `n` must follow: the earlier `out` lines of its window that its `after` names. -/
def mustFollow (snapshot : List (Option Line)) (n : Nat) : List Nat :=
  (((steps snapshot).flatMap fun w =>
    w.before.zipIdx.filterMap fun (o, k) =>
      if o.index - 1 == n then some ((o.line.after.getD []).filterMap (earlierWithId (w.before.take k)))
      else none).head?).getD []

/--
The snapshot lines, by number, whose pairing can depend on where the implementation line stands: those of a window that
share their type and name with a line that an `after` of the window names or orders.
-/
def placedLines (snapshot : List (Option Line)) : List Nat :=
  (steps snapshot).flatMap fun w =>
    let follows := w.before.zipIdx.map fun (o, k) =>
      (o.index, (o.line.after.getD []).filterMap fun id => (earlierWithId (w.before.take k) id).map (· + 1))
    let ordered := w.before.filter fun o =>
      follows.any fun (n, earlier) => (n == o.index && !earlier.isEmpty) || earlier.contains o.index
    (w.before.filter fun o => ordered.any fun m =>
      m.line.body.type == o.line.body.type && m.line.body.name? == o.line.body.name?).map (·.index)

/-- The line that orders a finding in a report: its `line`, or for `renaming` the last line of its uses. -/
def Finding.line : Finding → Nat
  | .mismatch (.renaming uses) => uses.foldl (fun n u => max n u.line) 0
  | .mismatch m =>
    match m.place.lookup "line" with
    | some (.num n) => n.mantissa.toNat
    | _ => 0
  | .uncomparable u =>
    match u.place.lookup "line" with
    | some (.num n) => n.mantissa.toNat
    | _ => 0

/--
The violations of comparing a trace with a snapshot, and the bindings. In `snapshot`, `none` is a blank line. `lines`
holds the trace lines before its first malformed line, with `none` for blank lines and repeated subscription answers,
and `malformed` is the number of that line. `internal` selects the event lines that verify does not compare. An
`unknownAfters` id orders no line, because reading the snapshot reports it before the comparison.
-/
def compare (snapshot lines : List (Option Line)) (malformed : Option Nat) (internal : Line → Bool) : Compared :=
  let expected := steps snapshot
  let actual := steps lines
  let count := match malformed with
    | some _ => actual.length - 1
    | none => max expected.length actual.length
  let windows := (List.range count).map fun k =>
    (expected[k]?, actual[k]?, if k == 0 then none else (actual[k - 1]?).bind (·.input),
      if k == 0 then none else (expected[k - 1]?).bind (·.input))
  let ctx : Ctx := {
    requests := (snapshot.filterMap fun l => l.map fun l => (l.body.id, l)).reverse,
    follows := mustFollow snapshot,
    placed := placedLines snapshot,
    internal }
  match guideFor ctx windows with
  | .ok guide => compareFrom { ctx with guide } lines.length malformed windows {}
  | .error u => { findings := [.uncomparable u], bindings := [] }

end Tazuna.Verify
