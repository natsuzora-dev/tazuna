import Tazuna.Data.Trace
import Tazuna.Verify.Canonical
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable

/-!
This module compares an implementation trace with a snapshot.

- `in` lines split `out` lines into windows. In each window, verify pairs snapshot `out` lines with implementation
  `out` lines.
- Paired lines have equal type, place (the answered request for answer and unsubscribe lines, and the name otherwise),
  time and value. Values compare as CValue. A createKey value (snapshot `created`) binds to the implementation value at
  the same place. Bag elements pair with backtracking over bindings.
- Requests in one window with equal type, name and input stay unassigned until a later line (answer, unsubscribe,
  resultOf) names one.
- Subscriptions still open after the window pair by name and input.
- The order of paired lines must follow the snapshot's `after` (mustFollow). Verify reports an `after` id that names no
  earlier `out` line of the same window, and compares nothing.
- Each `in` line is compared with the `in` line at the same position. After a difference, nothing later is compared.
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

/--
Whether `w` already stands for a snapshot value other than `v`. A value stands for one snapshot value, so an
implementation key that equals another snapshot value is not taken as that value.
-/
def standsForOther (m : Bindings) (v w : String) : Bool := m.any fun (k, ws) => k != v && ws.contains w

macro "lex_decreasing" : tactic =>
  `(tactic| (simp_wf; simp only [Prod.lex_def] at *; first | done | omega | (simp_all; done) | (simp_all; omega)))

mutual

def CValue.mapStrings (f : String → String) : CValue → CValue
  | .leaf (.str s) => .leaf (.str (f s))
  | .leaf v => .leaf v
  | .arr xs => .arr (CValue.mapStringsList f xs)
  | .obj fs => .obj (CValue.mapStringsFields f fs)
  | .bag xs => .bag (CValue.mapStringsList f xs)
  | .runs rs => .runs (CValue.mapStringsList f rs)

def CValue.mapStringsList (f : String → String) : List CValue → List CValue
  | [] => []
  | x :: xs => x.mapStrings f :: CValue.mapStringsList f xs

def CValue.mapStringsFields (f : String → String) : List (String × CValue) → List (String × CValue)
  | [] => []
  | (k, v) :: fs => (k, v.mapStrings f) :: CValue.mapStringsFields f fs

end

/-- `v` with its snapshot createKey values replaced by their implementation values, for reports. -/
def substitute (m : Bindings) (v : CValue) : CValue :=
  v.mapStrings fun s => match m.lookup s with
    | some (w :: _) => w
    | _ => s

/--
The bindings `m` with each declared createKey value not yet in `m` bound to the implementation value at the same place,
unless that value stands for another snapshot value. It walks only arrays and plain objects; matchBag binds bag
elements.
-/
def bindValues (declared : List String) (s t : Option CValue) (m : Bindings) : Bindings :=
  match s, t with
  | some (.leaf (.str v)), t =>
    if declared.contains v && (m.lookup v).isNone then
      match t with
      | some (.leaf (.str w)) => if standsForOther m v w then m else setAt m v [w]
      | _ => m
    else m
  | some s, some t =>
    if s.isPlain && t.isPlain then
      (unionKeys s t).attach.foldl (init := m) fun m ⟨k, _⟩ =>
        match hs : s.at? k with
        | some sv =>
          have := at?_sizeOf hs
          bindValues declared (some sv) (t.at? k) m
        | none => m
    else m
  | _, _ => m
termination_by (s.map sizeOf).getD 0
decreasing_by simp_wf; omega

mutual

/--
Whether `s` equals `t`, and the updated `m`. A bound createKey value equals its bound implementation values. In an `in`
line (`inInputLine`), a snapshot value also equals itself and stays bound to itself, unless it stands for another
snapshot value. The bindings stay even on a difference, as TS mutates its map.
-/
def equal (declared : List String) (s t : CValue) (m : Bindings) (inInputLine : Bool) : Bool × Bindings :=
  match s with
  | .leaf (.str v) =>
    match m.lookup v with
    | some same =>
      match t with
      | .leaf (.str w) =>
        if same.contains w then (true, m)
        else if inInputLine && w == v && !standsForOther m v v then (true, setAt m v (same ++ [v]))
        else (false, m)
      | _ => (false, m)
    | none => (match t with | .leaf w => w == .str v | _ => false, m)
  | .leaf v => (match t with | .leaf w => w == v | _ => false, m)
  | .runs rs =>
    match t with
    | .runs rt => if rs.length == rt.length then equalList declared rs rt m inInputLine else (false, m)
    | _ => (false, m)
  | .bag xs =>
    match t with
    | .bag ys =>
      match matchBag declared xs ys m inInputLine with
      | some matched => (true, matched)
      | none => (false, m)
    | _ => (false, m)
  | .arr xs =>
    match t with
    | .arr ys => if xs.length == ys.length then equalList declared xs ys m inInputLine else (false, m)
    | _ => (false, m)
  | .obj fs =>
    match t with
    | .obj gs =>
      let ks := fs.map (·.1)
      let kt := gs.map (·.1)
      if ks.length == kt.length && ks.all kt.contains && kt.all ks.contains then
        equalFields declared fs gs m inInputLine
      else (false, m)
    | _ => (false, m)
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

/-- Whether the lists are equal element by element. It stops at the first difference (JS `every`). -/
def equalList (declared : List String) (xs ys : List CValue) (m : Bindings) (inInputLine : Bool) : Bool × Bindings :=
  match xs, ys with
  | [], [] => (true, m)
  | x :: xs, y :: ys =>
    match equal declared x y m inInputLine with
    | (true, m) => equalList declared xs ys m inInputLine
    | (false, m) => (false, m)
  | _, _ => (false, m)
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

/-- Whether the fields are equal, in the field order of `fs`. It stops at the first difference. -/
def equalFields (declared : List String) (fs gs : List (String × CValue)) (m : Bindings) (inInputLine : Bool) :
    Bool × Bindings :=
  match fs with
  | [] => (true, m)
  | (k, v) :: fs =>
    match gs.lookup k with
    | some w =>
      match equal declared v w m inInputLine with
      | (true, m) => equalFields declared fs gs m inInputLine
      | (false, m) => (false, m)
    | none => (false, m)
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

/--
The bindings that pair each element of `ss` with an equal element of `ts`, found by backtracking. Two equal candidates
give the same result, so only one of them is tried.
-/
def matchBag (declared : List String) (ss ts : List CValue) (m : Bindings) (inInputLine : Bool) : Option Bindings :=
  if ss.length != ts.length then none
  else
    match ss with
    | [] => some m
    | first :: rest => matchBagFrom declared first rest ts [] [] m inInputLine
termination_by (sizeOf ss, ts.length + 1)
decreasing_by all_goals lex_decreasing

/-- The search of matchBag for `first`. `passed` holds the candidates tried, and `tried` their JSON. -/
def matchBagFrom (declared : List String) (first : CValue) (rest cands passed : List CValue) (tried : List Value)
    (m : Bindings) (inInputLine : Bool) : Option Bindings :=
  match cands with
  | [] => none
  | t :: more =>
    if tried.contains t.flatten then matchBagFrom declared first rest more (t :: passed) tried m inInputLine
    else
      let tried := t.flatten :: tried
      let tentative := bindValues declared (some first) (some t) m
      let next := matchBagFrom declared first rest more (t :: passed) tried m inInputLine
      match equal declared first t tentative inInputLine with
      | (true, m') =>
        match matchBag declared rest (passed.reverse ++ more) m' inInputLine with
        | some r => some r
        | none => next
      | (false, _) => next
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

/-- Whether two optional values are equal. Two missing values (undefined) are equal, and one missing value is not. -/
def equalContent (declared : List String) (s t : Option CValue) (m : Bindings) (inInputLine : Bool) : Bool × Bindings :=
  match s, t with
  | some s, some t => equal declared s t m inInputLine
  | none, none => (true, m)
  | _, _ => (false, m)

/--
The pairs of snapshot and implementation ids of requests, subscriptions and inputs. Requests in one window with equal
type, name and input stay in `groups` until a later line names one.
-/
structure Ids where
  bound : List (String × String) := []
  taken : List String := []
  groups : List (String × List String) := []

def Ids.matches (ids : Ids) (s t : Option String) : Bool :=
  match s, t with
  | some s, some t =>
    match ids.bound.lookup s with
    | some b => b == t
    | none => ((ids.groups.lookup s).map (·.contains t)).getD false && !ids.taken.contains t
  | none, none => true
  | _, _ => false

def Ids.bind (ids : Ids) (s t : Option String) : Ids :=
  match s, t with
  | some s, some t =>
    if (ids.bound.lookup s).isSome then ids
    else { bound := ids.bound ++ [(s, t)], taken := ids.taken ++ [t], groups := ids.groups.filter (·.1 != s) }
  | _, _ => ids

def Ids.group (ids : Ids) (snapshot trace : List String) : Ids :=
  match snapshot with
  | [s] => ids.bind (some s) trace.head?
  | _ => { ids with groups := snapshot.foldl (fun g id => setAt g id trace) ids.groups }

def Ids.traceOf (ids : Ids) (s : String) : String := (ids.bound.lookup s).getD s

structure Ctx where
  /-- The line of each snapshot id. The later line wins (JS `new Map`). -/
  requests : List (String × Line)
  /-- The lines that must precede snapshot line `n`, counted from 0. -/
  follows : Nat → List Nat
  /-- Whether a line is an event that no contract lists, which verify does not compare. -/
  internal : Line → Bool

/-- An open subscription: its subscribe line and the subscribed query's name. -/
structure Subscription where
  out : Out
  name : String

structure St where
  findings : List Mismatch := []
  values : Bindings := []
  declared : List String := []
  ids : Ids := {}
  openSnapshot : List (String × Subscription) := []
  openTrace : List (String × Subscription) := []
  subscriptionIds : List (String × List String) := []
  reportedMissing : List String := []
  reportedUnexpected : List String := []

abbrev CompareM := ReaderT Ctx (StateM St)

def report (m : Mismatch) : CompareM Unit :=
  modify fun st => { st with findings := st.findings ++ [m] }

def Line.isRequest (l : Line) : Bool :=
  match l.body with
  | .command .. | .query .. => true
  | _ => false

def Line.isSubscribing (l : Line) : Bool :=
  match l.body with
  | .subscribe .. | .unsubscribe .. => true
  | _ => false

def subject (l : Line) : Subject :=
  match l.body with
  | .answer _ _ to _ | .unsubscribe _ _ to => .reply l.body.type to
  | _ => .named l.body.type l.body.name? l.body.id

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

def samePlace (ids : Ids) (s t : Line) : Bool :=
  match s.body with
  | .answer _ _ to _ | .unsubscribe _ _ to => ids.matches (some to) t.body.to?
  | _ => t.body.name? == s.body.name?

def json (v : Option CValue) : Option Value := v.map (·.flatten)

def jsonOrNull (v : Option CValue) : Value := (json v).getD .null

/-- Whether two values are equal after binding their createKey values. The tentative bindings stay. -/
def tryEqual (declared : List String) (s t : Option CValue) (m : Bindings) : Bool × Bindings :=
  equalContent declared s t (bindValues declared s t m) false

def valueMismatch (c : Ctx) (s : Line) (t : Out) (values : Bindings) : Option Mismatch :=
  let a := t.line
  let got := jsonOrNull a.content
  let sub (v : Option CValue) : Value := jsonOrNull (v.map (substitute values))
  match s.body, a.body with
  | .command _ _ name _, _ | .query _ _ name _, _ =>
    some (.request t.index a.body.id s.body.type name (sub s.content) got)
  | .event _ _ name _ _, _ => some (.event t.index name (sub s.content) got)
  | .answer _ _ snapshotTo e, .answer _ _ to g =>
    let output (x y : Option CValue) : Mismatch := .output t.index to (sub x) (jsonOrNull y)
    if c.answersQuery snapshotTo then some (output s.queryAnswer a.queryAnswer)
    else if e.result != g.result then some (.result t.index to e.result g.result)
    else
      match e, g with
      | .rejected er, .rejected gr => some (.rejection t.index to er.kind gr.kind)
      | .accepted _, .accepted _ => some (output s.value a.value)
      | _, _ => none
  | _, _ => none

/-- Reports the differences of a paired line and binds its createKey values. -/
def matchLine (s : Line) (t : Out) : CompareM Unit := do
  let c ← read
  if !sameTime s t.line then report (.time t.index (subject t.line) s.time.text t.line.time.text)
  if let .answer _ _ to _ := s.body then modify fun st => { st with ids := st.ids.bind (some to) t.line.body.to? }
  let (ev, av) := c.compared s t.line
  let st ← get
  let (same, values) := tryEqual st.declared ev av st.values
  set { st with values }
  if !same then if let some m := valueMismatch c s t values then report m

def missing (s : Out) (line : Nat) : CompareM Unit := do
  let st ← get
  let l := s.line
  match l.body with
  | .answer _ _ to _ | .unsubscribe _ _ to => report (.missingAnswer line l.body.type (st.ids.traceOf to) s.index)
  | _ =>
    let content := jsonOrNull (l.content.map (substitute st.values))
    report (.missingLine line l.body.type (l.body.name?.getD "") content s.index)

/-- A snapshot line and the implementation line paired with it. -/
abbrev Pair := Out × Out

/--
The pairs of each snapshot line with a distinct implementation line equal in type, place, time and value, found by
backtracking, and their bindings.
-/
def pairExactly (c : Ctx) (ids : Ids) (declared : List String) (ss ts : List Out) (m : Bindings) :
    Option (List Pair × Bindings) :=
  match ss with
  | [] => some ([], m)
  | first :: rest => go first rest ts [] [] m
termination_by (ss.length, 0)
decreasing_by all_goals lex_decreasing
where
  go (first : Out) (rest cands passed : List Out) (tried : List Value) (m : Bindings) :
      Option (List Pair × Bindings) :=
    match cands with
    | [] => none
    | t :: more =>
      let skip := go first rest more (t :: passed) tried m
      if t.line.body.type != first.line.body.type || !samePlace ids first.line t.line ||
          !sameTime first.line t.line then skip
      else
        let (ev, av) := c.compared first.line t.line
        let text := Value.arr [(t.line.body.to?.map .str).getD .null, (json av).getD .null]
        if tried.contains text then skip
        else
          let next := go first rest more (t :: passed) (text :: tried) m
          match tryEqual declared ev av m with
          | (true, m') =>
            match pairExactly c ids declared rest (passed.reverse ++ more) m' with
            | some (pairs, m'') => some ((first, t) :: pairs, m'')
            | none => next
          | (false, _) => next
  termination_by (rest.length, cands.length)
  decreasing_by all_goals lex_decreasing

/-- Pairs by type and place, preferring equal values, and reports differences. -/
def pairForReport (ss ts : List Out) (missingAt : Nat) : CompareM (List Pair) := do
  let mut used : List Nat := []
  let mut pairs : List Pair := []
  for s in ss do
    let c ← read
    let st ← get
    let candidates := ts.filter fun t =>
      !used.contains t.index && t.line.body.type == s.line.body.type && samePlace st.ids s.line t.line
    let sameContent (t : Out) : Bool :=
      let (ev, av) := c.compared s.line t.line
      (tryEqual st.declared ev av st.values).1
    let chosen := (candidates.find? fun t => sameContent t && sameTime s.line t.line) <|>
      candidates.find? sameContent <|> candidates.head?
    match chosen with
    | none => missing s missingAt
    | some t =>
      used := t.index :: used
      pairs := pairs ++ [(s, t)]
      matchLine s.line t
  return pairs

/-- Pairs exactly if possible, and pairs for reporting otherwise. -/
def pairLines (ss ts : List Out) (missingAt : Nat) : CompareM (List Pair) := do
  let c ← read
  let st ← get
  match pairExactly c st.ids st.declared ss ts st.values with
  | none => pairForReport ss ts missingAt
  | some (pairs, m) =>
    set { st with values := m }
    for (s, t) in pairs do matchLine s.line t
    return pairs

/-- Whether two lines have the same type, name and value, ignoring `created`. -/
def alike (a b : Line) : Bool :=
  a.body.type == b.body.type && a.body.name? == b.body.name? && plainEqual a.content b.content

/-- Collects paired requests by type, name and input, so that ids can bind in any order among requests of one set. -/
def groupRequests (pairs : List Pair) : CompareM Unit := do
  let groups := pairs.foldl (init := ([] : List (Line × List String × List String))) fun groups (s, t) =>
    match s.line.body.id, t.line.body.id with
    | some si, some ti =>
      match groups.findIdx? (fun (l, _, _) => alike l s.line) with
      | some i => groups.modify i fun (l, ss, ts) => (l, ss ++ [si], ts ++ [ti])
      | none => groups ++ [(s.line, [si], [ti])]
    | _, _ => groups
  modify fun st => { st with ids := groups.foldl (fun ids (_, ss, ts) => ids.group ss ts) st.ids }

/--
Pairs the lines of a window. It pairs the requests and collects them by type, name and input first, so that answer and
unsubscribe lines in the window can name them.
-/
def pairWindow (ss ts : List Out) (missingAt : Nat) : CompareM (List Pair) := do
  let requests ← pairLines (ss.filter (·.line.isRequest)) ts missingAt
  groupRequests requests
  let left := ts.filter fun t => !requests.any (·.2.index == t.index)
  let others ← pairLines (ss.filter (!·.line.isRequest)) left missingAt
  return requests ++ others

/-- The open subscriptions after the subscribe and unsubscribe lines of `lines`. -/
def follow (open_ : List (String × Subscription)) (lines : List Out) : List (String × Subscription) :=
  lines.foldl (init := open_) fun o l =>
    match l.line.body with
    | .subscribe _ (some id) name _ => if (o.lookup id).isSome then o else o ++ [(id, { out := l, name })]
    | .unsubscribe _ _ to => o.filter (·.1 != to)
    | _ => o

/--
The pairs of open snapshot subscriptions with open implementation subscriptions of equal name and input, found by
backtracking, and their bindings.
-/
def pairOpen (st : St) (ss ts : List String) (m : Bindings) : Option (List (String × String) × Bindings) :=
  match ss with
  | [] => if ts.isEmpty then some ([], m) else none
  | first :: rest => go first rest ts [] [] m
termination_by (ss.length, 0)
decreasing_by all_goals lex_decreasing
where
  go (first : String) (rest cands passed : List String) (tried : List (Option Value)) (m : Bindings) :
      Option (List (String × String) × Bindings) :=
    match cands with
    | [] => none
    | id :: more =>
      let skip := go first rest more (id :: passed) tried m
      match st.openSnapshot.lookup first, st.openTrace.lookup id with
      | some s, some t =>
        if s.name != t.name then skip
        else
          let text := json t.out.line.content
          if tried.contains text then skip
          else
            let next := go first rest more (id :: passed) (text :: tried) m
            match tryEqual st.declared s.out.line.content t.out.line.content m with
            | (true, m') =>
              match pairOpen st rest (passed.reverse ++ more) m' with
              | some (pairs, m'') => some ((first, id) :: pairs, m'')
              | none => next
            | (false, _) => next
      | _, _ => skip
  termination_by (rest.length, cands.length)
  decreasing_by all_goals lex_decreasing

/-- Compares the subscriptions still open after the window. Later answers name the pairs. -/
def compareSubscriptions (specOut traceOut : List Out) (missingAt : Nat) : CompareM Unit := do
  modify fun st =>
    { st with openSnapshot := follow st.openSnapshot specOut, openTrace := follow st.openTrace traceOut }
  let st ← get
  let exact := pairOpen st (st.openSnapshot.map (·.1)) (st.openTrace.map (·.1)) st.values
  let mut pairs : List (String × String) := (exact.map (·.1)).getD []
  match exact with
  | some (_, m) => set { st with values := m }
  | none =>
    let mut unpaired := st.openTrace.map (·.1)
    for (id, s) in st.openSnapshot do
      let found := unpaired.find? fun u =>
        match st.openTrace.lookup u with
        | some other => other.name == s.name &&
            (equalContent st.declared s.out.line.content other.out.line.content st.values false).1
        | none => false
      match found with
      | some t =>
        unpaired := unpaired.filter (· != t)
        pairs := pairs ++ [(id, t)]
      | none =>
        let st ← get
        if !st.reportedMissing.contains id then
          set { st with reportedMissing := st.reportedMissing ++ [id] }
          report (.unopenedSubscription missingAt s.name
            (jsonOrNull (s.out.line.content.map (substitute st.values))) s.out.index)
    for id in unpaired do
      let st ← get
      match st.openTrace.lookup id with
      | some t =>
        if !st.reportedUnexpected.contains id then
          set { st with reportedUnexpected := st.reportedUnexpected ++ [id] }
          report (.unexpectedSubscription t.out.index t.name (jsonOrNull t.out.line.content) id)
      | none => pure ()
  let st ← get
  let lineOf (s : String) : Option Line := (st.openSnapshot.lookup s).map (·.out.line)
  let subscriptionIds := pairs.foldl (init := st.subscriptionIds) fun all (s, _) =>
    let known := (all.lookup s).getD []
    let added := pairs.foldl (init := known) fun ids (other, t) =>
      match lineOf s, lineOf other with
      | some a, some b => if alike a b && !ids.contains t then ids ++ [t] else ids
      | _, _ => ids
    setAt all s added
  set { st with subscriptionIds }

/-- Compares the `out` lines between two `in` lines. -/
def compareWindow (allSpecOut allTraceOut : List Out) (missingAt : Nat) : CompareM Unit := do
  let c ← read
  modify fun st => { st with declared := allSpecOut.foldl (fun d s => d ++ s.line.created.getD []) st.declared }
  compareSubscriptions (allSpecOut.filter (·.line.isSubscribing)) (allTraceOut.filter (·.line.isSubscribing)) missingAt
  let specOut := allSpecOut.filter fun s => !s.line.isSubscribing
  let traceOut := allTraceOut.filter fun t => !c.internal t.line && !t.line.isSubscribing
  let pairs ← pairWindow (specOut.filter fun s => !c.internal s.line) traceOut missingAt
  for (s, t) in pairs do
    let before := pairs.find? fun (ps, pt) => pt.index > t.index && (c.follows (s.index - 1)).contains (ps.index - 1)
    if let some (_, bt) := before then
      report (.lineOrder t.index (subject t.line) (subject bt.line))
  for t in traceOut do
    if !pairs.any (·.2.index == t.index) then
      report (.unexpectedLine t.index (subject t.line))

/--
Whether two `in` lines are the same, and the updated state. Request and subscription ids are the same when `ids` can
bind them.
-/
def sameInput (st : St) (s t : Line) : Bool × St :=
  if s.body.type != t.body.type || s.body.name? != t.body.name? || !sameTime s t then (false, st)
  else
    match s.body, t.body with
    | .time .., _ | .restart .., _ => (true, st)
    | .unsubscribe _ _ to, _ => (st.ids.matches (some to) t.body.to?, st)
    | sb, tb =>
      let placed :=
        match sb, tb with
        | .answer _ _ snapshotTo _, .answer _ _ to _ =>
          match st.subscriptionIds.lookup snapshotTo with
          | some ids => ids.contains to
          | none => st.ids.matches (some snapshotTo) (some to)
        | _, _ => st.ids.matches sb.resultOf? tb.resultOf?
      if !placed then (false, st)
      else
        let (same, values) := equalContent st.declared s.content t.content st.values true
        (same, { st with values })

def runWindow (c : Ctx) (st : St) (specOut traceOut : List Out) (missingAt : Nat) : List Mismatch × St :=
  let ((), st) := ((compareWindow specOut traceOut missingAt).run c).run { st with findings := [] }
  (st.findings, st)

def differentInput (st : St) (s t : Out) : Uncomparable :=
  let mismatch : Uncomparable := .differentInput t.index s.index
    (substitute st.values (.ofValue (ToValue.toValue s.line.toTraceLine))).flatten (ToValue.toValue t.line.toTraceLine)
  match s.line.body, t.line.body with
  | .answer _ _ snapshotTo _, .answer _ _ to _ =>
    if st.ids.matches (some snapshotTo) (some to) then mismatch else .answersNoRequest t.index to s.index
  | _, _ => mismatch

mutual

/--
The violations from the windows. Each element holds a snapshot window, an implementation window and the previous
implementation `in` line. The `out` lines are compared before the `in` line, and `malformed` is reported after the last
element.
-/
def compareFrom (c : Ctx) (lineCount : Nat) (malformed : Option Nat) :
    List (Option Window × Option Window × Option Out) → St → Compared
  | [], st => { findings := (malformed.map fun n => .uncomparable (.lineSchema n)).toList, bindings := st.values }
  | (expected, actual, previous) :: rest, st =>
    let (found, st) := runWindow c st ((expected.map (·.before)).getD []) ((actual.map (·.before)).getD [])
      ((previous.map (·.index)).getD 1)
    let later := compareInputs c lineCount malformed (expected.bind (·.input)) (actual.bind (·.input)) rest st
    { later with findings := found.map .mismatch ++ later.findings }
termination_by L => 2 * L.length

/--
The violations from the `in` lines and the rest. The comparison reports and stops when only one side has a line or the
lines differ, and it stops when neither side has one.
-/
def compareInputs (c : Ctx) (lineCount : Nat) (malformed : Option Nat) (expected actual : Option Out)
    (rest : List (Option Window × Option Window × Option Out)) (st : St) : Compared :=
  match expected, actual with
  | none, none => { findings := [], bindings := st.values }
  | none, some t =>
    { findings := [.uncomparable (.unexpectedInput t.index (ToValue.toValue t.line.toTraceLine))], bindings := st.values }
  | some s, none =>
    { findings := [.uncomparable (.missingInput lineCount (ToValue.toValue s.line.toTraceLine) s.index)],
      bindings := st.values }
  | some s, some t =>
    match sameInput st s.line t.line with
    | (false, st) => { findings := [.uncomparable (differentInput st s t)], bindings := st.values }
    | (true, st) =>
      let (sb, tb) := (s.line.body, t.line.body)
      compareFrom c lineCount malformed rest
        { st with ids := ((st.ids.bind sb.to? tb.to?).bind sb.resultOf? tb.resultOf?).bind sb.id tb.id }
termination_by 2 * rest.length + 1

end

/-- The latest of the earlier lines with the id, as an index counted from 0. -/
def earlierWithId (earlier : List Out) (id : String) : Option Nat :=
  (earlier.reverse.find? fun o => o.line.body.id == some id).map (·.index - 1)

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
    (expected[k]?, actual[k]?, if k == 0 then none else (actual[k - 1]?).bind (·.input))
  let ctx : Ctx := {
    requests := (snapshot.filterMap fun l => l.bind fun l => l.body.id.map (·, l)).reverse,
    follows := mustFollow snapshot,
    internal }
  compareFrom ctx lines.length malformed windows {}

end Tazuna.Verify
