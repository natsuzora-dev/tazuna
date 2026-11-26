import Tazuna.Trace.Run

/-! Replaying a trace against the spec. Each in line runs as the spec's input; the out lines up to the next in line
form its window, which must equal the spec's out lines as a multiset. An implementation names its own ids and wire
ids: each binds to the spec's at its first appearance in an out line, and the binding stays one to one. An id an in
line names before any out line showed it is an id from outside the service, called by that name. A window can bind
its new names in several ways, as when two alike events each show a new id; a later window may tell them apart, so
replay tries every way, depth first (`replay_iff`). -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

/-- The implementation's names for the spec's ids and wire ids, one to one. -/
structure Bind where
  ids : List (IdV × String) := []
  wires : List (Nat × String) := []

/-- `xs` with `n` named `s`, unless either already has another partner. -/
def bindPair {α : Type} [BEq α] (xs : List (α × String)) (n : α) (s : String) : Option (List (α × String)) :=
  match xs.lookup n, xs.find? (·.2 == s) with
  | some s', _ => if s' == s then some xs else none
  | none, some _ => none
  | none, none => some (xs ++ [(n, s)])

-- An id the trace has not bound is a named id.
set_option linter.tazuna.silentDefault false in
/-- The id an in line names: the one bound to the name, or else the outside id of that name. -/
def Bind.id? (b : Bind) (s : String) : Option IdV := some (((b.ids.find? (·.2 == s)).map (·.1)).getD (.named s))

/-- The binding with each outside id among `xs` called by its name. -/
def Bind.outside (b : Bind) (xs : List IdV) : Bind :=
  xs.foldl (fun b x => match x with
    | .named s => if b.ids.any (·.1 == x) then b else { b with ids := b.ids ++ [(x, s)] }
    | .fresh _ _ => b) b

def Bind.wire? (b : Bind) (s : String) : Option Nat := (b.wires.find? (·.2 == s)).map (·.1)

/-- Every way to match the values with the wire forms in order. -/
def seqMatch {α : Type} (f : α → Wire → Bind → List Bind) : List α → List Wire → Bind → List Bind
  | [], [], b => [b]
  | x :: xs, w :: ws, b => (f x w b).flatMap (seqMatch f xs ws)
  | _, _, _ => []

/-- `xs` match `ys` pair by pair in order, each pair extending the binding: `b` grows to `b'`. -/
inductive Chain {α β : Type} (f : α → β → Bind → List Bind) : Bind → List α → List β → Bind → Prop
  | nil (b : Bind) : Chain f b [] [] b
  | cons {b b₁ b' : Bind} {x : α} {y : β} {xs : List α} {ys : List β} :
    b₁ ∈ f x y b → Chain f b₁ xs ys b' → Chain f b (x :: xs) (y :: ys) b'

/-- Every way to match the values with the written items in some order: a multiset. Equal items are tried once, so
`k` equal lines cost one try, not `k!`. -/
def bagMatch {α β : Type} [DecidableEq β] (f : α → β → Bind → List Bind) : List α → List β → Bind → List Bind
  | [], [], b => [b]
  | x :: xs, ws, b => ws.eraseDups.flatMap fun w => (f x w b).flatMap (bagMatch f xs (ws.erase w))
  | _, _, _ => []

/-- How many matches of one value with one item `bagMatch` makes, counted from `acc` and given up once past `cap`:
the work of the window before its bindings are built, so a window with too many ways to bind costs no more than
`cap`. -/
def bagCost {α β : Type} [DecidableEq β] (f : α → β → Bind → List Bind) (cap : Nat) :
    List α → List β → Bind → Nat → Nat
  | x :: xs, ws, b, acc => ws.eraseDups.foldl (fun acc w =>
      (f x w b).foldl (fun acc b₁ => if cap < acc then acc else bagCost f cap xs (ws.erase w) b₁ (acc + 1)) acc) acc
  | [], _, _, acc => acc

/-- `bagMatch` finds every binding under which the values match the items in some order. -/
theorem mem_bagMatch {α β : Type} [DecidableEq β] (f : α → β → Bind → List Bind) :
    (xs : List α) → (ws : List β) → (b b' : Bind) →
    (b' ∈ bagMatch f xs ws b ↔ ∃ ws', ws'.Perm ws ∧ Chain f b xs ws' b')
  | [], [], b, b' => by
    simp only [bagMatch, List.mem_singleton]
    refine ⟨fun h => ⟨[], .nil, h ▸ .nil _⟩, fun ⟨ws', hp, hc⟩ => ?_⟩
    cases hc; rfl
  | [], w :: ws, b, b' => by
    simp only [bagMatch, List.not_mem_nil, false_iff]
    rintro ⟨ws', hp, hc⟩
    cases hc; exact absurd hp.symm.length_eq (by simp)
  | x :: xs, ws, b, b' => by
    simp only [bagMatch, List.mem_flatMap, List.mem_eraseDups, mem_bagMatch f xs]
    constructor
    · rintro ⟨w, hw, b₁, h₁, ws'', hp, hc⟩
      exact ⟨w :: ws'', (hp.cons w).trans (List.perm_cons_erase hw).symm, .cons h₁ hc⟩
    · rintro ⟨_, hp, hc⟩
      obtain _ | @⟨_, b₁, _, _, w, _, ws'', h₁, hc⟩ := hc
      have hw : w ∈ ws := hp.mem_iff.1 List.mem_cons_self
      exact ⟨w, hw, _, h₁, ws'', (hp.trans (List.perm_cons_erase hw)).cons_inv, hc⟩

/-- Whether a Bool's or Nil's wire form is the one written. -/
def matchLiteral (expected : Option Wire) (w : Wire) (b : Bind) : List Bind :=
  match expected, w with
  | some (.bool x), .bool y => if x == y then [b] else []
  | some .null, .null => [b]
  | _, _ => []

section
variable (T : List TypeDecl)

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- Every extension of the binding under which the wire form writes the value; a bag's or table's items match in any
order. -/
def matchVal : (t : Ty) → t.den0 → Wire → Bind → List Bind
  | .int, n, .num m, b => if @BEq.beq Int _ n m then [b] else []
  | .str, s, .str s', b => if @BEq.beq String _ s s' then [b] else []
  | .list t, xs, .arr ws, b => seqMatch (matchVal t) xs ws b
  | .bag t, xs, .arr ws, b => bagMatch (matchVal t) (Ty.sortBy T t xs) ws b
  | .tuple ts, x, .arr ws, b => matchs ts x ws b
  | .adt i _ vs, x, w, b =>
    if i = 0 then matchLiteral (encBool vs x) w b else if i = 1 then matchLiteral (encNil vs x) w b
    else match w with
      | .obj kvs => matchAlts ((T[i]?.map (·.variants)).getD []) kvs 0 vs x b
      | _ => []
  | .table k v, x, .arr ws, b => bagMatch (fun (p : k.den0 × v.den0) w b => match w with
      | .arr [wk, wv] => (matchVal k p.1 wk b).flatMap (matchVal v p.2 wv)
      | _ => []) (Ty.sortKeys T k v x.1) ws b
  | .date, d, .str s, b => if renderDate d == s then [b] else []
  | .id, n, .str s, b => ((bindPair b.ids n s).map fun ids => { b with ids }).toList
  | _, _, _, _ => []
def matchs : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Wire → Bind → List Bind
  | [], (), [], b => [b]
  | t :: ts, (x, xs), w :: ws, b => (matchVal t x w b).flatMap (matchs ts xs ws)
  | _, _, _, _ => []
def matchFields (kvs : List (String × Wire)) : (fs : List Ty) → (Ty.semsWith Dsl.base fs).1 → List String → Bind →
    List Bind
  | [], (), [], b => [b]
  | f :: fs, (x, xs), key :: keys, b => match kvs.lookup key with
    | some w => (matchVal f x w b).flatMap (matchFields kvs fs xs keys)
    | none => []
  | _, _, _, _ => []
def matchAlts (decl : List Variant) (kvs : List (String × Wire)) (k : Nat) :
    (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Bind → List Bind
  | [], x, _ => nomatch x
  | fs :: _, .inl x, b => match decl[k]? with
    | some var =>
      let keys := fieldKeys var.fields
      if (kvs.lookup "tag" >>= Wire.str?) == some var.name && kvs.length == keys.length + 1 then
        matchFields kvs fs x keys b
      else []
    | none => []
  | _ :: vs, .inr y, b => matchAlts decl kvs (k + 1) vs y b
end

variable (v : ServiceV)

/-- An out line the spec expects. -/
inductive Expect where
  | answered (to : String) (outcome : Outcome)
  | applied (event : v.event.den0)
  | sent (id : Nat) (external name : String) (input : WireVal)

def matchExpect (now : Int) (e : Expect v) (l : Line) (b : Bind) : List Bind :=
  if l.time != now then [] else
  match e, l with
  | .answered to o, .answered _ to' a => if to != to' then [] else match o, a with
    | .accepted, .accepted => [b]
    | .answered ⟨t, x⟩, .answered w => matchVal T t x w b
    | .rejected ⟨t, x⟩, .rejected w => matchVal T t x w b
    | .invalid rs, .invalid rs' => if rs.mergeSort (· ≤ ·) == rs'.mergeSort (· ≤ ·) then [b] else []
    | _, _ => []
  | .applied ev, .applied _ w => matchVal T v.event ev w b
  | .sent id x n ⟨t, i⟩, .sent _ id' x' n' w =>
    if x != x' || n != n' then [] else match bindPair b.wires id id' with
      | some wires => matchVal T t i w { b with wires }
      | none => []
  | _, _ => []

-- No answer target means no answered line.
set_option linter.tazuna.silentDefault false in
/-- The out lines the spec expects of a step's result. -/
def expects (answerTo : Option String) (r : Result v) : List (Expect v) :=
  (answerTo.map fun to => [Expect.answered to r.outcome]).getD [] ++ r.events.map .applied ++
    r.out.map fun o => .sent o.id o.external o.name o.input

-- Message text: an unbound wire id prints as `?<id>`.
set_option linter.tazuna.silentDefault false in
/-- The expected out lines, written with the binding so far. -/
def Expect.toLine (now : Int) (b : Bind) : Expect v → Option Line
  | .answered to o => match o with
    | .accepted => some (.answered now to .accepted)
    | .answered ⟨t, x⟩ => (enc T (b.ids.lookup ·) t x).map fun w => .answered now to (.answered w)
    | .rejected ⟨t, x⟩ => (enc T (b.ids.lookup ·) t x).map fun w => .answered now to (.rejected w)
    | .invalid rs => some (.answered now to (.invalid rs))
    | .fault _ => none
  | .applied ev => (enc T (b.ids.lookup ·) v.event ev).map (.applied now)
  | .sent id x n ⟨t, i⟩ =>
    (enc T (b.ids.lookup ·) t i).map (.sent now ((b.wires.lookup id).getD s!"?{id}") x n)

/-- What replaying a trace found. -/
inductive Verdict where
  | passed
  /-- The window after the in line at `line` differs: the spec's out lines left unmatched and the trace's. -/
  | differs (line : Nat) (expected actual : List Wire)
  | invalid (line : Nat) (message : String)
  | fault (line : Nat) (f : Fault)
  /-- Verify made `tryCap` tries, reaching the in line at `line`, and no binding read every window. -/
  | limit (line : Nat)

/-- Whether the verdict ends the search: passed, or out of tries. -/
def Verdict.settled : Verdict → Bool
  | .passed | .limit _ => true
  | .differs .. | .invalid .. | .fault .. => false

def Verdict.line : Verdict → Nat
  | .passed => 0
  | .differs n .. | .invalid n _ | .fault n _ | .limit n => n

/-- Of two failed bindings, the one that got further, the first on a tie. -/
def Verdict.further (v v' : Verdict) : Verdict := if v.line < v'.line then v' else v

/-- How many tries verify makes for a trace before it answers Undecided.limit (`readFrom`). A window of `k` alike
lines that each show a new id has `k!` bindings. -/
def tryCap : Nat := 100000

/-- An answer to a request, read from its wire form: a command's output or rejection, a query's output. -/
def decAnswer (b : Bind) (o : Ty) : (rj : Option Ty) → Except Wire Wire → Option (answerTy o rj).den0
  | some _, .ok w => (dec T b.id? o w).map fun x => .inl (x, ())
  | some j, .error w => (dec T b.id? j w).map fun x => .inr (.inl (x, ()))
  | none, .ok w => dec T b.id? o w
  | none, .error _ => none

/-- The input an in line writes, read with the binding so far, the id its answer names, and the ids it holds. -/
def readIn (s : State v) (b : Bind) : Line → Except String (Input v × Option String × List IdV)
  -- A clock line before the state's time is the step's own Invalid, as the semantics reads it, not a misread line.
  | .clock t => .ok (.clock t, none, [])
  | .request t id name c i => do
    if t != s.now then throw s!"the request is at {t}, but a clock line brought time only to {s.now}"
    let caller ← (dec T b.id? v.caller c).elim (.error "the caller does not read as the service's caller type") .ok
    match finIdx v.commands (·.name == name), finIdx v.queries (·.name == name) with
    | some k, _ => match dec T b.id? (v.commands.get k).input i with
      | some x => .ok (.command k caller x, some id, idsOf T v.caller caller ++ idsOf T _ x)
      | none => .error s!"the input does not read as {name}'s input type"
    | none, some k => match dec T b.id? (v.queries.get k).input i with
      | some x => .ok (.query k caller x, some id, idsOf T v.caller caller ++ idsOf T _ x)
      | none => .error s!"the input does not read as {name}'s input type"
    | none, none => .error s!"{v.name} has no request {name}"
  | .answer t to res => do
    if t != s.now then throw s!"the answer is at {t}, but a clock line brought time only to {s.now}"
    let some id := b.wire? to | throw s!"the answer names {to}, which no request the service sent had"
    match s.pending.find? (·.id == id) with
    -- The step itself faults on an answer to no pending request.
    | none => .ok (.answer id ⟨Ty.nil, .inl ()⟩, none, [])
    | some p =>
      match decAnswer T b p.request.output p.request.rejection res with
      | some x => .ok (.answer id ⟨_, x⟩, none, idsOf T _ x)
      | none => .error "the answer does not read as an answer to the request: an output, or a command's rejection"
  | .event t src name w => do
    if t != s.now then throw s!"the event is at {t}, but a clock line brought time only to {s.now}"
    let some k := finIdx v.subscribes fun sub => sub.source == src && sub.name == name
      | throw s!"{v.name} subscribes to no event {src}.{name}"
    match dec T b.id? (v.subscribes.get k).event w with
    | some x => .ok (.event k x, none, idsOf T _ x)
    | none => .error s!"the event does not read as {src}.{name}'s type"
  | _ => .error "an out line where an in line belongs"

/-- The window an in line opens: the out lines up to the next in line. -/
def window (more : List (Nat × Line)) : List Line := (more.takeWhile (!·.2.isIn)).map (·.2)

/-- The lines after the window. -/
def afterWindow (more : List (Nat × Line)) : List (Nat × Line) := more.dropWhile (!·.2.isIn)

/-- What the spec steps to from `s` on the in line `l`, read under `b`: the result, the binding with the line's
outside ids named, and the out lines it expects; or how the line failed. -/
def stepIn (s : State v) (b : Bind) (n : Nat) (l : Line) : Except Verdict (Result v × Bind × List (Expect v)) :=
  match readIn T v s b l with
  | .error m => .error (.invalid n m)
  | .ok (input, answerTo, ids) =>
    let r := step T v s input
    match r.outcome with
    | .fault f => .error (.fault n f)
    | _ => .ok (r, b.outside ids, expects v answerTo r)

/-- The trace reads as the spec from `s` under `b`: each in line reads as an input under the binding so far, its step
does not fault, and its window's out lines, in some order, are the spec's out lines, each written under a binding that
extends the one so far one to one. The bindings grow line by line into one bijection of the spec's ids and wire ids
with the trace's names. -/
inductive Reads : State v → Bind → List (Nat × Line) → Prop
  | nil (s : State v) (b : Bind) : Reads s b []
  | cons {s : State v} {b b' : Bind} {n : Nat} {l : Line} {more : List (Nat × Line)} {r : Result v}
    {b₀ : Bind} {es : List (Expect v)} {ls : List Line} :
    stepIn T v s b n l = .ok (r, b₀, es) → ls.Perm (window more) → Chain (matchExpect T v r.state.now) b₀ es ls b' →
    Reads r.state b' (afterWindow more) → Reads s b ((n, l) :: more)

theorem afterWindow_length (more : List (Nat × Line)) : (afterWindow more).length ≤ more.length :=
  (List.dropWhile_suffix _).length_le

mutual
/-- Reads the lines from `s` under `b`, trying every binding of each window depth first, with `fuel` tries left: the
verdict and the fuel left. A try matches one line on the way to a window's bindings, or reads the rest under one of
them. -/
def readFrom (fuel : Nat) (s : State v) (b : Bind) : List (Nat × Line) → Verdict × Nat
  | [] => (.passed, fuel)
  | (n, l) :: more =>
    match stepIn T v s b n l with
    | .error e => (e, fuel)
    | .ok (r, b₀, es) =>
      let cost := bagCost (matchExpect T v r.state.now) fuel es (window more) b₀ 0
      if fuel < cost then (.limit n, 0) else
      match bagMatch (matchExpect T v r.state.now) es (window more) b₀ with
      | [] => (.differs n ((es.filterMap (·.toLine T v r.state.now b₀)).map Line.toWire)
          ((window more).map Line.toWire), fuel - cost)
      | c :: cs => readEach (fuel - cost) n r.state (afterWindow more) c cs
termination_by ls => (ls.length, 0)
decreasing_by have := afterWindow_length more; simp only [List.length_cons]; exact Prod.Lex.left _ _ (by omega)
/-- Reads `rest` from `s` under each of the bindings `c :: cs` in turn until one passes or the fuel runs out; when all
fail, the failure that got furthest. -/
def readEach (fuel n : Nat) (s : State v) (rest : List (Nat × Line)) (c : Bind) (cs : List Bind) : Verdict × Nat :=
  if fuel = 0 then (.limit n, 0) else
  let r₁ := readFrom (fuel - 1) s c rest
  if r₁.1.settled then r₁ else
  match cs with
  | [] => r₁
  | c' :: cs' =>
    let r₂ := readEach r₁.2 n s rest c' cs'
    if r₂.1.settled then r₂ else (r₁.1.further r₂.1, r₂.2)
termination_by (rest.length, cs.length + 1)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.right _ (by simp)
end

/-- Replays the lines after the header, each with its line number. -/
def replay (lines : List (Nat × Line)) : Verdict := (readFrom T v tryCap (State.init v) {} lines).1

theorem further_ne_passed {v₁ v₂ : Verdict} (h₁ : v₁ ≠ .passed) (h₂ : v₂ ≠ .passed) : v₁.further v₂ ≠ .passed := by
  unfold Verdict.further; split <;> assumption

theorem ne_passed_of_not_settled {x : Verdict} (h : x.settled = false) : x ≠ .passed := by
  rintro rfl; cases h

theorem stepIn_error {s : State v} {b : Bind} {n : Nat} {l : Line} {e : Verdict}
    (h : stepIn T v s b n l = .error e) : e.settled = false := by
  unfold stepIn at h
  split at h
  · cases h; rfl
  · dsimp only at h
    split at h
    · cases h; rfl
    · cases h

theorem readEach_sound {n : Nat} {s : State v} {rest : List (Nat × Line)}
    (ih : ∀ fuel b, (readFrom T v fuel s b rest).1 = .passed → Reads T v s b rest) :
    (cs : List Bind) → (fuel : Nat) → (c : Bind) → (readEach T v fuel n s rest c cs).1 = .passed →
      ∃ b ∈ c :: cs, Reads T v s b rest
  | cs, fuel, c, h => by
    unfold readEach at h
    split at h
    · cases h
    · dsimp only at h
      split at h
      · exact ⟨c, List.mem_cons_self, ih _ _ h⟩
      · rename_i hs
        match cs, h with
        | [], h => exact absurd h (ne_passed_of_not_settled (by simpa using hs))
        | c' :: cs', h =>
          dsimp only at h
          split at h
          · obtain ⟨b, hb, hr'⟩ := readEach_sound ih cs' _ c' h
            exact ⟨b, List.mem_cons_of_mem _ hb, hr'⟩
          · rename_i hs₂
            exact absurd h (further_ne_passed (ne_passed_of_not_settled (by simpa using hs))
              (ne_passed_of_not_settled (by simpa using hs₂)))

/-- A passed verdict reads the trace as the spec. -/
theorem readFrom_sound : (lines : List (Nat × Line)) → (fuel : Nat) → (s : State v) → (b : Bind) →
    (readFrom T v fuel s b lines).1 = .passed → Reads T v s b lines
  | [], _, s, b, _ => .nil s b
  | (n, l) :: more, fuel, s, b, h => by
    unfold readFrom at h
    split at h
    · rename_i e he
      exact absurd (stepIn_error T v he) (by simp only at h; subst h; simp [Verdict.settled])
    · rename_i r b₀ es hstep
      dsimp only at h
      split at h
      · cases h
      split at h
      · cases h
      · rename_i c cs hcs
        have ih : ∀ fuel b, (readFrom T v fuel r.state b (afterWindow more)).1 = .passed →
            Reads T v r.state b (afterWindow more) := fun fuel b h =>
          have := afterWindow_length more
          readFrom_sound (afterWindow more) fuel r.state b h
        obtain ⟨b', hb', hreads⟩ := readEach_sound T v ih cs _ c h
        rw [← hcs, mem_bagMatch] at hb'
        obtain ⟨ls, hp, hc⟩ := hb'
        exact .cons hstep hp hc hreads
termination_by lines => lines.length

theorem readEach_complete {n : Nat} {s : State v} {rest : List (Nat × Line)} {b : Bind}
    (ih : ∀ fuel, (readFrom T v fuel s b rest).1.settled = true) :
    (cs : List Bind) → (fuel : Nat) → (c : Bind) → b ∈ c :: cs → (readEach T v fuel n s rest c cs).1.settled = true
  | cs, fuel, c, hb => by
    unfold readEach
    split
    · rfl
    · dsimp only
      split
      · assumption
      · rename_i hs
        have hc : c ≠ b := by rintro rfl; exact hs (ih _)
        match cs, hb with
        | [], hb => exact absurd (List.mem_singleton.1 hb).symm hc
        | c' :: cs', hb =>
          have hb' : b ∈ c' :: cs' := (List.mem_cons.1 hb).resolve_left (Ne.symm hc)
          dsimp only
          have := readEach_complete (n := n) ih cs' (readFrom T v (fuel - 1) s c rest).2 c' hb'
          simp [this]

/-- A trace that reads as the spec is passed, unless the tries run out first. -/
theorem readFrom_complete {s : State v} {b : Bind} {lines : List (Nat × Line)} (h : Reads T v s b lines) :
    ∀ fuel, (readFrom T v fuel s b lines).1.settled = true := by
  induction h with
  | nil => intro; simp [readFrom, Verdict.settled]
  | @cons s b b' n l more r b₀ es ls hstep hp hc _ ih =>
    intro fuel
    unfold readFrom
    rw [hstep]
    dsimp only
    have hm : b' ∈ bagMatch (matchExpect T v r.state.now) es (window more) b₀ :=
      (mem_bagMatch _ _ _ _ _).2 ⟨ls, hp, hc⟩
    split
    · rfl
    split
    · rename_i hnil; rw [hnil] at hm; cases hm
    · rename_i c cs hcs; rw [hcs] at hm; exact readEach_complete T v ih cs _ c hm

/-- Verify's oracle comparison: unless it runs out of tries (`tryCap`), it reads a trace as passed exactly
when some bijection of the spec's ids and wire ids with the trace's names, grown window by window, reads every window
as the spec's out lines in some order. -/
theorem replay_iff (lines : List (Nat × Line)) (h : ∀ k, replay T v lines ≠ .limit k) :
    replay T v lines = .passed ↔ Reads T v (State.init v) {} lines := by
  refine ⟨readFrom_sound T v lines _ _ _, fun hr => ?_⟩
  have := readFrom_complete T v hr tryCap
  unfold replay at h ⊢
  revert this h
  cases (readFrom T v tryCap (State.init v) {} lines).1 <;> simp [Verdict.settled]

end

end Tazuna.Trace
