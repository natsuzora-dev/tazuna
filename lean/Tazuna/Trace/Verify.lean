import Tazuna.Trace.LineDec

/-! Replaying a trace against the spec. Each in line runs as the spec's input; the out lines up to the next in line
form its window, which must be the spec's out lines in some order. An implementation names its own ids and wire ids:
one binding, one to one, names the spec's ids and wire ids by the trace's names, each from its first appearance in an
out line; an id an in line names before any out line showed it is an id from outside the service, called by that name
(`Reads`). Verify does not choose a binding for alike ids a window shows: it keeps them in blocks, each a set of keys
that are a set of names in some one-to-one way (`Cands`), narrows the blocks as later lines tell the ids apart, and
decides a key by trying each name of its block only where a line needs it: an in line that names one, or a window whose
items tie undecided keys. `replay_iff`: unless it runs out of tries, verify passes a trace exactly when some binding
reads it. -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

/-- The implementation's names for the spec's ids and wire ids. -/
structure Bind where
  ids : List (IdV × String) := []
  wires : List (Nat × String) := []

/-- The id bound to the name, if one is. -/
def Bind.idOf (b : Bind) (s : String) : Option IdV := (b.ids.find? (·.2 == s)).map (·.1)

-- An id the trace has not bound is a named id.
set_option linter.tazuna.silentDefault false in
/-- The id an in line names: the one bound to the name, or else the outside id of that name. -/
def Bind.id? (b : Bind) (s : String) : Option IdV := some ((b.idOf s).getD (.named s))

def Bind.wire? (b : Bind) (s : String) : Option Nat := (b.wires.find? (·.2 == s)).map (·.1)

/-- The binding with each outside id among `xs` called by its name, unless the id or the name is bound already, as the
trace writer names ids (`Names.bindOne`). -/
def Bind.outside (b : Bind) (xs : List IdV) : Bind :=
  xs.foldl (fun b x => match x with
    | .named s => if b.ids.any (·.1 == x) || b.ids.any (·.2 == s) then b else { b with ids := b.ids ++ [(x, s)] }
    | .fresh _ _ => b) b

-- A key the binding leaves unbound has no name; `Reads` binds every key a window shows.
set_option linter.tazuna.silentDefault false in
/-- The name the binding gives a key. -/
def Bind.name (b : Bind) : Key → Name
  | .id x => .id ((b.ids.lookup x).getD "")
  | .wire n => .wire ((b.wires.lookup n).getD "")

/-- No id or wire id has two names, and no name two ids or two wire ids. -/
structure Bind.OneToOne (b : Bind) : Prop where
  ids : ∀ x s s', (x, s) ∈ b.ids → (x, s') ∈ b.ids → s = s'
  idNames : ∀ x x' s, (x, s) ∈ b.ids → (x', s) ∈ b.ids → x = x'
  wires : ∀ n s s', (n, s) ∈ b.wires → (n, s') ∈ b.wires → s = s'
  wireNames : ∀ n n' s, (n, s) ∈ b.wires → (n', s) ∈ b.wires → n = n'

/-- Whether the binding names the key. -/
def Bind.Binds (b : Bind) : Key → Prop
  | .id x => ∃ s, (x, s) ∈ b.ids
  | .wire n => ∃ s, (n, s) ∈ b.wires

/-- `b'` is `b` grown one to one by names for keys among `ks`, and names every key of `ks`. -/
structure Grows (b : Bind) (ks : List Key) (b' : Bind) : Prop where
  ids : ∀ p ∈ b.ids, p ∈ b'.ids
  wires : ∀ p ∈ b.wires, p ∈ b'.wires
  newIds : ∀ p ∈ b'.ids, p ∈ b.ids ∨ Key.id p.1 ∈ ks
  newWires : ∀ p ∈ b'.wires, p ∈ b.wires ∨ Key.wire p.1 ∈ ks
  covers : ∀ k ∈ ks, b'.Binds k
  one : b'.OneToOne

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

/-- How many tries verify makes for a trace before it answers Undecided.limit (`readFrom`). A try decides a key of an
undecided block one way, where a line needs it decided. -/
def tryCap : Nat := 100000

variable (T : List TypeDecl) (v : ServiceV)

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

/-- What the spec steps to from `s` on the in line `l`, read under `b`: the result, the ids the line holds, and the out
lines the spec expects; or how the line failed. -/
def stepIn (s : State v) (b : Bind) (n : Nat) (l : Line) : Except Verdict (Result v × List IdV × List (Expect v)) :=
  match readIn T v s b l with
  | .error m => .error (.invalid n m)
  | .ok (input, answerTo, ids) =>
    let r := step T v s input
    match r.outcome with
    | .fault f => .error (.fault n f)
    | _ => .ok (r, ids, expects v answerTo r)

-- An expected line with no tree has no keys; no trace line writes it.
set_option linter.tazuna.silentDefault false in
/-- The keys an expected line shows. -/
def Expect.keys (now : Int) (e : Expect v) : List Key := ((e.tree T v now).map Tree.leaves).getD []

/-- The wire form `w` writes the value `x` of type `t` under the binding: decoded with the binding's names for ids, it
is `x` up to the order of its bags and tables. -/
def Bind.Writes (b : Bind) (t : Ty) (x : t.den0) (w : Wire) : Prop := ∃ y, dec T b.idOf t w = some y ∧ Ty.Same t x y

-- A trace line of another kind than the expected line writes nothing of it.
set_option linter.tazuna.silentDefault false in
/-- The trace line `l` writes the expected line `e` under the binding `b`: a line of `e`'s kind at `e`'s time naming
what `e` names, whose value `b` reads as `e`'s, whose rules are `e`'s in some order, and whose request id `b` names
as `e`'s. -/
def LineW (b : Bind) (now : Int) : Expect v → Line → Prop
  | .answered to o, .answered t to' a => t = now ∧ to' = to ∧ match o, a with
    | .accepted, .accepted => True
    | .answered ⟨ty, x⟩, .answered w | .rejected ⟨ty, x⟩, .rejected w => b.Writes T ty x w
    | .invalid rs, .invalid rs' => rs.Perm rs'
    | _, _ => False
  | .applied ev, .applied t w => t = now ∧ b.Writes T v.event ev w
  | .sent id x n ⟨ty, i⟩, .sent t wn x' n' w => t = now ∧ x' = x ∧ n' = n ∧ b.wire? wn = some id ∧ b.Writes T ty i w
  | _, _ => False

/-- The trace reads as the spec from `s` under `b`: each in line reads as an input under the binding so far, with the
outside ids it names bound to their names, and its step does not fault; the binding grows one to one by the keys the
spec's out lines show; and the window's out lines, in some order, write the spec's out lines under it. -/
inductive Reads : State v → Bind → List (Nat × Line) → Prop
  | nil (s : State v) (b : Bind) : Reads s b []
  | cons {s : State v} {b b' : Bind} {n : Nat} {l : Line} {more : List (Nat × Line)} {r : Result v}
    {ids : List IdV} {es : List (Expect v)} :
    stepIn T v s b n l = .ok (r, ids, es) → Grows (b.outside ids) (es.flatMap (Expect.keys T v r.state.now)) b' →
    Multi (LineW T v b' r.state.now) es (window more) → Reads r.state b' (afterWindow more) →
    Reads s b ((n, l) :: more)

mutual
/-- The strings a wire form holds as values: every name it can read an id by. -/
def Wire.strs : Wire → List String
  | .str s => [s]
  | .arr ws => Wire.strss ws
  | .obj kvs => Wire.strsKvs kvs
  | .null | .bool _ | .num _ => []
def Wire.strss : List Wire → List String
  | [] => []
  | w :: ws => w.strs ++ Wire.strss ws
def Wire.strsKvs : List (String × Wire) → List String
  | [] => []
  | (_, w) :: kvs => w.strs ++ Wire.strsKvs kvs
end

/-- The names an in line can read ids and a wire id by: every string of its values, and an answer's `to`. -/
def Line.inNames : Line → List Name
  | .request _ _ _ c i => (c.strs ++ i.strs).map .id
  | .answer _ to (.ok w) | .answer _ to (.error w) => .wire to :: w.strs.map .id
  | .event _ _ _ w => w.strs.map .id
  | _ => []

namespace Cands

/-- The bindings the blocks decide, as verify reads an in line with them. -/
def bind (C : Cands) : Bind where
  ids := C.blocks.filterMap fun
    | ([.id x], [.id s]) => some (x, s)
    | _ => none
  wires := C.blocks.filterMap fun
    | ([.wire n], [.wire s]) => some (n, s)
    | _ => none

/-- The blocks with each outside id among `xs` decided as its name, unless the id or the name lies in a block, as
`Bind.outside` binds them. -/
def outside (C : Cands) (xs : List IdV) : Cands :=
  xs.foldl (fun C x => match x with
    | .named s => if C.keys.contains (.id x) || C.names.contains (.id s) then C else ⟨C.blocks ++ [([.id x], [.id s])]⟩
    | .fresh _ _ => C) C

/-- The first of the names that lies in an undecided block, with the block. -/
def undecidedIn (C : Cands) (ns : List Name) : Option (Name × Block) :=
  ns.findSome? fun s => (C.blockOfName s).bind fun b => if 2 ≤ b.1.length then some (s, b) else none

end Cands

theorem lookup_strs {kvs : List (String × Wire)} {key : String} {w : Wire} (h : kvs.lookup key = some w) :
    ∀ s ∈ w.strs, s ∈ Wire.strsKvs kvs := by
  induction kvs with
  | nil => simp at h
  | cons kv kvs ih =>
    obtain ⟨k, w'⟩ := kv
    intro s hs
    simp only [List.lookup_cons] at h
    split at h
    · cases h; simp [Wire.strsKvs, hs]
    · simp [Wire.strsKvs, ih h s hs]

section
variable (T : List TypeDecl) {f g : String → Option IdV}

theorem mapM_congr_strs {β : Type} {F G : Wire → Option β} : (ws : List Wire) →
    (∀ w ∈ ws, (∀ s ∈ w.strs, f s = g s) → F w = G w) → (∀ s ∈ Wire.strss ws, f s = g s) → ws.mapM F = ws.mapM G
  | [], _, _ => rfl
  | w :: ws, hF, h => by
    simp only [List.mapM_cons]
    rw [hF w (by simp) fun s hs => h s (by simp [Wire.strss, hs]),
      mapM_congr_strs ws (fun w' hw' => hF w' (by simp [hw'])) fun s hs => h s (by simp [Wire.strss, hs])]

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- Reading a value looks ids up only by the strings its wire form holds. -/
theorem dec_congr : (t : Ty) → (w : Wire) → (∀ s ∈ w.strs, f s = g s) → dec T f t w = dec T g t w
  | .int, .num _, _ | .str, .str _, _ | .date, .str _, _ => rfl
  | .list t, .arr ws, h => by
    show ws.mapM (dec T f t) = ws.mapM (dec T g t)
    exact mapM_congr_strs ws (fun w _ hw => dec_congr t w hw) (by simpa [Wire.strs] using h)
  | .bag t, .arr ws, h => by
    show ws.mapM (dec T f t) = ws.mapM (dec T g t)
    exact mapM_congr_strs ws (fun w _ hw => dec_congr t w hw) (by simpa [Wire.strs] using h)
  | .tuple ts, .arr ws, h => by
    show decs T f ts ws = decs T g ts ws; exact decs_congr ts ws (by simpa [Wire.strs] using h)
  | .adt 0 _ vs, w, _ => rfl
  | .adt 1 _ vs, w, _ => rfl
  | .adt (i + 2) _ vs, .obj kvs, h => by
    show ((do
      let decl : List Variant := (T[i + 2]?.map (·.variants)).getD []
      let .str tag ← kvs.lookup "tag" | none
      let k ← decl.findIdx? (fun (var : Variant) => var.name == tag)
      decAlts T f decl kvs k 0 vs) : Option (Ty.semAltsWith Dsl.base vs).1) = (do
      let decl : List Variant := (T[i + 2]?.map (·.variants)).getD []
      let .str tag ← kvs.lookup "tag" | none
      let k ← decl.findIdx? (fun (var : Variant) => var.name == tag)
      decAlts T g decl kvs k 0 vs)
    simp only [Wire.strs] at h
    simp only [decAlts_congr _ kvs _ 0 vs h]
  | .adt (_ + 2) _ _, .null, _ | .adt (_ + 2) _ _, .bool _, _ | .adt (_ + 2) _ _, .num _, _
  | .adt (_ + 2) _ _, .str _, _ | .adt (_ + 2) _ _, .arr _, _ => rfl
  | .table k v, .arr ws, h => by
    have e : ∀ f' : String → Option IdV, dec T f' (.table k v) (.arr ws) = (do
        let pairs ← ws.mapM fun (w : Wire) => match w with
          | .arr [a, b] => do pure (← dec T f' k a, ← dec T f' v b)
          | _ => none
        if h : KeysUnique (Ty.semWith Dsl.base k).2 pairs then some ⟨pairs, h⟩ else none) := fun _ => rfl
    rw [e f, e g]
    simp only [Wire.strs] at h
    rw [mapM_congr_strs ws (fun w _ hw => ?_) h]
    match w with
    | .arr [a, b] =>
      simp only
      rw [dec_congr k a fun s hs => hw s (by simp [Wire.strs, Wire.strss, hs]),
        dec_congr v b fun s hs => hw s (by simp [Wire.strs, Wire.strss, hs])]
    | .null | .bool _ | .num _ | .str _ | .obj _ | .arr [] | .arr [_] | .arr (_ :: _ :: _ :: _) => rfl
  | .id, .str s, h => h s (by simp [Wire.strs])
  | .int, .null, _ | .int, .bool _, _ | .int, .str _, _ | .int, .arr _, _ | .int, .obj _, _ => rfl
  | .str, .null, _ | .str, .bool _, _ | .str, .num _, _ | .str, .arr _, _ | .str, .obj _, _ => rfl
  | .date, .null, _ | .date, .bool _, _ | .date, .num _, _ | .date, .arr _, _ | .date, .obj _, _ => rfl
  | .id, .null, _ | .id, .bool _, _ | .id, .num _, _ | .id, .arr _, _ | .id, .obj _, _ => rfl
  | .list _, .null, _ | .list _, .bool _, _ | .list _, .num _, _ | .list _, .str _, _ | .list _, .obj _, _ => rfl
  | .bag _, .null, _ | .bag _, .bool _, _ | .bag _, .num _, _ | .bag _, .str _, _ | .bag _, .obj _, _ => rfl
  | .tuple _, .null, _ | .tuple _, .bool _, _ | .tuple _, .num _, _ | .tuple _, .str _, _ | .tuple _, .obj _, _ => rfl
  | .table .., .null, _ | .table .., .bool _, _ | .table .., .num _, _ | .table .., .str _, _
  | .table .., .obj _, _ => rfl
  | .fn .., _, _ | .param _, _, _ | .dsl .., _, _ => rfl
theorem decs_congr : (ts : List Ty) → (ws : List Wire) → (∀ s ∈ Wire.strss ws, f s = g s) →
    decs T f ts ws = decs T g ts ws
  | [], [], _ => rfl
  | t :: ts, w :: ws, h => by
    simp only [decs]
    rw [dec_congr t w fun s hs => h s (by simp [Wire.strss, hs]),
      decs_congr ts ws fun s hs => h s (by simp [Wire.strss, hs])]
  | [], _ :: _, _ | _ :: _, [], _ => rfl
theorem decFields_congr (kvs : List (String × Wire)) (h : ∀ s ∈ Wire.strsKvs kvs, f s = g s) :
    (fs : List Ty) → (keys : List String) → decFields T f kvs fs keys = decFields T g kvs fs keys
  | [], [] => rfl
  | f' :: fs, key :: keys => by
    show ((do pure (← dec T f f' (← kvs.lookup key), ← decFields T f kvs fs keys)) :
      Option (Ty.semsWith Dsl.base (f' :: fs)).1) = (do pure (← dec T g f' (← kvs.lookup key), ← decFields T g kvs fs keys))
    cases hk : kvs.lookup key with
    | none => rfl
    | some w =>
      simp only [Option.bind_eq_bind, Option.bind_some, dec_congr f' w (fun s hs => h s (lookup_strs hk s hs)),
        decFields_congr kvs h fs keys]
  | [], _ :: _ | _ :: _, [] => rfl
theorem decAlts_congr (decl : List Variant) (kvs : List (String × Wire)) (k : Nat) :
    (j : Nat) → (vs : List (List Ty)) → (∀ s ∈ Wire.strsKvs kvs, f s = g s) →
    decAlts T f decl kvs k j vs = decAlts T g decl kvs k j vs
  | _, [], _ => rfl
  | j, fs :: vs, h => by
    simp only [decAlts]
    split
    · simp only [decFields_congr kvs h fs]
    · rw [decAlts_congr decl kvs k (j + 1) vs h]
end

end

theorem further_ne_passed {v₁ v₂ : Verdict} (h₁ : v₁ ≠ .passed) (h₂ : v₂ ≠ .passed) : v₁.further v₂ ≠ .passed := by
  unfold Verdict.further; split <;> assumption

theorem ne_passed_of_not_settled {x : Verdict} (h : x.settled = false) : x ≠ .passed := by
  rintro rfl; cases h

/-- Tries each alternative in turn with the fuel left, each try costing one, until one passes or the fuel runs out;
when all fail, the failure that got furthest, or `empty` if there is none. -/
def tryAll {α : Type} (n : Nat) (empty : Verdict) (fuel : Nat) (f : Nat → α → Verdict × Nat) : List α → Verdict × Nat
  | [] => (empty, fuel)
  | a :: as =>
    if fuel = 0 then (.limit n, 0) else
    let r₁ := f (fuel - 1) a
    if r₁.1.settled then r₁ else
    match as with
    | [] => r₁
    | _ :: _ =>
      let r₂ := tryAll n empty r₁.2 f as
      if r₂.1.settled then r₂ else (r₁.1.further r₂.1, r₂.2)

/-- Every way to pick one item of each list, in order. -/
def product {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (product xss).map (x :: ·)

/-- The position of `a` in the list, where it is in it. -/
def indexIn {α : Type} [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | x :: l => if x = a then 0 else indexIn a l + 1

theorem get_indexIn {α : Type} [DecidableEq α] {a : α} : {l : List α} → a ∈ l → l[indexIn a l]? = some a
  | [], h => absurd h (by simp)
  | x :: l, h => by
    unfold indexIn
    split
    · rename_i hx; subst hx; simp
    · rename_i hx
      simpa using get_indexIn ((List.mem_cons.1 h).resolve_left (Ne.symm hx))

/-- A window's line as verify compares it: its tree after the index of its value's type among the window's types
`tys`, so a trace line read with one type meets only expected lines of that type. -/
def winTree {α : Type} (tys : List (Option Ty)) (ty : Option Ty) (t : Tree α) : Tree α :=
  .seq [.atom (.int (indexIn ty tys)), t]

/-- The types of the expected lines' values, each once. -/
def Expect.tys (es : List (Expect v)) : List (Option Ty) := Cands.nub (es.map (Expect.ty v))

/-- The expected lines' trees, if every one has one. -/
def expTrees (now : Int) (es : List (Expect v)) : Option (List (Tree Key)) :=
  es.mapM fun e => (e.tree T v now).map (winTree (Expect.tys v es) (Expect.ty v e))

/-- Every reading of the window's out lines: each line read with a type an expected line of its head has. -/
def readings (now : Int) (es : List (Expect v)) (ls : List Line) : List (List (Tree Name)) :=
  product (ls.map fun (l : Line) =>
    (Cands.nub ((es.filter fun (e : Expect v) => some (e.head v now) == l.head).map (Expect.ty v))).filterMap fun ty =>
      (lineTree T ty l).map (winTree (Expect.tys v es) ty))

theorem afterWindow_length (more : List (Nat × Line)) : (afterWindow more).length ≤ more.length :=
  (List.dropWhile_suffix _).length_le

theorem undecidedIn_some {C : Cands} {ns : List Name} {s : Name} {b : Block} (h : C.undecidedIn ns = some (s, b)) :
    s ∈ ns ∧ b ∈ C.blocks ∧ s ∈ b.2 ∧ 2 ≤ b.1.length := by
  obtain ⟨s', hs', h'⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.bind_eq_some_iff] at h'
  obtain ⟨b', hb', h'⟩ := h'
  split at h'
  · cases h'
    exact ⟨hs', List.mem_of_find?_eq_some hb', by simpa using List.find?_some hb', by assumption⟩
  · cases h'

theorem readIn_congr (T : List TypeDecl) (v : ServiceV) {s : State v} {b b' : Bind} {l : Line}
    (hid : ∀ x, Name.id x ∈ l.inNames → b.id? x = b'.id? x)
    (hw : ∀ to, Name.wire to ∈ l.inNames → b.wire? to = b'.wire? to) : readIn T v s b l = readIn T v s b' l := by
  have dc : ∀ {w : Wire}, (∀ x ∈ w.strs, Name.id x ∈ l.inNames) → ∀ t, dec T b.id? t w = dec T b'.id? t w :=
    fun hs t => dec_congr T t _ fun x hx => hid x (hs x hx)
  cases l with
  | clock => rfl
  | request t id name c i =>
    have h1 := dc (w := c) (fun x hx => by simp [Line.inNames, hx])
    have h2 := dc (w := i) (fun x hx => by simp [Line.inNames, hx])
    simp only [readIn, h1, h2]
  | answer t to res =>
    have hto := hw to (by cases res <;> simp [Line.inNames])
    have hda : ∀ o rj, decAnswer T b o rj res = decAnswer T b' o rj res := by
      intro o rj
      cases res with
      | ok w =>
        have := dc (w := w) (fun x hx => by simp [Line.inNames, hx])
        cases rj
        · exact this o
        · simp only [decAnswer, this]
      | error w =>
        have := dc (w := w) (fun x hx => by simp [Line.inNames, hx])
        cases rj <;> simp only [decAnswer, this]
    simp only [readIn, hto, hda]
  | event t src name w =>
    have := dc (w := w) (fun x hx => by simp [Line.inNames, hx])
    simp only [readIn, this]
  | answered | applied | sent => rfl

theorem tryAll_sound {α : Type} {n : Nat} {empty : Verdict} {f : Nat → α → Verdict × Nat} (he : empty ≠ .passed) :
    (as : List α) → (fuel : Nat) → (tryAll n empty fuel f as).1 = .passed → ∃ a ∈ as, ∃ fuel', (f fuel' a).1 = .passed
  | [], _, h => absurd h he
  | a :: as, fuel, h => by
    unfold tryAll at h
    split at h
    · cases h
    · dsimp only at h
      split at h
      · exact ⟨a, List.mem_cons_self, _, h⟩
      · rename_i hs
        match as, h with
        | [], h => exact absurd h (ne_passed_of_not_settled (by simpa using hs))
        | a' :: as', h =>
          dsimp only at h
          split at h
          · obtain ⟨a'', ha'', fuel', h'⟩ := tryAll_sound he (a' :: as') _ h
            exact ⟨a'', List.mem_cons_of_mem _ ha'', fuel', h'⟩
          · rename_i hs₂
            exact absurd h (further_ne_passed (ne_passed_of_not_settled (by simpa using hs))
              (ne_passed_of_not_settled (by simpa using hs₂)))

theorem tryAll_complete {α : Type} {n : Nat} {empty : Verdict} {f : Nat → α → Verdict × Nat} {a : α}
    (ha : ∀ fuel, (f fuel a).1.settled = true) : (as : List α) → a ∈ as → (fuel : Nat) →
    (tryAll n empty fuel f as).1.settled = true
  | [], h, _ => absurd h (by simp)
  | c :: as, h, fuel => by
    unfold tryAll
    split
    · rfl
    · dsimp only
      split
      · assumption
      · rename_i hs
        have hc : c ≠ a := by rintro rfl; exact hs (ha _)
        match as, h with
        | [], h => exact absurd (List.mem_singleton.1 h).symm hc
        | c' :: as', h =>
          dsimp only
          have := tryAll_complete (n := n) (empty := empty) ha (c' :: as') ((List.mem_cons.1 h).resolve_left (Ne.symm hc)) (f (fuel - 1) c).2
          simp [this]

/-- `b` names exactly the keys the blocks hold, each as `β` does. -/
def Agrees (b : Bind) (β : Key → Name) (C : Cands) : Prop :=
  (∀ x s, (x, s) ∈ b.ids ↔ Key.id x ∈ C.keys ∧ β (.id x) = .id s) ∧
  (∀ n s, (n, s) ∈ b.wires ↔ Key.wire n ∈ C.keys ∧ β (.wire n) = .wire s)

namespace Cands

variable {C : Cands} {β : Key → Name}

theorem Has.spaced (hC : C.Ok) (h : C.Has β) : ∀ k ∈ C.keys, (β k).isWire = k.isWire := by
  intro k hk
  obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.1 hk
  exact (hC.space b hb k hkb (β k) ((h b hb).mem_iff.1 (List.mem_map_of_mem hkb))).symm

theorem Has.id (hC : C.Ok) (h : C.Has β) {x : IdV} (hx : Key.id x ∈ C.keys) : ∃ s, β (.id x) = .id s := by
  have := h.spaced hC _ hx
  cases e : β (.id x) with
  | id s => exact ⟨s, rfl⟩
  | wire s => rw [e] at this; cases this

theorem Has.wire (hC : C.Ok) (h : C.Has β) {n : Nat} (hn : Key.wire n ∈ C.keys) : ∃ s, β (.wire n) = .wire s := by
  have := h.spaced hC _ hn
  cases e : β (.wire n) with
  | wire s => exact ⟨s, rfl⟩
  | id s => rw [e] at this; cases this

/-- A name of a decided block is the name of its one key. -/
theorem undecidedIn_none (hC : C.Ok) {ns : List Name} (h : C.undecidedIn ns = none) {s : Name} (hs : s ∈ ns)
    (hsC : s ∈ C.names) : ∃ k, ([k], [s]) ∈ C.blocks := by
  obtain ⟨b, hb, hsb⟩ := List.mem_flatMap.1 hsC
  have hfind := List.findSome?_eq_none_iff.1 h s hs
  rw [blockOfName_eq hC hb hsb] at hfind
  simp only [Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false, Nat.not_le] at hfind
  have hl := hC.len b hb
  have e2 := eq_single (by omega) hsb
  obtain ⟨k, hk⟩ : ∃ k, b.1 = [k] := by
    match e : b.1, hl with
    | [k], _ => exact ⟨k, rfl⟩
    | [], hl => rw [e2] at hl; simp at hl
    | _ :: _ :: _, _ => simp [e] at hfind; omega
  exact ⟨k, by rw [← hk, ← e2]; exact hb⟩

end Cands

theorem find_pair {α : Type} {L : List (α × String)} {x : String} {y : α} (hy : (y, x) ∈ L)
    (hu : ∀ y', (y', x) ∈ L → y' = y) : (L.find? (·.2 == x)).map (·.1) = some y := by
  cases h : L.find? (·.2 == x) with
  | none => exact absurd (List.find?_eq_none.1 h _ hy) (by simp)
  | some p =>
    have hp := List.mem_of_find?_eq_some h
    have h2 : p.2 = x := by simpa using List.find?_some h
    obtain ⟨y', x'⟩ := p
    simp only at h2; subst h2
    simp [hu y' hp]

theorem find_none {α : Type} {L : List (α × String)} {x : String} (hn : ∀ y, (y, x) ∉ L) :
    L.find? (·.2 == x) = none :=
  List.find?_eq_none.2 fun p hp he => hn p.1 (by
    have : p.2 = x := by simpa using he
    rw [← this]; exact hp)

namespace Cands

variable {C : Cands} {β : Key → Name}

theorem mem_bind_ids {x : IdV} {s : String} : (x, s) ∈ C.bind.ids ↔ ([.id x], [.id s]) ∈ C.blocks := by
  simp only [bind, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, h⟩
    match b, h with
    | ([.id _], [.id _]), h => cases h; exact hb
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_bind_wires {n : Nat} {s : String} : (n, s) ∈ C.bind.wires ↔ ([.wire n], [.wire s]) ∈ C.blocks := by
  simp only [bind, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, h⟩
    match b, h with
    | ([.wire _], [.wire _]), h => cases h; exact hb
  · intro h; exact ⟨_, h, rfl⟩

/-- Where a name lies in no undecided block, a binding that agrees with the blocks reads it as the decided bindings
do. -/
theorem id?_bind (hC : C.Ok) (h : C.Has β) {b : Bind} (ha : Agrees b β C) {x : String}
    (hd : Name.id x ∈ C.names → ∃ k, ([k], [Name.id x]) ∈ C.blocks) : b.id? x = C.bind.id? x := by
  simp only [Bind.id?, Bind.idOf]
  by_cases hx : Name.id x ∈ C.names
  · obtain ⟨k, hk⟩ := hd hx
    have hkm : k ∈ C.keys := mem_keys hk (by simp)
    have hβ : β k = .id x := by simpa using h _ hk
    obtain ⟨y, rfl⟩ : ∃ y, k = .id y := by
      have := h.spaced hC k hkm; rw [hβ] at this
      cases k with
      | id y => exact ⟨y, rfl⟩
      | wire _ => cases this
    have inj := h.inj hC
    rw [find_pair ((ha.1 y x).2 ⟨hkm, hβ⟩) fun y' hy' => by
        obtain ⟨h1, h2⟩ := (ha.1 y' x).1 hy'
        simpa using inj _ h1 _ hkm (h2.trans hβ.symm),
      find_pair (mem_bind_ids.2 hk) fun y' hy' => by
        have := hC.block_unique_name (mem_bind_ids.1 hy') hk (s := .id x) (by simp) (by simp)
        simpa using this]
  · rw [find_none (L := b.ids) fun y hy => hx (by have := (ha.1 y x).1 hy; rw [← this.2]; exact h.mem this.1),
      find_none (L := C.bind.ids) fun y hy => hx (mem_names (mem_bind_ids.1 hy) (by simp))]

theorem wire?_bind (hC : C.Ok) (h : C.Has β) {b : Bind} (ha : Agrees b β C) {x : String}
    (hd : Name.wire x ∈ C.names → ∃ k, ([k], [Name.wire x]) ∈ C.blocks) : b.wire? x = C.bind.wire? x := by
  simp only [Bind.wire?]
  by_cases hx : Name.wire x ∈ C.names
  · obtain ⟨k, hk⟩ := hd hx
    have hkm : k ∈ C.keys := mem_keys hk (by simp)
    have hβ : β k = .wire x := by simpa using h _ hk
    obtain ⟨y, rfl⟩ : ∃ y, k = .wire y := by
      have := h.spaced hC k hkm; rw [hβ] at this
      cases k with
      | wire y => exact ⟨y, rfl⟩
      | id _ => cases this
    have inj := h.inj hC
    rw [find_pair ((ha.2 y x).2 ⟨hkm, hβ⟩) fun y' hy' => by
        obtain ⟨h1, h2⟩ := (ha.2 y' x).1 hy'
        simpa using inj _ h1 _ hkm (h2.trans hβ.symm),
      find_pair (mem_bind_wires.2 hk) fun y' hy' => by
        have := hC.block_unique_name (mem_bind_wires.1 hy') hk (s := .wire x) (by simp) (by simp)
        simpa using this]
  · rw [find_none (L := b.wires) fun y hy => hx (by have := (ha.2 y x).1 hy; rw [← this.2]; exact h.mem this.1),
      find_none (L := C.bind.wires) fun y hy => hx (mem_names (mem_bind_wires.1 hy) (by simp))]

end Cands

theorem lookup_mem {α γ : Type} [BEq α] [LawfulBEq α] {a : α} {c : γ} : {L : List (α × γ)} → L.lookup a = some c →
    (a, c) ∈ L
  | [], h => by simp at h
  | (a', c') :: L, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i he; cases h; simp [beq_iff_eq.1 he]
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_isSome {α γ : Type} [BEq α] [LawfulBEq α] {a : α} {c : γ} : {L : List (α × γ)} → (a, c) ∈ L →
    ∃ c', L.lookup a = some c'
  | [], h => absurd h (by simp)
  | (a', c') :: L, h => by
    simp only [List.lookup_cons]
    split
    · exact ⟨_, rfl⟩
    · rename_i he
      rcases List.mem_cons.1 h with e | h
      · cases e; simp at he
      · exact lookup_isSome h

theorem Bind.name_id {b : Bind} (h : b.OneToOne) {x : IdV} {s : String} (hx : (x, s) ∈ b.ids) :
    b.name (.id x) = .id s := by
  obtain ⟨s', hs'⟩ := lookup_isSome hx
  simp only [Bind.name, hs', Option.getD_some, Name.id.injEq]
  exact h.ids x s' s (lookup_mem hs') hx

theorem Bind.name_wire {b : Bind} (h : b.OneToOne) {n : Nat} {s : String} (hn : (n, s) ∈ b.wires) :
    b.name (.wire n) = .wire s := by
  obtain ⟨s', hs'⟩ := lookup_isSome hn
  simp only [Bind.name, hs', Option.getD_some, Name.wire.injEq]
  exact h.wires n s' s (lookup_mem hs') hn

theorem Bind.outside_sub (b : Bind) : (xs : List IdV) → (∀ p ∈ b.ids, p ∈ (b.outside xs).ids) ∧
    (b.outside xs).wires = b.wires
  | [] => ⟨fun _ h => h, rfl⟩
  | x :: xs => by
    simp only [Bind.outside, List.foldl_cons]
    have step : ∀ b' : Bind, (∀ p ∈ b.ids, p ∈ b'.ids) → b'.wires = b.wires →
        (∀ p ∈ b.ids, p ∈ (b'.outside xs).ids) ∧ (b'.outside xs).wires = b.wires := fun b' h1 h2 => by
      obtain ⟨h3, h4⟩ := Bind.outside_sub b' xs
      exact ⟨fun p hp => h3 p (h1 p hp), h4.trans h2⟩
    match x with
    | .named s =>
      simp only
      split
      · exact Bind.outside_sub b xs
      · exact step _ (fun p hp => List.mem_append_left _ hp) rfl
    | .fresh _ _ => exact Bind.outside_sub b xs

namespace Cands

variable {C : Cands} {β : Key → Name}

theorem cond_iff (hC : C.Ok) (h : C.Has β) {b : Bind} (ha : Agrees b β C) (x : IdV) (s : String) :
    (b.ids.any (·.1 == x) || b.ids.any (·.2 == s)) = (C.keys.contains (.id x) || C.names.contains (.id s)) := by
  have e1 : b.ids.any (·.1 == x) = C.keys.contains (.id x) := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, beq_iff_eq, List.contains_iff_mem]
    constructor
    · rintro ⟨⟨y, t⟩, hp, rfl⟩; exact ((ha.1 y t).1 hp).1
    · intro hx; obtain ⟨t, ht⟩ := h.id hC hx; exact ⟨(x, t), (ha.1 x t).2 ⟨hx, ht⟩, rfl⟩
  have e2 : b.ids.any (·.2 == s) = C.names.contains (.id s) := by
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, beq_iff_eq, List.contains_iff_mem]
    constructor
    · rintro ⟨⟨y, t⟩, hp, rfl⟩; have := (ha.1 y t).1 hp; rw [← this.2]; exact h.mem this.1
    · intro hs
      obtain ⟨k, hk, he⟩ := List.mem_map.1 (h.perm.mem_iff.2 hs)
      have := h.spaced hC k hk; rw [he] at this
      cases k with
      | id y => exact ⟨(y, s), (ha.1 y s).2 ⟨hk, he⟩, rfl⟩
      | wire _ => cases this
  rw [e1, e2]

theorem outside_ok : (xs : List IdV) → {C : Cands} → C.Ok → (C.outside xs).Ok ∧
    (∀ b ∈ C.blocks, b ∈ (C.outside xs).blocks) ∧
    ∀ b ∈ (C.outside xs).blocks, b ∈ C.blocks ∨ ∃ s, b = ([.id (.named s)], [.id s])
  | [], _, hC => ⟨hC, fun _ h => h, fun _ h => .inl h⟩
  | x :: xs, C, hC => by
    simp only [outside, List.foldl_cons]
    match x with
    | .named s =>
      simp only
      split
      · exact outside_ok xs hC
      · rename_i hc
        simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at hc
        have hC' : Cands.Ok ⟨C.blocks ++ [([.id (.named s)], [.id s])]⟩ := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.nodup_append.2 ⟨hC.keys, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hc.1 ha⟩
          · simp only [names, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
            exact List.nodup_append.2 ⟨hC.names, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hc.2 ha⟩
          · intro b hb; rcases List.mem_append.1 hb with hb | hb
            · exact hC.len b hb
            · simp at hb; subst hb; rfl
          · intro b hb; rcases List.mem_append.1 hb with hb | hb
            · exact hC.space b hb
            · simp at hb; subst hb; simp [Key.isWire, Name.isWire]
        obtain ⟨h1, h2, h3⟩ := outside_ok xs hC'
        refine ⟨h1, fun b hb => h2 b (List.mem_append_left _ hb), fun b hb => ?_⟩
        rcases h3 b hb with hb | hb
        · rcases List.mem_append.1 hb with hb | hb
          · exact .inl hb
          · simp at hb; exact .inr ⟨s, hb⟩
        · exact .inr hb
    | .fresh _ _ => exact outside_ok xs hC

theorem outside_agrees : (xs : List IdV) → {C : Cands} → C.Ok → {b : Bind} → (C.outside xs).Has β → Agrees b β C →
    Agrees (b.outside xs) β (C.outside xs)
  | [], _, _, _, _, ha => ha
  | x :: xs, C, hC, b, h, ha => by
    have hC0 : C.Has β := fun bl hbl => h bl ((outside_ok (x :: xs) hC).2.1 bl hbl)
    simp only [outside, Bind.outside, List.foldl_cons] at h ⊢
    match x with
    | .named s =>
      simp only at h ⊢
      rw [cond_iff hC hC0 ha]
      by_cases hc : (C.keys.contains (.id (.named s)) || C.names.contains (.id s)) = true
      · simp only [hc, ↓reduceIte] at h ⊢
        exact outside_agrees xs hC h ha
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
        simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at hc
        let C' : Cands := ⟨C.blocks ++ [([.id (.named s)], [.id s])]⟩
        have e : C.outside [.named s] = C' := by
          simp only [outside, List.foldl_cons, List.foldl_nil, C']
          rw [show (C.keys.contains (.id (.named s)) || C.names.contains (.id s)) = false by simp [hc.1, hc.2]]
          rfl
        have hC' : C'.Ok := e ▸ (outside_ok [.named s] hC).1
        have hβ : β (.id (.named s)) = .id s := by
          have := h ([.id (.named s)], [.id s]) ((outside_ok xs hC').2.1 ([.id (.named s)], [.id s]) (by simp [C']))
          simpa using this
        refine outside_agrees xs hC' h ⟨fun y t => ?_, fun n t => ?_⟩
        · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq, keys, C', List.flatMap_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil]
          rw [(ha.1 y t)]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨rfl, rfl⟩)
            · exact ⟨.inl h1, h2⟩
            · exact ⟨.inr (by simp), hβ⟩
          · rintro ⟨h1 | h1, h2⟩
            · exact .inl ⟨h1, h2⟩
            · simp at h1; subst h1; rw [hβ] at h2; simp at h2; exact .inr ⟨rfl, h2.symm⟩
        · simp only [keys, C', List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
          exact ha.2 n t
    | .fresh _ _ => exact outside_agrees xs hC h ha

end Cands

theorem mem_product {α : Type} : (xss : List (List α)) → (R : List α) →
    (R ∈ product xss ↔ Forall2 (fun xs r => r ∈ xs) xss R)
  | [], R => by cases R <;> simp [product, Forall2]
  | xs :: xss, R => by
    cases R with
    | nil => simp [product, Forall2]
    | cons r R =>
      simp only [product, List.mem_flatMap, List.mem_map, List.cons.injEq, Forall2, ← mem_product xss R]
      constructor
      · rintro ⟨x, hx, R', hR', rfl, rfl⟩; exact ⟨hx, hR'⟩
      · rintro ⟨hx, hR⟩; exact ⟨r, hx, R, hR, rfl, rfl⟩

theorem forall2_comp {α β γ : Type} {A : α → β → Prop} {B : β → γ → Prop} :
    {as : List α} → {bs : List β} → {cs : List γ} → Forall2 A as bs → Forall2 B bs cs →
    Forall2 (fun a c => ∃ b, A a b ∧ B b c) as cs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h, hs⟩, ⟨h', hs'⟩ => ⟨⟨_, h, h'⟩, forall2_comp hs hs'⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim
  | [], [], _ :: _, _, h | _ :: _, _ :: _, [], _, h => h.elim

theorem forall2_multi_comp {α β γ : Type} {A : α → β → Prop} {B : β → γ → Prop} {as : List α} {bs : List β}
    {cs : List γ} (h : Forall2 A as bs) : Multi B bs cs → Multi (fun a c => ∃ b, A a b ∧ B b c) as cs
  | ⟨zs, hz, hp⟩ => ⟨zs, forall2_comp h hz, hp⟩

theorem multi_forall2_comp {α β γ : Type} {B : α → β → Prop} {C : γ → β → Prop} {as : List α} {bs : List β}
    {cs : List γ} (hm : Multi B as bs) (hf : Forall2 C cs bs) : Multi (fun a c => ∃ b, B a b ∧ C c b) as cs := by
  obtain ⟨zs, hz, hp⟩ := hm
  obtain ⟨cs', hcs, hf'⟩ := forall2_perm (R := C) hp.symm hf
  exact ⟨cs', forall2_comp hz (forall2_flip hf'), hcs⟩

theorem map_inj_of {α γ : Type} {f : α → γ} (hf : ∀ a b, f a = f b → a = b) :
    {l l' : List α} → l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a b h.1, map_inj_of hf h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem same_atoms {α : Type} [Leaf α] {H H' : List Erl} (h : Tree.Same (α := α) (.seq (H.map .atom)) (.seq (H'.map .atom))) :
    H = H' := by
  simp only [Tree.Same, Tree.erl, Tree.erls_eq, List.map_map, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq,
    true_and, and_true] at h
  exact map_inj_of (fun a b e => by simpa [Tree.erl] using e) h

theorem winTree_same {α : Type} [Leaf α] {tys : List (Option Ty)} {t₁ t₂ : Option Ty} {a b : Tree α}
    (h₁ : t₁ ∈ tys) (h₂ : t₂ ∈ tys) : Tree.Same (winTree tys t₁ a) (winTree tys t₂ b) ↔ t₁ = t₂ ∧ Tree.Same a b := by
  simp only [winTree, Tree.same_seq, Forall2, Tree.same_atom, Erl.int.injEq, and_true]
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨?_, hs⟩
    have := congrArg (tys[·]?) (Int.ofNat_inj.1 hi)
    simpa [get_indexIn h₁, get_indexIn h₂] using this
  · rintro ⟨rfl, hs⟩; exact ⟨rfl, hs⟩

theorem tree_heads {v : ServiceV} {T : List TypeDecl} {β : Key → Name} {now : Int} {e : Expect v} {l : Line}
    {te : Tree Key} {tl : Tree Name} (he : e.tree T v now = some te) (hl : lineTree T (Expect.ty v e) l = some tl)
    (hs : Tree.Same (te.map β) tl) : l.head = some (e.head v now) := by
  simp only [Expect.tree, Option.map_eq_some_iff] at he
  obtain ⟨b, -, rfl⟩ := he
  simp only [lineTree, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hl
  obtain ⟨h, hh, b', -, rfl⟩ := hl
  simp only [Tree.map, Tree.maps_eq, List.map_cons, List.map_nil, Tree.same_seq, Forall2, List.map_map] at hs
  have hmap : ∀ H : List Erl, (H.map Tree.atom).map (Tree.map β) = H.map Tree.atom := fun H => by
    induction H with
    | nil => rfl
    | cons x H ih => simp only [List.map_cons, ih]; rfl
  have := same_atoms (α := Name) (H := e.head v now) (H' := h) (by
    have h1 := hs.1
    rw [Tree.same_seq]
    rwa [← List.map_map, hmap] at h1)
  rw [hh, this]

section
variable {T : List TypeDecl} {v : ServiceV}

theorem Tree.map_atoms {α γ : Type} (f : α → γ) (hs : List Erl) :
    Tree.map f (.seq (hs.map Tree.atom)) = .seq (hs.map Tree.atom) := by
  simp only [Tree.map, Tree.maps_eq, List.map_map]; rfl

theorem leavess_atoms {α : Type} (hs : List Erl) : Tree.leavess (hs.map (Tree.atom (α := α))) = [] := by
  induction hs with
  | nil => rfl
  | cons h hs ih => simp [Tree.leavess, Tree.leaves, ih]

theorem keys_of {now : Int} {e : Expect v} {b : List (Tree Key)} (hb : e.body T v = some b) :
    Expect.keys T v now e = Tree.leavess b := by
  simp [Expect.keys, Expect.tree, hb, Tree.leaves, Tree.leavess, leavess_atoms]

theorem treeW_of {β : Key → Name} {now : Int} {e : Expect v} {l : Line} {b : List (Tree Key)} {bl : List (Tree Name)}
    (hb : e.body T v = some b) (hh : l.head = some (e.head v now)) (hl : l.body T (Expect.ty v e) = some bl)
    (hs : Forall2 Tree.Same (b.map (Tree.map β)) bl) : TreeW T v β now e l := by
  refine ⟨.seq [.seq ((e.head v now).map .atom), .seq b], .seq [.seq ((e.head v now).map .atom), .seq bl],
    by simp [Expect.tree, hb], by simp [lineTree, hh, hl], ?_⟩
  simp only [Tree.map, Tree.maps_eq, List.map_cons, List.map_nil]
  refine Tree.same_seq.2 ⟨?_, Tree.same_seq.2 hs, trivial⟩
  rw [← Tree.maps_eq, ← Tree.map, Tree.map_atoms]
  rfl

theorem treeW_body {β : Key → Name} {now : Int} {e : Expect v} {l : Line} (h : TreeW T v β now e l) :
    l.head = some (e.head v now) ∧ ∃ b bl, e.body T v = some b ∧ l.body T (Expect.ty v e) = some bl ∧
      Forall2 Tree.Same (b.map (Tree.map β)) bl := by
  obtain ⟨te, tl, he, hl, hs⟩ := h
  refine ⟨tree_heads he hl hs, ?_⟩
  simp only [Expect.tree, Option.map_eq_some_iff] at he
  obtain ⟨b, hb, rfl⟩ := he
  simp only [lineTree, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hl
  obtain ⟨hd, -, bl, hbl, rfl⟩ := hl
  simp only [Tree.map, Tree.maps_eq, List.map_cons, List.map_nil, Tree.same_seq, Forall2] at hs
  exact ⟨b, bl, hb, hbl, hs.2.1⟩

theorem Bind.idOf_mem {b : Bind} {s : String} {i : IdV} (h : b.idOf s = some i) : (i, s) ∈ b.ids := by
  simp only [Bind.idOf, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have h2 : p.2 = s := by simpa using List.find?_some hp
  rw [← h2]; exact List.mem_of_find?_eq_some hp

theorem Bind.wire?_mem {b : Bind} {s : String} {n : Nat} (h : b.wire? s = some n) : (n, s) ∈ b.wires := by
  simp only [Bind.wire?, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have h2 : p.2 = s := by simpa using List.find?_some hp
  rw [← h2]; exact List.mem_of_find?_eq_some hp

/-- Where the binding names every id among `ks`, it reads each back by its name. -/
theorem Bind.undoes {b : Bind} (hone : b.OneToOne) {ks : List Key} (hk : ∀ k ∈ ks, b.Binds k) :
    Undoes b.idOf b.name ks := fun i s hi he => by
  obtain ⟨t, ht⟩ := hk _ hi
  rw [Bind.name_id hone ht] at he
  have hts : t = s := by injection he
  subst hts
  exact find_pair ht fun y hy => hone.idNames y i t hy ht

theorem writes_of_tree {b : Bind} (hone : b.OneToOne) {t : Ty} (hc : t.comparable = true) {x : t.den0} {w : Wire}
    {te : Tree Key} {tl : Tree Name} (h1 : valTree T t x = some te) (h2 : wireTree T t w = some tl)
    (h3 : Tree.Same (te.map b.name) tl) (hk : ∀ k ∈ te.leaves, b.Binds k) : b.Writes T t x w :=
  tree_dec T b.idOf b.name t hc x w te tl h1 h2 h3 (Bind.undoes hone hk)

theorem tree_of_writes {b : Bind} (hone : b.OneToOne) {t : Ty} {x : t.den0} {w : Wire} (h : b.Writes T t x w) :
    ∃ te tl, valTree T t x = some te ∧ wireTree T t w = some tl ∧ Tree.Same (te.map b.name) tl := by
  obtain ⟨y, hy, hs⟩ := h
  obtain ⟨te, tl, h1, h2, h3⟩ := dec_tree T b.idOf b.name (fun _ _ h => Bind.name_id hone (Bind.idOf_mem h)) t w y hy
  obtain ⟨te', h1', hs'⟩ := valTree_same T t y x (Ty.same_symm hs) te h1
  exact ⟨te', tl, h1', h2, (Tree.Same.map b.name hs').symm.trans h3⟩

theorem same_rules {rs rs' : List String} {f : Key → Name} :
    Tree.Same ((Tree.bag (rs.map (Tree.atom ∘ Erl.bin))).map f) (.bag (rs'.map (Tree.atom ∘ Erl.bin))) ↔
      rs.Perm rs' := by
  have hm : (Tree.bag (rs.map (Tree.atom ∘ Erl.bin))).map f = .bag (rs.map (Tree.atom ∘ Erl.bin)) := by
    simp only [Tree.map, Tree.maps_eq, List.map_map]; rfl
  rw [hm]
  simp only [Tree.Same, Tree.erl, Tree.erls_eq, List.map_map, Erl.tuple.injEq, List.cons.injEq, Erl.list.injEq,
    true_and, and_true, Erl.sort_eq_iff]
  constructor
  · intro h
    obtain ⟨l', hl', he⟩ := perm_map_inv h rfl
    rw [map_inj_of (fun a b e => by simpa [Tree.erl] using e) he]; exact hl'
  · intro h; exact h.map _

/-- A trace line that matches an expected line as verify compares them writes it, where the binding names the
line's keys one to one and its value's type is comparable. -/
theorem lineW_of_treeW {b : Bind} (hone : b.OneToOne) {now : Int} {e : Expect v} {l : Line}
    (hk : ∀ k ∈ Expect.keys T v now e, b.Binds k) (hc : ∀ t, Expect.ty v e = some t → t.comparable = true)
    (h : TreeW T v b.name now e l) : LineW T v b now e l := by
  obtain ⟨hh, bs, bl, hb, hl, hs⟩ := treeW_body h
  rw [keys_of hb] at hk
  cases e with
  | answered to o =>
    cases l <;> simp [Line.head, Expect.head] at hh
    rename_i t to' a
    obtain ⟨rfl, rfl, htag⟩ := hh
    refine ⟨rfl, rfl, ?_⟩
    cases o <;> cases a <;> simp [outcomeTag, answerTag] at htag
    · trivial
    · rename_i x w
      obtain ⟨ty, x⟩ := x
      simp only [Expect.body, Option.map_eq_some_iff] at hb
      obtain ⟨te, hte, rfl⟩ := hb
      simp only [Line.body, Expect.ty, Option.bind_some, Option.map_eq_some_iff] at hl
      obtain ⟨tl, htl, rfl⟩ := hl
      exact writes_of_tree hone (hc ty rfl) hte htl hs.1 (by simpa [Tree.leavess] using hk)
    · rename_i x w
      obtain ⟨ty, x⟩ := x
      simp only [Expect.body, Option.map_eq_some_iff] at hb
      obtain ⟨te, hte, rfl⟩ := hb
      simp only [Line.body, Expect.ty, Option.bind_some, Option.map_eq_some_iff] at hl
      obtain ⟨tl, htl, rfl⟩ := hl
      exact writes_of_tree hone (hc ty rfl) hte htl hs.1 (by simpa [Tree.leavess] using hk)
    · simp only [Expect.body, Option.some.injEq] at hb
      simp only [Line.body, Option.some.injEq] at hl
      subst hb hl
      exact same_rules.1 hs.1
  | applied ev =>
    cases l <;> simp [Line.head, Expect.head] at hh
    rename_i t w
    refine ⟨hh, ?_⟩
    simp only [Expect.body, Option.map_eq_some_iff] at hb
    obtain ⟨te, hte, rfl⟩ := hb
    simp only [Line.body, Expect.ty, Option.bind_some, Option.map_eq_some_iff] at hl
    obtain ⟨tl, htl, rfl⟩ := hl
    exact writes_of_tree hone (hc _ rfl) hte htl hs.1 (by simpa [Tree.leavess] using hk)
  | sent id x n i =>
    obtain ⟨ty, i⟩ := i
    cases l <;> simp [Line.head, Expect.head] at hh
    rename_i t wn x' n' w
    obtain ⟨rfl, rfl, rfl⟩ := hh
    simp only [Expect.body, Option.map_eq_some_iff] at hb
    obtain ⟨te, hte, rfl⟩ := hb
    simp only [Line.body, Expect.ty, Option.bind_some, Option.map_eq_some_iff] at hl
    obtain ⟨tl, htl, rfl⟩ := hl
    simp only [List.map_cons, List.map_nil, Forall2, Tree.map] at hs
    obtain ⟨⟨m, hm⟩, -⟩ : b.Binds (.wire id) ∧ True := ⟨hk _ (by simp [Tree.leavess, Tree.leaves]), trivial⟩
    have hw : b.name (.wire id) = .wire wn := Tree.same_leaf.1 hs.1
    rw [Bind.name_wire hone hm] at hw
    have hmw : m = wn := by injection hw
    subst hmw
    exact ⟨rfl, rfl, rfl, find_pair hm fun y hy => hone.wireNames y id m hy hm,
      writes_of_tree hone (hc ty rfl) hte htl hs.2.1 fun k hk' => hk k (by simp [Tree.leavess, Tree.leaves, hk'])⟩

/-- A trace line that writes an expected line matches it as verify compares them, where the binding is one to one. -/
theorem treeW_of_lineW {b : Bind} (hone : b.OneToOne) {now : Int} {e : Expect v} {l : Line}
    (h : LineW T v b now e l) : TreeW T v b.name now e l := by
  cases e with
  | answered to o =>
    cases l <;> simp only [LineW] at h
    rename_i t to' a
    obtain ⟨rfl, rfl, h⟩ := h
    cases o <;> cases a <;> simp only at h
    · exact treeW_of (b := []) rfl rfl rfl trivial
    · rename_i x w
      obtain ⟨ty, x⟩ := x
      obtain ⟨te, tl, h1, h2, h3⟩ := tree_of_writes hone h
      exact treeW_of (b := [te]) (bl := [tl]) (by simp [Expect.body, h1]) rfl (by simp [Line.body, Expect.ty, h2])
        ⟨h3, trivial⟩
    · rename_i x w
      obtain ⟨ty, x⟩ := x
      obtain ⟨te, tl, h1, h2, h3⟩ := tree_of_writes hone h
      exact treeW_of (b := [te]) (bl := [tl]) (by simp [Expect.body, h1]) rfl (by simp [Line.body, Expect.ty, h2])
        ⟨h3, trivial⟩
    · exact treeW_of rfl rfl rfl ⟨same_rules.2 h, trivial⟩
  | applied ev =>
    cases l <;> simp only [LineW] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨te, tl, h1, h2, h3⟩ := tree_of_writes hone h
    exact treeW_of (b := [te]) (bl := [tl]) (by simp [Expect.body, h1]) rfl (by simp [Line.body, Expect.ty, h2])
      ⟨h3, trivial⟩
  | sent id x n i =>
    obtain ⟨ty, i⟩ := i
    cases l <;> simp only [LineW] at h
    rename_i wn _ _ _
    obtain ⟨rfl, rfl, rfl, hw, h⟩ := h
    obtain ⟨te, tl, h1, h2, h3⟩ := tree_of_writes hone h
    refine treeW_of (b := [.leaf (.wire id), te]) (bl := [.leaf (.wire wn), tl]) (by simp [Expect.body, h1]) rfl
      (by simp [Line.body, Expect.ty, h2]) ⟨?_, h3, trivial⟩
    show Tree.Same (.leaf (b.name (.wire id))) _
    rw [Bind.name_wire hone (Bind.wire?_mem hw)]; rfl

theorem winTree_map {α γ : Type} (tys : List (Option Ty)) (ty : Option Ty) (f : α → γ) (t : Tree α) :
    (winTree tys ty t).map f = winTree tys ty (t.map f) := rfl

theorem mem_tys {es : List (Expect v)} {e : Expect v} (he : e ∈ es) : Expect.ty v e ∈ Expect.tys v es :=
  Cands.mem_nub.2 (List.mem_map_of_mem he)

theorem mem_readings {now : Int} {es : List (Expect v)} {ls : List Line} {R : List (Tree Name)} :
    R ∈ readings T v now es ls ↔ Forall2 (fun l r => ∃ ty, (∃ e ∈ es, l.head = some (e.head v now) ∧ Expect.ty v e = ty) ∧
      ∃ tl, lineTree T ty l = some tl ∧ r = winTree (Expect.tys v es) ty tl) ls R := by
  rw [readings, mem_product, forall2_map_left_iff]
  refine ⟨fun h => forall2_imp (fun l r h => ?_) h, fun h => forall2_imp (fun l r h => ?_) h⟩
  · obtain ⟨ty, hty, h⟩ := List.mem_filterMap.1 h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (Cands.mem_nub.1 hty)
    obtain ⟨he1, he2⟩ := List.mem_filter.1 he
    obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, ⟨e, he1, (beq_iff_eq.1 he2).symm, rfl⟩, tl, htl, rfl⟩
  · obtain ⟨ty, ⟨e, he, hh, rfl⟩, tl, htl, rfl⟩ := h
    exact List.mem_filterMap.2 ⟨_, Cands.mem_nub.2 (List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp [hh]⟩, rfl⟩),
      by simp [htl]⟩

theorem expTrees_spec {now : Int} {es : List (Expect v)} {ets : List (Tree Key)} (h : expTrees T v now es = some ets) :
    Forall2 (fun e t => ∃ te, e.tree T v now = some te ∧ t = winTree (Expect.tys v es) (Expect.ty v e) te) es ets :=
  forall2_imp (fun _ _ h => by obtain ⟨te, h1, h2⟩ := Option.map_eq_some_iff.1 h; exact ⟨te, h1, h2.symm⟩)
    (mapM_forall2 h)

/-- A reading under which the expected trees are the trace's makes the window's lines write the expected lines. -/
theorem readings_sound {β : Key → Name} {now : Int} {es : List (Expect v)} {ls : List Line} {R : List (Tree Name)}
    {ets : List (Tree Key)} (hR : R ∈ readings T v now es ls) (he : expTrees T v now es = some ets)
    (hm : Multi (fun a b => Tree.Same (a.map β) b) ets R) : Multi (TreeW T v β now) es ls := by
  have h1 := forall2_multi_comp (expTrees_spec he) hm
  have h2 := multi_forall2_comp h1 (mem_readings.1 hR)
  refine Multi.imp_mem (fun e he' l _ h => ?_) h2
  obtain ⟨r, ⟨t, ⟨te, hte, rfl⟩, hs⟩, ⟨ty, ⟨e', he'', _, rfl⟩, tl, htl, rfl⟩⟩ := h
  rw [winTree_map, winTree_same (mem_tys he') (mem_tys he'')] at hs
  obtain ⟨hty, hs⟩ := hs
  exact ⟨te, tl, hte, hty ▸ htl, hs⟩

/-- Lines that write the expected lines give a reading under which the expected trees are the trace's. -/
theorem readings_complete {β : Key → Name} {now : Int} {es : List (Expect v)} {ls : List Line}
    (hm : Multi (TreeW T v β now) es ls) :
    ∃ ets, expTrees T v now es = some ets ∧ ∃ R ∈ readings T v now es ls,
      Multi (fun a b => Tree.Same (a.map β) b) ets R := by
  obtain ⟨ls', hf, hp⟩ := hm
  have build : ∀ (es' : List (Expect v)) (ls'' : List Line), (∀ e ∈ es', e ∈ es) → Forall2 (TreeW T v β now) es' ls'' →
      ∃ ets R', Forall2 (fun e t => (e.tree T v now).map (winTree (Expect.tys v es) (Expect.ty v e)) = some t) es' ets ∧
        Forall2 (fun a b => Tree.Same (a.map β) b) ets R' ∧
        Forall2 (fun l r => ∃ ty, (∃ e ∈ es, l.head = some (e.head v now) ∧ Expect.ty v e = ty) ∧
          ∃ tl, lineTree T ty l = some tl ∧ r = winTree (Expect.tys v es) ty tl) ls'' R' := by
    intro es' ls''
    induction es' generalizing ls'' with
    | nil => intro _ h; cases ls'' with
      | nil => exact ⟨[], [], trivial, trivial, trivial⟩
      | cons => exact h.elim
    | cons e es' ih =>
      intro hsub h
      cases ls'' with
      | nil => exact h.elim
      | cons l ls'' =>
        obtain ⟨⟨te, tl, hte, htl, hs⟩, hs'⟩ := h
        obtain ⟨ets, R', h1, h2, h3⟩ := ih ls'' (fun e' he' => hsub e' (by simp [he'])) hs'
        have hes : e ∈ es := hsub e (by simp)
        refine ⟨winTree (Expect.tys v es) (Expect.ty v e) te :: ets, winTree (Expect.tys v es) (Expect.ty v e) tl :: R',
          ⟨by simp [hte], h1⟩, ⟨?_, h2⟩, ⟨⟨_, ⟨e, hes, tree_heads hte htl hs, rfl⟩, tl, htl, rfl⟩, h3⟩⟩
        show Tree.Same ((winTree (Expect.tys v es) (Expect.ty v e) te).map β) _
        rw [winTree_map, winTree_same (mem_tys hes) (mem_tys hes)]
        exact ⟨rfl, hs⟩
  obtain ⟨ets, R', h1, h2, h3⟩ := build es ls' (fun _ h => h) hf
  obtain ⟨R, hRp, hR⟩ := forall2_perm (R := fun r l => ∃ ty, (∃ e ∈ es, l.head = some (e.head v now) ∧
    Expect.ty v e = ty) ∧ ∃ tl, lineTree T ty l = some tl ∧ r = winTree (Expect.tys v es) ty tl) hp (forall2_flip h3)
  exact ⟨ets, mapM_of_forall2 h1, R, mem_readings.2 (forall2_flip hR), R', h2, hRp.symm⟩

end

namespace Cands

variable {C : Cands} {β β' : Key → Name}

theorem Has.congr (hβ : ∀ k ∈ C.keys, β k = β' k) (h : C.Has β) : C.Has β' := fun b hb => by
  rw [← List.map_congr_left fun k hk => hβ k (mem_keys hb hk)]; exact h b hb

theorem agrees_congr {b : Bind} (hβ : ∀ k ∈ C.keys, β k = β' k) (h : Agrees b β C) : Agrees b β' C :=
  ⟨fun x s => (h.1 x s).trans ⟨fun ⟨h1, h2⟩ => ⟨h1, (hβ _ h1).symm.trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hβ _ h1).trans h2⟩⟩,
    fun n s => (h.2 n s).trans ⟨fun ⟨h1, h2⟩ => ⟨h1, (hβ _ h1).symm.trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hβ _ h1).trans h2⟩⟩⟩

theorem agrees_keys {C' : Cands} {b : Bind} (hk : ∀ k, k ∈ C.keys ↔ k ∈ C'.keys) (h : Agrees b β C) : Agrees b β C' :=
  ⟨fun x s => (h.1 x s).trans (by rw [hk]), fun n s => (h.2 n s).trans (by rw [hk])⟩

theorem agrees_one (hC : C.Ok) (h : C.Has β) {b : Bind} (ha : Agrees b β C) : b.OneToOne := by
  have inj := h.inj hC
  refine ⟨fun x s s' h1 h2 => ?_, fun x x' s h1 h2 => ?_, fun n s s' h1 h2 => ?_, fun n n' s h1 h2 => ?_⟩
  · have := ((ha.1 x s).1 h1).2.symm.trans ((ha.1 x s').1 h2).2; simpa using this
  · have e := inj _ ((ha.1 x s).1 h1).1 _ ((ha.1 x' s).1 h2).1 (((ha.1 x s).1 h1).2.trans ((ha.1 x' s).1 h2).2.symm)
    simpa using e
  · have := ((ha.2 n s).1 h1).2.symm.trans ((ha.2 n s').1 h2).2; simpa using this
  · have e := inj _ ((ha.2 n s).1 h1).1 _ ((ha.2 n' s).1 h2).1 (((ha.2 n s).1 h1).2.trans ((ha.2 n' s).1 h2).2.symm)
    simpa using e

/-- The binding `β` gives the blocks' keys, as a binding of lists. -/
def bindOf (β : Key → Name) (C : Cands) : Bind where
  ids := C.keys.filterMap fun k => match k, β k with
    | .id x, .id s => some (x, s)
    | _, _ => none
  wires := C.keys.filterMap fun k => match k, β k with
    | .wire n, .wire s => some (n, s)
    | _, _ => none

theorem bindOf_agrees : Agrees (bindOf β C) β C := by
  refine ⟨fun x s => ?_, fun n s => ?_⟩
  · simp only [bindOf, List.mem_filterMap]
    constructor
    · rintro ⟨k, hk, h⟩
      cases k with
      | id y =>
        cases e : β (.id y) with
        | id t => simp only [e, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hk, e⟩
        | wire t => simp [e] at h
      | wire n => simp at h
    · rintro ⟨hk, h⟩; exact ⟨_, hk, by simp [h]⟩
  · simp only [bindOf, List.mem_filterMap]
    constructor
    · rintro ⟨k, hk, h⟩
      cases k with
      | wire y =>
        cases e : β (.wire y) with
        | wire t => simp only [e, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hk, e⟩
        | id t => simp [e] at h
      | id n => simp at h
    · rintro ⟨hk, h⟩; exact ⟨_, hk, by simp [h]⟩

theorem agrees_add {b : Bind} {s : String} (ha : Agrees b β C) (hβ : β (.id (.named s)) = .id s) :
    Agrees { b with ids := b.ids ++ [(.named s, s)] } β ⟨C.blocks ++ [([.id (.named s)], [.id s])]⟩ := by
  refine ⟨fun y t => ?_, fun n t => ?_⟩
  · simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq, keys, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [(ha.1 y t)]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨rfl, rfl⟩)
      · exact ⟨.inl h1, h2⟩
      · exact ⟨.inr (by simp), hβ⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact .inl ⟨h1, h2⟩
      · simp at h1; subst h1; rw [hβ] at h2; simp at h2; exact .inr ⟨rfl, h2.symm⟩
  · simp only [keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_singleton, reduceCtorEq, or_false]
    exact ha.2 n t

/-- Where `β` binds every outside id `b.outside` binds to its name, the blocks with the outside ids decided hold `β`
possible. -/
theorem outside_complete : (xs : List IdV) → {C : Cands} → C.Ok → {b : Bind} → C.Has β → Agrees b β C →
    (∀ p ∈ (b.outside xs).ids, β (.id p.1) = .id p.2) → (C.outside xs).Has β
  | [], _, _, _, h, _, _ => h
  | x :: xs, C, hC, b, h, ha, hp => by
    simp only [outside, Bind.outside, List.foldl_cons] at hp ⊢
    match x with
    | .named s =>
      simp only at hp ⊢
      rw [cond_iff hC h ha] at hp
      by_cases hc : (C.keys.contains (.id (.named s)) || C.names.contains (.id s)) = true
      · simp only [hc, ↓reduceIte] at hp ⊢
        exact outside_complete xs hC h ha hp
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp ⊢
        simp only [Bool.or_eq_true, List.contains_iff_mem, not_or] at hc
        have e : C.outside [.named s] = ⟨C.blocks ++ [([.id (.named s)], [.id s])]⟩ := by
          simp [outside, hc.1, hc.2]
        have hβ : β (.id (.named s)) = .id s :=
          hp _ ((Bind.outside_sub _ xs).1 _ (List.mem_append_right _ (List.mem_singleton_self _)))
        refine outside_complete xs (e ▸ (outside_ok [.named s] hC).1) (fun bl hbl => ?_) (agrees_add ha hβ) hp
        rcases List.mem_append.1 hbl with hbl | hbl
        · exact h bl hbl
        · simp at hbl; subst hbl; simp [hβ]
    | .fresh _ _ => exact outside_complete xs hC h ha hp

end Cands

section
variable {T : List TypeDecl} {v : ServiceV}

theorem leavess_ets {now : Int} {es : List (Expect v)} {ets : List (Tree Key)} (h : expTrees T v now es = some ets) :
    Tree.leavess ets = es.flatMap (Expect.keys T v now) := by
  have hf := expTrees_spec h
  clear h
  generalize Expect.tys v es = tys at hf
  induction es generalizing ets with
  | nil => cases ets with
    | nil => rfl
    | cons => exact hf.elim
  | cons e es ih =>
    cases ets with
    | nil => exact hf.elim
    | cons t ets =>
      obtain ⟨⟨te, hte, rfl⟩, hs⟩ := hf
      simp only [Tree.leavess, List.flatMap_cons, winTree, Tree.leaves, Tree.leavess, List.nil_append,
        List.append_nil, Expect.keys, hte, Option.map_some, Option.getD_some]
      rw [ih hs]

theorem treeW_congr {β β' : Key → Name} {now : Int} {e : Expect v} {l : Line}
    (hβ : ∀ k ∈ Expect.keys T v now e, β k = β' k) (h : TreeW T v β now e l) : TreeW T v β' now e l := by
  obtain ⟨te, tl, hte, htl, hs⟩ := h
  refine ⟨te, tl, hte, htl, ?_⟩
  rw [← Tree.map_congr te fun k hk => hβ k (by simp [Expect.keys, hte, hk])]
  exact hs

theorem stepIn_error {s : State v} {b : Bind} {n : Nat} {l : Line} {e : Verdict}
    (h : stepIn T v s b n l = .error e) : e.settled = false := by
  unfold stepIn at h
  split at h
  · cases h; rfl
  · dsimp only at h
    split at h
    · cases h; rfl
    · cases h

end

namespace Cands

variable {C : Cands} {β : Key → Name}

theorem name_eq (hC : C.Ok) (h : C.Has β) {b : Bind} (ha : Agrees b β C) {k : Key} (hk : k ∈ C.keys) :
    b.name k = β k := by
  have hone := agrees_one hC h ha
  cases k with
  | id x => obtain ⟨t, ht⟩ := h.id hC hk; rw [ht]; exact Bind.name_id hone ((ha.1 x t).2 ⟨hk, ht⟩)
  | wire n => obtain ⟨t, ht⟩ := h.wire hC hk; rw [ht]; exact Bind.name_wire hone ((ha.2 n t).2 ⟨hk, ht⟩)

theorem grows_of {C₀ C₁ : Cands} {b₀ b₁ : Bind} {ks : List Key} (hC₁ : C₁.Ok) (h₁ : C₁.Has β)
    (ha₀ : Agrees b₀ β C₀) (ha₁ : Agrees b₁ β C₁) (hk : ∀ k, k ∈ C₁.keys ↔ k ∈ C₀.keys ∨ k ∈ ks) : Grows b₀ ks b₁ := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun k hk' => ?_, agrees_one hC₁ h₁ ha₁⟩
  · obtain ⟨h1, h2⟩ := (ha₀.1 p.1 p.2).1 hp; exact (ha₁.1 p.1 p.2).2 ⟨(hk _).2 (.inl h1), h2⟩
  · obtain ⟨h1, h2⟩ := (ha₀.2 p.1 p.2).1 hp; exact (ha₁.2 p.1 p.2).2 ⟨(hk _).2 (.inl h1), h2⟩
  · obtain ⟨h1, h2⟩ := (ha₁.1 p.1 p.2).1 hp
    rcases (hk _).1 h1 with h1 | h1
    · exact .inl ((ha₀.1 p.1 p.2).2 ⟨h1, h2⟩)
    · exact .inr h1
  · obtain ⟨h1, h2⟩ := (ha₁.2 p.1 p.2).1 hp
    rcases (hk _).1 h1 with h1 | h1
    · exact .inl ((ha₀.2 p.1 p.2).2 ⟨h1, h2⟩)
    · exact .inr h1
  · have hk1 := (hk k).2 (.inr hk')
    cases k with
    | id x => obtain ⟨t, ht⟩ := h₁.id hC₁ hk1; exact ⟨t, (ha₁.1 x t).2 ⟨hk1, ht⟩⟩
    | wire n => obtain ⟨t, ht⟩ := h₁.wire hC₁ hk1; exact ⟨t, (ha₁.2 n t).2 ⟨hk1, ht⟩⟩

end Cands

theorem same_bag_map {β : Key → Name} {ets : List (Tree Key)} {R : List (Tree Name)} :
    Tree.Same ((Tree.bag ets).map β) (Tree.bag R) ↔ Multi (fun a b => Tree.Same (a.map β) b) ets R := by
  simp only [Tree.map, Tree.maps_eq, Tree.same_bag, multi_map_left_iff]

mutual
/-- Reads the lines from `s` with the blocks `C`, depth first over the choices it must make, with `fuel` tries left:
the verdict and the fuel left. An in line that names a name of an undecided block decides it first, by each key of the
block in turn. -/
def readFrom (fuel : Nat) (s : State v) (C : Cands) : List (Nat × Line) → Verdict × Nat
  | [] => (.passed, fuel)
  | (n, l) :: more =>
    match _h : C.undecidedIn l.inNames with
    | some (nm, b) =>
      tryAll n (.limit n) fuel (fun fuel (k : { k // k ∈ b.1 }) => readFrom fuel s (C.narrow k nm) ((n, l) :: more))
        b.1.attach
    | none =>
      match stepIn T v s C.bind n l with
      | .error e => (e, fuel)
      | .ok (r, ids, es) =>
        let C₀ := C.outside ids
        let now := r.state.now
        let fail := Verdict.differs n ((es.filterMap (·.toLine T v now C₀.bind.ids C₀.bind.wires)).map Line.toWire)
          ((window more).map Line.toWire)
        match expTrees T v now es with
        | none => (fail, fuel)
        | some ets => tryAll n fail fuel (fun fuel R => match C₀.addNew (Tree.leavess ets) (Tree.leavess R) with
            | some C₁ => windowFrom fuel n fail r.state C₁ ets R (afterWindow more)
            | none => (fail, fuel)) (readings T v now es (window more))
termination_by ls => (ls.length, 1, C.weight)
decreasing_by
  · obtain ⟨-, hb, -, h2⟩ := undecidedIn_some _h
    exact Prod.Lex.right _ (Prod.Lex.right _ (Cands.narrow_lt hb k.2 h2))
  · have := afterWindow_length more
    simp only [List.length_cons]
    rcases Nat.lt_or_eq_of_le this with h | h
    · exact Prod.Lex.left _ _ (by omega)
    · rw [h]; exact Prod.Lex.left _ _ (by omega)
/-- Reads the window's out lines `R` against the expected trees `ets` with the blocks `C`, then the lines after it.
Where the window's items tie undecided keys, it decides one first, by each name of its block in turn. -/
def windowFrom (fuel n : Nat) (fail : Verdict) (s : State v) (C : Cands) (ets : List (Tree Key))
    (R : List (Tree Name)) (rest : List (Nat × Line)) : Verdict × Nat :=
  match _h : C.window ets R with
  | .done C' => readFrom fuel s C' rest
  | .differs => (fail, fuel)
  | .decide k b =>
    tryAll n fail fuel (fun fuel (nm : { x // x ∈ b.2 }) => windowFrom fuel n fail s (C.narrow k nm) ets R rest)
      b.2.attach
termination_by (rest.length, 2, C.weight)
decreasing_by
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
  · obtain ⟨hb, hk, h2⟩ := Cands.window_decide _h
    exact Prod.Lex.right _ (Prod.Lex.right _ (Cands.narrow_lt hb hk h2))
end

/-- Replays the lines after the header, each with its line number. -/
def replay (lines : List (Nat × Line)) : Verdict := (readFrom T v tryCap (State.init v) {} lines).1

section
variable (T : List TypeDecl) (v : ServiceV)

/-- Every value a result's out lines carry has a comparable type. -/
def OutComparable (r : Result v) : Prop :=
  v.event.comparable = true ∧ (∀ w, r.outcome = .answered w → w.1.comparable = true) ∧
    (∀ w, r.outcome = .rejected w → w.1.comparable = true) ∧ ∀ o ∈ r.out, o.input.1.comparable = true

theorem expects_comparable {r : Result v} (hr : OutComparable v r) (a : Option String) :
    ∀ e ∈ expects v a r, ∀ t, Expect.ty v e = some t → t.comparable = true := by
  intro e he t ht
  simp only [expects, List.mem_append, List.mem_map] at he
  rcases he with (he | ⟨ev, -, rfl⟩) | ⟨o, ho, rfl⟩
  · cases a <;> simp at he
    subst he
    cases hout : r.outcome <;> simp [Expect.ty, hout] at ht
    · subst ht; exact hr.2.1 _ hout
    · subst ht; exact hr.2.2.1 _ hout
  · simp only [Expect.ty, Option.some.injEq] at ht; subst ht; exact hr.1
  · simp only [Expect.ty, Option.some.injEq] at ht; subst ht; exact hr.2.2.2 o ho

theorem stepIn_ok {s : State v} {b : Bind} {n : Nat} {l : Line} {r : Result v} {ids : List IdV}
    {es : List (Expect v)} (h : stepIn T v s b n l = .ok (r, ids, es)) :
    ∃ x a, r = step T v s x ∧ es = expects v a r := by
  unfold stepIn at h
  split at h
  · cases h
  · rename_i input answerTo ids' _
    dsimp only at h
    split at h
    · cases h
    · cases h; exact ⟨input, answerTo, rfl, rfl⟩

variable {T v} {I : State v → Prop} (hI : ∀ s x, I s → I (step T v s x).state ∧ OutComparable v (step T v s x))
include hI

-- One mutual block proves the theorems together; `windowFrom_sound` passes the invariant on without using it.
set_option linter.unusedSectionVars false in
mutual
/-- A passed verdict reads the trace as the spec, from a state of an invariant `I` whose steps' out lines carry values
of comparable types: some binding the blocks hold possible reads it from any binding that names the blocks' keys as
it does. -/
theorem readFrom_sound : (lines : List (Nat × Line)) → (fuel : Nat) → (s : State v) → I s → (C : Cands) → C.Ok →
    (readFrom T v fuel s C lines).1 = .passed → ∃ β, C.Has β ∧ ∀ b, Agrees b β C → Reads T v s b lines
  | [], _, s, _, C, hC, _ => by
    obtain ⟨β, hβ⟩ := hC.exists_has
    exact ⟨β, hβ, fun b _ => .nil s b⟩
  | (n, l) :: more, fuel, s, hs, C, hC, h => by
    unfold readFrom at h
    split at h
    · rename_i nm bl hu
      obtain ⟨-, hbl, hnb, h2⟩ := undecidedIn_some hu
      obtain ⟨⟨k, hk⟩, -, fuel', h'⟩ := tryAll_sound (by simp) _ _ h
      obtain ⟨hok, hkeys, -⟩ := Cands.narrow_ok hC hbl hk hnb
      obtain ⟨β, hβ, hr⟩ := readFrom_sound ((n, l) :: more) fuel' s hs (C.narrow k nm) hok h'
      exact ⟨β, ((Cands.narrow_has hC hbl hk hnb).1 hβ).1,
        fun b ha => hr b (Cands.agrees_keys (fun x => hkeys.mem_iff.symm) ha)⟩
    · rename_i hu
      split at h
      · rename_i e he
        have := stepIn_error he
        simp only at h; subst h; cases this
      · rename_i r ids es hstep
        dsimp only at h
        split at h
        · cases h
        · rename_i ets hets
          obtain ⟨R, hR, fuel', h'⟩ := tryAll_sound (by simp) _ _ h
          split at h'
          · rename_i C₁ hC₁
            have hC₀ := Cands.outside_ok ids hC
            obtain ⟨hok₁, hsub₁, hkeys₁, hnames₁, -⟩ := Cands.addNew_ok (β := fun _ => default) hC₀.1 hC₁
            obtain ⟨x, a, hrx, hes⟩ := stepIn_ok T v hstep
            have hIr := hI s x hs
            rw [← hrx] at hIr
            obtain ⟨β, hβ, hsame, hr⟩ := windowFrom_sound fuel' n _ r.state hIr.1 C₁ ets R (afterWindow more) h'
              (by simp) hok₁ (fun k hk => (hkeys₁ k).2 (.inr hk)) (fun x hx => (hnames₁ x).2 (.inr hx))
            have hβ₀ : (C.outside ids).Has β := fun bl hbl => hβ bl (hsub₁ bl hbl)
            have hβC : C.Has β := fun bl hbl => hβ₀ bl (hC₀.2.1 bl hbl)
            refine ⟨β, hβC, fun b ha => ?_⟩
            have hst : stepIn T v s b n l = stepIn T v s C.bind n l := by
              unfold stepIn
              rw [readIn_congr T v (fun x hx => Cands.id?_bind hC hβC ha fun hxC => Cands.undecidedIn_none hC hu hx hxC)
                (fun to hto => Cands.wire?_bind hC hβC ha fun hC' => Cands.undecidedIn_none hC hu hto hC')]
            have ha₀ := Cands.outside_agrees ids hC hβ₀ ha
            have ha₁ : Agrees (Cands.bindOf β C₁) β C₁ := Cands.bindOf_agrees
            have hks : ∀ k, k ∈ C₁.keys ↔ k ∈ (C.outside ids).keys ∨ k ∈ es.flatMap (Expect.keys T v r.state.now) :=
              fun k => by rw [← leavess_ets hets]; exact hkeys₁ k
            have hg := Cands.grows_of hok₁ hβ ha₀ ha₁ hks
            refine .cons (hst.trans hstep) hg ?_ (hr _ ha₁)
            refine Multi.imp_mem (fun e he l _ hw => lineW_of_treeW hg.one
              (fun k hk => hg.covers k (List.mem_flatMap.2 ⟨e, he, hk⟩)) (expects_comparable v hIr.2 a e (hes ▸ he))
              (treeW_congr (fun k hk => ?_) hw)) (readings_sound hR hets (same_bag_map.1 hsame))
            exact (Cands.name_eq hok₁ hβ ha₁ ((hks k).2 (.inr (List.mem_flatMap.2 ⟨e, he, hk⟩)))).symm
          · cases h'
termination_by lines _ _ _ C => (lines.length, 1, C.weight)
decreasing_by
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Cands.narrow_lt hbl hk h2))
  · have := afterWindow_length more
    simp only [List.length_cons]
    rcases Nat.lt_or_eq_of_le this with h | h
    · exact Prod.Lex.left _ _ (by omega)
    · rw [h]; exact Prod.Lex.left _ _ (by omega)
theorem windowFrom_sound : (fuel n : Nat) → (fail : Verdict) → (s : State v) → I s → (C : Cands) →
    (ets : List (Tree Key)) → (R : List (Tree Name)) → (rest : List (Nat × Line)) →
    (windowFrom T v fuel n fail s C ets R rest).1 = .passed → fail ≠ .passed → C.Ok →
    (∀ k ∈ Tree.leavess ets, k ∈ C.keys) → (∀ x ∈ Tree.leavess R, x ∈ C.names) →
    ∃ β, C.Has β ∧ Tree.Same ((Tree.bag ets).map β) (Tree.bag R) ∧ ∀ b, Agrees b β C → Reads T v s b rest
  | fuel, n, fail, s, hs, C, ets, R, rest, h, hf, hC, hes, hRs => by
    unfold windowFrom at h
    split at h
    · rename_i C' hw
      obtain ⟨hok, hk, -, -⟩ := Cands.window_done (β := fun _ => default) hC hes hRs hw
      obtain ⟨β, hβ, hr⟩ := readFrom_sound rest fuel s hs C' hok h
      obtain ⟨h1, h2⟩ := ((Cands.window_done (β := β) hC hes hRs hw).2.2.2).1 hβ
      exact ⟨β, h1, h2, fun b ha => hr b (Cands.agrees_keys (fun x => hk.mem_iff.symm) ha)⟩
    · exact absurd h hf
    · rename_i k bl hw
      obtain ⟨hbl, hkb, h2⟩ := Cands.window_decide hw
      obtain ⟨⟨nm, hnm⟩, -, fuel', h'⟩ := tryAll_sound hf _ _ h
      obtain ⟨hok, hkeys, hnames⟩ := Cands.narrow_ok hC hbl hkb hnm
      obtain ⟨β, hβ, hs', hr⟩ := windowFrom_sound fuel' n fail s hs (C.narrow k nm) ets R rest h' hf hok
        (fun x hx => hkeys.mem_iff.2 (hes x hx)) (fun x hx => hnames.mem_iff.2 (hRs x hx))
      exact ⟨β, ((Cands.narrow_has hC hbl hkb hnm).1 hβ).1, hs',
        fun b ha => hr b (Cands.agrees_keys (fun x => hkeys.mem_iff.symm) ha)⟩
termination_by _ _ _ _ _ C _ _ rest => (rest.length, 2, C.weight)
decreasing_by
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Cands.narrow_lt hbl hkb h2))
end

end

theorem Bind.name_inj {b : Bind} (h : b.OneToOne) {a c : Key} (ha : b.Binds a) (hc : b.Binds c)
    (he : b.name a = b.name c) : a = c := by
  cases a with
  | id x =>
    cases c with
    | id y =>
      obtain ⟨t, ht⟩ := ha; obtain ⟨t', ht'⟩ := hc
      rw [Bind.name_id h ht, Bind.name_id h ht'] at he
      cases he; rw [h.idNames x y t ht ht']
    | wire _ => simp [Bind.name] at he
  | wire n =>
    cases c with
    | wire m =>
      obtain ⟨t, ht⟩ := ha; obtain ⟨t', ht'⟩ := hc
      rw [Bind.name_wire h ht, Bind.name_wire h ht'] at he
      cases he; rw [h.wireNames n m t ht ht']
    | id _ => simp [Bind.name] at he

theorem Bind.binds_of_agrees {b : Bind} {β : Key → Name} {C : Cands} (hC : C.Ok) (h : C.Has β) (ha : Agrees b β C)
    {k : Key} (hk : k ∈ C.keys) : b.Binds k := by
  cases k with
  | id x => obtain ⟨t, ht⟩ := h.id hC hk; exact ⟨t, (ha.1 x t).2 ⟨hk, ht⟩⟩
  | wire n => obtain ⟨t, ht⟩ := h.wire hC hk; exact ⟨t, (ha.2 n t).2 ⟨hk, ht⟩⟩

theorem Bind.binds_mono {b b' : Bind} (hi : ∀ p ∈ b.ids, p ∈ b'.ids) (hw : ∀ p ∈ b.wires, p ∈ b'.wires) {k : Key}
    (h : b.Binds k) : b'.Binds k := by
  cases k with
  | id x => obtain ⟨t, ht⟩ := h; exact ⟨t, hi _ ht⟩
  | wire n => obtain ⟨t, ht⟩ := h; exact ⟨t, hw _ ht⟩

section
variable (T : List TypeDecl) (v : ServiceV)

/-- Where a binding reads a window and the lines after it, verify settles on the window. -/
theorem windowFrom_complete {fail : Verdict} {n : Nat} {s : State v} {b' : Bind} {rest : List (Nat × Line)}
    {ets : List (Tree Key)} {R : List (Tree Name)}
    (ih : ∀ C β, C.Ok → C.Has β → Agrees b' β C → ∀ fuel, (readFrom T v fuel s C rest).1.settled = true) :
    ∀ (w : Nat) (C : Cands) (β : Key → Name), C.weight = w → C.Ok → C.Has β → Agrees b' β C →
    (∀ k ∈ Tree.leavess ets, k ∈ C.keys) → (∀ x ∈ Tree.leavess R, x ∈ C.names) →
    Tree.Same ((Tree.bag ets).map β) (Tree.bag R) →
    ∀ fuel, (windowFrom T v fuel n fail s C ets R rest).1.settled = true := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w iw =>
  intro C β hw hC hβ ha hes hRs hs fuel
  rcases Cands.window_complete hC hes hRs hβ hs with ⟨C', hC', hβ'⟩ | ⟨k, bl, hd, hbl, hkb⟩
  · unfold windowFrom
    split
    · rename_i C'' heq
      rw [hC'] at heq; cases heq
      obtain ⟨hok, hk, -, -⟩ := Cands.window_done (β := β) hC hes hRs hC'
      exact ih C' β hok hβ' (Cands.agrees_keys (fun x => hk.mem_iff.symm) ha) fuel
    · rename_i heq; rw [hC'] at heq; cases heq
    · rename_i heq; rw [hC'] at heq; cases heq
  · obtain ⟨-, -, h2⟩ := Cands.window_decide hd
    have hnm : β k ∈ bl.2 := (hβ bl hbl).mem_iff.1 (List.mem_map_of_mem hkb)
    obtain ⟨hok, hkeys, hnames⟩ := Cands.narrow_ok hC hbl hkb hnm
    have hsub := fun fuel => iw _ (hw ▸ Cands.narrow_lt hbl hkb h2) (C.narrow k (β k)) β rfl hok
      ((Cands.narrow_has hC hbl hkb hnm).2 ⟨hβ, rfl⟩) (Cands.agrees_keys (fun x => hkeys.mem_iff.symm) ha)
      (fun x hx => hkeys.mem_iff.2 (hes x hx)) (fun x hx => hnames.mem_iff.2 (hRs x hx)) hs fuel
    unfold windowFrom
    split
    · rename_i heq; rw [hd] at heq; cases heq
    · rename_i heq; rw [hd] at heq; cases heq
    · rename_i k' bl' heq
      rw [hd] at heq; cases heq
      exact tryAll_complete (a := ⟨β k, hnm⟩) hsub _ (List.mem_attach _ _) fuel

/-- A trace that reads as the spec is passed, unless the tries run out first. -/
theorem readFrom_complete {s : State v} {b : Bind} {lines : List (Nat × Line)} (h : Reads T v s b lines) :
    ∀ C β, C.Ok → C.Has β → Agrees b β C → ∀ fuel, (readFrom T v fuel s C lines).1.settled = true := by
  induction h with
  | nil => intro _ _ _ _ _ _; simp [readFrom, Verdict.settled]
  | @cons s b b' n l more r ids es hstep hgrow hm _ ih =>
    suffices key : ∀ w C β, C.weight = w → C.Ok → C.Has β → Agrees b β C →
        ∀ fuel, (readFrom T v fuel s C ((n, l) :: more)).1.settled = true from
      fun C β hC hβ ha fuel => key _ C β rfl hC hβ ha fuel
    intro w
    induction w using Nat.strongRecOn with
    | _ w iw =>
    intro C β hw hC hβ ha fuel
    unfold readFrom
    split
    · rename_i nm bl hu
      obtain ⟨-, hbl, hnb, h2⟩ := undecidedIn_some hu
      obtain ⟨k, hk, hkn⟩ := List.mem_map.1 ((hβ bl hbl).mem_iff.2 hnb)
      obtain ⟨hok, hkeys, -⟩ := Cands.narrow_ok hC hbl hk hnb
      exact tryAll_complete (a := ⟨k, hk⟩) (fun fuel => iw _ (hw ▸ Cands.narrow_lt hbl hk h2) _ β rfl hok
        ((Cands.narrow_has hC hbl hk hnb).2 ⟨hβ, hkn⟩) (Cands.agrees_keys (fun x => hkeys.mem_iff.symm) ha) fuel)
        _ (List.mem_attach _ _) fuel
    · rename_i hu
      have hst : stepIn T v s C.bind n l = .ok (r, ids, es) := by
        rw [← hstep]; unfold stepIn
        rw [readIn_congr T v (fun x hx => (Cands.id?_bind hC hβ ha fun hxC => Cands.undecidedIn_none hC hu hx hxC).symm)
          (fun to hto => (Cands.wire?_bind hC hβ ha fun hC' => Cands.undecidedIn_none hC hu hto hC').symm)]
      rw [hst]
      dsimp only
      have hone := hgrow.one
      have hsub := Bind.outside_sub b ids
      have hβ' : ∀ k ∈ C.keys, β k = b'.name k := by
        intro k hk
        cases k with
        | id x =>
          obtain ⟨t, ht⟩ := hβ.id hC hk
          rw [ht, Bind.name_id hone (hgrow.ids _ (hsub.1 _ ((ha.1 x t).2 ⟨hk, ht⟩)))]
        | wire m =>
          obtain ⟨t, ht⟩ := hβ.wire hC hk
          rw [ht, Bind.name_wire hone (hgrow.wires _ (hsub.2 ▸ (ha.2 m t).2 ⟨hk, ht⟩))]
      have hβC := Cands.Has.congr hβ' hβ
      have haC := Cands.agrees_congr hβ' ha
      have hβ₀ : (C.outside ids).Has b'.name :=
        Cands.outside_complete ids hC hβC haC fun p hp => Bind.name_id hone (hgrow.ids p hp)
      have hC₀ := Cands.outside_ok ids hC
      have ha₀ : Agrees (b.outside ids) b'.name (C.outside ids) := Cands.outside_agrees ids hC hβ₀ haC
      obtain ⟨ets, hets, R, hR, hsame⟩ := readings_complete (Multi.imp (fun _ _ h => treeW_of_lineW hone h) hm)
      rw [hets]
      dsimp only
      have hks := leavess_ets hets
      have hsame' := same_bag_map.2 hsame
      have hperm : (Tree.leavess ets).map b'.name |>.Perm (Tree.leavess R) := by
        have := hsame'.leaves
        simpa [Tree.leaves_map, Tree.leaves] using this
      have bindsC₀ : ∀ k ∈ (C.outside ids).keys, b'.Binds k := fun k hk =>
        Bind.binds_mono hgrow.ids hgrow.wires (Bind.binds_of_agrees hC₀.1 hβ₀ ha₀ hk)
      have bindsK : ∀ k ∈ Tree.leavess ets, b'.Binds k := fun k hk => hgrow.covers k (hks ▸ hk)
      obtain ⟨C₁, hC₁, hβ₁⟩ := Cands.addNew_complete hβ₀ (ks := Tree.leavess ets) (ns := Tree.leavess R)
        (fun a ha' c hc he => by
          have ba := (List.mem_append.1 ha').elim (bindsC₀ a) (bindsK a)
          have bc := (List.mem_append.1 hc).elim (bindsC₀ c) (bindsK c)
          exact Bind.name_inj hone ba bc he)
        (fun k hk => hperm.mem_iff.1 (List.mem_map_of_mem hk))
        (fun x hx => by
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hx)
          exact ⟨k, List.mem_append_right _ hk, rfl⟩)
        (fun k _ => by cases k <;> rfl)
      obtain ⟨hok₁, -, hkeys₁, -, -⟩ := Cands.addNew_ok (β := b'.name) hC₀.1 hC₁
      have hnames₁ := (Cands.addNew_ok (β := b'.name) hC₀.1 hC₁).2.2.2.1
      have ha₁ : Agrees b' b'.name C₁ := by
        have binds1 : ∀ k ∈ C₁.keys, b'.Binds k := fun k hk => ((hkeys₁ k).1 hk).elim (bindsC₀ k) (bindsK k)
        refine ⟨fun x t => ⟨fun hp => ⟨?_, Bind.name_id hone hp⟩, fun ⟨hk, he⟩ => ?_⟩,
          fun m t => ⟨fun hp => ⟨?_, Bind.name_wire hone hp⟩, fun ⟨hk, he⟩ => ?_⟩⟩
        · rcases hgrow.newIds _ hp with hp | hp
          · exact (hkeys₁ _).2 (.inl ((ha₀.1 x t).1 hp).1)
          · exact (hkeys₁ _).2 (.inr (hks ▸ hp))
        · obtain ⟨t', ht'⟩ := binds1 _ hk
          rw [Bind.name_id hone ht'] at he; cases he; exact ht'
        · rcases hgrow.newWires _ hp with hp | hp
          · exact (hkeys₁ _).2 (.inl ((ha₀.2 m t).1 hp).1)
          · exact (hkeys₁ _).2 (.inr (hks ▸ hp))
        · obtain ⟨t', ht'⟩ := binds1 _ hk
          rw [Bind.name_wire hone ht'] at he; cases he; exact ht'
      refine tryAll_complete (a := R) (fun fuel => ?_) _ hR fuel
      rw [hC₁]
      exact windowFrom_complete T v ih _ C₁ b'.name rfl hok₁ hβ₁ ha₁ (fun k hk => (hkeys₁ k).2 (.inr hk))
        (fun x hx => (hnames₁ x).2 (.inr hx)) hsame' fuel

/-- Verify's oracle comparison, for a service whose reachable states keep an invariant `I` under which every step's out
lines carry values of comparable types: unless it runs out of tries (`tryCap`), it reads a trace as passed exactly when
some binding reads it. -/
theorem replay_iff_of {I : State v → Prop} (hI : ∀ s x, I s → I (step T v s x).state ∧ OutComparable v (step T v s x))
    (h0 : I (State.init v)) (lines : List (Nat × Line)) (h : ∀ k, replay T v lines ≠ .limit k) :
    replay T v lines = .passed ↔ Reads T v (State.init v) {} lines := by
  have hok : Cands.Ok {} := ⟨by simp [Cands.keys], by simp [Cands.names], by simp, by simp⟩
  have hag : ∀ β, Agrees {} β {} := fun β => ⟨by simp [Cands.keys], by simp [Cands.keys]⟩
  refine ⟨fun hp => ?_, fun hr => ?_⟩
  · obtain ⟨β, -, hr⟩ := readFrom_sound hI lines _ _ h0 _ hok hp
    exact hr {} (hag β)
  · have := readFrom_complete T v hr {} (fun _ => default) hok (fun _ h => by simp at h) (hag _) tryCap
    unfold replay at h ⊢
    revert this h
    cases (readFrom T v tryCap (State.init v) {} lines).1 <;> simp [Verdict.settled]

end

end Tazuna.Trace
