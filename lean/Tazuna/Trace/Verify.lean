import Tazuna.Trace.Run

/-! Replaying a trace against the spec. Each in line runs as the spec's input; the out lines up to the next in line
form its window, which must equal the spec's out lines as a multiset. An implementation names its own ids and wire
ids: each binds to the spec's at its first appearance in an out line, and the binding stays one to one. An id an in
line names before any out line showed it is an id from outside the service, called by that name. -/

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

/-- The id an in line names: the one bound to the name, or else the outside id of that name. -/
def Bind.id? (b : Bind) (s : String) : Option IdV := some (((b.ids.find? (·.2 == s)).map (·.1)).getD (.named s))

/-- The binding with each outside id among `xs` called by its name. -/
def Bind.outside (b : Bind) (xs : List IdV) : Bind :=
  xs.foldl (fun b x => match x with
    | .named s => if b.ids.any (·.1 == x) then b else { b with ids := b.ids ++ [(x, s)] }
    | .fresh _ => b) b

def Bind.wire? (b : Bind) (s : String) : Option Nat := (b.wires.find? (·.2 == s)).map (·.1)

/-- Every way to match the values with the wire forms in order. -/
def seqMatch {α : Type} (f : α → Wire → Bind → List Bind) : List α → List Wire → Bind → List Bind
  | [], [], b => [b]
  | x :: xs, w :: ws, b => (f x w b).flatMap (seqMatch f xs ws)
  | _, _, _ => []

/-- Every way to match the values with the written items in some order: a multiset. -/
def bagMatch {α β : Type} (f : α → β → Bind → List Bind) : List α → List β → Bind → List Bind
  | [], [], b => [b]
  | x :: xs, ws, b => (List.range ws.length).flatMap fun i => match ws[i]? with
    | some w => (f x w b).flatMap (bagMatch f xs (ws.eraseIdx i))
    | none => []
  | _, _, _ => []

/-- Whether a Bool's or Nil's wire form is the one written. -/
def matchLiteral (expected : Option Wire) (w : Wire) (b : Bind) : List Bind :=
  match expected, w with
  | some (.bool x), .bool y => if x == y then [b] else []
  | some .null, .null => [b]
  | _, _ => []

section
variable (T : List TypeDecl)

mutual
/-- Every extension of the binding under which the wire form writes the value. -/
def matchVal : (t : Ty) → t.den0 → Wire → Bind → List Bind
  | .int, n, .num m, b => if @BEq.beq Int _ n m then [b] else []
  | .str, s, .str s', b => if @BEq.beq String _ s s' then [b] else []
  | .list t, xs, .arr ws, b => seqMatch (matchVal t) xs ws b
  | .bag t, xs, .arr ws, b => bagMatch (matchVal t) xs ws b
  | .tuple ts, x, .arr ws, b => matchs ts x ws b
  | .adt i _ vs, x, w, b =>
    if i = 0 then matchLiteral (encBool vs x) w b else if i = 1 then matchLiteral (encNil vs x) w b
    else match w with
      | .obj kvs => matchAlts ((T[i]?.map (·.variants)).getD []) kvs 0 vs x b
      | _ => []
  | .table k v, x, .arr ws, b => bagMatch (fun (p : k.den0 × v.den0) w b => match w with
      | .arr [wk, wv] => (matchVal k p.1 wk b).flatMap (matchVal v p.2 wv)
      | _ => []) x.1 ws b
  | .date, d, .str s, b => if renderDate? d == some s then [b] else []
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

/-- The out lines the spec expects of a step's result. -/
def expects (answerTo : Option String) (r : Result v) : List (Expect v) :=
  (answerTo.map fun to => [Expect.answered to r.outcome]).getD [] ++ r.events.map .applied ++
    r.out.map fun o => .sent o.id o.external o.name o.input

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

/-- An answer to a request, read from its wire form: a command's output or rejection, a query's output. -/
def decAnswer (b : Bind) (o : Ty) : (rj : Option Ty) → Except Wire Wire → Option (answerTy o rj).den0
  | some _, .ok w => (dec T b.id? o w).map fun x => .inl (x, ())
  | some j, .error w => (dec T b.id? j w).map fun x => .inr (.inl (x, ()))
  | none, .ok w => dec T b.id? o w
  | none, .error _ => none

/-- The input an in line writes, read with the binding so far, the id its answer names, and the ids it holds. -/
def readIn (s : State v) (b : Bind) : Line → Except String (Input v × Option String × List IdV)
  | .clock t => if t < s.now then .error "time moves back" else .ok (.clock t, none, [])
  | .request t id name c i => do
    if t != s.now then throw s!"the request is at {t}, but a clock line brought time only to {s.now}"
    let caller ← (dec T b.id? v.caller c).elim (.error "the caller does not read as the service's caller type") .ok
    match finIdx v.commands (·.name == name), finIdx v.queries (·.name == name) with
    | some k, _ => match dec T b.id? (v.commands.get k).input i with
      | some x => .ok (.command k caller x, some id, idsOf v.caller caller ++ idsOf _ x)
      | none => .error s!"the input does not read as {name}'s input type"
    | none, some k => match dec T b.id? (v.queries.get k).input i with
      | some x => .ok (.query k caller x, some id, idsOf v.caller caller ++ idsOf _ x)
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
      | some x => .ok (.answer id ⟨_, x⟩, none, idsOf _ x)
      | none => .error "the answer does not read as an answer to the request: an output, or a command's rejection"
  | .event t src name w => do
    if t != s.now then throw s!"the event is at {t}, but a clock line brought time only to {s.now}"
    let some k := finIdx v.subscribes fun sub => sub.source == src && sub.name == name
      | throw s!"{v.name} subscribes to no event {src}.{name}"
    match dec T b.id? (v.subscribes.get k).event w with
    | some x => .ok (.event k x, none, idsOf _ x)
    | none => .error s!"the event does not read as {src}.{name}'s type"
  | _ => .error "an out line where an in line belongs"

/-- Replays the lines after the header, each with its line number. -/
def replay (lines : List (Nat × Line)) : Verdict := Id.run do
  let mut s := State.init v
  let mut b : Bind := {}
  let mut rest := lines
  while true do
    match rest with
    | [] => return .passed
    | (n, l) :: more =>
      let window := more.takeWhile (!·.2.isIn)
      rest := more.drop window.length
      match readIn T v s b l with
      | .error m => return .invalid n m
      | .ok (input, answerTo, ids) =>
        b := b.outside ids
        let r := step T v s input
        if let .fault f := r.outcome then
          -- The trace names requests by its own ids, so a fault names the answer's request as the trace does.
          return .fault n (match f, l with
            | .answerUnmatched _, .answer _ to _ => .answerUnmatched to
            | f, _ => f)
        let es := expects v answerTo r
        let actual := window.map (·.2)
        match bagMatch (matchExpect T v r.state.now) es actual b with
        | b' :: _ => b := b'; s := r.state
        | [] => return .differs n ((es.filterMap (·.toLine T v r.state.now b)).map Line.toWire) (actual.map Line.toWire)
  return .passed

end

end Tazuna.Trace
