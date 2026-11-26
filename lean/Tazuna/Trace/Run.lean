import Tazuna.Semantics.Step
import Tazuna.Trace.Line

/-! Running a scenario: each step becomes one input line, the step runs, and its outputs become out lines. The trace
names fresh ids `id1`, `id2`, ... and the requests the service sends `r1`, `r2`, ... in the order they first appear,
so a snapshot shows what a reader can compare, not the engine's numbering. A scenario never names an id by text: a command step hands the steps after it the source its
new ids came from. -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

/-- The names a trace gives ids, one to one, each from its first appearance: an id from outside the service is called
by its own name, and a fresh id by the next `idK` that no other id is called and that is not `avoid`ed. The writer of
a run avoids every outside id's name its inputs hold before it starts (`traceOf`), so a fresh id's name never meets
an outside id the run names later (`Names.bind_ok`). -/
structure Names where
  ids : List (IdV × String) := []
  next : Nat := 1
  wires : List (Nat × String) := []
  avoid : List String := []

def Names.name (ns : Names) (x : IdV) : Option String := ns.ids.lookup x

def Names.taken (ns : Names) (s : String) : Bool := ns.ids.any (·.2 == s)

/-- Whether a fresh id may take the name: no id has it and it is not avoided. -/
def Names.free (ns : Names) (s : String) : Bool := !ns.taken s && !ns.avoid.contains s

/-- The name of the service's request with wire id `n`: `rK` for the `K`-th request the trace names. -/
def Names.wire (ns : Names) (n : Nat) : Names × String :=
  match ns.wires.lookup n with
  | some w => (ns, w)
  | none => let w := s!"r{ns.wires.length + 1}"; ({ ns with wires := ns.wires ++ [(n, w)] }, w)

/-- A name longer than every name taken or avoided, so free. -/
def Names.long (ns : Names) : String :=
  String.ofList (List.replicate ((ns.ids.map (·.2.length) ++ ns.avoid.map (·.length)).sum + 1) '0')

theorem le_sum_of_mem : {l : List Nat} → {a : Nat} → a ∈ l → a ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | _ :: _, _, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem Names.free_long (ns : Names) : ns.free ns.long = true := by
  have hlen : ∀ s ∈ ns.ids.map (·.2) ++ ns.avoid, s ≠ ns.long := fun s hs he => by
    have h1 : s.length ∈ ns.ids.map (·.2.length) ++ ns.avoid.map (·.length) := by
      simp only [List.mem_append, List.mem_map] at hs ⊢
      rcases hs with ⟨p, hp, rfl⟩ | hs
      · exact .inl ⟨p, hp, rfl⟩
      · exact .inr ⟨s, hs, rfl⟩
    have h2 := le_sum_of_mem h1
    rw [he] at h2
    simp [Names.long] at h2
    omega
  simp only [Names.free, Names.taken, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
  refine ⟨fun p hp he => hlen p.2 (List.mem_append_left _ (List.mem_map_of_mem hp)) he, ?_⟩
  cases h : ns.avoid.contains ns.long
  · rfl
  · exact absurd rfl (hlen _ (List.mem_append_right _ (List.elem_iff.1 h)))

-- Of the `ids.length + avoid.length + 1` candidates at most `ids.length + avoid.length` are taken or avoided, so
-- `long` stands in only where that count fails; it is free either way.
set_option linter.tazuna.silentDefault false in
/-- The name of the next fresh id, free by construction, and the counter after it: the first free `idK` from `next`
on. -/
def Names.freshName (ns : Names) : { s : String // ns.free s = true } × Nat :=
  match h : (List.range (ns.ids.length + ns.avoid.length + 1)).find? fun j => ns.free s!"id{ns.next + j}" with
  | some k => (⟨s!"id{ns.next + k}", by simpa using List.find?_some h⟩, ns.next + k + 1)
  | none => (⟨ns.long, ns.free_long⟩, ns.next)

/-- The names with the id `x` named, unless it has a name. An outside id whose name another id has stays unnamed, so a
value holding it has no wire form; a run's writer avoids every outside name of its inputs, so this never happens to
them (`Names.bind_ok`). -/
def Names.bindOne (ns : Names) (x : IdV) : Names :=
  if ns.ids.any (·.1 == x) then ns else match x with
    | .named s => if ns.taken s then ns else { ns with ids := ns.ids ++ [(x, s)] }
    | .fresh .. => { ns with ids := ns.ids ++ [(x, ns.freshName.1.1)], next := ns.freshName.2 }

def Names.bind (ns : Names) (xs : List IdV) : Names := xs.foldl Names.bindOne ns

/-- What the names keep: an id named by an avoided name is the outside id of that name, an outside id is named by its
own name, and no two ids share a name. -/
structure Names.Ok (ns : Names) : Prop where
  avoided : ∀ p ∈ ns.ids, ns.avoid.contains p.2 = true → p.1 = .named p.2
  named : ∀ s n, (IdV.named s, n) ∈ ns.ids → n = s
  nodup : (ns.ids.map (·.2)).Nodup

theorem Names.ok_avoid (avoid : List String) : ({ avoid } : Names).Ok :=
  ⟨nofun, nofun, .nil⟩

theorem lookup_of_any {x : IdV} : {l : List (IdV × String)} → l.any (·.1 == x) = true → (l.lookup x).isSome
  | [], h => by simp at h
  | (a, b) :: ps, h => by
    by_cases hx : x = a
    · subst hx; simp [List.lookup]
    · have hax : (x == a) = false := by simp [hx]
      simp only [List.any_cons] at h
      simp only [List.lookup, hax]
      exact lookup_of_any (by simpa [Ne.symm hx] using h)

theorem Names.not_taken {ns : Names} {s : String} (h : ns.taken s = false) : ∀ p ∈ ns.ids, p.2 ≠ s := by
  intro p hp he
  have : ns.taken s = true := List.any_eq_true.2 ⟨p, hp, by simp [he]⟩
  rw [h] at this; cases this

theorem Names.bindOne_ok {ns : Names} (h : ns.Ok) (x : IdV) : (ns.bindOne x).Ok ∧ (ns.bindOne x).avoid = ns.avoid ∧
    ∀ y n, ns.name y = some n → (ns.bindOne x).name y = some n := by
  have keep : ∀ (q : IdV × String), ∀ y n, ns.name y = some n → (ns.ids ++ [q]).lookup y = some n :=
    fun q y n hy => by rw [List.lookup_append]; simp [Names.name] at hy; simp [hy]
  unfold Names.bindOne
  split
  · exact ⟨h, rfl, fun _ _ hy => hy⟩
  · rename_i hx
    match x with
    | .named s =>
      dsimp only
      split
      · exact ⟨h, rfl, fun _ _ hy => hy⟩
      · rename_i ht
        refine ⟨⟨fun p hp ha => ?_, fun s' n hp => ?_, ?_⟩, rfl, keep _⟩
        · rcases List.mem_append.1 hp with hp | hp
          · exact h.avoided p hp ha
          · simp at hp; subst hp; rfl
        · rcases List.mem_append.1 hp with hp | hp
          · exact h.named s' n hp
          · simp at hp; obtain ⟨rfl, rfl⟩ := hp; rfl
        · simp only [List.map_append, List.map_cons, List.map_nil]
          refine List.nodup_append.2 ⟨h.nodup, List.nodup_cons.2 ⟨List.not_mem_nil, .nil⟩, fun a ha b hb => ?_⟩
          simp at hb; subst hb
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
          exact Names.not_taken (by simpa using ht) p hp
    | .fresh a b =>
      dsimp only
      have hf := ns.freshName.1.2
      simp only [Names.free, Bool.and_eq_true, Bool.not_eq_true'] at hf
      refine ⟨⟨fun p hp ha => ?_, fun s' n hp => ?_, ?_⟩, rfl, keep _⟩
      · rcases List.mem_append.1 hp with hp | hp
        · exact h.avoided p hp ha
        · simp at hp; subst hp; simp_all
      · rcases List.mem_append.1 hp with hp | hp
        · exact h.named s' n hp
        · simp at hp
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h.nodup, List.nodup_cons.2 ⟨List.not_mem_nil, .nil⟩, fun a ha b hb => ?_⟩
        simp at hb; subst hb
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
        exact Names.not_taken hf.1 p hp

theorem Names.bindOne_names {ns : Names} (h : ns.Ok) {x : IdV} (hx : ∀ s, x = .named s → ns.avoid.contains s = true) :
    ((ns.bindOne x).name x).isSome := by
  unfold Names.bindOne
  split
  · exact lookup_of_any (by assumption)
  · rename_i hn
    match x with
    | .named s =>
      dsimp only
      have ht : ns.taken s = false := by
        simp only [Names.taken, List.any_eq_false, beq_iff_eq]
        intro p hp he
        have hp' := h.avoided p hp (by rw [he]; exact hx s rfl)
        rw [he] at hp'
        apply hn
        exact List.any_eq_true.2 ⟨p, hp, by simp [hp']⟩
      simp only [ht]
      simp [Names.name, List.lookup_append, List.lookup]
    | .fresh a b =>
      dsimp only
      simp [Names.name, List.lookup_append, List.lookup]

/-- The names of a trace never fail an id and never mix fresh ids with outside ones: binding ids whose outside names
are all avoided keeps `Names.Ok` and names each of them, every fresh id by a name no avoided name is (so by none the
run's outside ids carry) and every outside id by its own name, no two alike; ids named before keep their names. -/
theorem Names.bind_ok {ns : Names} (h : ns.Ok) :
    (xs : List IdV) → (∀ s, .named s ∈ xs → ns.avoid.contains s = true) →
    (ns.bind xs).Ok ∧ (ns.bind xs).avoid = ns.avoid ∧ (∀ y n, ns.name y = some n → (ns.bind xs).name y = some n) ∧
      ∀ x ∈ xs, ((ns.bind xs).name x).isSome
  | [], _ => ⟨h, rfl, fun _ _ hy => hy, nofun⟩
  | x :: xs, hx => by
    obtain ⟨h1, ha1, hk1⟩ := Names.bindOne_ok h x
    have hn1 := Names.bindOne_names h (x := x) fun s hs => hx s (by rw [hs]; exact List.mem_cons_self)
    obtain ⟨h2, ha2, hk2, hn2⟩ := Names.bind_ok h1 xs fun s hs => ha1 ▸ hx s (List.mem_cons_of_mem _ hs)
    refine ⟨h2, ha2.trans ha1, fun y n hy => hk2 y n (hk1 y n hy), fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hn1
      show (((ns.bindOne _).bind xs).name _).isSome
      rw [hk2 _ n hn]; rfl
    · exact hn2 y hy

/-- The wire form of a value, naming the ids it holds first. -/
def Names.enc (ns : Names) (T : List TypeDecl) (t : Ty) (x : t.den0) : Names × Option Wire :=
  let ns := ns.bind (idsOf T t x)
  (ns, Trace.enc T ns.name t x)

/-- The wire form of an answer to a request: a command's output under `ok` and its rejection under `error`, a
query's output under `ok`. -/
def Names.answerWire (ns : Names) (T : List TypeDecl) (o : Ty) :
    (rj : Option Ty) → (answerTy o rj).den0 → Names × Option (Except Wire Wire)
  | some _, .inl (x, ()) => let (ns, w) := ns.enc T o x; (ns, w.map .ok)
  | some j, .inr (.inl (x, ())) => let (ns, w) := ns.enc T j x; (ns, w.map .error)
  | none, x => let (ns, w) := ns.enc T o x; (ns, w.map .ok)

/-- Why a scenario stopped before its end. -/
inductive Stop where
  /-- The spec faulted at step `step`. -/
  | fault (step : Nat) (f : Fault)
  /-- Step `step` cannot run: its answer matches no pending request or more than one, it waits a negative time, it
  sends a request the service does not list, or a value has no wire form. -/
  | badStep (step : Nat) (message : String)

def _root_.Tazuna.Ir.Sender.matches : Sender → Sender → Bool
  | .machine n ⟨t, k⟩, .machine n' ⟨t', k'⟩ =>
    n == n' && match Ty.same t t' with
      | some ⟨h⟩ => (Ty.semWith Dsl.base t').2 (h ▸ k) k'
      | none => false
  | .reaction n, .reaction n' => n == n'
  | _, _ => false

def finIdx {α : Type} (xs : List α) (p : α → Bool) : Option (Fin xs.length) :=
  (List.finRange xs.length).find? fun i => p (xs.get i)

section
variable (T : List TypeDecl) (v : ServiceV)

/-- The out lines of one step's result: the answer to a request (named by `answerTo`), each event applied, each
request sent. -/
def outLines (ns : Names) (answerTo : Option String) (r : Result v) : Names × Option (List Line) := Id.run do
  let mut ns := ns
  let mut lines : List Line := []
  let t := r.state.now
  if let some to := answerTo then
    let answer ← match r.outcome with
      | .accepted => pure (some Answer.accepted)
      | .answered ⟨ty, x⟩ => do let (ns', w) := ns.enc T ty x; ns := ns'; pure (w.map .answered)
      | .rejected ⟨ty, x⟩ => do let (ns', w) := ns.enc T ty x; ns := ns'; pure (w.map .rejected)
      | .invalid rules => pure (some (.invalid rules))
      | .fault _ => pure none
    match answer with
    | some a => lines := lines ++ [.answered t to a]
    | none => return (ns, none)
  for ev in r.events do
    let (ns', w) := ns.enc T v.event ev
    ns := ns'
    match w with
    | some w => lines := lines ++ [.applied t w]
    | none => return (ns, none)
  for o in r.out do
    let (ns', id) := ns.wire o.id
    let (ns', w) := ns'.enc T o.input.1 o.input.2
    ns := ns'
    match w with
    | some w => lines := lines ++ [.sent t id o.external o.name w]
    | none => return (ns, none)
  return (ns, some lines)

/-- What runs a scenario step needs between steps. -/
structure Run where
  state : State v
  names : Names := {}
  requests : Nat := 0
  lines : List Line := []

/-- Runs the input and appends its in lines and out lines. -/
def Run.finish' (run : Run v) (input : Input v) (inLines : List Line) (answerTo : Option String) (k : Nat) :
    Except Stop (Run v) := do
  let r := step T v run.state input
  if let .fault f := r.outcome then throw (.fault k f)
  let (ns, outs) := outLines T v run.names answerTo r
  let some outs := outs | throw (.badStep k "an output has no wire form")
  pure { run with state := r.state, names := ns, lines := run.lines ++ inLines ++ outs }

/-- One input, written as its in line, run, and its out lines: what scenarios and generate's traces share, so the two
cannot write an input differently. A request's id is the count of requests so far; an answer names the request by the
name the trace gave its wire id. -/
def Run.input (run : Run v) (k : Nat) : Input v → Except Stop (Run v)
  | .command i caller input => request (v.commands.get i).name (.command i caller input) caller ⟨_, input⟩
  | .query i caller input => request (v.queries.get i).name (.query i caller input) caller ⟨_, input⟩
  | .answer to ⟨ty, value⟩ => do
    let some p := run.state.pending.find? (·.id == to) | throw (.badStep k s!"no pending request has wire id {to}")
    let some ⟨h⟩ := Ty.same ty (answerTy p.request.output p.request.rejection)
      | throw (.badStep k s!"the answer's type is not the type of answers to {p.external}.{p.request.name}")
    let (ns, w) := run.names.wire p.id
    let (ns, a) := ns.answerWire T p.request.output p.request.rejection (h ▸ value)
    let some a := a | throw (.badStep k "the answer has no wire form")
    { run with names := ns }.finish' T v (.answer to ⟨ty, value⟩) [.answer run.state.now w a] none k
  | .event i value => do
    let sub := v.subscribes.get i
    let (ns, w) := run.names.enc T sub.event value
    let some w := w | throw (.badStep k "the event has no wire form")
    { run with names := ns }.finish' T v (.event i value) [.event run.state.now sub.source sub.name w] none k
  | .clock t => run.finish' T v (.clock t) [.clock t] none k
where
  request (name : String) (input : Input v) (caller : v.caller.den0) (value : WireVal) : Except Stop (Run v) := do
    let id := toString (run.requests + 1)
    let (ns, c) := run.names.enc T v.caller caller
    let (ns, i) := ns.enc T value.1 value.2
    let (some c, some i) := (c, i) | throw (.badStep k "the request has no wire form")
    { run with names := ns, requests := run.requests + 1 }.finish' T v input
      [.request run.state.now id name c i] (some id) k

/-- One scenario step: the input it names, through `Run.input`. -/
def Run.step (run : Run v) (k : Nat) : StepV v.records v.event v.caller → Except Stop (Run v)
  | .command x caller input _ => do
    let some i := finIdx v.commands fun c => c.name == x.name | throw (.badStep k s!"{v.name} lists no command {x.name}")
    let some ⟨h⟩ := Ty.same x.input (v.commands.get i).input | throw (.badStep k s!"{x.name} has another input type")
    run.input T v k (.command i caller (h ▸ input))
  | .query x caller input => do
    let some i := finIdx v.queries fun q => q.name == x.name | throw (.badStep k s!"{v.name} lists no query {x.name}")
    let some ⟨h⟩ := Ty.same x.input (v.queries.get i).input | throw (.badStep k s!"{x.name} has another input type")
    run.input T v k (.query i caller (h ▸ input))
  | .wait ms => do
    if ms < 0 then throw (.badStep k "a step waits a negative time")
    run.input T v k (.clock (run.state.now + ms))
  | .answer name input output rejection snd w => do
    let same (a b : Ty) := (Ty.same a b).isSome
    let ps := run.state.pending.filter fun p =>
      p.request.name == name && same p.request.input input && same p.request.output output &&
        (match p.request.rejection, rejection with
          | some a, some b => same a b
          | none, none => true
          | _, _ => false) && p.sender.matches snd
    let [p] := ps | throw (.badStep k s!"{ps.length} pending requests to {name} match the sender")
    run.input T v k (.answer p.id w)
  | .event name ⟨ty, x⟩ => do
    let some i := finIdx v.subscribes fun sub => sub.name == name && (Ty.same ty sub.event).isSome
      | throw (.badStep k s!"{v.name} subscribes to no source {name} of this event type")
    let some ⟨h⟩ := Ty.same ty (v.subscribes.get i).event | throw (.badStep k s!"{name} has another type")
    run.input T v k (.event i (h ▸ x))

end

/-- The header line of a trace of `service`. -/
def header (service : String) : Wire := .obj [("trace", .num 1), ("service", .str service)]

/-- The service a header line names. -/
def headerService? : Wire → Option String
  | .obj kvs => match kvs.lookup "trace", kvs.lookup "service" with
    | some (.num 1), some (.str s) => some s
    | _, _ => none
  | _ => none

/-- A trace: the service its header names, and its lines after the header. -/
structure TraceFile where
  service : String
  lines : List Line

/-- The trace as its file holds it, one wire value per line: the header, then each line. -/
def TraceFile.wires (tr : TraceFile) : List Wire := header tr.service :: tr.lines.map Line.toWire

/-- The lines, each with its line number in the trace's file, where the header is line 1: as verify numbers them. -/
def TraceFile.numbered (tr : TraceFile) : List (Nat × Line) := tr.lines.zipIdx.map fun (l, k) => (k + 2, l)

/-- Reading a trace's wire values back gives what was written: the header names its service, and every line after it
reads as itself (`Line.ofWire_toWire`). Between the wire values and the file's text stands only Lean's JSON printer
and parser. -/
theorem TraceFile.read_wires (tr : TraceFile) :
    tr.wires = header tr.service :: tr.lines.map Line.toWire ∧ headerService? (header tr.service) = some tr.service ∧
      (tr.lines.map Line.toWire).mapM Line.ofWire = some tr.lines := by
  refine ⟨rfl, by simp [headerService?, header, List.lookup], ?_⟩
  induction tr.lines with
  | nil => rfl
  | cons l ls ih => simp [List.mapM_cons, Line.ofWire_toWire, ih]

/-- The ids an input carries, in the order its in line writes them. -/
def _root_.Tazuna.Ir.Input.ids (T : List TypeDecl) {v : ServiceV} : Input v → List IdV
  | .command i caller input => idsOf T v.caller caller ++ idsOf T (v.commands.get i).input input
  | .query i caller input => idsOf T v.caller caller ++ idsOf T (v.queries.get i).input input
  | .answer _ ⟨t, value⟩ => idsOf T t value
  | .event i value => idsOf T (v.subscribes.get i).event value
  | .clock _ => []

/-- The names of the outside ids the inputs carry. -/
def outsideNames (T : List TypeDecl) {v : ServiceV} (xs : List (Input v)) : List String :=
  xs.flatMap fun x => (x.ids T).filterMap fun | .named s => some s | .fresh .. => none

/-- The trace of a run of the inputs from the initial state: what generate writes, in the format of snapshots, or why
a step stopped. Its names avoid every outside id's name the inputs carry, so a fresh id is never called like an
outside id the run names later (`Names.bind_ok`). -/
def traceOf (T : List TypeDecl) (v : ServiceV) (xs : List (Input v)) : Except Stop TraceFile := do
  let (run, _) ← xs.foldlM (fun (run, k) x => do pure (← run.input T v (k + 1) x, k + 1))
    (({ state := State.init v, names := { avoid := outsideNames T xs } } : Run v), 0)
  pure ⟨v.name, run.lines⟩

instance : Inhabited Stop := ⟨.badStep 0 ""⟩

/-- Runs the steps in order, numbering them from `k + 1`; the steps a command hands on run right after it. A
continuation is a function the spec wrote, so nothing bounds how deep it nests and the run is `partial`. -/
partial def runSteps (T : List TypeDecl) (v : ServiceV) (run : Run v) (k : Nat) :
    List (StepV v.records v.event v.caller) → Except Stop (Run v × Nat)
  | [] => pure (run, k)
  | st :: rest => do
    let fresh := run.state.fresh
    let run ← run.step T v (k + 1) st
    match st with
    | .command _ _ _ next =>
      let (run, k) ← runSteps T v run (k + 1) (next fresh)
      runSteps T v run k rest
    | _ => runSteps T v run (k + 1) rest

/-- The trace of a scenario, or why it stopped. -/
def runScenario (T : List TypeDecl) (v : ServiceV) (steps : List (StepV v.records v.event v.caller)) :
    Except Stop TraceFile := do
  let (run, _) ← runSteps T v ({ state := State.init v } : Run v) 0 steps
  pure ⟨v.name, run.lines⟩

end Tazuna.Trace
