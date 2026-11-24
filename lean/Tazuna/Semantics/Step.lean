import Tazuna.Semantics.Eval
import Tazuna.Semantics.Order
import Tazuna.Semantics.Rules

/-! The step semantics of one service. A step takes one input line and yields exactly one outcome, the events it
applied, the out lines and the next state. Inside a step the cascade runs to completion: each event is applied, then
every machine instance and reaction reacts to it, in a fixed canonical order (machines and reactions in declaration
order, a machine's instances in the canonical order of their keys, `Tazuna.Semantics.Order`, so the order is a
function of the keys alone, never of how a bag stores them or of when an instance started). A request to an external goes out at once, to the external
that lists what it asks for; a command or
query of the service's own waits in a queue and runs in turn as one internal step, and the cascade bound limits how
many internal steps one input takes. Timers fire only on clock lines. Out lines and pending requests form multisets:
the canonical order fixes how the step computes them, and no outcome depends on their order. -/

namespace Tazuna.Ir

namespace Step

def toB : Ty.bool.den0 → Bool
  | .inl _ => true
  | .inr _ => false

/-- The names of the rules that do not hold. -/
def broken (xs : Ty.rules.den0) : List String := xs.filterMap fun (n, b, ()) => if toB b then none else some n

/-- One live machine instance: its key, its state and the timer it waits for (the deadline and the state it enters). -/
structure Instance {r e : Ty} (m : MachineV r e) where
  key : m.key.den0
  state : m.state.den0
  timer : Option (Int × m.state.den0)

/-- A machine with its live instances, in the canonical order of their keys. -/
abbrev MachineState (r e : Ty) := (m : MachineV r e) × List (Instance m)

/-- An out line: a request to an external, with the wire id its answer names in `to`. -/
structure OutLine where
  id : Nat
  external : String
  name : String
  input : WireVal

/-- A multiset: two values are the same when one is a permutation of the other. -/
abbrev Bag (α : Type) := List α

/-- A request sent and not yet answered, to the external that lists what it asks for. -/
structure Pending (e : Ty) where
  id : Nat
  sender : Sender
  external : String
  request : RequestV e

end Step

open Step

/-- What a service is between two inputs. -/
structure State (v : ServiceV) where
  records : v.records.den0
  machines : List (MachineState v.records v.event)
  /-- Requests sent and not yet answered: a multiset. -/
  pending : Bag (Pending v.event)
  now : Int
  /-- The counter `fresh` builds ids from; every command step advances it. -/
  fresh : Nat
  /-- The next wire id. -/
  nextId : Nat

/-- One input line, typed by the service it goes to. -/
inductive Input (v : ServiceV) where
  | command (i : Fin v.commands.length) (caller : v.caller.den0) (input : (v.commands.get i).input.den0)
  | query (i : Fin v.queries.length) (caller : v.caller.den0) (input : (v.queries.get i).input.den0)
  /-- The answer to the request whose wire id is `to`: an output or a rejection, of the types the request names. -/
  | answer (to : Nat) (value : WireVal)
  | event (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
  | clock (time : Int)

/-- A step that cannot happen in a correct spec. -/
inductive Fault where
  /-- A service or machine invariant is broken after the step. -/
  | invariant (name : String)
  /-- A command's `ensures` rule is broken once its events are applied. -/
  | ensures (name : String)
  /-- The step took more internal steps than `bounds.cascade`. -/
  | cascadeLimit
  /-- An answer names no pending request, or not with the types that request has. `to` is the name the input gave
  the request. -/
  | answerUnmatched (to : String)
  /-- An effect asked for what its target does not accept: a command or query of the service's own that was Invalid
  (the rules broken, as Invalid names them) or that the service does not list (`service`), or an external's command
  or query that no external of the spec lists with these types (`declared`). -/
  | invalidEffect (name : String) (rules : List String)

inductive Outcome where
  | accepted
  | answered (output : WireVal)
  | rejected (rejection : WireVal)
  | invalid (rules : List String)
  | fault (f : Fault)

def Outcome.summary : Outcome → String
  | .accepted => "accepted"
  | .answered _ => "answered"
  | .rejected _ => "rejected"
  | .invalid rs => s!"invalid {rs}"
  | .fault (.invariant n) => s!"fault invariant {n}"
  | .fault (.ensures n) => s!"fault ensures {n}"
  | .fault .cascadeLimit => "fault cascadeLimit"
  | .fault (.answerUnmatched n) => s!"fault answerUnmatched {n}"
  | .fault (.invalidEffect n rs) => s!"fault invalidEffect {n} {rs}"

/-- What one step yields: the next state, the outcome, every event it applied in order, and the out lines. -/
structure Result (v : ServiceV) where
  state : State v
  outcome : Outcome
  events : List v.event.den0
  out : Bag OutLine

namespace Step

variable {v : ServiceV}

def State.init (v : ServiceV) : State v :=
  { records := v.init, machines := v.machines.map (⟨·, []⟩), pending := [], now := 0, fresh := 0, nextId := 0 }

/-- An instance entering `st`: its timer and its effect. -/
def enter {r e : Ty} (m : MachineV r e) (records : r.den0) (now : Int) (key : m.key.den0) (st : m.state.den0) :
    Instance m × List (Sender × EffectV e) :=
  let timer := match m.after.fn (.inl (key, st, records, now, ()), ()) with
    | .inl (.inl (d, target, ()), ()) => some (now + (show Int from d), target)
    | _ => none
  (⟨key, st, timer⟩, (m.effectAt key st records now).toList.map (.machine m.name ⟨m.key, key⟩, ·))

variable (T : List TypeDecl)

/-- A machine after an event: instances whose key left go, and in the canonical order of the keys each other key's
instance reacts with `on` or, when the key is new, starts at `initial`. The instances stay in that order. -/
def machineStep {r e : Ty} (records : r.den0) (now : Int) (ev : e.den0) : MachineState r e →
    MachineState r e × List (Sender × EffectV e)
  | ⟨m, insts⟩ =>
    let eqK := (Ty.semWith Dsl.base m.key).2
    let keys := Ty.sortBy T m.key (dedupBy eqK (m.instances.fn (records, ())))
    let (insts, effs) := keys.foldl (fun (acc, effs) k =>
      match insts.find? (eqK k ·.key) with
      | some i => match m.on.fn (.inl (i.key, i.state, records, now, ()), ev, ()) with
        | .inr (.inl (s, ())) => let (i', es) := enter m records now i.key s; (acc ++ [i'], effs ++ es)
        | _ => (acc ++ [i], effs)
      | none => let (i, es) := enter m records now k m.initial; (acc ++ [i], effs ++ es)) ([], [])
    (⟨m, insts⟩, effs)

/-- One event: apply it, then let every machine and reaction react. -/
def react (s : State v) (ev : v.event.den0) : State v × List (Sender × EffectV v.event) :=
  let records := v.apply.fn (s.records, ev, ())
  let (machines, effs) := s.machines.foldl (fun (ms, effs) ms0 =>
    let (m', es) := machineStep T records s.now ev ms0; (ms ++ [m'], effs ++ es)) ([], [])
  let effs := effs ++ v.reactions.flatMap fun x => (x.effectsAt ev records s.now).map (.reaction x.name, ·)
  ({ s with records, machines }, effs)

/-- The broken invariants of the service and of every machine instance. -/
def invariants (s : State v) : List String :=
  broken (v.invariants.fn (s.records, ())) ++
    s.machines.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => broken (m.invariants.fn (.inl (i.key, i.state, s.records, s.now, ()), ()))

/-- A step in progress: the state, the events applied and the out lines so far, and the own commands and queries
waiting to run. -/
structure Acc (v : ServiceV) where
  state : State v
  events : List v.event.den0 := []
  out : Bag OutLine := []
  own : List (EffectV v.event) := []

/-- The external that lists the command or query a request asks for, with its types. -/
def _root_.Tazuna.Ir.RequestV.ownerIn {e : Ty} (r : RequestV e) (ds : List (String × DeclaredV)) : Option String :=
  let same (a b : Ty) := (Ty.same a b).isSome
  (ds.find? fun (_, d) => match d, r.rejection with
    | .externalCommand n i o j, some j' => n == r.name && same i r.input && same o r.output && same j j'
    | .externalQuery n i o _, none => n == r.name && same i r.input && same o r.output
    | _, _ => false).map (·.1)

/-- Starts effects in order: a request to an external goes out with a fresh wire id; an own command or query waits. -/
def start (a : Acc v) (effs : List (Sender × EffectV v.event)) : Except Fault (Acc v) :=
  effs.foldlM (fun a (snd, eff) => match eff with
    | .request r => match r.ownerIn v.declared with
      | none => .error (.invalidEffect r.name ["declared"])
      | some x =>
        let s := a.state
        .ok { a with state := { s with pending := s.pending ++ [⟨s.nextId, snd, x, r⟩], nextId := s.nextId + 1 },
                     out := a.out ++ [⟨s.nextId, x, r.name, ⟨r.input, r.value⟩⟩] }
    | own => .ok { a with own := a.own ++ [own] }) a

/-- Applies the events in order, each followed by every machine's and reaction's reaction. -/
def applyEvents (a : Acc v) (events : List v.event.den0) : Except Fault (Acc v) :=
  events.foldlM (fun a ev =>
    let (s, effs) := react T a.state ev
    start { a with state := s, events := a.events ++ [ev] } effs) a

def ctx {r i c : Ty} (s : State v) (records : r.den0) (caller : c.den0) (input : i.den0) : (Ty.ctx r i c).den0 :=
  .inl (records, input, caller, s.now, s.fresh, ())

/-- Why a request is Invalid: a caller it does not list, or the input's broken `accepts` rules. -/
def admit {i : Ty} (callers : List v.caller.den0) (accepts : Fun (Ty.fn [i] Ty.rules)) (caller : v.caller.den0)
    (input : i.den0) : List String :=
  if callers.any ((Ty.semWith Dsl.base v.caller).2 caller) then broken (accepts.fn (input, ())) else ["callers"]

def okNil {j : Ty} : (Ty.result Ty.nil j).den0 := .inl (.inl (), ())

/-- Runs an own command as an internal step: its events are applied and its `ensures` checked, then its answer's
events are applied. -/
def runCommand (a : Acc v) (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) : Except Fault (Acc v) :=
  match admit x.callers x.accepts caller input with
  | r :: rs => .error (.invalidEffect x.name (r :: rs))
  | [] => do
    let cx := ctx a.state a.state.records caller input
    let a := { a with state := { a.state with fresh := a.state.fresh + 1 } }
    match x.decide.fn (cx, ()) with
    | .inl (events, ()) =>
      let a ← applyEvents T a events
      match broken (x.ensures.fn (cx, a.state.records, ())) with
      | n :: _ => .error (.ensures n)
      | [] => applyEvents T a (onAnswer.fn (okNil, ()))
    | .inr (.inl (j, ())) => applyEvents T a (onAnswer.fn (.inr (.inl (j, ())), ()))

/-- Runs an own query as an internal step: its answer's events are applied. -/
def runQuery (a : Acc v) (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [x.output] (.list v.event))) : Except Fault (Acc v) :=
  match admit x.callers x.accepts caller input with
  | r :: rs => .error (.invalidEffect x.name (r :: rs))
  | [] => applyEvents T a (onAnswer.fn (x.resolve.fn (ctx a.state a.state.records caller input, ()), ()))

/-- The command the service lists by the name and types an effect gives. -/
def ownCommand (name : String) (i j : Ty) :
    Option ((x : CommandV v.records v.event v.caller) ×' (i = x.input ∧ j = x.rejection)) :=
  v.commands.findSome? fun x => if x.name == name then
    match Ty.same i x.input, Ty.same j x.rejection with
    | some ⟨hi⟩, some ⟨hj⟩ => some ⟨x, hi, hj⟩
    | _, _ => none
  else none

/-- The query the service lists by the name and types an effect gives. -/
def ownQuery (name : String) (i o : Ty) : Option ((x : QueryV v.records v.caller) ×' (i = x.input ∧ o = x.output)) :=
  v.queries.findSome? fun x => if x.name == name then
    match Ty.same i x.input, Ty.same o x.output with
    | some ⟨hi⟩, some ⟨ho⟩ => some ⟨x, hi, ho⟩
    | _, _ => none
  else none

/-- Runs an own command or query: the one the service lists by the effect's name and types. -/
def runOwn (a : Acc v) : EffectV v.event → Except Fault (Acc v)
  | .request _ => .ok a
  | .command name c i j caller value onAnswer =>
    match Ty.same c v.caller, ownCommand (v := v) name i j with
    | some ⟨hc⟩, some ⟨x, hi, hj⟩ =>
      runCommand T a x (cast (congrArg Ty.den0 hc) caller) (cast (congrArg Ty.den0 hi) value) (hj ▸ onAnswer)
    | _, _ => .error (.invalidEffect name ["service"])
  | .query name c i o caller value onAnswer =>
    match Ty.same c v.caller, ownQuery (v := v) name i o with
    | some ⟨hc⟩, some ⟨x, hi, ho⟩ =>
      runQuery T a x (cast (congrArg Ty.den0 hc) caller) (cast (congrArg Ty.den0 hi) value) (ho ▸ onAnswer)
    | _, _ => .error (.invalidEffect name ["service"])

/-- Runs the waiting own commands and queries in order, one internal step each, until none waits; more than `fuel`
internal steps is a fault. -/
def settle : Nat → Acc v → Except Fault (Acc v)
  | fuel, a => match a.own, fuel with
    | [], _ => .ok a
    | _ :: _, 0 => .error .cascadeLimit
    | eff :: rest, f + 1 => do settle f (← runOwn T { a with own := rest } eff)

/-- Ends a step: runs what waits and checks the invariants. A fault leaves the state as `s0`. -/
def finish (s0 : State v) (a : Except Fault (Acc v)) (outcome : Outcome) : Result v :=
  match a >>= settle T v.bounds.cascade.toNat with
  | .error f => ⟨s0, .fault f, [], []⟩
  | .ok a => match invariants a.state with
    | n :: _ => ⟨s0, .fault (.invariant n), [], []⟩
    | [] => ⟨a.state, outcome, a.events, a.out⟩

/-- Fires the timers due at `now`, earliest deadline first, then machines in order and instances in key order. Entering a state
may start another due timer; the cascade bound limits how many fire. -/
def fire (s : State v) : (fuel : Nat) → Option (State v × List (Sender × EffectV v.event))
  | 0 => none
  | fuel + 1 =>
    let due := s.machines.flatMap fun ⟨_, insts⟩ => insts.filterMap fun i => i.timer.bind fun (d, _) =>
      if d ≤ s.now then some d else none
    match due.min? with
    | none => some (s, [])
    | some d =>
      let (machines, effs, _) := s.machines.foldl (fun (ms, effs, done) ⟨m, insts⟩ =>
        let (insts, effs, done) := insts.foldl (fun (acc, effs, done) i =>
          match done, i.timer with
          | false, some (d', target) =>
            if d' = d then let (i', es) := enter m s.records s.now i.key target; (acc ++ [i'], effs ++ es, true)
            else (acc ++ [i], effs, done)
          | _, _ => (acc ++ [i], effs, done)) ([], effs, done)
        (ms ++ [⟨m, insts⟩], effs, done)) ([], [], false)
      (fire { s with machines } fuel).map fun (s, es) => (s, effs ++ es)

end Step

open Step in
/-- The step: one input, exactly one outcome. A command's `ensures` is checked once its own events are applied,
before the own commands and queries they start run. -/
def step (T : List TypeDecl) (v : ServiceV) (s : State v) : Input v → Result v
  | .command i caller input =>
    let c := v.commands.get i
    let s' := { s with fresh := s.fresh + 1 }
    match admit c.callers c.accepts caller input with
    | r :: rs => ⟨s', .invalid (r :: rs), [], []⟩
    | [] =>
      let cx := ctx s s.records caller input
      match c.decide.fn (cx, ()) with
      | .inr (.inl (j, ())) => ⟨s', .rejected ⟨c.rejection, j⟩, [], []⟩
      | .inl (events, ()) =>
        match applyEvents T { state := s' } events with
        | .error f => ⟨s', .fault f, [], []⟩
        | .ok a => match broken (c.ensures.fn (cx, a.state.records, ())) with
          | n :: _ => ⟨s', .fault (.ensures n), [], []⟩
          | [] => finish T s' (.ok a) .accepted
  | .query i caller input =>
    let q := v.queries.get i
    match admit q.callers q.accepts caller input with
    | r :: rs => ⟨s, .invalid (r :: rs), [], []⟩
    | [] => ⟨s, .answered ⟨q.output, q.resolve.fn (ctx s s.records caller input, ())⟩, [], []⟩
  | .answer to ⟨t, value⟩ =>
    match s.pending.find? (·.id == to) with
    | none => ⟨s, .fault (.answerUnmatched (toString to)), [], []⟩
    | some p => match Ty.same t (answerTy p.request.output p.request.rejection) with
      | none => ⟨s, .fault (.answerUnmatched (toString to)), [], []⟩
      | some ⟨h⟩ => match broken (p.request.holds (h ▸ value)) with
        -- The external broke what its query ensures: the answer is refused and the request stays pending.
        | r :: rs => ⟨s, .invalid (r :: rs), [], []⟩
        | [] =>
          let s' := { s with pending := s.pending.filter (·.id != to) }
          finish T s (applyEvents T { state := s' } (p.request.onAnswer.fn (h ▸ value, ()))) .accepted
  | .event i value => finish T s (applyEvents T { state := s } [(v.subscribes.get i).wrap.fn (value, ())]) .accepted
  | .clock time =>
    if time < s.now then ⟨s, .invalid ["time moves forward"], [], []⟩ else
    match fire { s with now := time } (v.bounds.cascade.toNat + 1) with
    | none => ⟨s, .fault .cascadeLimit, [], []⟩
    | some (s', effs) => finish T s (start { state := s' } effs) .accepted

/-- Runs the inputs in order from `s`: the final state and every step's result. -/
def run (T : List TypeDecl) (v : ServiceV) : State v → List (Input v) → State v × List (Result v)
  | s, [] => (s, [])
  | s, i :: is =>
    let r := step T v s i
    let (s', rest) := run T v r.state is
    (s', r :: rest)

/-- Every input yields exactly one outcome. -/
theorem run_outcomes (T : List TypeDecl) (v : ServiceV) : (s : State v) → (is : List (Input v)) →
    (run T v s is).2.length = is.length
  | _, [] => rfl
  | s, i :: is => by simp only [run, List.length_cons]; rw [run_outcomes T v _ is]

/-- The run is determined by the start state and the inputs: the canonical order leaves it no choice. -/
theorem run_deterministic (T : List TypeDecl) (v : ServiceV) (s : State v) (is : List (Input v))
    (a b : State v × List (Result v)) (ha : run T v s is = a) (hb : run T v s is = b) : a = b := ha ▸ hb

end Tazuna.Ir
