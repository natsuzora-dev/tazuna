import Tazuna.Semantics.Rules

/-! The step semantics of one service. A step takes one input line and yields exactly one outcome, the out lines and
the next state. Inside a step the cascade runs to completion: each event is applied, then every machine instance and
reaction reacts to it, in a fixed canonical order (machines and reactions in declaration order, instances in the order
their keys first appeared). Timers fire only on clock lines. Out lines and pending requests form multisets: the
canonical order fixes how the step computes them, and no outcome depends on their order. -/

namespace Tazuna.Ir

/-- A value with its type, as it crosses the wire. -/
abbrev WireVal := (t : Ty) × t.den0

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

abbrev MachineState (r e : Ty) := (m : MachineV r e) × List (Instance m)

/-- An out line: a request to an external, with the wire id its answer names in `to`. -/
structure OutLine where
  id : Nat
  external : String
  command : String
  input : WireVal

/-- A multiset: two values are the same when one is a permutation of the other. -/
abbrev Bag (α : Type) := List α

structure Pending (e : Ty) where
  id : Nat
  effect : EffectV e

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
  /-- A command's `ensures` rule is broken after it accepted. -/
  | ensures (name : String)
  /-- The cascade took more internal steps than `bounds.cascade`. -/
  | cascadeLimit
  /-- An answer names no pending request, or not with the types that request has. -/
  | answerUnmatched (to : Nat)

inductive Outcome where
  | accepted (events : List WireVal)
  | answered (output : WireVal)
  | rejected (rejection : WireVal)
  | invalid (rules : List String)
  | fault (f : Fault)

def Outcome.summary : Outcome → String
  | .accepted es => s!"accepted {es.length}"
  | .answered _ => "answered"
  | .rejected _ => "rejected"
  | .invalid rs => s!"invalid {rs}"
  | .fault (.invariant n) => s!"fault invariant {n}"
  | .fault (.ensures n) => s!"fault ensures {n}"
  | .fault .cascadeLimit => "fault cascadeLimit"
  | .fault (.answerUnmatched n) => s!"fault answerUnmatched {n}"

structure Result (v : ServiceV) where
  state : State v
  outcome : Outcome
  out : Bag OutLine

namespace Step

variable {v : ServiceV}

def State.init (v : ServiceV) : State v :=
  { records := v.init, machines := v.machines.map (⟨·, []⟩), pending := [], now := 0, fresh := 0, nextId := 0 }

/-- Effects become requests with fresh wire ids, in order. -/
def send (s : State v) (effects : List (EffectV v.event)) : State v × Bag OutLine :=
  effects.foldl (fun (s, out) eff =>
    ({ s with pending := s.pending ++ [⟨s.nextId, eff⟩], nextId := s.nextId + 1 },
     out ++ [⟨s.nextId, eff.external, eff.command, ⟨eff.input, eff.value⟩⟩])) (s, [])

/-- An instance entering `st`: its timer and its effect. -/
def enter {r e : Ty} (m : MachineV r e) (records : r.den0) (now : Int) (key : m.key.den0) (st : m.state.den0) :
    Instance m × List (EffectV e) :=
  let timer := match m.after (key, st, records, now, ()) with
    | .inl (.inl (d, target, ()), ()) => some (now + (show Int from d), target)
    | _ => none
  (⟨key, st, timer⟩, (m.effect key st records now).toList)

/-- A machine after an event: instances whose key left go, new keys start at `initial`, the others react with `on`. -/
def machineStep {r e : Ty} (records : r.den0) (now : Int) (ev : e.den0) : MachineState r e →
    MachineState r e × List (EffectV e)
  | ⟨m, insts⟩ =>
    let eqK := (Ty.semWith Dsl.base m.key).2
    let keys := (m.instances (records, ())).foldl (fun ks k => if ks.any (eqK k) then ks else ks ++ [k]) []
    let kept := insts.filter fun i => keys.any (eqK i.key)
    let (reacted, effs) := kept.foldl (fun (acc, effs) i =>
      match m.on (i.key, i.state, ev, records, now, ()) with
      | .inr (.inl (s, ())) => let (i', es) := enter m records now i.key s; (acc ++ [i'], effs ++ es)
      | _ => (acc ++ [i], effs)) ([], [])
    let fresh := keys.filter fun k => !insts.any (eqK k ·.key)
    let (born, effs) := fresh.foldl (fun (acc, effs) k =>
      let (i, es) := enter m records now k m.initial; (acc ++ [i], effs ++ es)) (reacted, effs)
    (⟨m, born⟩, effs)

/-- One event of the cascade: apply it, then let every machine and reaction react. -/
def react (s : State v) (ev : v.event.den0) : State v × List (EffectV v.event) :=
  let records := v.apply (s.records, ev, ())
  let (machines, effs) := s.machines.foldl (fun (ms, effs) ms0 =>
    let (m', es) := machineStep records s.now ev ms0; (ms ++ [m'], effs ++ es)) ([], [])
  let effs := effs ++ v.reactions.flatMap fun x => x.react ev records s.now
  ({ s with records, machines }, effs)

/-- The broken invariants of the service and of every machine instance. -/
def invariants (s : State v) : List String :=
  broken (v.invariants (s.records, ())) ++
    s.machines.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => broken (m.invariants (i.key, i.state, s.records, ()))

/-- Runs the cascade for `events` and checks the invariants: the outcome is `ok` unless something faults. -/
def cascade (s0 s : State v) (events : List v.event.den0) (ok : State v → List String) (outcome : Outcome) :
    Result v :=
  if (v.bounds.cascade : Int) < events.length then ⟨s0, .fault .cascadeLimit, []⟩ else
  let (s, effs) := events.foldl (fun (s, effs) ev => let (s, es) := react s ev; (s, effs ++ es)) (s, [])
  let (s, out) := send s effs
  match invariants s, ok s with
  | n :: _, _ => ⟨s0, .fault (.invariant n), []⟩
  | [], n :: _ => ⟨s0, .fault (.ensures n), []⟩
  | [], [] => ⟨s, outcome, out⟩

/-- Fires the timers due at `now`, earliest deadline first, then machines and instances in order. Entering a state
may start another due timer; the cascade bound limits how many fire. -/
def fire (s : State v) : (fuel : Nat) → Option (State v × List (EffectV v.event))
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

def ctx {r i c : Ty} (s : State v) (records : r.den0) (caller : c.den0) (input : i.den0) : (Ty.ctx r i c).den0 :=
  .inl (records, input, caller, s.now, s.fresh, ())

end Step

open Step in
/-- The step: one input, exactly one outcome. -/
def step (v : ServiceV) (s : State v) : Input v → Result v
  | .command i caller input =>
    let c := v.commands.get i
    let eqC := (Ty.semWith Dsl.base v.caller).2
    let s' := { s with fresh := s.fresh + 1 }
    if !c.callers.any (eqC caller) then ⟨s', .invalid ["callers"], []⟩ else
    match broken (c.accepts (input, ())) with
    | r :: rs => ⟨s', .invalid (r :: rs), []⟩
    | [] =>
      let cx := ctx s s.records caller input
      match c.decide (cx, ()) with
      | .inr (.inl (j, ())) => ⟨s', .rejected ⟨c.rejection, j⟩, []⟩
      | .inl (events, ()) =>
        cascade s' s' events (fun s => broken (c.ensures (cx, s.records, ())))
          (.accepted (events.map (⟨v.event, ·⟩)))
  | .query i caller input =>
    let q := v.queries.get i
    let eqC := (Ty.semWith Dsl.base v.caller).2
    if !q.callers.any (eqC caller) then ⟨s, .invalid ["callers"], []⟩ else
    match broken (q.accepts (input, ())) with
    | r :: rs => ⟨s, .invalid (r :: rs), []⟩
    | [] => ⟨s, .answered ⟨q.output, q.resolve (ctx s s.records caller input, ())⟩, []⟩
  | .answer to ⟨t, value⟩ =>
    match s.pending.find? (·.id == to) with
    | none => ⟨s, .fault (.answerUnmatched to), []⟩
    | some p => match Ty.same t (Ty.result p.effect.output p.effect.rejection) with
      | none => ⟨s, .fault (.answerUnmatched to), []⟩
      | some ⟨h⟩ =>
        let events := p.effect.onAnswer (h ▸ value, ())
        let s' := { s with pending := s.pending.filter (·.id != to) }
        cascade s s' events (fun _ => []) (.accepted (events.map (⟨v.event, ·⟩)))
  | .event i value =>
    let events := [(v.subscribes.get i).wrap (value, ())]
    cascade s s events (fun _ => []) (.accepted (events.map (⟨v.event, ·⟩)))
  | .clock time =>
    if time < s.now then ⟨s, .invalid ["time moves forward"], []⟩ else
    match fire { s with now := time } (v.bounds.cascade.toNat + 1) with
    | none => ⟨s, .fault .cascadeLimit, []⟩
    | some (s', effs) =>
      let (s', out) := send s' effs
      match invariants s' with
      | n :: _ => ⟨s, .fault (.invariant n), []⟩
      | [] => ⟨s', .accepted [], out⟩

/-- Runs the inputs in order from `s`: the final state and, per input, its outcome and out lines. -/
def run (v : ServiceV) : State v → List (Input v) → State v × List (Outcome × Step.Bag Step.OutLine)
  | s, [] => (s, [])
  | s, i :: is =>
    let r := step v s i
    let (s', rest) := run v r.state is
    (s', (r.outcome, r.out) :: rest)

/-- Every input yields exactly one outcome. -/
theorem run_outcomes (v : ServiceV) : (s : State v) → (is : List (Input v)) → (run v s is).2.length = is.length
  | _, [] => rfl
  | s, i :: is => by simp only [run, List.length_cons]; rw [run_outcomes v _ is]

/-- The run is determined by the start state and the inputs: the canonical order leaves it no choice. -/
theorem run_deterministic (v : ServiceV) (s : State v) (is : List (Input v)) (a b : State v × List (Outcome × Step.Bag Step.OutLine))
    (ha : run v s is = a) (hb : run v s is = b) : a = b := ha ▸ hb

end Tazuna.Ir
