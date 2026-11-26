import Tazuna.Semantics.Eval
import Tazuna.Semantics.Order
import Tazuna.Semantics.Rules
import Tazuna.Semantics.PerMachine

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
def broken (xs : Ty.rules.den0) : List String := xs.filterMap fun (n, b, ()) => if toB b then none else some (n : Str).1

/-- One live machine instance: its key, its state and the timer it waits for (the deadline and the state it enters). -/
structure Instance {r e : Ty} (m : MachineV r e) where
  key : m.key.den0
  state : m.state.den0
  timer : Option (Int × m.state.den0)

/-- A machine with its live instances, in the canonical order of their keys. -/
abbrev MachineState (r e : Ty) := (m : MachineV r e) × List (Instance m)

/-- The live instances of each machine of `ms`, each machine's in the canonical order of their keys. -/
abbrev Machines {r e : Ty} (ms : List (MachineV r e)) := PerMachine (fun m => List (Instance m)) ms

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
  machines : Machines v.machines
  /-- Requests sent and not yet answered: a multiset. -/
  pending : Bag (Pending v.event)
  now : Int
  /-- The counter `fresh` builds ids from; only commands read it. Every command step and every own query advances it,
  so the two orders of two internal steps differ by swapping two counters. -/
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
  /-- An answer names no pending request, or not with the types that request has. The answer's in line names the
  request, so the fault carries no id: wire ids are names, compared only up to renaming. -/
  | answerUnmatched
  /-- An effect asked for what its target does not accept: a command or query of the service's own that was Invalid
  (the rules broken, as Invalid names them) or that the service does not list (`service`), or an external's command
  or query that no external of the spec lists with these types (`declared`). Check's unknownHandle rule keeps the
  last two out of checked specs; the step is defined for every service, so they stay faults. -/
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
  | .fault .answerUnmatched => "fault answerUnmatched"
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
  { records := v.init, machines := PerMachine.ofFn (fun _ => []) v.machines, pending := [], now := 0, fresh := 0, nextId := 0 }

/-- The timer `after` asks for at `now`: due after its delay, entering its state. -/
def timerAt {st : Ty} (now : Int) : (Ty.option (Ty.timer st)).den0 → Option (Int × st.den0)
  | .inl (.inl (d, target, ()), ()) => some (now + (show Int from d), target)
  | _ => none

/-- An instance entering `st`: its timer and its effect. -/
def enter {r e : Ty} (m : MachineV r e) (records : r.den0) (now : Int) (key : m.key.den0) (st : m.state.den0) :
    Instance m × List (Sender × EffectV e) :=
  (⟨key, st, timerAt now (m.after.fn (.inl (key, st, records, now, ()), ()))⟩,
    (m.effectAt key st records now).toList.map (.machine m.name ⟨m.key, key⟩, ·))

variable (T : List TypeDecl)

/-- How the instance of key `k` reacts to an event, given the instances before it: an instance with that key reacts
with `on` (and may enter a state), and with none an instance starts at `initial`. -/
def reactKey {r e : Ty} (m : MachineV r e) (insts : List (Instance m)) (records : r.den0) (now : Int) (ev : e.den0)
    (k : m.key.den0) : Instance m × List (Sender × EffectV e) :=
  match insts.find? ((Ty.semWith Dsl.base m.key).2 k ·.key) with
  | some i => match m.on.fn (.inl (i.key, i.state, records, now, ()), ev, ()) with
    | .inr (.inl (s, ())) => enter m records now i.key s
    | _ => (i, [])
  | none => enter m records now k m.initial

/-- A machine after an event: instances whose key left go, and each key `instances` lists reacts alone
(`reactKey`), in the canonical order of the keys. The instances stay in that order, and so do their effects. -/
def machineStep {r e : Ty} (records : r.den0) (now : Int) (ev : e.den0) (m : MachineV r e) (insts : List (Instance m)) :
    List (Instance m) × List (Sender × EffectV e) :=
  let keys := Ty.sortBy T m.key (dedupBy (Ty.semWith Dsl.base m.key).2 (m.instances.fn (records, ())))
  let rs := keys.map (reactKey m insts records now ev)
  (rs.map (·.1), rs.flatMap (·.2))

/-- Every machine after an event, in order, and the effects they start, in that order. -/
def reactMachines {r e : Ty} (records : r.den0) (now : Int) (ev : e.den0) :
    {ms : List (MachineV r e)} → Machines ms → Machines ms × List (Sender × EffectV e)
  | _, .nil => (.nil, [])
  | _, .cons insts rest =>
    let x := machineStep T records now ev _ insts
    let y := reactMachines records now ev rest
    (.cons x.1 y.1, x.2 ++ y.2)

/-- One event: apply it, then let every machine and reaction react. -/
def react (s : State v) (ev : v.event.den0) : State v × List (Sender × EffectV v.event) :=
  let records := v.apply.fn (s.records, ev, ())
  let x := reactMachines T records s.now ev s.machines
  let effs := x.2 ++ v.reactions.flatMap fun x => (x.effectsAt ev records s.now).map (.reaction x.name, ·)
  ({ s with records, machines := x.1 }, effs)

/-- The broken invariants of the service and of every machine instance. -/
def invariants (s : State v) : List String :=
  broken (v.invariants.fn (s.records, ())) ++
    s.machines.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i => broken (m.invariants.fn (.inl (i.key, i.state, s.records, s.now, ()), ()))

/-- A step in progress: the state, the events applied and the out lines so far, and the own commands and queries
waiting to run. -/
structure Acc (v : ServiceV) where
  state : State v
  events : List v.event.den0 := []
  out : Bag OutLine := []
  own : List (OwnEffectV v.event) := []

/-- Whether a declaration lists the command or query a request asks for, with its types. -/
def _root_.Tazuna.Ir.RequestV.declaredBy {e : Ty} (r : RequestV e) (xd : String × DeclaredV) : Bool :=
  let same (a b : Ty) := (Ty.same a b).isSome
  match xd.2, r.rejection with
  | .externalCommand n i o j, some j' => n == r.name && same i r.input && same o r.output && same j j'
  | .externalQuery n i o _, none => n == r.name && same i r.input && same o r.output
  | _, _ => false

/-- The external that lists the command or query a request asks for, with its types. -/
def _root_.Tazuna.Ir.RequestV.ownerIn {e : Ty} (r : RequestV e) (ds : List (String × DeclaredV)) : Option String :=
  (ds.find? r.declaredBy).map (·.1)

/-- Whether an effect is a request to an external, which goes out at once; the others wait in the own queue. -/
def _root_.Tazuna.Ir.EffectV.isRequest {e : Ty} : EffectV e → Bool
  | .request _ => true
  | _ => false

/-- Starts effects in order: a request to an external goes out with a fresh wire id; an own command or query waits. -/
def start (a : Acc v) (effs : List (Sender × EffectV v.event)) : Except Fault (Acc v) :=
  effs.foldlM (fun a (snd, eff) => match eff with
    | .request r => match r.ownerIn v.declared with
      | none => .error (.invalidEffect r.name ["declared"])
      | some x =>
        let s := a.state
        .ok { a with state := { s with pending := s.pending ++ [⟨s.nextId, snd, x, r⟩], nextId := s.nextId + 1 },
                     out := a.out ++ [⟨s.nextId, x, r.name, ⟨r.input, r.value⟩⟩] }
    | .command n c i j value f => .ok { a with own := a.own ++ [.command n c i j value f] }
    | .query n c i o value f => .ok { a with own := a.own ++ [.query n c i o value f] }) a

/-- Applies the events in order, each followed by every machine's and reaction's reaction. -/
def applyEvents (a : Acc v) (events : List v.event.den0) : Except Fault (Acc v) :=
  events.foldlM (fun a ev =>
    let (s, effs) := react T a.state ev
    start { a with state := s, events := a.events ++ [ev] } effs) a

/-- The origin of a request line from the outside caller `c`. -/
def outside {c : Ty} (x : c.den0) : (Ty.origin c).den0 := .inl (x, ())

/-- The origin of an own effect. -/
def own {c : Ty} : (Ty.origin c).den0 := .inr (.inl ())

def ctx {r i c : Ty} (s : State v) (records : r.den0) (caller : (Ty.origin c).den0) (input : i.den0) :
    (Ty.ctx r i c).den0 :=
  .inl (records, input, caller, s.now, s.fresh, ())

def queryCtx {r i c : Ty} (s : State v) (records : r.den0) (caller : (Ty.origin c).den0) (input : i.den0) :
    (Ty.queryCtx r i c).den0 :=
  .inl (records, input, caller, s.now, ())

/-- Why a request is Invalid: an origin it does not list, or the input's broken `accepts` rules. -/
def admit {i : Ty} (callers : List (Ty.origin v.caller).den0) (accepts : Fun (Ty.fn [i] Ty.rules))
    (caller : (Ty.origin v.caller).den0) (input : i.den0) : List String :=
  if callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 caller) then broken (accepts.fn (input, ()))
  else ["callers"]

def okNil {j : Ty} : (Ty.result Ty.nil j).den0 := .inl (.inl (), ())

/-- How a command runs up to its answer: Invalid with the broken rules, rejected by `decide` (the fresh counter
advanced), or accepted with its events applied and `ensures` holding. Applying the events may fault, and a broken
`ensures` rule is a fault. -/
inductive Ran (v : ServiceV) (j : Ty) where
  | invalid (rules : List String)
  | rejected (a : Acc v) (rejection : j.den0)
  | accepted (a : Acc v)

/-- Runs a command from the step in progress `a`, for the step's input and for an own command alike. -/
def execCommand (a : Acc v) (x : CommandV v.records v.event v.caller) (caller : (Ty.origin v.caller).den0)
    (input : x.input.den0) :
    Except Fault (Ran v x.rejection) :=
  match admit x.callers x.accepts caller input with
  | r :: rs => .ok (.invalid (r :: rs))
  | [] =>
    let cx := ctx a.state a.state.records caller input
    let a := { a with state := { a.state with fresh := a.state.fresh + 1 } }
    match x.decide.fn (cx, ()) with
    | .inl (events, ()) => do
      let a ← applyEvents T a events
      match broken (x.ensures.fn (cx, a.state.records, ())) with
      | n :: _ => .error (.ensures n)
      | [] => .ok (.accepted a)
    | .inr (.inl (j, ())) => .ok (.rejected a j)

/-- Runs a query at the state `s`: its answer, or the broken rules that make it Invalid. -/
def execQuery (s : State v) (x : QueryV v.records v.caller) (caller : (Ty.origin v.caller).den0) (input : x.input.den0) :
    Except (List String) x.output.den0 :=
  match admit x.callers x.accepts caller input with
  | r :: rs => .error (r :: rs)
  | [] => .ok (x.resolve.fn (queryCtx s s.records caller input, ()))

/-- Runs an own command as an internal step: its answer's events are applied after it runs. -/
def runCommand (a : Acc v) (x : CommandV v.records v.event v.caller) (caller : (Ty.origin v.caller).den0)
    (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) : Except Fault (Acc v) := do
  match ← execCommand T a x caller input with
  | .invalid rs => .error (.invalidEffect x.name rs)
  | .accepted a => applyEvents T a (onAnswer.fn (okNil, ()))
  | .rejected a j => applyEvents T a (onAnswer.fn (.inr (.inl (j, ())), ()))

/-- Runs an own query as an internal step: its answer's events are applied. -/
def runQuery (a : Acc v) (x : QueryV v.records v.caller) (caller : (Ty.origin v.caller).den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [x.output] (.list v.event))) : Except Fault (Acc v) :=
  match execQuery a.state x caller input with
  | .error rs => .error (.invalidEffect x.name rs)
  | .ok o => applyEvents T { a with state := { a.state with fresh := a.state.fresh + 1 } } (onAnswer.fn (o, ()))

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

/-- Runs an own command or query: the one the service lists by the effect's name and types, as `Own`. -/
def runOwn (a : Acc v) : OwnEffectV v.event → Except Fault (Acc v)
  | .command name c i j value onAnswer =>
    match Ty.same c v.caller, ownCommand (v := v) name i j with
    | some _, some ⟨x, hi, hj⟩ => runCommand T a x own (cast (congrArg Ty.den0 hi) value) (hj ▸ onAnswer)
    | _, _ => .error (.invalidEffect name ["service"])
  | .query name c i o value onAnswer =>
    match Ty.same c v.caller, ownQuery (v := v) name i o with
    | some _, some ⟨x, hi, ho⟩ => runQuery T a x own (cast (congrArg Ty.den0 hi) value) (ho ▸ onAnswer)
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
  match a >>= settle T v.bounds.cascadeNat with
  | .error f => ⟨s0, .fault f, [], []⟩
  | .ok a => match invariants a.state with
    | n :: _ => ⟨s0, .fault (.invariant n), [], []⟩
    | [] => ⟨a.state, outcome, a.events, a.out⟩

/-- Whether an instance's timer has the deadline `d`. -/
def hitsAt {r e : Ty} {m : MachineV r e} (d : Int) (i : Instance m) : Bool :=
  match i.timer with
  | some (d', _) => decide (d' = d)
  | none => false

/-- An instance whose timer fires: it enters the state its timer names. -/
def fired {r e : Ty} (m : MachineV r e) (records : r.den0) (now : Int) (i : Instance m) :
    Instance m × List (Sender × EffectV e) :=
  match i.timer with
  | some (_, target) => enter m records now i.key target
  | none => (i, [])

/-- The first instance whose timer has the deadline `d` fires; the flag says whether one did. -/
def fireFirst {r e : Ty} (m : MachineV r e) (records : r.den0) (now : Int) (d : Int) :
    List (Instance m) → List (Instance m) × List (Sender × EffectV e) × Bool
  | [] => ([], [], false)
  | i :: is =>
    if hitsAt d i then ((fired m records now i).1 :: is, (fired m records now i).2, true)
    else let x := fireFirst m records now d is; (i :: x.1, x.2.1, x.2.2)

/-- One round over the machines in order: unless an earlier one fired (`done`), a machine's first instance with the
deadline `d` fires. -/
def fireMachines {r e : Ty} (records : r.den0) (now : Int) (d : Int) :
    Bool → {ms : List (MachineV r e)} → Machines ms → Machines ms × List (Sender × EffectV e) × Bool
  | done, _, .nil => (.nil, [], done)
  | true, _, .cons insts rest => let x := fireMachines records now d true rest; (.cons insts x.1, x.2.1, true)
  | false, _, .cons insts rest =>
    let y := fireFirst _ records now d insts
    let x := fireMachines records now d y.2.2 rest
    (.cons y.1 x.1, y.2.1 ++ x.2.1, x.2.2)

/-- The deadlines of the timers due at `now`. -/
def dues {r e : Ty} (machines : List (MachineState r e)) (now : Int) : List Int :=
  machines.flatMap fun ⟨_, insts⟩ => insts.filterMap fun i => i.timer.bind fun (d, _) => if d ≤ now then some d else none

/-- Fires the timers due at `now`, earliest deadline first, then machines in order and instances in key order (one
`fireMachines` round per timer). Entering a state may start another due timer; the cascade bound limits how many
fire. -/
def fire (s : State v) : (fuel : Nat) → Option (State v × List (Sender × EffectV v.event))
  | 0 => none
  | fuel + 1 =>
    match (dues s.machines.toSigma s.now).min? with
    | none => some (s, [])
    | some d =>
      let x := fireMachines s.records s.now d false s.machines
      (fire { s with machines := x.1 } fuel).map fun (s', es) => (s', x.2.1 ++ es)

end Step

open Step in
/-- The step: one input, exactly one outcome. A command's `ensures` is checked once its own events are applied,
before the own commands and queries they start run. -/
def step (T : List TypeDecl) (v : ServiceV) (s : State v) : Input v → Result v
  | .command i caller input =>
    let c := v.commands.get i
    let s' := { s with fresh := s.fresh + 1 }
    match execCommand T { state := s } c (outside caller) input with
    | .ok (.invalid rs) => ⟨s', .invalid rs, [], []⟩
    | .ok (.rejected _ j) => ⟨s', .rejected ⟨c.rejection, j⟩, [], []⟩
    | .error f => ⟨s', .fault f, [], []⟩
    | .ok (.accepted a) => finish T s' (.ok a) .accepted
  | .query i caller input =>
    let q := v.queries.get i
    match execQuery s q (outside caller) input with
    | .error rs => ⟨s, .invalid rs, [], []⟩
    | .ok o => ⟨s, .answered ⟨q.output, o⟩, [], []⟩
  | .answer to ⟨t, value⟩ =>
    match s.pending.find? (·.id == to) with
    | none => ⟨s, .fault .answerUnmatched, [], []⟩
    | some p => match Ty.same t (answerTy p.request.output p.request.rejection) with
      | none => ⟨s, .fault .answerUnmatched, [], []⟩
      | some ⟨h⟩ => match broken (p.request.holds (h ▸ value)) with
        -- The external broke what its query ensures: the answer is refused and the request stays pending.
        | r :: rs => ⟨s, .invalid (r :: rs), [], []⟩
        | [] =>
          let s' := { s with pending := s.pending.filter (·.id != to) }
          finish T s (applyEvents T { state := s' } (p.request.onAnswer.fn (h ▸ value, ()))) .accepted
  | .event i value => finish T s (applyEvents T { state := s } [(v.subscribes.get i).wrap.fn (value, ())]) .accepted
  | .clock time =>
    if time < s.now then ⟨s, .invalid ["time moves forward"], [], []⟩ else
    match fire { s with now := time } (v.bounds.cascadeNat + 1) with
    | none => ⟨s, .fault .cascadeLimit, [], []⟩
    | some (s', effs) => finish T s (start { state := s' } effs) .accepted

namespace Step

variable (T : List TypeDecl) {v : ServiceV}

/-- Where a step from `s` on `x` starts its cascade, read off `step`'s branches: the step in progress an accepted
command, a matched answer whose `ensures` holds, an event or a clock line not before the state's time hands to
`finish`. -/
inductive Begins (s : State v) : Input v → Acc v → Prop
  | command (i : Fin v.commands.length) (caller : v.caller.den0) (input : (v.commands.get i).input.den0) (a : Acc v) :
      execCommand T { state := s } (v.commands.get i) (outside caller) input = .ok (.accepted a) →
      Begins s (.command i caller input) a
  | answer (to : Nat) {t : Ty} (value : t.den0) (p : Pending v.event)
      (h : t = answerTy p.request.output p.request.rejection) (a : Acc v) :
      s.pending.find? (·.id == to) = some p → broken (p.request.holds (h ▸ value)) = [] →
      applyEvents T { state := { s with pending := s.pending.filter (·.id != to) } }
        (p.request.onAnswer.fn (h ▸ value, ())) = .ok a →
      Begins s (.answer to ⟨t, value⟩) a
  | event (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0) (a : Acc v) :
      applyEvents T { state := s } [(v.subscribes.get i).wrap.fn (value, ())] = .ok a → Begins s (.event i value) a
  | clock (time : Int) (s' : State v) (effs : List (Sender × EffectV v.event)) (a : Acc v) : ¬ time < s.now →
      fire { s with now := time } (v.bounds.cascadeNat + 1) = some (s', effs) → start { state := s' } effs = .ok a →
      Begins s (.clock time) a

end Step

/-- Runs the inputs in order from `s`: the final state and every step's result. -/
def run (T : List TypeDecl) (v : ServiceV) : State v → List (Input v) → State v × List (Result v)
  | s, [] => (s, [])
  | s, i :: is =>
    let r := step T v s i
    let (s', rest) := run T v r.state is
    (s', r :: rest)

end Tazuna.Ir
