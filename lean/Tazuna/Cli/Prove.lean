import Tazuna.Cli.Search
import Tazuna.Trace.Run
import Tazuna.Smt.Prove
import Tazuna.Semantics.After
import Tazuna.Smt.ServiceLayout
import Tazuna.Smt.Timer
import Tazuna.Semantics.NoTimer
import Tazuna.Smt.PairOrders
import Tazuna.Smt.Pair
import Tazuna.Smt.Dead
import Tazuna.Smt.RespStep
import Tazuna.Cli.Generate

/-! The `prove` command: for each target of each service, the base case by evaluating the initial state and one
question per input kind for the step, one line per question. A response is a target too: its question per input kind
(`respStep`) asks whether the step breaks one of the three facts the induction over steps rests on. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace

def _root_.Tazuna.Smt.Target.text : Target → String
  | .invariant none r => "invariant " ++ ruleText r
  | .invariant (some m) r => m ++ " invariant " ++ ruleText r
  | .ensures c r => c ++ " ensures " ++ ruleText r
  | .cascade => "cascade bound"
  | .effect c => "effect " ++ c ++ " accepted"
  | .timer m => "timers of " ++ m ++ " fire forward"
  | .pair a b _ => a ++ " and " ++ b ++ " commute"
  | .response n => "response " ++ n
where
  ruleText : Option String → String
    | some r => r
    | none => "(a computed name)"

def _root_.Tazuna.Smt.Target.isInvariant : Target → Bool
  | .invariant .. => true
  | _ => false

/-- Wire forms of values, naming ids in order of appearance; a value without a wire form shows as null. -/
abbrev Show := StateM Names

-- A report shows a value without a wire form (an outside id whose name another id has) as null.
set_option linter.tazuna.silentDefault false in
def wireOf (T : List TypeDecl) (t : Ty) (x : t.den0) : Show Wire := do
  let (ns, w) := (← get).enc T t x
  set ns
  pure (w.getD .null)

def stateWire (T : List TypeDecl) {v : ServiceV} (s : State v) : Show Wire := do
  let records ← wireOf T v.records s.records
  let machines ← s.machines.toSigma.mapM fun ⟨m, insts⟩ => do
    let is ← insts.mapM fun i => do
      pure (Wire.obj [("key", ← wireOf T m.key i.key), ("state", ← wireOf T m.state i.state)])
    pure (m.name, Wire.arr is)
  let pending ← s.pending.mapM fun p => do
    pure (Wire.obj [("id", .num p.id), ("external", .str p.external), ("name", .str p.request.name),
      ("input", ← wireOf T p.request.input p.request.value)])
  pure (.obj [("records", records), ("machines", .obj machines), ("pending", .arr pending), ("now", .num s.now),
    ("fresh", .num s.fresh), ("nextId", .num s.nextId)])

def inputWire (T : List TypeDecl) {v : ServiceV} : Input v → Show Wire
  | .command i caller input => do
    let x := v.commands.get i
    pure (.obj [("command", .str x.name), ("caller", ← wireOf T v.caller caller), ("input", ← wireOf T x.input input)])
  | .query i caller input => do
    let q := v.queries.get i
    pure (.obj [("query", .str q.name), ("caller", ← wireOf T v.caller caller), ("input", ← wireOf T q.input input)])
  | .answer to ⟨t, value⟩ => do pure (.obj [("answer", .num to), ("value", ← wireOf T t value)])
  | .event i value => do
    let x := v.subscribes.get i
    pure (.obj [("event", .str x.name), ("value", ← wireOf T x.event value)])
  | .clock time => pure (.obj [("clock", .num time)])

/-- The rules of the target the state `s` breaks, by the spec's functions. -/
def brokenAt {v : ServiceV} (s : State v) : Target → List String
  | .invariant none _ => broken (v.invariants.fn (s.records, ()))
  | .invariant (some name) _ => s.machines.toSigma.flatMap fun ⟨m, insts⟩ =>
    if m.name = name then insts.flatMap fun i => broken (m.invariants.fn (.inl (i.key, i.state, s.records, s.now, ()), ()))
    else []
  | _ => []

/-- One line of the report, with what decides the verdicts of the targets it is about. -/
inductive Report where
  /-- The question about `target` (none: the bound question) of the input kind `step` was unsat. -/
  | unsat (service step : String) (target : Option Target)
  /-- A state and input that break the target, from the initial state or from a state of the right shape. -/
  | violated (service step : String) (target : Target) (fields : List (String × Json))
  /-- A state of the right shape whose step of the kind leaves the slots. -/
  | boundReached (service step : String)
  /-- No verdict: the solver's, or a refusal of the encoding. -/
  | undecided (kind : Kind) (service step : String) (target : Option Target) (fields : List (String × Json))

/-- A line of the report in its place: known at once, or the answer to a question. -/
inductive Item where
  | ready (r : Report)
  | ask (o : Obligation (Except String Report))
  /-- A question `--only` leaves out: it prints nothing, and its target is not proved. -/
  | skipped (service : String) (target : Target)

/-- A dead-target question family: one of generate's targets and, per input kind whose terms do not rule it out, the
question whether the kind's step shows a class the target aims at (`showsAsk`), with the kind's place
(`SymInput.place`). -/
structure ShowsItem where
  target : GenTarget
  asks : List (String × TypedScript)

structure ServiceItems where
  items : List Item := []
  /-- The dead-target questions, empty where an input kind's questions are refused or the initial state breaks an
  invariant: `unshown_within` rests on every kind's questions and on the initial state's invariants. -/
  shows : List ShowsItem := []
  /-- The bounds of the service's scope (`scopeBounds`). -/
  scope : List Json := []
  /-- The bounds the service's inputs can go past (`inputBounds`). -/
  inputScope : List Json := []
  /-- The names of the service's input kinds, whose bound questions keep every state a run reaches within the slots. -/
  steps : List String := []
  /-- Whether every value an input carries fits the slots and the initial state does (`proved_sound`). -/
  fits : Bool := false
  /-- An engine bug: a state its proofs rule out. -/
  internal : Option String := none

section
variable (solver : Solver) (c : CheckedSpec) (v : ServiceV)

/-- The base case: the initial state breaks no rule of a service invariant target. Machines have no instances
there. -/
def initReports (targets : List Target) : List Report :=
  let s := Step.State.init v
  let broken := Step.broken (v.invariants.fn (s.records, ()))
  targets.filterMap fun g => match g with
    | .invariant none r =>
      let hit := match r with
        | some r => broken.contains r
        | none => !broken.isEmpty
      if hit then
        let st := (stateWire c.T s).run' {}
        some (.violated v.name "init" g [("from", Json.str "init"), ("state", st.toJson),
          ("violated", Json.arr (broken.map Json.str).toArray)])
      else some (.unsat v.name "init" (some g))
    | _ => none

-- A step that does not reach its invariant check shows no state after it, nor rules broken there; out lines without
-- a wire form show as none.
set_option linter.tazuna.silentDefault false in
/-- The report of one question's answer. -/
def answerReport (L : Layout) (senv : StepEnv L (shapes v)) (hc : v.caller.isData = true)
    (q : Question v (shapes v) senv.nT) (a : Smt.Answer) : Except String Report :=
  let name := q.input.text
  match a with
  | .unsat => .ok (.unsat v.name name q.target)
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name name q.target [("why", Json.str why)])
  | .timeout ms => .ok (.undecided (.undecided .timeout) v.name name q.target [("why", Json.str (timeoutWhy ms))])
  | .sat vs =>
    let M := modelOf vs
    match (SymState.vars (v := v) 0).decode M L c.T (shapes v), q.input.decode M L hc with
    | some s, some x =>
      let r := step c.T v s x
      let after := Step.settled c.T s x
      let shown : Show (List (String × Json)) := do
        let st ← stateWire c.T s
        let inp ← inputWire c.T x
        let aft ← match after with
          | some a => do pure (← stateWire c.T a.state).toJson
          | none => pure Json.null
        let (ns, outs) := outLines c.T v (← get) none r
        set ns
        pure [("from", Json.str "validState"), ("state", st.toJson), ("input", inp.toJson), ("after", aft),
          ("outcome", Json.str r.outcome.summary),
          ("out", Json.arr ((outs.getD []).map (·.toWire.toJson)).toArray)]
      let fields : List (String × Json) := shown.run' {}
      match q.target with
      | none => .ok (.boundReached v.name name)
      | some g =>
        let violated := match g, r.outcome with
          | .invariant .., _ => (after.map fun (a : Acc v) => brokenAt a.state g).getD []
          | _, .fault (.ensures n) => [n]
          | _, .fault (.invalidEffect _ rs) => rs
          | _, _ => []
        .ok (.violated v.name name g (fields ++ [("violated", Json.arr (violated.map Json.str).toArray)]))
    -- Unreachable while the solver answers as SMT-LIB says (`questions_decode`).
    | _, _ => .error s!"a model of {name} does not decode"

/-- The report of a bound question's answer: whether a step of the kind `step` can leave the slots. -/
def boundReport (service step : String) : Smt.Answer → Except String Report
  | .unsat => .ok (.unsat service step none)
  | .sat _ => .ok (.boundReached service step)
  | .unknown why => .ok (.undecided (.undecided .unknown) service step none [("why", Json.str why)])
  | .timeout ms => .ok (.undecided (.undecided .timeout) service step none [("why", Json.str (timeoutWhy ms))])

/-- The first part a response's question asks about, as its line names it. -/
def respOpens : String := "a trigger has no deadline within its time"

/-- What the step from `s` on `x` breaks of the response for the trigger `tr`, recomputed in Lean: the names of the
three parts its question asks about. -/
def respBroken (resp : ResponseV v.records v.event) (s : State v) (x : Input v) (tr : v.event.den0) : List String :=
  let r := step c.T v s x
  let late := r.events.any fun ev => resp.opens ev && !resp.answers ev r.moment &&
    match resp.deadlineAt r.state.records ev with
    | some d => decide (d > r.state.now + (resp.withinNat : Int))
    | none => true
  let moved := match resp.deadlineAt s.records tr with
    | some d => !resp.answers tr r.moment && match resp.deadlineAt r.state.records tr with
      | some d' => decide (d' > d)
      | none => true
    | none => false
  let past := match x, resp.deadlineAt s.records tr with
    | .clock time, some d => decide (d < time)
    | _, _ => false
  (if late then [respOpens] else []) ++
    (if moved then ["an open deadline goes or moves later without its answer"] else []) ++
    (if past then ["a clock line passes an open deadline"] else [])

-- A step that does not reach its end shows no state after it; out lines without a wire form show as none.
set_option linter.tazuna.silentDefault false in
/-- The report of a response's step question (`respStep`): a model is a state, an input and a trigger whose step
breaks the response, recomputed in Lean (`respBroken`). A model where Lean finds nothing broken has the response's
functions outside their slots. -/
def respReport (L : Layout) (senv : StepEnv L (shapes v)) (hc : v.caller.isData = true)
    (resp : ResponseV v.records v.event) (inp : SymInput v (shapes v) senv.nT) (a : Smt.Answer) : Except String Report :=
  let name := inp.text
  let g := Target.response resp.name
  match a with
  | .unsat => .ok (.unsat v.name name (some g))
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name name (some g) [("why", Json.str why)])
  | .timeout ms => .ok (.undecided (.undecided .timeout) v.name name (some g) [("why", Json.str (timeoutWhy ms))])
  | .sat vs =>
    let M := modelOf vs
    match (SymState.vars (v := v) 0).decode M L c.T (shapes v), inp.decode M L hc,
        decodeV L v.event (M.vars (trigVar inp)) with
    | some s, some x, some tr =>
      let tr := Ty.down _ v.event_data tr
      let r := step c.T v s x
      let after := Step.settled c.T s x
      let shown : Show (List (String × Json) × (String × Json)) := do
        let st ← stateWire c.T s
        let inp ← inputWire c.T x
        let aft ← match after with
          | some a => do pure (← stateWire c.T a.state).toJson
          | none => pure Json.null
        let (ns, outs) := outLines c.T v (← get) none r
        set ns
        let trw ← wireOf c.T v.event tr
        pure ([("from", Json.str "validState"), ("state", st.toJson), ("input", inp.toJson), ("after", aft),
          ("outcome", Json.str r.outcome.summary),
          ("out", Json.arr ((outs.getD []).map (·.toWire.toJson)).toArray)], ("trigger", trw.toJson))
      let (fields, trigger) : List (String × Json) × (String × Json) := shown.run' {}
      match respBroken c v resp s x tr with
      | [] => .ok (.undecided (.undecided .limit) v.name name (some g)
          (fields ++ [trigger, ("limit", Json.str "a function of the response reads past its slots")]))
      | bs =>
        -- The trigger is the waiting one the second and third parts read; the first part's trigger is in `out`.
        let shownTrigger := if bs == [respOpens] then [] else [trigger]
        .ok (.violated v.name name g (fields ++ shownTrigger ++ [("violated", Json.arr (bs.map Json.str).toArray)]))
    | _, _, _ => .error s!"a model of {name} does not decode"

/-- The report of a timer machine's target question (`timerQuestions`): a model is an instance whose timer enters a
state that waits for an earlier timer, recomputed in Lean from the model's values. -/
def timerReport (L : Layout) (m : MachineV v.records v.event) (step : String) (a : Smt.Answer) :
    Except String Report :=
  let g := Target.timer m.name
  match a with
  | .unsat => .ok (.unsat v.name step (some g))
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name step (some g) [("why", Json.str why)])
  | .timeout ms => .ok (.undecided (.undecided .timeout) v.name step (some g) [("why", Json.str (timeoutWhy ms))])
  | .sat vs =>
    let M := modelOf vs
    match TimerVals.decode L m M with
    | some ⟨key, st, records, _, _, _⟩ =>
      match m.timerAt records key st with
      | some (d, target) =>
        match m.timerAt records key target with
        | some (d', target') =>
          if d' < d then
            let shown : Show (List (String × Json)) := do
              let k ← wireOf c.T m.key key
              let s ← wireOf c.T m.state st
              let r ← wireOf c.T v.records records
              let t ← wireOf c.T m.state target
              let t' ← wireOf c.T m.state target'
              pure [("from", Json.str "validState"), ("instance", Json.mkObj [("key", k.toJson), ("state", s.toJson)]),
                ("records", r.toJson),
                ("timer", Json.mkObj [("deadline", Lean.toJson d), ("state", t.toJson)]),
                ("next", Json.mkObj [("deadline", Lean.toJson d'), ("state", t'.toJson)]),
                ("violated", Json.arr #[Json.str "timer enters a state with an earlier timer"])]
            .ok (.violated v.name step g (shown.run' {}))
          else .error s!"a model of {step} enters a state with a timer at {d'}, not before {d}"
        | none => .error s!"a model of {step} enters a state with no timer"
      | none => .error s!"a model of {step} gives no timer"
    -- Unreachable while the solver answers as SMT-LIB says (`timer_decode`).
    | none => .error s!"a model of {step} does not decode"

/-- An own kind as a line names it: its command or query, and where its `on_answer` is written when another own kind
has the same name. -/
def ownText (owns : List OwnKey) (key : OwnKey) : String :=
  let word := match key with
    | .command .. => "command"
    | .query .. => "query"
  let a := key.answer.site
  if (owns.filter (·.name == key.name)).length > 1 then s!"own {word} {key.name} answered at {a.module}:{a.line}:{a.col}"
  else s!"own {word} {key.name}"

def effectWire (T : List TypeDecl) {e : Ty} : EffectV e → Show Wire
  | .request r => do pure (.obj [("request", .str r.name), ("input", ← wireOf T r.input r.value)])
  | .command name _ i _ value _ => do pure (.obj [("command", .str name), ("input", ← wireOf T i value)])
  | .query name _ i _ value _ => do pure (.obj [("query", .str name), ("input", ← wireOf T i value)])

/-- Where one order of a pair ends: its fault, or the state with the events it applied and the own effects it queued. -/
def orderWire (T : List TypeDecl) {v : ServiceV} : Except Fault (Acc v) → Show Wire
  | .error f => pure (.obj [("outcome", .str (Outcome.fault f).summary)])
  | .ok a => do
    let st ← stateWire T a.state
    let evs ← a.events.mapM (wireOf T v.event)
    let own ← a.own.mapM (effectWire T ·.effect)
    pure (.obj [("outcome", .str "accepted"), ("state", st), ("events", .arr evs), ("queued", .arr own)])

/-- The report of a pair's target question (`pairQuestions`): a model is a state and two own effects whose two orders
the solver finds different with each effect keeping the ids it made. Lean runs both orders from the model's state
(`pairOrders`): where they agree up to renaming the ids the pair made, or differ only in the functions they keep, the
line is undecided, else violated. -/
def pairReport (L : Layout) (k1 k2 : OwnPlace L v.event) (g : Target) (step : String) (a : Smt.Answer) : Except String Report :=
  match a with
  | .unsat => .ok (.unsat v.name step (some g))
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name step (some g) [("why", Json.str why)])
  | .timeout ms => .ok (.undecided (.undecided .timeout) v.name step (some g) [("why", Json.str (timeoutWhy ms))])
  | .sat vs =>
    let M := modelOf vs
    match (SymState.vars (v := v) 0).decode M L c.T (shapes v), decodeOwn L c.P v k1 (M.vars (pairVar v)),
        decodeOwn L c.P v k2 (M.vars (pairVar v + 1)) with
    | some s, some e1, some e2 =>
      let a0 : Acc v := { state := s }
      let shown (more : List (String × Json)) : List (String × Json) := (do
        let st ← stateWire c.T s
        let w1 ← effectWire c.T e1.effect
        let w2 ← effectWire c.T e2.effect
        let o1 ← orderWire c.T (runOwn c.T a0 e1 >>= fun b => runOwn c.T b e2)
        let o2 ← orderWire c.T (canonPair c.T a0 e1 e2)
        pure ([("from", Json.str "validState"), ("state", st.toJson), ("first", w1.toJson), ("second", w2.toJson),
          ("firstThenSecond", o1.toJson), ("secondThenFirst", o2.toJson)] ++ more) : Show _).run' {}
      match pairOrders c.T a0 e1 e2 with
      | .error why => .error s!"a model of {step} {why}"
      | .ok r =>
        if r.violated then
          .ok (Report.violated v.name step g (shown [("violated", Json.arr #[Json.str "steps do not commute"])]))
        else match r with
          | .capped n =>
            .ok (.undecided (.undecided .limit) v.name step (some g) (shown [("limit", Json.str ((Limit.renamings n).text c.T))]))
          | .keptDiffer =>
            .ok (.undecided (.undecided .limit) v.name step (some g) (shown [("limit", Json.str (Limit.keptFunctions.text c.T))]))
          | _ => .ok (.undecided (.undecided .upToRenaming) v.name step (some g) (shown []))
    -- Unreachable while the solver answers as SMT-LIB says (`pair_decode`).
    | _, _, _ => .error s!"a model of {step} does not decode"

/-- The line of a refused encoding of the step's questions about `g` (none: all of the step's): undecided where the
refusal is the spec's, else an engine bug. -/
def refusedItems (step : String) (g : Option Target) (r : Refused) : Except String (List Item) :=
  match refusedLine c.T r with
  | .ok (k, fields) => .ok [.ready (.undecided k v.name step g fields)]
  | .error m => .error s!"service {v.name}, {step}: {m}"

/-- The lines of a question family with one target and two questions (a timer machine, a pair of own kinds): its
bound question and its target question where `--only` keeps the target, else the target skipped; `place` tells the
family apart where `step` may not, for the questions' names. -/
def familyItems (ids : Option Nat) (only : String → Bool) (g : Target) (step place : String)
    (built : Except Refused (TypedScript × TypedScript)) (report : Smt.Answer → Except String Report) :
    Except String (List Item) :=
  match built with
  | .error r => refusedItems c v step (some g) r
  | .ok (bq, tq) => .ok (if only (v.name ++ "/" ++ g.text ++ "/" ++ step) then
      [.ask ⟨["bound", v.name, g.text, place], bq.script, ids, boundReport v.name step⟩,
        .ask ⟨["target", v.name, g.text, place], tq.script, ids, report⟩]
    else [.skipped v.name g])

-- The bound question has no target, and its name says so.
set_option linter.tazuna.silentDefault false in
/-- Every line of the service in order: the base case, then each input kind's questions. -/
def serviceItems (sv : CheckedService c) (only : String → Bool) : ServiceItems := Id.run do
  let v := sv.v
  let L := sv.L
  let senv := sv.senv
  let b := stateWidth v
  let mut items : List Item := []
  let mut targets : List Target := []
  let rules := ruleNamesOf v
  let goals := (Tazuna.Ir.targets c.T v rules).filter fun g => !g.byQuery v && only (v.name ++ "/" ++ g.text)
  let mut shows : Option (List (GenTarget × List (String × TypedScript))) :=
    if (Step.invariants (Step.State.init v)).isEmpty then some (goals.map (·, [])) else none
  for ⟨inp, hinp⟩ in (stepInputs v (shapes v) senv.nT b).attach do
    let step := inp.text
    let asked := Sound.get (stepAsk L c.T c.P v senv inp) (stepAsk_ofService sv.mem c.T senv inp hinp)
    shows := match shows, asked with
      | some acc, .ok ⟨a, _⟩ =>
        some (acc.map fun (g, qs) => (g, qs ++ (showsAsk L c.T rules g a inp).toList.map (inp.place, ·)))
      | _, _ => none
    -- Each response's question about the kind (`respStep`); where the kind's questions are refused, its line is.
    if let .ok ⟨a, _⟩ := asked then
      for ⟨resp, hr⟩ in v.responses.attach do
        let g := Target.response resp.name
        unless targets.contains g do targets := targets ++ [g]
        if only (v.name ++ "/" ++ g.text ++ "/" ++ step) then
          match Sound.get (respStep L resp inp a) (respStep_ofService c sv.mem hr inp a) with
          | .ok ⟨q, _⟩ =>
            items := items ++ [.ask ⟨["response", v.name, g.text, inp.place], q.script, L.ids,
              respReport c v L senv sv.callerData resp inp⟩]
          | .error r =>
            match refusedItems c v step (some g) r with
            | .ok more => items := items ++ more
            | .error why => return { internal := some why }
        else items := items ++ [.skipped v.name g]
    match Sound.get (questions L c.T c.P v senv inp) (questions_ofService sv.mem c.T senv inp hinp) with
    | .error r =>
      match refusedItems c v step none r with
      | .ok more => items := items ++ more
      | .error why => return { internal := some why }
    | .ok ⟨(gs, qs), _⟩ =>
      for g in gs do
        unless targets.contains g do targets := targets ++ [g]
      let kept := qs.filter fun q => match q.target with
        | some g => only (v.name ++ "/" ++ g.text ++ "/" ++ step)
        | none => true
      -- The bound questions of every input kind decide together whether the service's lines say proved or within
      -- the bounds (`proved_sound`), so each is asked whatever `--only` keeps.
      let asked := if kept.any (·.target.isSome) then kept else kept.filter (·.target.isNone)
      items := items ++ asked.map (fun q => .ask ⟨match q.target with
          | some g => ["target", v.name, g.text, inp.place]
          | none => ["bound", v.name, "", inp.place], q.script, L.ids, answerReport c v L senv sv.callerData q⟩) ++
        (qs.filterMap fun q => q.target.bind fun g => if kept.any (·.target == some g) then none else some g).map
          (.skipped v.name)
  -- A machine whose `timer` never gives a timer fires forward by itself (`timerForward_of_noTimer`), so it gets no line.
  for ⟨m, hm⟩ in v.machines.attach.filter (!·.1.noTimer) do
    let step := "timer " ++ m.name
    match familyItems c v L.ids only (.timer m.name) step step
        ((Sound.get (timerQuestions L m) (timerQuestions_ofService sv.mem hm)).map (·.1)) (timerReport c v L m step) with
    | .ok more => items := items ++ more
    | .error why => return { internal := some why }
  let owns := L.ownsOf v.event
  let exact := Layout.exactOwns c.program.defs.parts v
  for (k1, k2) in L.ownPairs v.event do
    let key1 := owns[k1]
    let key2 := owns[k2]
    let widened := [key1, key2].filterMap fun k =>
      if exact.any (OwnKey.same k) then none else some (ownText owns k)
    let g := Target.pair (ownText owns key1) (ownText owns key2) widened.eraseDups
    let step := ownText owns key1 ++ " then " ++ ownText owns key2
    match familyItems c v L.ids only g step s!"own {k1} {k2}"
        ((Sound.get (pairQuestions L c.T c.P v senv k1 k2) (pairQuestions_ofService sv.mem c.T senv k1 k2)).map (·.1))
        (pairReport c v L k1 k2 g step) with
    | .ok more => items := items ++ more
    | .error why => return { internal := some why }
  let init := (initReports c v targets).map fun r => match r with
    | .unsat _ _ (some g) | .violated _ _ g _ =>
      if only (v.name ++ "/" ++ g.text ++ "/init") then Item.ready r else .skipped v.name g
    | r => .ready r
  let steps := (stepInputs v (shapes v) senv.nT b).map (·.text)
  let fits := inputsFit L v && initFits L v
  let dead : List ShowsItem := (shows.getD []).map fun (g, asks) => { target := g, asks }
  return {
    items := init ++ items
    shows := dead
    scope := scopeBounds c.T L v
    inputScope := inputBounds c.T L v
    steps
    fits }

end


def Report.service : Report → String
  | .unsat s .. | .violated s .. | .boundReached s .. | .undecided _ s .. => s

def targetOf : Report → Option Target
  | .unsat _ _ g | .undecided _ _ _ g _ => g
  | .violated _ _ g _ => some g
  | .boundReached .. => none

/-- Whether the report keeps the target from holding within the bounds: a violation of it, or no verdict for it or
for an input kind (a refused encoding or an unknown bound question, which may hide any target's question). -/
def blocks (service : String) (g : Target) : Report → Bool
  | .unsat .. | .boundReached .. => false
  | .violated s _ g' _ => s == service && g' == g
  | .undecided _ s _ none _ => s == service
  | .undecided _ s _ (some g') _ => s == service && g' == g

/-- The line of a report, given the targets not proved and the bounds each input kind's step can go past (none: the
bound question was unsat). A bound question prints no line of its own: it decides whether its kind's target lines say
proved or within the bounds. -/
def lineOf (unproved : String → List Target) (past : String → String → Option (List Json)) :
    Report → Option (Kind × List (String × Json))
  | .unsat s step (some g) =>
    let common := [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step), assumes s step g] ++
      widenedField g
    some <| match past s step with
      | none => (.prove .proved, common)
      | some bs => (.prove .withinBounds, common ++ [("bounds", Json.arr bs.toArray)])
  | .unsat _ _ none | .boundReached .. => none
  | .violated s step g fields =>
    some (.prove .violated, [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step)] ++ fields ++
      [assumes s step g] ++ widenedField g)
  | .undecided k s step g fields =>
    some (k, [("service", Json.str s)] ++ (g.map fun g => ("target", Json.str g.text)).toList ++
      [("step", Json.str step)] ++ fields ++ g.toList.flatMap widenedField)
where
  /-- A pair line's own kinds that stand for any handle or site of their type, where it has any. -/
  widenedField : Target → List (String × Json)
    | .pair _ _ (w :: ws) => [("widened", Json.arr ((w :: ws).map Json.str).toArray)]
    | _ => []
  /-- What a line's question assumes: for a step's, valid inputs (`Step.Assumption.validInputs`), which keep every
  name of a state below its counter as the question's state has them (`fault_sound`), and the invariants on the state
  before the step; for the initial state's, no input assumption, as no input led there; none for a timer machine's
  question, whose context is any key, state, records and time; for a pair's, valid inputs, which `run_lines` rests on,
  and no invariant. -/
  assumes (s step : String) (g : Target) : String × Json :=
    let held : List String := match g with
      | .timer _ => []
      | .pair .. => [Step.Assumption.validInputs.text]
      | .response _ => [Step.Assumption.validInputs.text, Step.Assumption.timelyClock.text] ++
        ((unproved s).filter fun g' => g'.isInvariant).map (·.text)
      | _ => (if step == "init" then [] else [Step.Assumption.validInputs.text]) ++
        ((unproved s).filter fun g' => g'.isInvariant && g' != g).map (·.text)
    ("assumes", Json.arr (held.map Json.str).toArray)

/-- A line of the report once its question is a job: known at once, left out by `--only`, or the answer its own job
writes. -/
inductive Placed where
  | ready (r : Report)
  | skipped (service : String) (target : Target)
  | asked (result : IO.Ref (Option (Except String Report)))

-- Every service a report names has a scope, so the empty list is never read.
set_option linter.tazuna.silentDefault false in
def prove (root path : String) (opts : Options) : Cmd Unit := do
  match ← loadSpec root path with
  | none => pure ()
  | some c =>
    let solver ← Solver.find
    -- The engine's own digest names this build in the direct keys; it is read while the questions are built.
    let engine ← IO.asTask (prio := .dedicated) do return Sha256.hex (← IO.FS.readBinFile (← IO.appPath))
    let mut items : List Item := []
    let mut scopes : List (String × ServiceItems) := []
    for sv in c.services do
      let r := serviceItems c sv opts.keeps
      if let some m := r.internal then return ← internal m
      items := items ++ r.items
      scopes := scopes ++ [(sv.v.name, { r with items := [] })]
    let version ← solver.version
    let cache := opts.cache / Sha256.hex version.toUTF8
    -- What builds every question's script, for the direct keys: the IR is the whole spec.
    let ir := Sha256.hex (← IO.FS.readBinFile path)
    let inputs := [← IO.ofExcept (← IO.wait engine), version] ++ solver.header ++ [ir]
    let mut names : Std.HashSet (List String) := {}
    let mut questions : Array Job := #[]
    let mut placed : Array Placed := #[]
    let mut deads : Array (String × GenTarget × List (IO.Ref (Option (Except String Smt.Answer)))) := #[]
    for (s, sc) in scopes do
      let ids := (c.services.find? (·.v.name == s)).bind (·.L.ids)
      for it in sc.shows do
        let mut refs := []
        for (step, q) in it.asks do
          let name := ["shows", s, it.target.text, step]
          if names.contains name then return ← internal s!"two questions are named {name}"
          names := names.insert name
          let (j, r) ← Job.of (solver.ask cache (directKey inputs name) ids q.script)
          questions := questions.push j
          refs := refs ++ [r]
        deads := deads.push (s, it.target, refs)
    for it in items do
      match it with
      | .ready r => placed := placed.push (.ready r)
      | .skipped s g => placed := placed.push (.skipped s g)
      | .ask o =>
        if names.contains o.name then return ← internal s!"two questions are named {o.name}"
        names := names.insert o.name
        let (j, r) ← Job.of do pure ((← solver.ask cache (directKey inputs o.name) o.ids o.script) >>= o.read)
        questions := questions.push j
        placed := placed.push (.asked r)
    runAll opts.jobs questions
    let mut reports : List Report := []
    let mut skipped : List (String × Target) := []
    for p in placed do
      match p with
      | .ready r => reports := reports ++ [r]
      | .skipped s g => skipped := skipped ++ [(s, g)]
      | .asked r =>
        match ← r.get with
        | some (.ok r) => reports := reports ++ [r]
        | some (.error m) => return ← internal m
        | none => return ← internal "a question's job never ran"
    let targets := (placed.toList.filterMap fun
      | .ready r => (targetOf r).map (r.service, ·)
      | .skipped s g => some (s, g)
      | .asked _ => none) ++ reports.filterMap fun r => (targetOf r).map (r.service, ·)
    let skips (s : String) (g : Target) : Bool := skipped.any fun (s', g') => s' == s && g' == g
    let unproved (s : String) : List Target :=
      (targets.filterMap fun (s', g) => if s' == s && (reports.any (blocks s g) || skips s g) then some g else none).foldl
        (fun acc g => if acc.contains g then acc else acc ++ [g]) []
    -- A bound question with no verdict leaves its kind's lines within the bounds too.
    let left (s : String) (at? : String → Bool) : Bool := reports.any fun
      | .boundReached s' step' | .undecided _ s' step' none _ => s' == s && at? step'
      | _ => false
    let scope (s : String) : List Json := ((scopes.lookup s).map (·.scope)).getD []
    let inputScope (s : String) : List Json := ((scopes.lookup s).map (·.inputScope)).getD []
    let steps (s : String) : List String := ((scopes.lookup s).map (·.steps)).getD []
    let fits (s : String) : Bool := ((scopes.lookup s).map (·.fits)).getD false
    if let some (s, step) := reports.findSome? (fun r => match r with
        | .boundReached s step => if (scope s).isEmpty then some (s, step) else none
        | _ => none) then
      return ← internal s!"service {s}, {step}: a step left the slots of a layout with no collection"
    -- A line rests on the states runs reach. They stay within the slots only where no input kind's step leaves them,
    -- every input fits and the initial state does (`run_within`); the initial state's line rests on no input.
    let reach (s : String) (here : Bool) : Option (List Json) :=
      if here || left s (steps s).contains then some (scope s)
      else if fits s then none
      else if (inputScope s).isEmpty then some (scope s) else some (inputScope s)
    let past (s step : String) : Option (List Json) :=
      if step == "init" then none else reach s (left s (· == step))
    for r in reports do
      if let some (kind, fields) := lineOf unproved past r then printLine kind fields
    -- A dead target is a fact, not a verdict: only where every kind's question is unsat (`unshown_within`, at any
    -- depth `unshown_sound`); a model or no answer says nothing.
    for (s, g, refs) in deads do
      let mut dead := true
      for r in refs do
        match ← r.get with
        | some (.ok .unsat) => pure ()
        | some (.ok _) => dead := false
        | some (.error m) => return ← internal m
        | none => return ← internal "a question's job never ran"
      if dead then
        let fields := [("service", Json.str s), ("target", Json.str g.text),
          ("assumes", Json.arr (Step.Assumption.ofRuns.map (Json.str ·.text)).toArray)]
        printLine (.prove .unreachable) (fields ++ ((reach s false).map fun bs => ("bounds", Json.arr bs.toArray)).toList)

end Tazuna.Cli
