import Tazuna.Cli.Check
import Tazuna.Trace.Run
import Tazuna.Smt.Prove
import Tazuna.Semantics.After
import Tazuna.Smt.ServiceLayout
import Tazuna.Smt.Timer
import Tazuna.Semantics.NoTimer
import Tazuna.Smt.PairOrders
import Tazuna.Smt.Pair
import Tazuna.Smt.RespGoal

/-! The `prove` command: for each target of each service, the base case by evaluating the initial state and one
question per input kind for the step, one line per question; then each bounded response, searched for a violation by
deepening an unrolled run from the initial state (`unrollBase` with `respGoalE`) up to the spec's `steps` bound, one line
per response. -/

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
where
  ruleText : Option String → String
    | some r => r
    | none => "(a computed name)"

def _root_.Tazuna.Smt.Target.isInvariant : Target → Bool
  | .invariant .. => true
  | _ => false

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

def senderText : {ks : List Ty} → SenderShape ks → String
  | _, .machine m _ => m
  | _, .reaction r => r

def _root_.Tazuna.Smt.SymInput.text : SymInput v shs n → String
  | .command i .. => "command " ++ (v.commands.get i).name
  | .query i .. => "query " ++ (v.queries.get i).name
  | .answer k j .. => s!"answer {shs[k].external}.{shs[k].name} to {senderText shs[k].sender} at slot {(j : Nat)}"
  | .unmatched .. => "unmatched answer"
  | .event i _ => "event " ++ (v.subscribes.get i).name
  | .clock _ => "clock"

end

-- A script's answer reports every variable it declares, so the default is never read.
set_option linter.tazuna.silentDefault false in
/-- The values the solver gave, as a model. -/
def modelOf (vs : List (Nat × Val)) : Model :=
  { vars := fun n => (vs.lookup n).getD default, divZero := fun _ => 0, modZero := fun _ => 0,
    selOther := fun _ _ _ _ => default, defs := fun _ => default }

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
      let timer ← match i.timer with
        | some (d, st) => do pure (Wire.arr [.num d, ← wireOf T m.state st])
        | none => pure .null
      pure (Wire.obj [("key", ← wireOf T m.key i.key), ("state", ← wireOf T m.state i.state), ("timer", timer)])
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

structure ServiceItems where
  items : List Item := []
  /-- The bounds of the service's scope (`scopeBounds`). -/
  scope : List Json := []
  /-- An engine bug: a state its proofs rule out. -/
  internal : Option String := none

-- A type the table does not declare shows by its index.
set_option linter.tazuna.silentDefault false in
/-- A type as Gleam writes it. -/
def tyText (T : List TypeDecl) : Ty → String
  | .int => "Int"
  | .str => "String"
  | .list t => s!"List({tyText T t})"
  | .tuple ts => s!"#({", ".intercalate (ts.map (tyText T))})"
  | .fn ps r => s!"fn({", ".intercalate (ps.map (tyText T))}) -> {tyText T r}"
  | .adt i args _ =>
    let name := (T[i]?.map (·.name)).getD s!"type {i}"
    if args.isEmpty then name else s!"{name}({", ".intercalate (args.map (tyText T))})"
  | .param k => s!"t{k}"
  | .bag t => s!"Bag({tyText T t})"
  | .table k v => s!"Table({tyText T k}, {tyText T v})"
  | .date => "Date"
  | .id => "Id"
  | .dsl k args =>
    let name := k.decl.1
    if args.isEmpty then name else s!"{name}({", ".intercalate (args.map (tyText T))})"

def _root_.Tazuna.Smt.Limit.text (T : List TypeDecl) : Limit → String
  | .function t => s!"a value of {tyText T t} is a function where a term is needed"
  | .equality t => s!"== on {tyText T t} compares slots in their order, not values"
  | .dynamicName => "a handle, command or query named by a value that is no literal"
  | .builtin n => s!"the built-in {n} has no terms"
  | .effectClosure => "a kept function returns effects"
  | .unsortable t => s!"a value of {tyText T t} holds a type variable or a structure value"
  | .slots t => s!"a value the spec writes of {tyText T t} holds more items than its bounds give"
  | .renamings n => s!"the two steps sent {n} requests, more than the {wireSearchCap} whose renamings are searched"
  | .keptFunctions => "the two orders end with the same data but keep different functions, whose results are not compared"

/-- Every bound a step of the service can go past: each table and bag type of its layout, with the bound its slots
come from, and the pending requests where the service has a request shape. A list's slots are its type's longest
literal and no built-in makes a longer list, so no list bound is ever past. -/
def scopeBounds (T : List TypeDecl) (L : Layout) (v : ServiceV) : List Json :=
  L.types.filterMap fun (t, n) =>
    let line (name bound : String) : Option Json :=
      some (Json.mkObj [("type", Json.str name), ("bound", Json.str bound), ("slots", Lean.toJson n)])
    if (Ty.same t (pendingTable (shapes v))).isSome then
      if (shapes v).isEmpty then none else line "pending requests" "items"
    else match t with
      | .table k w => line (tyText T t) (if v.bounds.creates.any (·.bounds (.table k w)) then "creates" else "items")
      | .bag _ => line (tyText T t) "items"
      | _ => none

def refusalLine (T : List TypeDecl) (r : Refusal) : Option (Kind × List (String × Json)) :=
  match r with
  | .unencodableString s => some (.undecided .unencodableString, [("string", Json.str s)])
  | .limit l => some (.undecided .limit, [("limit", Json.str (l.text T))])
  | .layout _ | .unexpected _ => none

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
def answerReport (L : Layout) (senv : StepEnv L (shapes v)) (q : Question v (shapes v) senv.nT)
    (a : Smt.Answer) : Except String Report :=
  let name := q.input.text
  match a with
  | .unsat => .ok (.unsat v.name name q.target)
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name name q.target [("why", Json.str why)])
  | .sat vs =>
    let M := modelOf vs
    if hc : v.caller.isData = true then
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
    else .error "the caller type is no data"

/-- The report of a bound question's answer: whether a step of the kind `step` can leave the slots. -/
def boundReport (service step : String) : Smt.Answer → Except String Report
  | .unsat => .ok (.unsat service step none)
  | .sat _ => .ok (.boundReached service step)
  | .unknown why => .ok (.undecided (.undecided .unknown) service step none [("why", Json.str why)])

/-- The report of a timer machine's target question (`timerQuestions`): a model is a context where `after` sets a timer
before the time it sets it at, recomputed in Lean from the model's values. -/
def timerReport (L : Layout) (m : MachineV v.records v.event) (step : String) (a : Smt.Answer) :
    Except String Report :=
  let g := Target.timer m.name
  match a with
  | .unsat => .ok (.unsat v.name step (some g))
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name step (some g) [("why", Json.str why)])
  | .sat vs =>
    let M := modelOf vs
    match TimerVals.decode L m M with
    | some ⟨key, st, records, now, _, _, _, _⟩ =>
      match Step.timerAt now (m.after.fn (.inl (key, st, records, now, ()), ())) with
      | some (d, target) =>
        if d < now then
          let shown : Show (List (String × Json)) := do
            let k ← wireOf c.T m.key key
            let s ← wireOf c.T m.state st
            let r ← wireOf c.T v.records records
            let t ← wireOf c.T m.state target
            pure [("from", Json.str "validState"), ("instance", Json.mkObj [("key", k.toJson), ("state", s.toJson)]),
              ("records", r.toJson), ("now", Lean.toJson now),
              ("timer", Json.mkObj [("deadline", Lean.toJson d), ("state", t.toJson)]),
              ("violated", Json.arr #[Json.str "timer set before its time"])]
          .ok (.violated v.name step g (shown.run' {}))
        else .error s!"a model of {step} sets a timer at {d}, not before {now}"
      | none => .error s!"a model of {step} sets no timer"
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
  | .command name c i _ caller value _ => do
    pure (.obj [("command", .str name), ("caller", ← wireOf T c caller), ("input", ← wireOf T i value)])
  | .query name c i _ caller value _ => do
    pure (.obj [("query", .str name), ("caller", ← wireOf T c caller), ("input", ← wireOf T i value)])

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
def refusedItems (step : String) (g : Option Target) (r : Refusal) : Except String (List Item) :=
  match refusalLine c.T r with
  | some (k, fields) => .ok [.ready (.undecided k v.name step g fields)]
  | none => .error s!"service {v.name}, {step}: the encoding refused: {reprStr r}"

/-- The lines of a question family with one target and two questions (a timer machine, a pair of own kinds): its
bound question and its target question where `--only` keeps the target, else the target skipped. -/
def familyItems (only : String → Bool) (g : Target) (step : String) (built : Except Refusal (TypedScript × TypedScript))
    (report : Smt.Answer → Except String Report) : Except String (List Item) :=
  match built with
  | .error r => refusedItems c v step (some g) r
  | .ok (bq, tq) => .ok (if only (v.name ++ "/" ++ g.text ++ "/" ++ step) then
      [.ask ⟨bq.script, boundReport v.name step⟩, .ask ⟨tq.script, report⟩]
    else [.skipped v.name g])

-- The bound question has no target, and its name says so.
set_option linter.tazuna.silentDefault false in
/-- Every line of the service in order: the base case, then each input kind's questions. -/
def serviceItems (only : String → Bool) : ServiceItems := Id.run do
  let L := Layout.ofService c.program.defs v
  let .ok senv := StepEnv.of L (shapes v)
    | return { internal := some s!"service {v.name}: no step environment in its layout" }
  let b := stateWidth v
  let mut items : List Item := []
  let mut targets : List Target := []
  for inp in stepInputs v (shapes v) senv.nT b do
    let step := inp.text
    match questions L c.T c.P v senv inp with
    | .error r =>
      match refusedItems c v step none r with
      | .ok more => items := items ++ more
      | .error why => return { internal := some why }
    | .ok (gs, qs) =>
      for g in gs do
        unless targets.contains g do targets := targets ++ [g]
      let kept := qs.filter fun q => match q.target with
        | some g => only (v.name ++ "/" ++ g.text ++ "/" ++ step)
        | none => true
      -- The bound question decides whether a kept target's lines say proved or within the bounds, so it is asked
      -- whenever a target question of its kind is.
      let asked := if kept.any (·.target.isSome) then kept else []
      items := items ++ asked.map (fun q => .ask ⟨q.script, answerReport c v L senv q⟩) ++
        (qs.filterMap fun q => q.target.bind fun g => if kept.any (·.target == some g) then none else some g).map
          (.skipped v.name)
  -- A machine whose `after` never sets a timer fires forward by itself (`timerForward_of_noTimer`), so it gets no line.
  for m in v.machines.filter (!·.noTimer) do
    let step := "timer " ++ m.name
    match familyItems c v only (.timer m.name) step (timerQuestions L m) (timerReport c v L m step) with
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
    match familyItems c v only g step (pairQuestions L c.T c.P v senv k1 k2) (pairReport c v L k1 k2 g step) with
    | .ok more => items := items ++ more
    | .error why => return { internal := some why }
  let init := (initReports c v targets).map fun r => match r with
    | .unsat _ _ (some g) | .violated _ _ g _ =>
      if only (v.name ++ "/" ++ g.text ++ "/init") then Item.ready r else .skipped v.name g
    | r => .ready r
  return { items := init ++ items, scope := scopeBounds c.T L v }

end

section
variable (solver : Solver) (c : CheckedSpec) (v : ServiceV) (L : Layout) (senv : StepEnv L (shapes v))

/-- One depth's unrolled run as every target's goal at that depth shares it: its base, merged into one object per
equal subterm (`shareCommon'`, the identity on values) so a goal built from its steps finds its shared terms among
the assertions' at once, and the prefix of its scripts (`ScriptPrefix`), read once; or the refusal of its
encoding. -/
abbrev Depth (v : ServiceV) (n : Nat) := Except Refusal (UnrollBase v n × Option ScriptPrefix)

/-- The run at depth `d`, each target's goal aside. -/
def depthAt (d : Nat) : Depth v senv.nT :=
  (unrollBase L c.T c.P v senv d).map fun B =>
    let B := ShareCommon.shareCommon' B
    (B, B.script.prefix? solver.header)

end

/-- What prove found for one response. -/
inductive RespResult where
  /-- A run from the initial state, of the steps it took, that violates the response. -/
  | violated (steps : Nat) (run : List Wire)
  /-- No run of at most `steps` inputs violates it. -/
  | within (steps : Nat)
  | undecided (kind : Kind) (fields : List (String × Json))

/-- Whether every clock line of the run from `s` is timely (`Step.TimelyRun`). -/
def timelyRun (T : List TypeDecl) (v : ServiceV) : State v → List (Input v) → Bool
  | _, [] => true
  | s, x :: xs => (match x with
    | .clock time => Step.timely s time
    | _ => true) && timelyRun T v (step T v s x).state xs

/-- The words an assumption is named by in a response line. -/
def responseAssumes : List String := [Step.Assumption.validInputs.text, Step.Assumption.timelyClock.text]

def _root_.Tazuna.Ir.ResponseV.text {e : Ty} (resp : ResponseV e) : String := "response " ++ resp.name

section
variable (solver : Solver) (cache : System.FilePath) (c : CheckedSpec) (v : ServiceV) (L : Layout)
  (senv : StepEnv L (shapes v))

/-- The response's search over the depths 1, 2, ... (`ds`, each awaited when the search reaches it), stopping at the
first model, which is played back in Lean: its run must have timely clock lines and violate the response
(`response_sound`). A refused encoding of the run, of the goal, or of an input kind (which the script then lacks)
leaves the response undecided unless a model is found; the goal's refusal is never a layout gap
(`respGoalE_ofService`). An error is an engine bug. -/
def searchResponse (ds : List (Task (Depth v senv.nT))) (resp : ResponseV v.event) : IO (Except String RespResult) := do
  if hc : v.caller.isData = false then return .error "the caller type is no data" else
  have hc : v.caller.isData = true := by simpa using hc
  let mut refused : Option (SymInput v (shapes v) senv.nT × Refusal) := none
  let refusedLine (step : Option String) (r : Refusal) : Except String RespResult :=
    match refusalLine c.T r with
    | some (kind, fields) => .ok (.undecided kind (step.toList.map (("step", Json.str ·)) ++ fields))
    | none => .error s!"service {v.name}, {resp.text}: the encoding refused: {reprStr r}"
  for (t, i) in ds.zipIdx do
    let d := i + 1
    match ← IO.wait t with
    | .error r => return refusedLine none r
    | .ok (B, pre) =>
      match respGoalE L v resp B.steps with
      | .error r => return refusedLine none r
      | .ok g =>
        let U := B.withGoal g
        if refused.isNone then refused := U.refused.head?
        let unsorted : RespResult := .undecided (.undecided .unknown) [("depth", Lean.toJson d),
          ("why", Json.str "a shared term of the script has no sort")]
        let some pre := pre | return .ok unsorted
        let some q := pre.ask g | return .ok unsorted
        match ← solver.runKeyed cache q with
        | .unsat => pure ()
        | .unknown why =>
          return .ok (.undecided (.undecided .unknown) [("depth", Lean.toJson d), ("why", Json.str why)])
        | .sat vs =>
          let M := modelOf vs
          -- `unroll_decode`: every model's steps decode to a run that faults nowhere.
          let some xs := U.steps.mapM (·.decode M L hc)
            | return .error s!"service {v.name}, {resp.text}: a model of depth {d} does not decode"
          -- `response_sound`: the decoded run has timely clock lines and violates the response, so this check never
          -- fails; writing the run as a trace is checked, not proved.
          unless resp.violatedBy c.T (State.init v) xs && timelyRun c.T v (State.init v) xs do
            return .error s!"service {v.name}, {resp.text}: a model of depth {d} does not violate it"
          match traceOf c.T v xs with
          | .ok ws => return .ok (.violated d ws.tail)
          | .error _ => return .error s!"service {v.name}, {resp.text}: a model of depth {d} does not write as a trace"
  match refused with
  | some (inp, r) => return refusedLine (some inp.text) r
  | none => return .ok (.within ds.length)

end

/-- The line of a response's result. -/
def responseLine (service : String) (name : String) (scope : List Json) : RespResult → Kind × List (String × Json)
  | .violated d ws => (.prove .violated, [("service", Json.str service), ("target", Json.str ("response " ++ name)),
      ("from", Json.str "init"), ("steps", Lean.toJson d), ("run", Json.arr (ws.map (·.toJson)).toArray),
      ("violated", Json.arr #[Json.str name]), ("assumes", Json.arr (responseAssumes.map Json.str).toArray)])
  | .within k => (.prove .withinBounds, [("service", Json.str service), ("target", Json.str ("response " ++ name)),
      ("assumes", Json.arr (responseAssumes.map Json.str).toArray),
      ("bounds", Json.arr (scope ++ [Json.mkObj [("bound", Json.str "steps"), ("size", Lean.toJson k)]]).toArray)])
  | .undecided kind fields => (kind, [("service", Json.str service), ("target", Json.str ("response " ++ name))] ++ fields)

/-- What one job of prove's pool gives: nothing (a depth built), a step question's report, or a response's result. -/
inductive Done where
  | built
  | answer (r : Except String Report)
  | response (r : Except String RespResult)
deriving Inhabited

/-- `f` at every item, at most `jobs` at a time, results in order. -/
def runAll {α β : Type} [Inhabited β] (jobs : Nat) (f : α → IO β) (xs : Array α) : IO (Array β) := do
  let next ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate xs.size (none : Option β))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < xs.size then
        let r ← f xs[i]
        results.modify (·.set! i (some r))
      else break
  let tasks ← (List.range (max jobs 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e
  return (← results.get).map (·.get!)

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
    let common := [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step), assumes s g] ++
      widenedField g
    some <| match past s step with
      | none => (.prove .proved, common)
      | some bs => (.prove .withinBounds, common ++ [("bounds", Json.arr bs.toArray)])
  | .unsat _ _ none | .boundReached .. => none
  | .violated s step g fields =>
    some (.prove .violated, [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step)] ++ fields ++
      [assumes s g] ++ widenedField g)
  | .undecided k s step g fields =>
    some (k, [("service", Json.str s)] ++ (g.map fun g => ("target", Json.str g.text)).toList ++
      [("step", Json.str step)] ++ fields ++ g.toList.flatMap widenedField)
where
  /-- A pair line's own kinds that stand for any handle or site of their type, where it has any. -/
  widenedField : Target → List (String × Json)
    | .pair _ _ (w :: ws) => [("widened", Json.arr ((w :: ws).map Json.str).toArray)]
    | _ => []
  /-- What a line's question assumes: the invariants on the state before the step; none for a timer machine's
  question, whose context is any key, state, records and time; for a pair's, the assumption `run_lines` rests on
  (`Step.Assumption.validInputs`), which keeps every name of a state below its counter, as the question's state has
  them, and no invariant. -/
  assumes (s : String) (g : Target) : String × Json :=
    let held : List String := match g with
      | .timer _ => []
      | .pair .. => [Step.Assumption.validInputs.text]
      | _ => ((unproved s).filter fun g' => g'.isInvariant && g' != g).map (·.text)
    ("assumes", Json.arr (held.map Json.str).toArray)

/-- The options of `prove`: the prefix `--only` keeps questions by, how many solvers run at once, and the cache
directory. -/
structure ProveOptions where
  only : Option String := none
  jobs : Nat := 4
  cache : System.FilePath

-- Every service a report names has a scope, so the empty list is never read.
set_option linter.tazuna.silentDefault false in
def prove (root path : String) (opts : ProveOptions) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok c =>
    let solver : Solver := {}
    let keep (name : String) : Bool := match opts.only with
      | some p => p.isPrefixOf name
      | none => true
    let mut items : List Item := []
    let mut scopes : List (String × List Json) := []
    for v in c.spec.services do
      let r := serviceItems c v keep
      if let some m := r.internal then
        IO.eprintln s!"tazuna-engine: internal error: {m}"
        return 4
      items := items ++ r.items
      scopes := scopes ++ [(v.name, r.scope)]
    let asks := (items.filterMap fun | .ask o => some o | _ => none).toArray
    let cache := opts.cache / Sha256.hex (← solver.version).toUTF8
    -- Each response's search is one job; a service's depths are built once for all its responses, each as one job
    -- that resolves a promise the searches wait on when they reach that depth. A build takes its depth as the job's
    -- argument: a build closed over it would have its pure work floated out of the job by the compiler, onto this
    -- thread.
    let mut rjobs : Array (String × String × List Json × IO (Except String RespResult)) := #[]
    let mut builds : Array (Nat × (Nat → IO Done)) := #[]
    for v in c.spec.services do
      let resps := v.responses.filter fun r => keep (v.name ++ "/" ++ r.text)
      if resps.isEmpty then continue
      let L := Layout.ofService c.program.defs v
      let .ok senv := StepEnv.of L (shapes v)
        | IO.eprintln s!"tazuna-engine: internal error: service {v.name}: no step environment in its layout"
          return 4
      have : Nonempty (Depth v senv.nT) := ⟨.error (.limit .dynamicName)⟩
      let mut depths : Array (Task (Depth v senv.nT)) := #[]
      for d in List.range' 1 v.bounds.steps.toNat do
        let p ← IO.Promise.new
        builds := builds.push (d, fun d => do p.resolve (depthAt solver c v L senv d); pure .built)
        depths := depths.push p.result!
      for resp in resps do
        rjobs := rjobs.push (v.name, resp.name, scopeBounds c.T L v,
          searchResponse solver cache c v L senv depths.toList resp)
    -- One pool for all: the builds first, so a search waits only on a build some worker runs, then the searches,
    -- the longest jobs, then the step questions, which fill the workers while the searches deepen.
    let searches : Array (Nat × (Nat → IO Done)) := rjobs.map fun (_, _, _, job) => (0, fun _ => Done.response <$> job)
    let questions : Array (Nat × (Nat → IO Done)) :=
      asks.map fun o => (0, fun _ => do pure (.answer (o.read (← solver.runCached cache o.script))))
    let done ← runAll opts.jobs (fun (d, job) => job d) (builds ++ searches ++ questions)
    let answers := done.filterMap fun | .answer r => some r | _ => none
    let rresults := done.filterMap fun | .response r => some r | _ => none
    let mut reports : List Report := []
    let mut skipped : List (String × Target) := []
    let mut k := 0
    for it in items do
      match it with
      | .ready r => reports := reports ++ [r]
      | .skipped s g => skipped := skipped ++ [(s, g)]
      | .ask _ =>
        match (answers[k]? : Option (Except String Report)) with
        | some (.ok r) => reports := reports ++ [r]
        | some (.error m) =>
          IO.eprintln s!"tazuna-engine: internal error: {m}"
          return 4
        | none => pure ()
        k := k + 1
    let targets := (items.filterMap fun
      | .ready r => (targetOf r).map (r.service, ·)
      | .skipped s g => some (s, g)
      | .ask _ => none) ++ reports.filterMap fun r => (targetOf r).map (r.service, ·)
    let skips (s : String) (g : Target) : Bool := skipped.any fun (s', g') => s' == s && g' == g
    let unproved (s : String) : List Target :=
      (targets.filterMap fun (s', g) => if s' == s && (reports.any (blocks s g) || skips s g) then some g else none).foldl
        (fun acc g => if acc.contains g then acc else acc ++ [g]) []
    -- A bound question with no verdict leaves its kind's lines within the bounds too.
    let left (s step : String) : Bool := reports.any fun
      | .boundReached s' step' | .undecided _ s' step' none _ => s' == s && step' == step
      | _ => false
    let scope (s : String) : List Json := (scopes.lookup s).getD []
    if let some (s, step) := reports.findSome? (fun r => match r with
        | .boundReached s step => if (scope s).isEmpty then some (s, step) else none
        | _ => none) then
      IO.eprintln s!"tazuna-engine: internal error: service {s}, {step}: a step left the slots of a layout with no collection"
      return 4
    let past (s step : String) : Option (List Json) := if left s step then some (scope s) else none
    let mut rlines : List (Kind × List (String × Json)) := []
    for ((service, name, scope, _), res) in rjobs.zip rresults do
      match res with
      | .error m =>
        IO.eprintln s!"tazuna-engine: internal error: {m}"
        return 4
      | .ok r => rlines := rlines ++ [responseLine service name scope r]
    for r in reports do
      if let some (kind, fields) := lineOf unproved past r then printLine kind fields
    for (kind, fields) in rlines do printLine kind fields
    if reports.any (fun | .violated .. => true | _ => false) || rlines.any (·.1 matches .prove .violated) then return 1
    if reports.any (fun | .undecided .. => true | _ => false) || rlines.any (·.1 matches .undecided _) then return 2
    return 0

-- An IR path without a directory part is in the working directory.
set_option linter.tazuna.silentDefault false in
/-- `prove`'s arguments after the root: `--only <prefix>` and `--jobs <n>` in any order, then `--ir <path>`. The
cache lives beside the IR, in the user's build directory. -/
def proveArgs : List String → Option (ProveOptions × String) :=
  go none 4
where
  go (only : Option String) (jobs : Nat) : List String → Option (ProveOptions × String)
    | ["--ir", path] =>
      some ({ only, jobs, cache := (System.FilePath.mk path).parent.getD "." / "prove-cache" }, path)
    | "--only" :: p :: rest => go (some p) jobs rest
    | "--jobs" :: n :: rest => n.toNat?.bind fun j => if j = 0 then none else go only j rest
    | _ => none

end Tazuna.Cli
