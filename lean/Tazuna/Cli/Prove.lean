import Tazuna.Cli.Check
import Tazuna.Trace.Run
import Tazuna.Smt.Prove
import Tazuna.Semantics.After
import Tazuna.Smt.ServiceLayout

/-! The `prove` command: for each target of each service, the base case by evaluating the initial state and one
question per input kind for the step, one line per question. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace

def _root_.Tazuna.Smt.Target.text : Target → String
  | .invariant none r => "invariant " ++ ruleText r
  | .invariant (some m) r => m ++ " invariant " ++ ruleText r
  | .ensures c r => c ++ " ensures " ++ ruleText r
where
  ruleText : Option String → String
    | some r => r
    | none => "(a computed name)"

def _root_.Tazuna.Smt.Target.machine? : Target → Option String
  | .invariant m _ => m
  | .ensures .. => none

def _root_.Tazuna.Smt.Target.isInvariant : Target → Bool
  | .invariant .. => true
  | .ensures .. => false

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

/-- Whether only the target questions of this input kind decide an `ensures` target of the command. -/
def _root_.Tazuna.Smt.SymInput.command? : SymInput v shs n → Option String
  | .command i .. => some (v.commands.get i).name
  | _ => none

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
  | .ensures .. => []

/-- One line of the report, with what decides the verdicts of the targets it is about. -/
inductive Report where
  /-- The question about `target` (none: the bound question) of the input kind `step` was unsat. -/
  | unsat (service step : String) (command? : Option String) (target : Option Target)
  /-- A state and input that break the target, from the initial state or from a state of the right shape. -/
  | violated (service step : String) (target : Target) (fields : List (String × Json))
  /-- A state of the right shape whose step of the kind leaves the slots or a side condition. -/
  | boundReached (service step : String) (command? : Option String) (fields : List (String × Json))
  /-- No verdict: the solver's, or a refusal of the encoding. -/
  | undecided (kind : Kind) (service step : String) (command? : Option String) (target : Option Target)
      (fields : List (String × Json))

structure ProveResult where
  reports : List Report := []
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
      else some (.unsat v.name "init" none (some g))
    | _ => none

-- A step that does not reach its invariant check shows no state after it, nor rules broken there; out lines without
-- a wire form show as none.
set_option linter.tazuna.silentDefault false in
/-- The report of one question's answer. -/
def answerReport (L : Layout) (senv : StepEnv L (shapes v c.P)) (q : Question v (shapes v c.P) senv.nT)
    (a : Smt.Answer) : Except String Report :=
  let name := q.input.text
  match a with
  | .unsat => .ok (.unsat v.name name q.input.command? q.target)
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name name q.input.command? q.target [("why", Json.str why)])
  | .sat vs =>
    let M := modelOf vs
    if hc : v.caller.isData = true then
      match (SymState.vars (v := v) 0).decode M L c.T (shapes v c.P), q.input.decode M L hc with
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
        | none => .ok (.boundReached v.name name q.input.command? fields)
        | some g =>
          let violated := match g, r.outcome with
            | .ensures .., .fault (.ensures n) => [n]
            | g, _ => (after.map fun (a : Acc v) => brokenAt a.state g).getD []
          .ok (.violated v.name name g (fields ++ [("violated", Json.arr (violated.map Json.str).toArray)]))
      | _, _ => .error s!"a model of {name} does not decode"
    else .error "the caller type is no data"

-- The bound question has no target, and its name says so.
set_option linter.tazuna.silentDefault false in
/-- Every report of the service: the base case, then each input kind's questions in order. -/
def serviceReports (only : String → Bool) : IO ProveResult := do
  let L := Layout.ofService c.program.defs v
  let .ok senv := StepEnv.of L (shapes v c.P)
    | return { internal := some s!"service {v.name}: no step environment in its layout" }
  let b := 5 + v.machines.length
  let mut reports : List Report := []
  let mut targets : List Target := []
  for inp in stepInputs v (shapes v c.P) senv.nT b do
    let step := inp.text
    match questions L c.T c.P v senv inp with
    | .error r =>
      match refusalLine c.T r with
      | some (k, fields) => reports := reports ++ [.undecided k v.name step inp.command? none fields]
      | none => return { internal := some s!"service {v.name}, {step}: the encoding refused: {reprStr r}" }
    | .ok (gs, qs) =>
      for g in gs do
        unless targets.contains g do targets := targets ++ [g]
      for q in qs do
        let name := v.name ++ "/" ++ ((q.target.map Target.text).getD "bounds") ++ "/" ++ step
        unless only name do continue
        match answerReport c v L senv q (← solver.run q.script) with
        | .ok rep => reports := reports ++ [rep]
        | .error m => return { internal := some m }
  let init := (initReports c v targets).filter fun
    | .unsat _ _ _ (some g) | .violated _ _ g _ => only (v.name ++ "/" ++ g.text ++ "/init")
    | _ => false
  return { reports := init ++ reports }

end

def targetOf : Report → Option Target
  | .unsat _ _ _ g | .undecided _ _ _ _ g _ => g
  | .violated _ _ g _ => some g
  | .boundReached .. => none

/-- Whether the report keeps the target from Proved: a violation, no verdict, or a step that may leave the slots,
of an input kind the target needs (every kind for an invariant, its command for an `ensures`). -/
def blocks (service : String) (g : Target) : Report → Bool
  | .unsat .. => false
  | .violated s _ g' _ => s == service && g' == g
  | .boundReached s _ cmd _ | .undecided _ s _ cmd none _ => s == service && (match g with
    | .ensures c _ => cmd == some c
    | .invariant .. => true)
  | .undecided _ s _ _ (some g') _ => s == service && g' == g

def lineOf (unproved : String → List Target) : Report → Kind × List (String × Json)
  | .unsat s step _ (some g) =>
    (.prove .proved, [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step),
      ("assumes", Json.arr (((unproved s).filter fun g' => g'.isInvariant && g' != g).map (Json.str ·.text)).toArray)])
  | .unsat s step _ none =>
    (.prove .withinBounds, [("service", Json.str s), ("step", Json.str step)])
  | .violated s step g fields =>
    (.prove .violated, [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step)] ++ fields ++
      [("assumes", Json.arr (((unproved s).filter fun g' => g'.isInvariant && g' != g).map (Json.str ·.text)).toArray)])
  | .boundReached s step _ fields =>
    (.undecided .boundReached, [("service", Json.str s), ("step", Json.str step)] ++ fields)
  | .undecided k s step _ g fields =>
    (k, [("service", Json.str s)] ++ (g.map fun g => ("target", Json.str g.text)).toList ++
      [("step", Json.str step)] ++ fields)

def prove (root path : String) (only : Option String) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok c =>
    let solver : Solver := {}
    let keep (name : String) : Bool := match only with
      | some p => p.isPrefixOf name
      | none => true
    let mut reports : List Report := []
    for v in c.spec.services do
      let r ← serviceReports solver c v keep
      if let some m := r.internal then
        IO.eprintln s!"tazuna-engine: internal error: {m}"
        return 4
      reports := reports ++ r.reports
    let targets := reports.filterMap fun r => (targetOf r).map fun g => (r, g)
    let unproved (s : String) : List Target :=
      (targets.filterMap fun (r, g) => match r with
        | .unsat s' .. | .violated s' .. | .undecided _ s' .. => if s' == s && reports.any (blocks s g) then some g else none
        | .boundReached .. => none).foldl (fun acc g => if acc.contains g then acc else acc ++ [g]) []
    for r in reports do
      let (k, fields) := lineOf unproved r
      printLine k fields
    if reports.any fun | .violated .. => true | _ => false then return 1
    if reports.any fun | .boundReached .. | .undecided .. => true | _ => false then return 2
    return 0

end Tazuna.Cli
