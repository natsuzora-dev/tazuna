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
  | unsat (service step : String) (target : Option Target)
  /-- A state and input that break the target, from the initial state or from a state of the right shape. -/
  | violated (service step : String) (target : Target) (fields : List (String × Json))
  /-- A state of the right shape whose step of the kind goes past the bounds `bounds`, as far as the state it leaves
  shows them. -/
  | boundReached (service step : String) (bounds : List Json)
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

mutual
/-- The collection types inside the value that hold more items than the layout gives them, with their sizes. -/
def overV (L : Layout) : (t : Ty) → t.den → List (Ty × Nat)
  | .list t, xs => (if (show List t.den from xs).length > L.count (.list t) then [(.list t, xs.length)] else []) ++
      (show List t.den from xs).flatMap (overV L t)
  | .bag t, xs => (if (show List t.den from xs).length > L.count (.bag t) then [(.bag t, xs.length)] else []) ++
      (show List t.den from xs).flatMap (overV L t)
  | .table k w, x => (if x.1.length > L.count (.table k w) then [(.table k w, x.1.length)] else []) ++
      x.1.flatMap fun e => overV L k e.1 ++ overV L w e.2
  | .tuple ts, x => overVs L ts x
  | .adt (_ + 1) _ vs, x => overAlts L vs x
  | _, _ => []
def overVs (L : Layout) : (ts : List Ty) → Ty.dens ts → List (Ty × Nat)
  | [], _ => []
  | t :: ts, (x, xs) => overV L t x ++ overVs L ts xs
def overAlts (L : Layout) : (vs : List (List Ty)) → Ty.alts vs → List (Ty × Nat)
  | [], _ => []
  | fs :: _, .inl x => overVs L fs x
  | _ :: vs, .inr y => overAlts L vs y
end

/-- The bounds a state goes past: each collection type that holds more items than its slots, with the bound the slots
come from. A step can also go past a bound only inside, in a value no state keeps; then the list is empty. -/
def boundsPast (T : List TypeDecl) (L : Layout) {v : ServiceV} (shs : List (PendingShape v.event)) (s : State v) :
    List Json :=
  let over := overV L v.records (Ty.up _ v.records_data s.records) ++
    (if s.pending.length > L.count (pendingTable shs) then [(pendingTable shs, s.pending.length)] else []) ++
    s.machines.toSigma.filterMap fun ⟨m, insts⟩ =>
      if insts.length > L.count m.table then some (m.table, insts.length) else none
  let firsts := over.foldl (fun (acc : List (Ty × Nat)) o =>
    if acc.any fun a => (Ty.same a.1 o.1).isSome then acc else acc ++ [o]) []
  firsts.map fun (t, n) =>
    Json.mkObj [("type", Json.str (tyText T t)), ("bound", Json.str (boundName t)), ("slots", Lean.toJson (L.count t)),
      ("size", Lean.toJson n)]
where
  boundName : Ty → String
    | .table k w => if v.bounds.creates.any (·.bounds (.table k w)) then "creates" else "items"
    | .list _ => "list literals"
    | _ => "items"

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
def answerReport (L : Layout) (senv : StepEnv L (shapes v c.P)) (q : Question v (shapes v c.P) senv.nT)
    (a : Smt.Answer) : Except String Report :=
  let name := q.input.text
  match a with
  | .unsat => .ok (.unsat v.name name q.target)
  | .unknown why => .ok (.undecided (.undecided .unknown) v.name name q.target [("why", Json.str why)])
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
        | none => .ok (.boundReached v.name name
            ((after.map fun (a : Acc v) => boundsPast c.T L (shapes v c.P) a.state).getD []))
        | some g =>
          let violated := match g, r.outcome with
            | .ensures .., .fault (.ensures n) => [n]
            | g, _ => (after.map fun (a : Acc v) => brokenAt a.state g).getD []
          .ok (.violated v.name name g (fields ++ [("violated", Json.arr (violated.map Json.str).toArray)]))
      | _, _ => .error s!"a model of {name} does not decode"
    else .error "the caller type is no data"

-- The bound question has no target, and its name says so.
set_option linter.tazuna.silentDefault false in
/-- Every line of the service in order: the base case, then each input kind's questions. -/
def serviceItems (only : String → Bool) : ServiceItems := Id.run do
  let L := Layout.ofService c.program.defs v
  let .ok senv := StepEnv.of L (shapes v c.P)
    | return { internal := some s!"service {v.name}: no step environment in its layout" }
  let b := 5 + v.machines.length
  let mut items : List Item := []
  let mut targets : List Target := []
  for inp in stepInputs v (shapes v c.P) senv.nT b do
    let step := inp.text
    match questions L c.T c.P v senv inp with
    | .error r =>
      match refusalLine c.T r with
      | some (k, fields) => items := items ++ [.ready (.undecided k v.name step none fields)]
      | none => return { internal := some s!"service {v.name}, {step}: the encoding refused: {reprStr r}" }
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
  let init := (initReports c v targets).map fun r => match r with
    | .unsat _ _ (some g) | .violated _ _ g _ =>
      if only (v.name ++ "/" ++ g.text ++ "/init") then Item.ready r else .skipped v.name g
    | r => .ready r
  return { items := init ++ items }

end

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
    let common := [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step), assumes s g]
    some <| match past s step with
      | none => (.prove .proved, common)
      | some bs => (.prove .withinBounds, common ++ [("bounds", Json.arr bs.toArray)])
  | .unsat _ _ none | .boundReached .. => none
  | .violated s step g fields =>
    some (.prove .violated, [("service", Json.str s), ("target", Json.str g.text), ("step", Json.str step)] ++ fields ++
      [assumes s g])
  | .undecided k s step g fields =>
    some (k, [("service", Json.str s)] ++ (g.map fun g => ("target", Json.str g.text)).toList ++
      [("step", Json.str step)] ++ fields)
where
  assumes (s : String) (g : Target) : String × Json :=
    ("assumes", Json.arr (((unproved s).filter fun g' => g'.isInvariant && g' != g).map (Json.str ·.text)).toArray)

/-- The options of `prove`: the prefix `--only` keeps questions by, how many solvers run at once, and the cache
directory. -/
structure ProveOptions where
  only : Option String := none
  jobs : Nat := 4
  cache : System.FilePath

def prove (root path : String) (opts : ProveOptions) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok c =>
    let solver : Solver := {}
    let keep (name : String) : Bool := match opts.only with
      | some p => p.isPrefixOf name
      | none => true
    let mut items : List Item := []
    for v in c.spec.services do
      let r := serviceItems c v keep
      if let some m := r.internal then
        IO.eprintln s!"tazuna-engine: internal error: {m}"
        return 4
      items := items ++ r.items
    let asks := (items.filterMap fun | .ask o => some o | _ => none).toArray
    let cache := opts.cache / s!"{hash (← solver.version)}"
    let answers : Array (Except String Report) ← runAll opts.jobs
      (fun o => do pure (o.read (← solver.runCached cache o.script))) asks
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
    -- A bound question with no verdict leaves its kind's lines within the bounds, naming none.
    let past (s step : String) : Option (List Json) := reports.findSome? fun
      | .boundReached s' step' bs => if s' == s && step' == step then some bs else none
      | .undecided _ s' step' none _ => if s' == s && step' == step then some [] else none
      | _ => none
    for r in reports do
      if let some (kind, fields) := lineOf unproved past r then printLine kind fields
    if reports.any fun | .violated .. => true | _ => false then return 1
    if reports.any fun | .undecided .. => true | _ => false then return 2
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
