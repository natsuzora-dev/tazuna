import Tazuna.Cli.Check
import Tazuna.Smt.Break
import Std.Sync.Semaphore
import Lean.Util.ShareCommon
import Tazuna.Smt.Bounds
import Tazuna.Smt.PairOrders
import Tazuna.Smt.Reached
import Tazuna.Smt.Boundary
import Tazuna.Trace.ReplayOk
import Tazuna.Smt.GenGoal
import Tazuna.Trace.Verify

/-! What prove, explore and search share: their options, the solver pool, the lines of a refused encoding and of a
service's scope, the targets' texts, and the traces explore and search write for a run they found. -/


namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace

/-- The `why` of a question the wall-clock safety net stopped. -/
def timeoutWhy (ms : Nat) : String :=
  s!"the solver ran past {ms} ms of wall clock before its resource limit, which decides every other answer"

/-- A service of a checked spec with what its checks give the commands: its membership, so `c.checked` applies, the
bounds its model's scope gives it, and its layout's step environment, which `stepEnv_ofService` proves is found. -/
structure CheckedService (c : CheckedSpec) where
  v : ServiceV
  mem : v ∈ c.spec.services
  b : BoundsV v.records
  senv : StepEnv (Layout.ofService c.program.defs v b) (shapes v)

/-- The step environment a found one proves exists. -/
def stepEnvOf {L : Layout} {v : ServiceV} (h : ∃ senv, StepEnv.of L (shapes v) = .ok senv) : StepEnv L (shapes v) :=
  match e : StepEnv.of L (shapes v) with
  | .ok senv => senv
  | .error _ => False.elim (by obtain ⟨_, h⟩ := h; rw [e] at h; cases h)

/-- Each service of the model's spec, in order, within the bounds the model gives it. -/
def CheckedModel.services (cm : CheckedModel) : List (CheckedService cm.checked) :=
  cm.checked.spec.services.attach.map fun ⟨v, hv⟩ =>
    ⟨v, hv, cm.bounds v hv, stepEnvOf (stepEnv_ofService (bnd := cm.bounds v hv) cm.checked.program.defs (cm.checked.checked v hv))⟩

abbrev CheckedService.L {c : CheckedSpec} (s : CheckedService c) : Layout := Layout.ofService c.program.defs s.v s.b

theorem CheckedService.callerData {c : CheckedSpec} (s : CheckedService c) : s.v.caller.isData = true :=
  (c.checked s.v s.mem).callerData

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

/-- The input kind by its place, which tells apart kinds whose text is the same (answers to two pending shapes with
the same request and sender). -/
def _root_.Tazuna.Smt.SymInput.place : SymInput v shs n → String
  | .command i .. => s!"command {(i : Nat)}"
  | .query i .. => s!"query {(i : Nat)}"
  | .answer k j .. => s!"answer {(k : Nat)} {(j : Nat)}"
  | .unmatched .. => "unmatched answer"
  | .event i _ => s!"event {(i : Nat)}"
  | .clock _ => "clock"

end

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
  | .point .day => "Date"
  | .point .ms => "Instant"
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
  | .tableKey t => s!"a value of {tyText T t} holds a table whose key is no plain value"

/-- Every bound of the service's layout among the types `keep` holds: each table, bag and list type, and the pending
requests where the service has a request shape, with the bound its slots come from (`stepBound`), its slots as
`Layout.count` gives them, the function every slot-fit premise (`StepFits`, `RunIn`, `RespFits`, `inputVals`) reads,
and the machines whose table of instances has the type. -/
def boundsOf (T : List TypeDecl) (L : Layout) (v : ServiceV) (b : BoundsV v.records) (keep : Ty → Bool) : List Json :=
  L.types.filterMap fun (t, _) =>
    let machines := (v.machines.filter fun m => (Ty.same m.table t).isSome).map (Json.str ·.name)
    let line (name bound : String) : Option Json :=
      some (Json.mkObj ([("type", Json.str name), ("bound", Json.str bound), ("slots", Lean.toJson (L.count t))] ++
        if machines.isEmpty then [] else [("machines", Json.arr machines.toArray)]))
    if !keep t then none
    else if (Ty.same t (pendingTable (shapes v))).isSome then
      if (shapes v).isEmpty then none else line "pending requests" (stepBound v b (L.count t) t)
    else match t with
      | .table .. | .bag _ => line (tyText T t) (stepBound v b (L.count t) t)
      | .list _ => line (tyText T t) "longest literal"
      | _ => none

/-- Every bound a step of the service can go past: each bound of its layout. A list from an input can be longer than
every literal of its type, so lists are named too. -/
def scopeBounds (T : List TypeDecl) (L : Layout) (v : ServiceV) (b : BoundsV v.records) : List Json :=
  boundsOf T L v b fun _ => true

mutual
/-- The lists, bags and tables a value of the type can hold, the type itself first. -/
def Ty.collections : Ty → List Ty
  | .list a => .list a :: Ty.collections a
  | .bag a => .bag a :: Ty.collections a
  | .table k w => .table k w :: Ty.collections k ++ Ty.collections w
  | .tuple ts => Ty.collectionsOf ts
  | .adt _ _ vs => Ty.collectionsOfAlts vs
  | _ => []
def Ty.collectionsOf : List Ty → List Ty
  | [] => []
  | t :: ts => Ty.collections t ++ Ty.collectionsOf ts
def Ty.collectionsOfAlts : List (List Ty) → List Ty
  | [] => []
  | ts :: vs => Ty.collectionsOf ts ++ Ty.collectionsOfAlts vs
end

/-- The bounds an input of the service can go past: the lists, bags and tables its inputs carry. A verdict over runs
covers every run only where every input fits them (`proved_sound`), so a line whose inputs may not fit names them. -/
def inputBounds (T : List TypeDecl) (L : Layout) (v : ServiceV) (b : BoundsV v.records) : List Json :=
  let held := Ty.collectionsOf (inputTys v)
  boundsOf T L v b fun t => held.any fun u => (Ty.same t u).isSome

/-- The bounds a line about runs is scoped to, from whether a step can go past the slots (`left`: a bound question is
not unsat) and whether every input and the initial state fit them: none where neither can leave them, as every state
a run reaches is then within them (`run_within`); else the bounds the inputs carry where only an input can, else the
service's whole scope. -/
def runScope (left fits : Bool) (scope inputScope : List Json) : Option (List Json) :=
  if left then some scope
  else if fits then none
  else if inputScope.isEmpty then some scope else some inputScope

/-- A builder's refusal as a line where it is the spec's; else an engine bug, a case the loaded program's types rule
out. -/
def refusedLine (T : List TypeDecl) : Refused → Except String (Kind × List (String × Json))
  | .spec l => .ok (.undecided .limit, [("limit", Json.str (l.text T))])
  | .unexpected u => .error s!"the encoding met a case the loaded program's types rule out: {reprStr u}"

/-- The options of `prove`, `explore` and `search`: the model `--model` names, if any, the prefix `--only` keeps lines
by, how many solvers run at once, the cache directory, and the wall-clock limit of the run in seconds, if any. -/
structure Options where
  model : Option String := none
  only : Option String := none
  jobs : Nat := 4
  cache : System.FilePath := "prove-cache"
  timeout : Option Nat := none

/-- Whether `--only` keeps the line named `name`. -/
def Options.keeps (o : Options) (name : String) : Bool := match o.only with
  | some p => p.isPrefixOf name
  | none => true

-- An IR path without a directory part is in the working directory.
set_option linter.tazuna.silentDefault false in
/-- The arguments of `prove`, `explore` and `search` after their own: `--model <name>`, `--only <prefix>`, `--jobs <n>`
and `--timeout <seconds>` in any order, then `--ir <path>`. The cache lives beside the IR, in the user's build
directory. -/
def optionsOf : List String → Option (Options × String) :=
  go {}
where
  go (o : Options) : List String → Option (Options × String)
    | ["--ir", path] => some ({ o with cache := (System.FilePath.mk path).parent.getD "." / "prove-cache" }, path)
    | "--model" :: m :: rest => go { o with model := some m } rest
    | "--only" :: p :: rest => go { o with only := some p } rest
    | "--jobs" :: n :: rest => n.toNat?.bind fun j => if j = 0 then none else go { o with jobs := j } rest
    | "--timeout" :: n :: rest => n.toNat?.bind fun t => go { o with timeout := some t } rest
    | _ => none

/-- The model a run checks in: its name and its values the lines name. -/
structure RunModel where
  name : String
  model : ModelV

/-- The `scope` field of a line whose verdict rests on the model: its name and the values of it the verdict reads. -/
def RunModel.field (m : RunModel) (values : List (String × Json)) : String × Json :=
  ("scope", Json.mkObj (("model", Json.str m.name) :: values))

/-- An undecided line with the resource limit it ran out of, where it is an unknown answer, which that limit decides. -/
def RunModel.undecided (m : RunModel) (k : Kind) (fields : List (String × Json)) : List (String × Json) :=
  match k with
  | .undecided .unknown => fields ++ [m.field [("resourceLimit", Json.num m.model.rlimit)]]
  | _ => fields

/-- Prints the engine's bug, as `internal` does, for a stage, which then gives nothing. -/
def stop {α : Type} (message : String) : Cmd (Option α) := do
  internal message
  pure none

/-- A job of the solver pool: its argument and its work. A job whose pure work is its point (building a depth) takes
what it builds from as its argument: a job closed over it would have that work floated out of the job by the compiler,
onto the thread that makes the jobs. -/
abbrev Job := Nat × (Nat → IO Unit)

/-- `f` as a job, and where its result lands; none once the pool has run means the job never ran, an engine bug. -/
def Job.of {α : Type} (f : IO α) : IO (Job × IO.Ref (Option α)) := do
  let r ← IO.mkRef none
  pure ((0, fun _ => do r.set (some (← f))), r)

/-- Every job, at most `jobs` at a time, each taken in order by the next free worker. Past the solver's deadline
(`Solver.deadline`) no worker takes another job, and the call returns at once without waiting for the jobs that run:
their solvers stop themselves, and a job waiting on one that never ran would never end. A job cut off so never writes
its result. -/
def runAll (solver : Solver) (jobs : Nat) (xs : Array Job) : IO Unit := do
  let next ← IO.mkRef 0
  let worker : IO Unit := do
    repeat
      if ← solver.past then break
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < xs.size then
        try xs[i].2 xs[i].1
        catch e => if ← solver.past then break else throw e
      else break
  let tasks ← (List.range (max jobs 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  if solver.deadline.isSome then
    while !(← tasks.allM fun t => IO.hasFinished t) && !(← solver.past) do
      IO.sleep 20
    if ← solver.past then
      solver.drain
      return
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e

/-- `f` holding one of the pool's permits, which bound the jobs of a kind running at once. -/
def withPermit {α : Type} (pool : Std.Semaphore) (f : IO α) : IO α := do
  IO.wait (← pool.acquire).result!
  try f finally pool.release

/-- Whether every question of a dead-target family reads unsat, asked in order: the first answer that is not unsat
settles that the target is not dead, so the rest are not asked. One job asks them all, so which run is a function of
the spec and the solver, not of the schedule. A question's script is built only where its direct key has no answer:
an entry is written only for a question asked from the same inputs, so the kind has that question. -/
def allUnsat (solver : Solver) (cache : System.FilePath) (inputs : List String) (ids : Option Nat) :
    List (List String × Thunk (Option TypedScript)) → IO (Except String Bool)
  | [] => pure (.ok true)
  | (name, q) :: rest => do
    let key := directKey inputs name
    let answer ← match ← Solver.cached cache key ids with
      | some a => pure (some (.ok a))
      | none => match q.get with
        | some q => some <$> solver.ask cache key ids q.script
        | none => pure none
    match answer with
    | none | some (.ok .unsat) => allUnsat solver cache inputs ids rest
    | some (.ok _) => pure (.ok false)
    | some (.error m) => pure (.error m)

/-- Whether an outcome is no fault. -/
instance (o : Outcome) : Decidable (∀ f, o ≠ .fault f) :=
  match o with
  | .fault f => isFalse fun h => h f rfl
  | .accepted | .answered _ | .rejected _ | .invalid _ => isTrue nofun

/-- The trace of a run a search found; else an engine bug. A run that faults nowhere and whose inputs carry only ids
from outside or ones an earlier out line showed, as `unroll_decode` proves of every model's run, always writes
(`traceOf_ok`), and its trace reads as the spec (`foundTrace_reads`). -/
def foundTrace {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (chk : Smt.Checked P E T v) (xs : List (Input v)) : Except String TraceFile :=
  if hnf : NoFaultRun T (State.init v) xs then
    if knownRun T [] (State.init v) xs then
      match h : traceOf T v xs with
      | .ok tr => .ok tr
      | .error _ => absurd h (by obtain ⟨tr, h'⟩ := traceOf_ok chk hnf; rw [h']; nofun)
    else .error "carries an id no earlier out line showed, which unroll_decode rules out"
  else
    let k := (run T v (State.init v) xs).2.findIdx fun r => match r.outcome with
      | .fault _ => true
      | _ => false
    .error s!"faults at step {k + 1}, which unroll_decode rules out"

/-- A found run's trace reads as the spec from the initial state, so verify replays it as passed unless it runs out
of tries (`replay_iff`). -/
theorem foundTrace_reads {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    {chk : Smt.Checked P E T v} (hv : v.Equivariant) {xs : List (Input v)} {tr : TraceFile}
    (h : foundTrace chk xs = .ok tr) : Reads T v (State.init v) {} tr.numbered := by
  unfold foundTrace at h
  split at h
  · rename_i hnf
    split at h
    · rename_i hkn
      split at h
      · rename_i tr' htr
        cases h
        exact traceOf_reads chk ⟨hv, fun m hm => (chk.keys m hm).2⟩ hnf hkn htr
      · rename_i htr
        obtain ⟨tr'', h''⟩ := traceOf_ok chk hnf
        rw [h''] at htr; cases htr
    · cases h
  · cases h

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

def _root_.Tazuna.Ir.GenTarget.text : GenTarget → String
  | .accepted c => c ++ " accepted"
  | .rejected c (some k) => c ++ " rejected " ++ k
  | .rejected c none => c ++ " rejected"
  | .invalid q (some r) => q ++ " invalid " ++ r
  | .invalid q none => q ++ " invalid (a computed name)"
  | .answered q => q ++ " answered"
  | .event (some k) => "event " ++ k
  | .event none => "event"
  | .request x n => "request " ++ x ++ "." ++ n

section
variable (T : List TypeDecl) (v : ServiceV) (rules : RuleNames) (g : GenTarget)

/-- Whether the last step of the run on `xs` from the initial state shows a class the target aims at, by running the
decoded run in Lean. It stays because the solver's model is not the model the decoded run is read in: `modelOf` sets
`(div a 0)`, `(mod a 0)` and a selector on a value of another constructor to fixed defaults, where z3 picks its own
values, and no theorem shows a goal's assertions never read them. `search_sound` needs every assertion to hold in the
model it reads, which z3's answer gives only under z3's own values, so this check is what keeps a written trace from
missing its target. -/
def lastHits (xs : List (Input v)) : Bool :=
  match xs.getLast? with
  | some x => (classes T v x (step T v (run T v (State.init v) xs.dropLast).1 x)).any (g.covers rules)
  | none => false

/-- The trace explore and search write for a run that reaches the target: the run's trace (`foundTrace`, which reads as
the spec) where its last step shows the target. -/
def reachTrace {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (xs : List (Input v)) :
    Except String TraceFile := do
  let tr ← foundTrace chk xs
  if lastHits T v rules g xs then .ok tr else .error "misses the target"

/-- T6: a written trace reaches its target. Its lines read as the spec from the initial state, so verify replays them
as passed unless it runs out of tries (`replay_iff`), and the last step of its run from the initial state shows a
class the target aims at. -/
theorem reach_trace {P : List AnySite} {E : List AnyEffectSite} {chk : Checked P E T v} (hv : v.Equivariant)
    {xs : List (Input v)} {tr : TraceFile} (h : reachTrace T v rules g chk xs = .ok tr) :
    Reads T v (State.init v) {} tr.numbered ∧
      ∃ ys x, xs = ys ++ [x] ∧ Hits T v rules g x (step T v (run T v (State.init v) ys).1 x) := by
  simp only [reachTrace, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i tr' htr
    split at h
    · rename_i hit
      cases h
      refine ⟨foundTrace_reads hv htr, ?_⟩
      unfold lastHits at hit
      split at hit
      · rename_i x hx
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hx
        refine ⟨ys, x, rfl, ?_⟩
        obtain ⟨c, hc, hcov⟩ := List.any_eq_true.1 hit
        simp only [List.dropLast_concat] at hc
        exact ⟨c, hc, hcov⟩
      · cases hit
    · cases h

end

section
variable (T : List TypeDecl) (v : ServiceV) (g : Target)

/-- The trace explore and search write for a run that breaks the target, with the fault: the run on `xs` from the initial state,
run in Lean, faults nowhere before its last step and faults there by a fault the target covers, and verify replays its
trace (the run's lines up to the last step's in line) to a fault the target covers at its last line. A fault the target
does not cover is the inner error: a rule whose name the run computes meets the target's (`Target.meets`) but is
another. Anything else is an engine bug. -/
def breakTrace (xs : List (Input v)) : Except String (Except String (TraceFile × Fault)) :=
  match xs.getLast? with
  | none => .error "is empty"
  | some x =>
    if NoFaultRun T (State.init v) xs.dropLast then
      match (step T v (run T v (State.init v) xs.dropLast).1 x).outcome with
      | .fault f =>
        if g.covers f then
          match traceOf T v xs with
          | .error (.fault _ _ lines) =>
            let tr : TraceFile := ⟨v.name, lines⟩
            match replay T v tr.numbered with
            | .fault n f' =>
              if n == lines.length + 1 && g.covers f' then .ok (.ok (tr, f))
              else .error s!"replays to a fault at line {n}, not to the target's at its last"
            | _ => .error "does not replay to its fault"
          | _ => .error "writes no trace that ends at its fault"
        else .ok (.error s!"faults by {(Outcome.fault f).summary}, which the target does not name")
      | _ => .error "does not fault at its last step"
    else .error "faults before its last step"

/-- A run explore or search reports as breaking a target does: the run of its inputs from the initial state faults nowhere
before its last step and faults there by a fault the target covers, and verify replays the written trace to such a
fault at its last line. -/
theorem break_trace {xs : List (Input v)} {tr : TraceFile} {f : Fault}
    (h : breakTrace T v g xs = .ok (.ok (tr, f))) :
    ∃ ys x, xs = ys ++ [x] ∧ NoFaultRun T (State.init v) ys ∧
      (step T v (run T v (State.init v) ys).1 x).outcome = .fault f ∧ g.covers f = true ∧
      ∃ f', replay T v tr.numbered = .fault (tr.lines.length + 1) f' ∧ g.covers f' = true := by
  unfold breakTrace at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hx
    simp only [List.dropLast_concat] at h
    split at h
    · rename_i hnf
      split at h
      · rename_i f0 ho
        split at h
        · rename_i hcov
          split at h
          · rename_i k f1 lines _
            split at h
            · rename_i n f' hr
              split at h
              · rename_i hok
                cases h
                simp only [Bool.and_eq_true, beq_iff_eq] at hok
                exact ⟨ys, x, rfl, hnf, ho, hcov, f', by rw [hr, hok.1], hok.2⟩
              · cases h
            all_goals cases h
          all_goals cases h
        · cases h
      all_goals cases h
    · cases h

end

end Tazuna.Cli
