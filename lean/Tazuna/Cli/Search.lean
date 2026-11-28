import Tazuna.Cli.Check
import Tazuna.Smt.Break
import Std.Sync.Semaphore
import Lean.Util.ShareCommon
import Tazuna.Smt.Bounds
import Tazuna.Smt.PairOrders
import Tazuna.Smt.Reached
import Tazuna.Smt.Boundary
import Tazuna.Trace.ReplayOk

/-! What `prove` and `generate` share: their options, the solver pool, the lines of a refused encoding and of a
service's scope, and the search of a service's unrolled run depth by depth for a model of a goal, each depth split into
cubes (`CubesCover`), with each depth's run built once for every search over it. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace

/-- The `why` of a question the wall-clock safety net stopped. -/
def timeoutWhy (ms : Nat) : String :=
  s!"the solver ran past {ms} ms of wall clock before its resource limit, which decides every other answer"

/-- A service of a checked spec with what its checks give the commands: its membership, so `c.checked` applies, and its
layout's step environment, which `stepEnv_ofService` proves is found. -/
structure CheckedService (c : CheckedSpec) where
  v : ServiceV
  mem : v ∈ c.spec.services
  senv : StepEnv (Layout.ofService c.program.defs v) (shapes v)

/-- The step environment a found one proves exists. -/
def stepEnvOf {L : Layout} {v : ServiceV} (h : ∃ senv, StepEnv.of L (shapes v) = .ok senv) : StepEnv L (shapes v) :=
  match e : StepEnv.of L (shapes v) with
  | .ok senv => senv
  | .error _ => False.elim (by obtain ⟨_, h⟩ := h; rw [e] at h; cases h)

/-- Each service of the spec, in order. -/
def _root_.Tazuna.Smt.CheckedSpec.services (c : CheckedSpec) : List (CheckedService c) :=
  c.spec.services.attach.map fun ⟨v, hv⟩ => ⟨v, hv, stepEnvOf (stepEnv_ofService c.program.defs (c.checked v hv))⟩

abbrev CheckedService.L {c : CheckedSpec} (s : CheckedService c) : Layout := Layout.ofService c.program.defs s.v

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
def boundsOf (T : List TypeDecl) (L : Layout) (v : ServiceV) (keep : Ty → Bool) : List Json :=
  L.types.filterMap fun (t, _) =>
    let machines := (v.machines.filter fun m => (Ty.same m.table t).isSome).map (Json.str ·.name)
    let line (name bound : String) : Option Json :=
      some (Json.mkObj ([("type", Json.str name), ("bound", Json.str bound), ("slots", Lean.toJson (L.count t))] ++
        if machines.isEmpty then [] else [("machines", Json.arr machines.toArray)]))
    if !keep t then none
    else if (Ty.same t (pendingTable (shapes v))).isSome then
      if (shapes v).isEmpty then none else line "pending requests" (stepBound v (L.count t) t)
    else match t with
      | .table .. | .bag _ => line (tyText T t) (stepBound v (L.count t) t)
      | .list _ => line (tyText T t) "longest literal"
      | _ => none

/-- Every bound a step of the service can go past: each bound of its layout. A list from an input can be longer than
every literal of its type, so lists are named too. -/
def scopeBounds (T : List TypeDecl) (L : Layout) (v : ServiceV) : List Json := boundsOf T L v fun _ => true

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
def inputBounds (T : List TypeDecl) (L : Layout) (v : ServiceV) : List Json :=
  let held := Ty.collectionsOf (inputTys v)
  boundsOf T L v fun t => held.any fun u => (Ty.same t u).isSome

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

/-- The options of `prove` and `generate`: the model `--model` names, if any, the prefix `--only` keeps lines by, how
many solvers run at once, the cache directory, and the wall-clock limit of the run in seconds, if any. -/
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
/-- The arguments of `prove` and `generate` after their own: `--model <name>`, `--only <prefix>`, `--jobs <n>` and
`--timeout <seconds>` in any order, then `--ir <path>`. The cache lives beside the IR, in the user's build directory. -/
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

/-- Whether each question of a family is unsat, read as `allUnsat` reads one, all of them asked in order. -/
def eachUnsat (solver : Solver) (cache : System.FilePath) (inputs : List String) (ids : Option Nat)
    (qs : List (List String × Thunk (Option TypedScript))) : IO (Except String (List Bool)) := do
  let mut us := #[]
  for (name, q) in qs do
    match ← allUnsat solver cache inputs ids [(name, q)] with
    | .error m => return .error m
    | .ok u => us := us.push u
  return .ok us.toList

/-- How many cubes a search asks at once, in their order, taking the first with a model: fixed, so the questions asked
and the trace found are the same whatever the number of solvers. -/
def cubeChunk : Nat := 4

/-- The solver for a cube's second question. A cube that can still split and that the solver leaves undecided is asked
once more before it splits, with the resource limit of a whole chunk of cubes (`cubeChunk` times the solver's), the
most the split's first chunk can cost. Only an unsat answer is read: the cube then has no model, so no cube of its
split has one. A sat answer is not, so the run found stays the one the split finds: the limit only stops the solver, so
a decided answer is the same under any limit it fits in. -/
def _root_.Tazuna.Smt.Solver.retry (s : Solver) : Solver := { s with rlimit := cubeChunk * s.rlimit }

/-- One depth's unrolled run as every goal at that depth shares it: its base, merged into one object per equal subterm
(`shareCommon`, the identity on values) so a goal built from its steps finds its shared terms among the assertions'
at once, with the merging's state, which merges a cube's goal into the same objects, the input kinds it refused with their refusals (no gap, by `unrollBase_ofService`), and for each smaller
number `j` of steps the prefix its cubes with `j` unfixed steps are asked with (`cubeAsk`: the run of `j` steps, this
depth's declarations and literals), printed once when a cube first needs it, and the same prefixes under the second
question's limit (`Solver.retry`). -/
structure DepthRun (v : ServiceV) (n : Nat) where
  base : UnrollBase v n
  merged : ShareCommon.State Lean.ShareCommon.persistentObjectFactory
  refused : List (SymInput v (shapes v) n × Refused)
  prefixes : Array (Thunk (Option SentPrefix))
  retries : Array (Thunk (Option SentPrefix))

abbrev Depth (v : ServiceV) (n : Nat) := Except Refused (DepthRun v n)

section
variable (solver : Solver) {c : CheckedSpec} (s : CheckedService c)

/-- The run at depth `d`, each goal aside, with its cubes' prefixes over the runs `ds` of fewer steps. -/
def depthAt (ds : Array (Task (Option (Depth s.v s.senv.nT)))) (d : Nat) : Depth s.v s.senv.nT :=
  (Sound.get (unrollBase s.L c.T c.P s.v s.senv (List.replicate d none))
    (unrollBase_ofService s.mem c.T s.senv _)).map fun ⟨B, hB⟩ =>
    let refused := B.refused.attach.map fun ⟨p, hp⟩ => (p.1, p.2.refused (hB p hp))
    let (B, merged) := (ShareCommon.State.mk Lean.ShareCommon.persistentObjectFactory).shareCommon B
    let ls := B.script.lits
    let ids := s.L.ids
    let shared (Bj : UnrollBase s.v s.senv.nT) : TypedScript :=
      ⟨B.datatypes, B.tys, B.vars, [], Bj.asserts ++ [litsFact ls]⟩
    let prefixes (header : List String) := (List.range d).toArray.map fun j => Thunk.mk fun _ =>
      match (ds[j]?).bind (·.get) with
      | some (.ok r) => some ((shared r.base).script.sentPrefix? ids header)
      | _ => none
    ⟨B, merged, refused, prefixes solver.header, prefixes solver.retry.header⟩

/-- Each depth from 0 to `k`, built by its own job holding a permit of `pool`, once for every search over it: the
jobs, and each depth as a task a search awaits when it reaches that depth; none if its job never ran, an engine bug. -/
def depthJobs (pool : Std.Semaphore) (k : Nat) :
    IO (Array Job × Array (Task (Option (Depth s.v s.senv.nT)))) := do
  let ps ← (List.range (k + 1)).toArray.mapM fun _ => IO.Promise.new
  let ds := ps.map (·.resultD none)
  let jobs := ps.zipIdx.map fun (p, d) => ((d, fun d => withPermit pool (p.resolve (some (depthAt solver s ds d)))) : Job)
  return (jobs, ds)

end

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

/-- What a search over depths found. -/
inductive SearchResult (α : Type) where
  /-- A model at depth `steps`, played back. -/
  | found (steps : Nat) (a : α)
  /-- No model at any depth up to `steps`. -/
  | noModel (steps : Nat)
  /-- No pick is live (`live` gave none): no step of any kind can be the last, at any depth. -/
  | dead
  | undecided (kind : Kind) (fields : List (String × Json))

/-- What a cube's question gave. -/
inductive CubeAnswer (α : Type) where
  /-- A model, played back. -/
  | found (a : α)
  /-- No model: unsat, or a goal false by its shape (`Term.falsy`). -/
  | none
  /-- No answer: the kind and fields of its undecided line. -/
  | open (kind : Kind) (fields : List (String × Json))

section
variable (solver : Solver) (cache : System.FilePath) {c : CheckedSpec} (s : CheckedService c)

/-- The search over the depths 1, 2, ... of the service's unrolled run (`ds`, each awaited when the search reaches it)
for a model of the goal each depth's steps give, stopping at the first, whose decoded run `play` reads. A depth is
asked as cubes (`CubesCover`): one per pick of its last step, and a cube with no answer, which its second question
(`Solver.retry`) does not find unsat, splits on the step before its fixed ones, in pick order. A cube whose last step
takes only kinds `ruledOut` rules out needs no question, nor, from depth 2 on, once depth 1 found no model, one whose
last pick is not among those `live` gives. The cubes are asked
`cubeChunk` at a time, and the first in order with a model is the one taken, so the questions and the run found do not
depend on timing. A depth whose cubes all have no model is unreached; a cube with every step fixed and no answer
leaves the depth undecided. A refused encoding of the run or of the goal ends the search undecided; a refused input
kind (which the script then lacks) leaves it undecided unless a model is found. `what` names the search in an engine
bug's message. With `brk`, a target a fault breaks, the search is for a run that breaks it (`BreakCover`): a cube's
last fixed step is a break step (`breakAfter`) and `goal` is not read, and `live` gives at every depth the picks of
the kinds whose step question whether the step breaks the target is not unsat. -/
def searchDepths {α : Type} (what : String) (ds : Array (Task (Option (Depth s.v s.senv.nT))))
    (live : IO (Except String (Option (List Nat))) := pure (.ok none))
    (ruledOut : SymInput s.v (shapes s.v) s.senv.nT → Bool := fun _ => false) (brk : Option Target := none)
    (goal : List (UnrollStep s.v s.senv.nT) → Except Refused Term) (play : List (Input s.v) → Except String α) :
    IO (Except String (SearchResult α)) := do
  let fail (m : String) : Except String (SearchResult α) := .error s!"service {s.v.name}, {what}: {m}"
  let undecided (step : Option String) (r : Refused) : Except String (SearchResult α) :=
    match refusedLine c.T r with
    | .ok (kind, fields) => .ok (.undecided kind (step.toList.map (("step", Json.str ·)) ++ fields))
    | .error m => fail m
  let depth (j : Nat) : IO (Except (Except String (SearchResult α)) (DepthRun s.v s.senv.nT)) := do
    let some t := ds[j]? | return .error (fail s!"depth {j} has no job")
    match ← IO.wait t with
    | none => return .error (fail s!"depth {j} was never built")
    | some (.error r) => return .error (undecided none r)
    | some (.ok r) => return .ok r
  -- The layout once: `CheckedService.L` derives it from the program at each use.
  let L := s.L
  let ids := L.ids
  let some S0 := initState L s.v | return fail "the initial state has no terms, which its depths' runs rule out"
  let mut refused : Option (SymInput s.v (shapes s.v) s.senv.nT × Refused) := none
  let liveAll ← if brk.isSome then
    match ← live with
    | .error m => return .error m
    | .ok ks => pure ks
    else pure none
  let mut liveFrom2 : Option (Option (List Nat)) := none
  for d in List.range' 1 (ds.size - 1) do
    let rd ← match ← depth d with
      | .error e => return e
      | .ok r => pure r
    if refused.isNone then refused := rd.refused.head?
    let livePicks ← if brk.isSome then pure liveAll
      else if d < 2 then pure none
      else match liveFrom2 with
        | some ks => pure ks
        | none =>
          match ← live with
          | .error m => return .error m
          | .ok ks => liveFrom2 := some ks; pure ks
    if livePicks == some [] then return .ok .dead
    -- A cube's question: its fixed steps after the run of its unfixed ones, and its goal; none where the goal is
    -- false by its shape, which needs no solver.
    let prepare (ps : List Nat) :
        IO (Except (Except String (SearchResult α)) (Option (List Nat × List (UnrollStep s.v s.senv.nT) × Term))) := do
      if let (some ks, some k) := (livePicks, ps.getLast?) then
        if !ks.contains k then return .ok none
      let rj ← match ← depth (d - ps.length) with
        | .error e => return .error e
        | .ok r => pure r
      do
        let B ← match extendBase L c.T c.P s.v s.senv S0 rj.base ((if brk.isSome then ps.dropLast else ps).map some) with
          | .error _ => return .error (fail s!"cube {ps} of depth {d} refused, which its depth's run rules out")
          | .ok B => pure B
        if !B.refused.isEmpty && rd.refused.isEmpty then
          return .error (fail s!"cube {ps} of depth {d} refused a kind its depth's run did not")
        match brk, ps.getLast? with
        | some g, some k =>
          let (_, asserts, st, brkRefused) := breakAfter L c.T c.P s.v s.senv S0 B k g
          if !brkRefused.isEmpty && rd.refused.isEmpty then
            return .error (fail s!"break cube {ps} of depth {d} refused a kind its depth's run did not")
          let q := breakGoal rj.base B asserts
          if q.falsy then return .ok none
          return .ok (some (ps, B.steps ++ [st], (rj.merged.shareCommon q).1))
        | some _, none => return .error (fail s!"a break cube of depth {d} fixes no step")
        | none, _ =>
          if B.steps.getLast?.any fun st => st.kinds.all (ruledOut ·.1) then return .ok none
          let g ← match goal B.steps with
            | .error r => return .error (undecided none r)
            | .ok g => pure g
          let q := cubeGoal rj.base B g
          if q.falsy then return .ok none
          return .ok (some (ps, B.steps, (rj.merged.shareCommon q).1))
    -- A cube asked with the prefix of its unfixed steps at this depth; the exact script only once every step is fixed.
    let ask (cube : List Nat × List (UnrollStep s.v s.senv.nT) × Term) :
        IO (Except (Except String (SearchResult α)) (CubeAnswer α)) := do
      let (ps, steps, q) := cube
      let j := d - ps.length
      let some pre := (rd.prefixes[j]?.map (·.get)).join | return .error (fail s!"depth {d} has no prefix for {j} steps")
      let some answer ← solver.askGoal cache ids pre q (fallback := j == 0)
        | return .error (fail s!"depth {d}: {noText}")
      if let (.unknown _, true) := (answer, j != 0) then
        let some pre := (rd.retries[j]?.map (·.get)).join
          | return .error (fail s!"depth {d} has no prefix for {j} steps")
        let some empty ← solver.retry.askUnsat cache pre q | return .error (fail s!"depth {d}: {noText}")
        if empty then return .ok .none
      match answer with
      | .unsat => return .ok .none
      | .unknown why => return .ok (.open (.undecided .unknown) [("depth", Lean.toJson d), ("why", Json.str why)])
      | .timeout ms =>
        return .ok (.open (.undecided .timeout) [("depth", Lean.toJson d), ("why", Json.str (timeoutWhy ms))])
      | .sat vs =>
        -- `unroll_decode`: every model's unrolled steps decode to a run that faults nowhere; a break step's input is
        -- the kind it takes, decoded, and `play` runs the whole run in Lean.
        let some xs := steps.mapM (·.decode (modelOf vs) L s.callerData)
          | return .error (fail s!"a model of depth {d} does not decode")
        match play xs with
        | .ok a => return .ok (.found a)
        | .error why => return .error (fail s!"a model of depth {d} {why}")
    let splits (ps : List Nat) : List (List Nat) := (List.range (pickCount s.v)).map (· :: ps)
    let mut todo := splits []
    let mut open? : Option (Kind × List (String × Json)) := none
    while !todo.isEmpty do
      -- The next `cubeChunk` cubes in order that need the solver.
      let mut chunk := []
      while chunk.length < cubeChunk && !todo.isEmpty do
        let ps := todo.head!
        todo := todo.tail
        match ← prepare ps with
        | .error e => return e
        | .ok none => pure ()
        | .ok (some cube) => chunk := chunk ++ [cube]
      let tasks ← chunk.mapM fun cube => IO.asTask (ask cube) (prio := .dedicated)
      let mut next := []
      for ((ps, _), t) in chunk.zip tasks do
        match ← IO.ofExcept (← IO.wait t) with
        | .error e => return e
        | .ok (.found a) => return .ok (.found d a)
        | .ok .none => pure ()
        | .ok (.open kind fields) =>
          if ps.length < d then next := next ++ splits ps
          else if open?.isNone then open? := some (kind, fields)
      todo := next ++ todo
    if let some (kind, fields) := open? then return .ok (.undecided kind fields)
  match refused with
  | some (inp, r) => return undecided (some inp.text) r
  | none => return .ok (.noModel (ds.size - 1))

end

end Tazuna.Cli
