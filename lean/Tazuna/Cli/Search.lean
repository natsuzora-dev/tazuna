import Tazuna.Cli.Check
import Tazuna.Smt.Unroll
import Tazuna.Smt.Bounds
import Tazuna.Smt.PairOrders
import Tazuna.Smt.Reached
import Tazuna.Smt.Boundary
import Tazuna.Trace.ReplayOk

/-! What `prove` and `generate` share: their options, the solver pool, the lines of a refused encoding and of a
service's scope, and the search of a service's unrolled run depth by depth for a model of a goal, with each depth's
run built once for every search over it. -/

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
  | .tableKey t => s!"a value of {tyText T t} holds a table whose key is no plain value"

/-- Every bound of the service's layout among the types `keep` holds: each table, bag and list type, and the pending
requests where the service has a request shape, with the bound its slots come from (`stepBound`; a list's, its type's
longest literal) and its slots as `Layout.count` gives them, the function every slot-fit premise (`StepFits`, `RunIn`,
`RespFits`, `inputVals`) reads. -/
def boundsOf (T : List TypeDecl) (L : Layout) (v : ServiceV) (keep : Ty → Bool) : List Json :=
  L.types.filterMap fun (t, _) =>
    let line (name bound : String) : Option Json :=
      some (Json.mkObj [("type", Json.str name), ("bound", Json.str bound), ("slots", Lean.toJson (L.count t))])
    if !keep t then none
    else if (Ty.same t (pendingTable (shapes v))).isSome then
      if (shapes v).isEmpty then none else line "pending requests" (stepBound v t)
    else match t with
      | .table .. | .bag _ => line (tyText T t) (stepBound v t)
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

/-- A builder's refusal as a line where it is the spec's; else an engine bug, a case the loaded program's types rule
out. -/
def refusedLine (T : List TypeDecl) : Refused → Except String (Kind × List (String × Json))
  | .spec l => .ok (.undecided .limit, [("limit", Json.str (l.text T))])
  | .unexpected u => .error s!"the encoding met a case the loaded program's types rule out: {reprStr u}"

/-- The options of `prove` and `generate`: the prefix `--only` keeps lines by, how many solvers run at once, and the
cache directory. -/
structure Options where
  only : Option String := none
  jobs : Nat := 4
  cache : System.FilePath

/-- Whether `--only` keeps the line named `name`. -/
def Options.keeps (o : Options) (name : String) : Bool := match o.only with
  | some p => p.isPrefixOf name
  | none => true

-- An IR path without a directory part is in the working directory.
set_option linter.tazuna.silentDefault false in
/-- The arguments of `prove` and `generate` after their own: `--only <prefix>` and `--jobs <n>` in any order, then
`--ir <path>`. The cache lives beside the IR, in the user's build directory. -/
def optionsOf : List String → Option (Options × String) :=
  go none 4
where
  go (only : Option String) (jobs : Nat) : List String → Option (Options × String)
    | ["--ir", path] =>
      some ({ only, jobs, cache := (System.FilePath.mk path).parent.getD "." / "prove-cache" }, path)
    | "--only" :: p :: rest => go (some p) jobs rest
    | "--jobs" :: n :: rest => n.toNat?.bind fun j => if j = 0 then none else go only j rest
    | _ => none

/-- A job of the solver pool: its argument and its work. A job whose pure work is its point (building a depth) takes
what it builds from as its argument: a job closed over it would have that work floated out of the job by the compiler,
onto the thread that makes the jobs. -/
abbrev Job := Nat × (Nat → IO Unit)

/-- `f` as a job, and where its result lands; none once the pool has run means the job never ran, an engine bug. -/
def Job.of {α : Type} (f : IO α) : IO (Job × IO.Ref (Option α)) := do
  let r ← IO.mkRef none
  pure ((0, fun _ => do r.set (some (← f))), r)

/-- Every job, at most `jobs` at a time, each taken in order by the next free worker. -/
def runAll (jobs : Nat) (xs : Array Job) : IO Unit := do
  let next ← IO.mkRef 0
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < xs.size then xs[i].2 xs[i].1 else break
  let tasks ← (List.range (max jobs 1)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  for t in tasks do
    match ← IO.wait t with
    | .ok () => pure ()
    | .error e => throw e

section
variable (solver : Solver) {c : CheckedSpec} (s : CheckedService c)

/-- One depth's unrolled run as every goal at that depth shares it: its base, merged into one object per equal subterm
(`shareCommon'`, the identity on values) so a goal built from its steps finds its shared terms among the assertions'
at once, the input kinds it refused with their refusals (no gap, by `unrollBase_ofService`), and the prefix of its
scripts (`ScriptPrefix`), read once; or the refusal of its encoding. -/
abbrev Depth (v : ServiceV) (n : Nat) :=
  Except Refused (UnrollBase v n × List (SymInput v (shapes v) n × Refused) × SentPrefix)

/-- The run at depth `d`, each goal aside. -/
def depthAt (d : Nat) : Depth s.v s.senv.nT :=
  (Sound.get (unrollBase s.L c.T c.P s.v s.senv d) (unrollBase_ofService s.mem c.T s.senv d)).map fun ⟨B, hB⟩ =>
    let refused := B.refused.attach.map fun ⟨p, hp⟩ => (p.1, p.2.refused (hB p hp))
    let B := ShareCommon.shareCommon' B
    (B, refused, B.script.sentPrefix? s.L.ids solver.header)

/-- Each depth from 1 to `k`, built by its own job once for every search over it: the jobs, and each depth as a task a
search awaits when it reaches that depth; none if its job never ran, an engine bug. -/
def depthJobs (k : Nat) : IO (Array Job × Array (Task (Option (Depth s.v s.senv.nT)))) := do
  let mut jobs : Array Job := #[]
  let mut ds := #[]
  for d in List.range' 1 k do
    let p ← IO.Promise.new
    jobs := jobs.push (d, fun d => (p.resolve (some (depthAt solver s d)) : BaseIO Unit))
    ds := ds.push (p.resultD none)
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
  | undecided (kind : Kind) (fields : List (String × Json))

section
variable (solver : Solver) (cache : System.FilePath) {c : CheckedSpec} (s : CheckedService c)

/-- The search over the depths 1, 2, ... of the service's unrolled run (`ds`, each awaited when the search reaches it)
for a model of the goal each depth's steps give, stopping at the first, whose decoded run `play` reads. A refused
encoding of the run or of the goal ends the search undecided; a refused input kind (which the script then lacks)
leaves it undecided unless a model is found. `what` names the search in an engine bug's message. -/
def searchDepths {α : Type} (what : String) (ds : Array (Task (Option (Depth s.v s.senv.nT))))
    (goal : List (UnrollStep s.v s.senv.nT) → Except Refused Term) (play : List (Input s.v) → Except String α) :
    IO (Except String (SearchResult α)) := do
  let fail (m : String) : Except String (SearchResult α) := .error s!"service {s.v.name}, {what}: {m}"
  let undecided (step : Option String) (r : Refused) : Except String (SearchResult α) :=
    match refusedLine c.T r with
    | .ok (kind, fields) => .ok (.undecided kind (step.toList.map (("step", Json.str ·)) ++ fields))
    | .error m => fail m
  let mut refused : Option (SymInput s.v (shapes s.v) s.senv.nT × Refused) := none
  for (t, i) in ds.toList.zipIdx do
    let d := i + 1
    let some depth ← IO.wait t | return fail s!"depth {d} was never built"
    let (B, kinds, pre) ← match depth with
      | .error r => return undecided none r
      | .ok x => pure x
    let g ← match goal B.steps with
      | .error r => return undecided none r
      | .ok g => pure g
    let U := B.withGoal g
    if refused.isNone then refused := kinds.head?
    let some answer ← solver.askGoal cache s.L.ids pre g | return fail s!"depth {d}: {noSort}"
    match answer with
    | .unsat => pure ()
    | .unknown why => return .ok (.undecided (.undecided .unknown) [("depth", Lean.toJson d), ("why", Json.str why)])
    | .timeout ms =>
      return .ok (.undecided (.undecided .timeout) [("depth", Lean.toJson d), ("why", Json.str (timeoutWhy ms))])
    | .sat vs =>
      -- `unroll_decode`: every model's steps decode to a run that faults nowhere.
      let some xs := U.steps.mapM (·.decode (modelOf vs) s.L s.callerData)
        | return fail s!"a model of depth {d} does not decode"
      match play xs with
      | .ok a => return .ok (.found d a)
      | .error why => return fail s!"a model of depth {d} {why}"
  match refused with
  | some (inp, r) => return undecided (some inp.text) r
  | none => return .ok (.noModel ds.size)

end

end Tazuna.Cli
