import Tazuna.Cli.Check
import Tazuna.Smt.Unroll
import Tazuna.Smt.Bounds
import Tazuna.Smt.PairOrders
import Tazuna.Smt.Cover

/-! What `prove` and `generate` share: their options, the solver pool, the lines of a refused encoding and of a
service's scope, and the search of a service's unrolled run depth by depth for a model of a goal, with each depth's
run built once for every search over it. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt

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

/-- The kind and fields of a refused encoding's line where the refusal is the spec's; none for an engine gap. -/
def refusalLine (T : List TypeDecl) (r : Refusal) : Option (Kind × List (String × Json)) :=
  match r with
  | .unencodableString s => some (.undecided .unencodableString, [("string", Json.str s)])
  | .limit l => some (.undecided .limit, [("limit", Json.str (l.text T))])
  | .layout _ | .unexpected _ => none

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
variable (solver : Solver) (c : CheckedSpec) (v : ServiceV) (L : Layout) (senv : StepEnv L (shapes v))

/-- One depth's unrolled run as every goal at that depth shares it: its base, merged into one object per equal subterm
(`shareCommon'`, the identity on values) so a goal built from its steps finds its shared terms among the assertions'
at once, and the prefix of its scripts (`ScriptPrefix`), read once; or the refusal of its encoding. -/
abbrev Depth (v : ServiceV) (n : Nat) := Except Refusal (UnrollBase v n × Option ScriptPrefix)

/-- The run at depth `d`, each goal aside. -/
def depthAt (d : Nat) : Depth v senv.nT :=
  (unrollBase L c.T c.P v senv d).map fun B =>
    let B := ShareCommon.shareCommon' B
    (B, B.script.prefix? solver.header)

/-- Each depth from 1 to `k`, built by its own job once for every search over it: the jobs, and each depth as a task a
search awaits when it reaches that depth; none if its job never ran, an engine bug. -/
def depthJobs (k : Nat) : IO (Array Job × Array (Task (Option (Depth v senv.nT)))) := do
  let mut jobs : Array Job := #[]
  let mut ds := #[]
  for d in List.range' 1 k do
    let p ← IO.Promise.new
    jobs := jobs.push (d, fun d => (p.resolve (some (depthAt solver c v L senv d)) : BaseIO Unit))
    ds := ds.push (p.resultD none)
  return (jobs, ds)

end

/-- What a search over depths found. -/
inductive SearchResult (α : Type) where
  /-- A model at depth `steps`, played back. -/
  | found (steps : Nat) (a : α)
  /-- No model at any depth up to `steps`. -/
  | noModel (steps : Nat)
  | undecided (kind : Kind) (fields : List (String × Json))

section
variable (solver : Solver) (cache : System.FilePath) (T : List TypeDecl) (v : ServiceV) (L : Layout)
  (senv : StepEnv L (shapes v))

/-- The search over the depths 1, 2, ... of the service's unrolled run (`ds`, each awaited when the search reaches it)
for a model of the goal each depth's steps give, stopping at the first, whose decoded run `play` reads. A refused
encoding of the run or of the goal ends the search undecided; a refused input kind (which the script then lacks)
leaves it undecided unless a model is found. `what` names the search in an engine bug's message. -/
def searchDepths {α : Type} (what : String) (ds : Array (Task (Option (Depth v senv.nT))))
    (hc : v.caller.isData = true) (goal : List (UnrollStep v senv.nT) → Except Refusal Term)
    (play : List (Input v) → Except String α) : IO (Except String (SearchResult α)) := do
  let fail (m : String) : Except String (SearchResult α) := .error s!"service {v.name}, {what}: {m}"
  let refusedLine (step : Option String) (r : Refusal) : Except String (SearchResult α) :=
    match refusalLine T r with
    | some (kind, fields) => .ok (.undecided kind (step.toList.map (("step", Json.str ·)) ++ fields))
    | none => fail s!"the encoding refused: {reprStr r}"
  let mut refused : Option (SymInput v (shapes v) senv.nT × Refusal) := none
  for (t, i) in ds.toList.zipIdx do
    let d := i + 1
    let some depth ← IO.wait t | return fail s!"depth {d} was never built"
    let (B, pre) ← match depth with
      | .error r => return refusedLine none r
      | .ok x => pure x
    let g ← match goal B.steps with
      | .error r => return refusedLine none r
      | .ok g => pure g
    let U := B.withGoal g
    if refused.isNone then refused := U.refused.head?
    let unsorted : SearchResult α := .undecided (.undecided .unknown) [("depth", Lean.toJson d),
      ("why", Json.str "a shared term of the script has no sort")]
    let some q := pre.bind (·.ask g) | return .ok unsorted
    match ← solver.runKeyed cache q with
    | .unsat => pure ()
    | .unknown why => return .ok (.undecided (.undecided .unknown) [("depth", Lean.toJson d), ("why", Json.str why)])
    | .sat vs =>
      -- `unroll_decode`: every model's steps decode to a run that faults nowhere.
      let some xs := U.steps.mapM (·.decode (modelOf vs) L hc) | return fail s!"a model of depth {d} does not decode"
      match play xs with
      | .ok a => return .ok (.found d a)
      | .error why => return fail s!"a model of depth {d} {why}"
  match refused with
  | some (inp, r) => return refusedLine (some inp.text) r
  | none => return .ok (.noModel ds.size)

end

end Tazuna.Cli
