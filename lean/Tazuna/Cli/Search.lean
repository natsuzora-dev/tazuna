import Tazuna.Cli.Explore

/-! The search stage and the `search` command, which runs the prove and explore stages and then this one: for each
target explore left to it, the shortest run from the initial state that reaches or breaks it, found by deepening an
unrolled run one step at a time up to the scope's `steps`, each depth split into cubes (`CubesCover`), with each
depth's run built once for every search over it. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace

/-- How many cubes a search asks at once, in their order, taking the first with a model: fixed, so the questions asked
and the trace found are the same whatever the number of solvers. -/
def cubeChunk : Nat := 4

/-- One depth's unrolled run as every goal at that depth shares it: its base, merged into one object per equal subterm
(`shareCommon`, the identity on values) so a goal built from its steps finds its shared terms among the assertions'
at once, with the merging's state, which merges a cube's goal into the same objects, the input kinds it refused with their refusals (no gap, by `unrollBase_ofService`), and for each smaller
number `j` of steps the prefix its cubes with `j` unfixed steps are asked with (`cubeAsk`: the run of `j` steps, this
depth's declarations and literals), printed once when a cube first needs it. -/
structure DepthRun (v : ServiceV) (n : Nat) where
  base : UnrollBase v n
  merged : ShareCommon.State Lean.ShareCommon.persistentObjectFactory
  refused : List (SymInput v (shapes v) n × Refused)
  prefixes : Array (Thunk (Option SentPrefix))

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
    let prefixes := (List.range d).toArray.map fun j => Thunk.mk fun _ =>
      match (ds[j]?).bind (·.get) with
      | some (.ok r) => some ((shared r.base).script.sentPrefix? ids solver.header)
      | _ => none
    ⟨B, merged, refused, prefixes⟩

/-- Each depth from 0 to `k`, built by its own job holding a permit of `pool`, once for every search over it: the
jobs, and each depth as a task a search awaits when it reaches that depth; none if its job never ran, an engine bug. -/
def depthJobs (pool : Std.Semaphore) (k : Nat) :
    IO (Array Job × Array (Task (Option (Depth s.v s.senv.nT)))) := do
  let ps ← (List.range (k + 1)).toArray.mapM fun _ => IO.Promise.new
  let ds := ps.map (·.resultD none)
  let jobs := ps.zipIdx.map fun (p, d) => ((d, fun d => withPermit pool (p.resolve (some (depthAt solver s ds d)))) : Job)
  return (jobs, ds)

end

/-- What a search over depths found. -/
inductive SearchResult (α : Type) where
  /-- A model at depth `steps`, played back. -/
  | found (steps : Nat) (a : α)
  /-- No model at any depth up to `steps`. -/
  | noModel (steps : Nat)
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
asked as cubes (`CubesCover`): one per pick of its last step, and a cube with no answer splits on the step before its
fixed ones, in pick order. A cube whose last step takes only kinds `ruledOut` rules out needs no question, nor one
whose last pick is not among those `live` gives. The cubes are asked `cubeChunk` at a time, and the first in order
with a model is the one taken, so the questions and the run found do not depend on timing. A depth whose cubes all
have no model is unreached; a cube with every step fixed and no answer leaves the depth undecided. A refused encoding
of the run or of the goal ends the search undecided; a refused input kind (which the script then lacks) leaves it
undecided unless a model is found. `what` names the search in an engine bug's message. With `brk`, a target a fault
breaks, the search is for a run that breaks it (`BreakCover`): a cube's last fixed step is a break step
(`breakAfter`) and `goal` is not read, and `live` gives the picks of the kinds whose step question whether the step
breaks the target is not unsat. -/
def searchDepths {α : Type} (what : String) (ds : Array (Task (Option (Depth s.v s.senv.nT))))
    (live : Option (List Nat) := none)
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
  for d in List.range' 1 (ds.size - 1) do
    let rd ← match ← depth d with
      | .error e => return e
      | .ok r => pure r
    if refused.isNone then refused := rd.refused.head?
    -- A cube's question: its fixed steps after the run of its unfixed ones, and its goal; none where the goal is
    -- false by its shape, which needs no solver.
    let prepare (ps : List Nat) :
        IO (Except (Except String (SearchResult α)) (Option (List Nat × List (UnrollStep s.v s.senv.nT) × Term))) := do
      if let (some ks, some k) := (live, ps.getLast?) then
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

/-- Each input kind with its step question (`stepAsk`); none where the initial state breaks an invariant or does not
fit the slots, or a kind's question is refused, as `BreakCover.deadLast` rests on every kind's question, the initial
state's invariants and its fit. -/
def stepAsks (c : CheckedSpec) (sv : CheckedService c) :
    Option (List (SymInput sv.v (shapes sv.v) sv.senv.nT × StepAsk sv.v)) :=
  if !(Step.invariants (Step.State.init sv.v)).isEmpty || !initFits sv.L sv.v then none
  else (stepInputs sv.v (shapes sv.v) sv.senv.nT (stateWidth sv.v)).attach.mapM fun ⟨inp, hinp⟩ =>
    match Sound.get (stepAsk sv.L c.T c.P sv.v sv.senv inp) (stepAsk_ofService sv.mem c.T sv.senv inp hinp) with
    | .ok ⟨a, _⟩ => some (inp, a)
    | .error _ => none

/-- Whether each input kind's step breaks no target a fault breaks (its question with `breakAnyT` is unsat), all asked
at once; every kind is asked, so which are asked does not depend on the schedule. -/
def breakAnyDead {v : ServiceV} {n : Nat} (solver : Solver) (cache : System.FilePath) (inputs : List String)
    (ids : Option Nat) (service : String) (xs : List (SymInput v (shapes v) n × StepAsk v)) :
    IO (Except String (List (SymInput v (shapes v) n × StepAsk v × Bool))) := do
  let ts ← xs.mapM fun (inp, a) => IO.asTask (prio := .dedicated) do
    allUnsat solver cache inputs ids
      [(["breaks", service, inp.place], Thunk.mk fun _ => some (a.ask (breakAnyT inp a.t.out)))]
  let mut out := #[]
  for ((inp, a), t) in xs.zip ts do
    match ← IO.ofExcept (← IO.wait t) with
    | .error m => return .error m
    | .ok u => out := out.push (inp, a, u)
  return .ok out.toList

/-- What one target's job found: a behavior target's search, or a break target's, or that every kind's step question
whether it breaks the break target is unsat. -/
inductive Searched where
  | reach (r : SearchResult TraceFile)
  | brk (r : SearchResult (Except String (TraceFile × Fault)))
  | settled

/-- A target's job: its service, the target's text and file, the service's scope, and where its result lands. -/
structure TargetJob where
  service : String
  target : String
  file : String
  scope : List Json
  result : IO.Ref (Option (Except String Searched))

/-- The search stage: for each target explore left to it (`Explored.left`), the search for the shortest run that
reaches or breaks it, and one line per target; the targets the deadline left. -/
def searchStage (cm : CheckedModel) (name dir : String) (opts : Options) (deadline : Option Nat) (p : Proven)
    (e : Explored) : Cmd (Option (List String)) := do
  let c := cm.checked
  let model := cm.model
  let rm : RunModel := ⟨name, model⟩
  -- At most `jobs` solvers run at once, and at most `jobs` depth builds; a search builds its cubes' scripts while
  -- others' solvers run.
  let gate ← Std.Semaphore.new opts.jobs
  let solver := { (← Solver.find) with gate := some gate, rlimit := model.rlimit.toNat, deadline }
  let pool ← Std.Semaphore.new opts.jobs
  let cache := p.cache
  let inputs := p.inputs
  -- Each target's search is one job; a service's depths are built once for all its targets (`depthJobs`). Lines and
  -- files are written in target order once all are done.
  let mut builds : Array Job := #[]
  let mut searches : Array Job := #[]
  let mut jobs : Array TargetJob := #[]
  for sv in cm.services do
    let v := sv.v
    let L := sv.L
    let rules := ruleNamesOf v
    let takes (t : String) := opts.keeps (v.name ++ "/" ++ t) && e.left.contains (v.name ++ "/" ++ t)
    -- Each target once (a rule named `callers` repeats admission's), so with `targetFile_inj` no two share a file.
    let gs := dedupBy (· == ·) ((targets c.T v rules).filter (takes ·.text))
    -- Each input kind's step question (`stepAsk`), and the targets a fault breaks among the kinds' targets whose break
    -- term is not false by its terms, in the order prove's lines name them.
    let kinds := (stepInputs v (shapes v) sv.senv.nT (stateWidth v)).attach.map fun ⟨inp, hinp⟩ =>
      (inp, (Sound.get (stepAsk L c.T c.P v sv.senv inp) (stepAsk_ofService sv.mem c.T sv.senv inp hinp)).map
        Subtype.val)
    let bs := dedupBy (·.text == ·.text) ((kinds.flatMap fun (inp, r) => match r with
      | .ok a => (a.t.out.targets inp.command?).filter fun g =>
          (a.t.out.breaks inp.command? g).const?.map Val.toBool != some false
      | .error _ => []).filter fun g => g.byFault && takes g.text)
    if gs.isEmpty && bs.isEmpty then continue
    let (bjs, ds) ← depthJobs solver sv pool sv.b.stepsNat
    builds := builds ++ bjs
    let scope := scopeBounds c.T L v sv.b
    -- Whether each kind's step breaks no target a fault breaks (`breakAnyT` unsat), asked once for all of the
    -- service's break targets by its own job; none where `BreakCover.deadLast` does not apply (`stepAsks`).
    let anyDead : IO.Promise (Except String (Option (List (SymInput v (shapes v) sv.senv.nT × StepAsk v × Bool)))) ←
      IO.Promise.new
    if !bs.isEmpty then
      builds := builds.push (0, fun _ => do
        let r ← match stepAsks c sv with
          | none => pure (.ok none)
          | some xs => pure ((← breakAnyDead solver cache inputs L.ids v.name xs).map some)
        anyDead.resolve r)
    for g in gs do
      -- `search_sound`: the decoded run's last step shows the target, so "misses the target" is unreachable unless
      -- the goal read z3's values for division by zero or a selector on another constructor (`lastHits`).
      let (j, r) ← Job.of do
        return (← searchDepths solver cache sv g.text ds none (!mayShow c.P c.T g ·) none
          (fun sts => .ok (genGoal L c.T rules g sts)) (reachTrace c.T v rules g (c.checked v sv.mem))).map .reach
      searches := searches.push j
      jobs := jobs.push ⟨v.name, g.text, targetFile v.name g, scope, r⟩
    for g in bs do
      -- The picks of the kinds whose step question whether the step breaks `g` is not unsat (`BreakCover.deadLast`);
      -- every pick where `stepAsks` gives none.
      let live : IO (Except String (Option (List Nat))) := do
        match ← IO.wait anyDead.result? with
        | none => return .error s!"service {v.name}: its break questions never ran"
        | some (.error m) => return .error m
        | some (.ok none) => pure (.ok none)
        | some (.ok (some xs)) =>
          -- Every open kind's question is asked, so which are asked does not depend on the schedule.
          let open_ := xs.filterMap fun (inp, a, dead) =>
            let goal := breakT g inp a.t.out
            if dead || goal.const?.map Val.toBool == some false then none else some (inp, a.ask goal)
          let ts ← open_.mapM fun (inp, q) => IO.asTask (prio := .dedicated) do
            allUnsat solver cache inputs L.ids [(["break", v.name, g.text, inp.place], Thunk.mk fun _ => some q)]
          let mut picks : Array Nat := #[]
          for ((inp, _), t) in open_.zip ts do
            match ← IO.ofExcept (← IO.wait t) with
            | .error m => return .error m
            | .ok true => pure ()
            | .ok false => picks := picks.push inp.pick
          pure (.ok (some picks.toList.eraseDups))
      let (j, r) ← Job.of do
        match ← live with
        | .error m => pure (.error m)
        | .ok (some []) => pure (.ok .settled)
        | .ok ks => return (← searchDepths solver cache sv g.text ds ks (brk := some g)
            (goal := fun _ => .ok ff) (play := breakTrace c.T v g)).map .brk
      searches := searches.push j
      jobs := jobs.push ⟨v.name, g.text, breakFile v.name g.text, scope, r⟩
  -- One pool: the builds first, so a search waits only on a build some worker runs. Its workers mostly wait on
  -- their cubes, so there are enough of them to keep every solver busy.
  runAll solver (opts.jobs * cubeChunk) (builds ++ searches)
  let cut ← solver.past
  let mut unfinished : Array String := #[]
  for job in jobs do
    let common := [("service", Json.str job.service), ("target", Json.str job.target)]
    let res ← match ← job.result.get with
      | none =>
        -- A target the run's deadline cut off keeps whatever file it had: no line speaks for it.
        if cut then
          unfinished := unfinished.push (job.service ++ "/" ++ job.target)
          continue
        return ← stop s!"service {job.service}, {job.target}: its search never ran"
      | some (.error m) => return ← stop m
      | some (.ok res) => pure res
    match res with
    | .reach (.found d tr) =>
      writeTrace dir job.file tr
      printLine (.search .reached) (common ++ [("file", Json.str job.file), ("steps", Lean.toJson d)])
    -- T6b (`noModel_cubes`) at each depth up to `k`: no run of at most `k` inputs, within the bounds, shows the
    -- target at its last step.
    | .reach (.noModel k) =>
      unwriteTrace dir job.file
      printLine (.search .unreached) (common ++ [rm.field [("bounds", Json.arr job.scope.toArray),
        ("steps", Lean.toJson k)], ("assumes", Json.arr (Step.Assumption.ofRuns.map (Json.str ·.text)).toArray)])
    | .brk (.found d (.ok (tr, f))) =>
      writeTrace dir job.file tr
      printLine (.search .violated) (common ++ [("file", Json.str job.file), ("steps", Lean.toJson d),
        ("outcome", Json.str (Outcome.fault f).summary)])
    | .brk (.found d (.error why)) =>
      unwriteTrace dir job.file
      printLine (.undecided .limit) (common ++ [("limit", Json.str s!"the run of {d} steps found {why}")])
    -- `noModel_breaks` at each depth up to `k`: no run of at most `k` inputs, within the bounds, whose steps before
    -- the last fault nowhere, breaks the target at its last step.
    | .brk (.noModel k) =>
      unwriteTrace dir job.file
      printLine (.search .unsettled) (common ++ [rm.field [("bounds", Json.arr job.scope.toArray),
        ("steps", Lean.toJson k)],
        ("assumes", Json.arr #[Json.str Step.Assumption.validInputs.text, Json.str "no step before the last faults"])])
    | .reach (.undecided kind fields) | .brk (.undecided kind fields) =>
      unwriteTrace dir job.file
      printLine kind (rm.undecided kind (common ++ fields))
    | .settled => unwriteTrace dir job.file
  return some unfinished.toList

/-- The `search` command: the prove stage, the explore stage for the targets prove left, then the search stage for the
targets explore left. -/
def search (root dir path : String) (opts : Options) : Cmd Unit := do
  let some (cm, name, deadline) ← startRun root path opts | return
  let some p ← proveStage cm name path opts deadline | return
  let some e ← exploreStage cm name dir opts deadline p true | return
  let some u ← searchStage cm name dir opts deadline p e | return
  finish deadline (p.unfinished ++ e.unfinished ++ u)

end Tazuna.Cli
