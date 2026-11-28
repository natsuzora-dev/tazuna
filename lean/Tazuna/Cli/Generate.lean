import Tazuna.Cli.Search
import Tazuna.Cli.TargetFile
import Tazuna.Smt.GenGoal
import Tazuna.Smt.Dead
import Tazuna.Smt.Prove
import Tazuna.Trace.Verify

/-! The `generate` command: for each target of each service (`targets`), the shortest run from the initial state whose
last step shows the target's class of out line, found by deepening an unrolled run (`unrollBase` with `genGoal`) from one
step to the spec's `steps` bound, each depth asked as cubes that fix the kinds of its last steps (`searchDepths`). A
model is played back in Lean: its inputs are decoded and written with the trace writer scenarios use (`foundTrace`),
whose lines read as the spec, so verify replays them as passed unless it runs out of tries, and the trace is written
only when its last step shows the target (`generate_reaches`). A target whose cubes have no model at any depth is
unreached within the steps (`noModel_cubes`). A cube needs no question where the code rules out every kind its last
step takes (`mayShow`), or, from depth 2 on, where prove's dead-target question (`showsAsk`) of each kind of its last
pick is unsat. The targets of a service share each depth's run (`unrollBase`) and its cubes' prefixes, built once; only the goal differs, so an answer is looked up under a key read off the shared prefix's digest and the goal
(`ScriptPrefix.ask`), and a script's text is printed only for the solver.

A target a fault breaks (an invariant, an `ensures` rule, an own effect's acceptance, the cascade bound) is searched
only where some input kind's step question whether its step breaks it is not unsat: the run sought is one whose last
step breaks it (`brk`, `BreakCover`), and its last step only takes those kinds. One question per kind first asks
whether its step breaks any such target (`breakAnyT`), so most kinds need no question per target (`breakT`). A run
found is run in Lean and replayed by verify (`generate_breaks`); none within the steps leaves the target unsettled
(`noModel_breaks`). A behavior target every kind's dead-target question rules out is unreachable at every depth:
of every run where prove's bound questions are unsat and every input and the initial state fit (`unshown_sound`),
else within the slots (`unshown_within`). The pruning of last picks rests only on runs within the slots, which every
cube's run is, so it does not read the bound questions. -/

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
values, and no theorem shows a goal's assertions never read them. `generate_sound` needs every assertion to hold in the
model it reads, which z3's answer gives only under z3's own values, so this check is what keeps a written trace from
missing its target. -/
def lastHits (xs : List (Input v)) : Bool :=
  match xs.getLast? with
  | some x => (classes T v x (step T v (run T v (State.init v) xs.dropLast).1 x)).any (g.covers rules)
  | none => false

/-- The trace generate writes for the inputs: their trace (`foundTrace`, which reads as the spec) where the last step
shows the target. -/
def genTrace {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (xs : List (Input v)) :
    Except String TraceFile := do
  let tr ← foundTrace chk xs
  if lastHits T v rules g xs then .ok tr else .error "misses the target"

/-- T6: a written trace reaches its target. Its lines read as the spec from the initial state, so verify replays them
as passed unless it runs out of tries (`replay_iff`), and the last step of its run from the initial state shows a
class the target aims at. -/
theorem generate_reaches {P : List AnySite} {E : List AnyEffectSite} {chk : Checked P E T v} (hv : v.Equivariant)
    {xs : List (Input v)} {tr : TraceFile} (h : genTrace T v rules g chk xs = .ok tr) :
    Reads T v (State.init v) {} tr.numbered ∧
      ∃ ys x, xs = ys ++ [x] ∧ Hits T v rules g x (step T v (run T v (State.init v) ys).1 x) := by
  simp only [genTrace, bind, Except.bind] at h
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

/-- The trace generate writes for a run that breaks the target, with the fault: the run on `xs` from the initial state,
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

/-- A run generate reports as breaking a target does: the run of its inputs from the initial state faults nowhere
before its last step and faults there by a fault the target covers, and verify replays the written trace to such a
fault at its last line. -/
theorem generate_breaks {xs : List (Input v)} {tr : TraceFile} {f : Fault}
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

/-- Each input kind with its step question (`stepAsk`), from which prove's dead-target questions are read
(`showsAsk`); none where the initial state breaks an invariant or does not fit the slots, or a kind's question is
refused, as `CubesCover.deadLast` rests on every kind's question, the initial state's invariants and its fit. -/
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
inductive GenResult where
  | search (r : SearchResult TraceFile)
  | brk (r : SearchResult (Except String (TraceFile × Fault)))
  | settled

/-- A target's job: its service, the target's text and file, the service's scope and a dead target's, and where its
result lands. -/
structure GenJob where
  service : String
  target : String
  file : String
  scope : List Json
  deadScope : IO (Except String (Option (List Json)))
  result : IO.Ref (Option (Except String GenResult))

/-- `f`, run by its first call only; every later call gets that call's result. -/
def once {α : Type} (f : IO α) : IO (IO α) := do
  let r ← IO.mkRef none
  pure do
    match ← r.get with
    | some a => pure a
    | none =>
      let a ← f
      r.set (some a)
      pure a

def generate (root dir path : String) (opts : Options) : Cmd Unit := do
  match ← loadSpec root path with
  | none => pure ()
  | some c =>
    -- At most `jobs` solvers run at once, and at most `jobs` depth builds; a search builds its cubes' scripts while
    -- others' solvers run.
    let solver := { (← Solver.find) with gate := some (← Std.Semaphore.new opts.jobs) }
    let pool ← Std.Semaphore.new opts.jobs
    -- The engine's own digest names this build in the direct keys of prove's questions, which generate shares.
    let engine ← IO.asTask (prio := .dedicated) do return Sha256.hex (← IO.FS.readBinFile (← IO.appPath))
    let version ← solver.version
    let cache := opts.cache / Sha256.hex version.toUTF8
    let inputs := [← IO.ofExcept (← IO.wait engine), version] ++ solver.header ++ [Sha256.hex (← IO.FS.readBinFile path)]
    -- Each target's search is one job; a service's depths are built once for all its targets (`depthJobs`). Lines and
    -- files are written in target order once all are done.
    let mut builds : Array Job := #[]
    let mut searches : Array Job := #[]
    let mut jobs : Array GenJob := #[]
    for sv in c.services do
      let v := sv.v
      let L := sv.L
      let rules := ruleNamesOf v
      -- Each target once (a rule named `callers` repeats admission's), so with `targetFile_inj` no two share a file.
      let gs := dedupBy (· == ·) ((targets c.T v rules).filter fun g => opts.keeps (v.name ++ "/" ++ g.text))
      -- Each input kind's step question (`stepAsk`), and the targets a fault breaks among the kinds' targets whose break
      -- term is not false by its terms, in the order prove's lines name them.
      let kinds := (stepInputs v (shapes v) sv.senv.nT (stateWidth v)).attach.map fun ⟨inp, hinp⟩ =>
        (inp, (Sound.get (stepAsk L c.T c.P v sv.senv inp) (stepAsk_ofService sv.mem c.T sv.senv inp hinp)).map
          Subtype.val)
      let bs := dedupBy (·.text == ·.text) ((kinds.flatMap fun (inp, r) => match r with
        | .ok a => (a.t.out.targets inp.command?).filter fun g =>
            (a.t.out.breaks inp.command? g).const?.map Val.toBool != some false
        | .error _ => []).filter fun g => g.byFault && opts.keeps (v.name ++ "/" ++ g.text))
      if gs.isEmpty && bs.isEmpty then continue
      let (bjs, ds) ← depthJobs solver sv pool v.bounds.stepsNat
      builds := builds ++ bjs
      let asks := Thunk.mk fun _ => stepAsks c sv
      let scope := scopeBounds c.T L v
      -- A dead target's scope (`runScope`) from each input kind's bound question, the one prove asks: asked once a
      -- target of the service is dead, and not before.
      let deadScope ← once do
        let some xs := asks.get | return .error s!"service {v.name}: a target is dead without step questions"
        let qs := xs.map fun (inp, a) => (["bound", v.name, "", inp.place], Thunk.mk fun _ => some a.bound)
        return (← allUnsat solver cache inputs L.ids qs).map fun u =>
          runScope (!u) (inputsFit L v && initFits L v) scope (inputBounds c.T L v)
      -- Whether each kind's step breaks no target a fault breaks (`breakAnyT` unsat), asked once for all of the
      -- service's break targets by its own job; none where `BreakCover.deadLast` does not apply (`stepAsks`).
      let anyDead : IO.Promise (Except String (Option (List (SymInput v (shapes v) sv.senv.nT × StepAsk v × Bool)))) ←
        IO.Promise.new
      if !bs.isEmpty then
        builds := builds.push (0, fun _ => do
          let r ← match asks.get with
            | none => pure (.ok none)
            | some xs => pure ((← breakAnyDead solver cache inputs L.ids v.name xs).map some)
          anyDead.resolve r)
      for g in gs do
        -- The picks some kind of which has a dead-target question that is not unsat: a step of any other pick never shows
        -- the target, so no depth from the second asks a cube whose last step takes one, nor any where no pick is left.
        let live : IO (Except String (Option (List Nat))) :=
          if g.byQuery v then pure (.ok none) else do
            match asks.get with
            | none => pure (.ok none)
            | some xs =>
              let qs := xs.map fun (inp, a) =>
                (["shows", v.name, g.text, inp.place], Thunk.mk fun _ => showsAsk L c.T rules g c.P a inp)
              match ← eachUnsat solver cache inputs L.ids qs with
              | .error m => pure (.error m)
              | .ok us =>
                pure (.ok (some ((xs.zip us).filterMap fun ((inp, _), u) => if u then none else some inp.pick).eraseDups))
        -- `generate_sound`: the decoded run's last step shows the target, so "misses the target" is unreachable unless
        -- the goal read z3's values for division by zero or a selector on another constructor (`lastHits`).
        let (j, r) ← Job.of do
          return (← searchDepths solver cache sv g.text ds live (!mayShow c.P c.T g ·) none
            (fun sts => .ok (genGoal L c.T rules g sts)) (genTrace c.T v rules g (c.checked v sv.mem))).map .search
        searches := searches.push j
        jobs := jobs.push ⟨v.name, g.text, targetFile v.name g, scope, deadScope, r⟩
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
          | .ok ks => return (← searchDepths solver cache sv g.text ds (pure (.ok ks)) (brk := some g)
              (goal := fun _ => .ok ff) (play := breakTrace c.T v g)).map .brk
        searches := searches.push j
        jobs := jobs.push ⟨v.name, g.text, breakFile v.name g.text, scope, deadScope, r⟩
    -- One pool: the builds first, so a search waits only on a build some worker runs. Its workers mostly wait on
    -- their cubes, so there are enough of them to keep every solver busy.
    runAll (opts.jobs * cubeChunk) (builds ++ searches)
    for job in jobs do
      let file := System.FilePath.mk dir / job.file
      let common := [("service", Json.str job.service), ("target", Json.str job.target)]
      let write (tr : TraceFile) : IO Unit := do
        if let some d := file.parent then IO.FS.createDirAll d
        IO.FS.writeFile file (String.join (tr.wires.map (·.text ++ "\n")))
      let unwrite : IO Unit := do if ← file.pathExists then IO.FS.removeFile file
      let res ← match ← job.result.get with
        | none => return ← internal s!"service {job.service}, {job.target}: its search never ran"
        | some (.error m) => return ← internal m
        | some (.ok res) => pure res
      match res with
      | .search (.found d tr) =>
        write tr
        printLine (.generate .reached) (common ++ [("file", Json.str job.file), ("steps", Lean.toJson d)])
      -- T6b (`noModel_cubes`) at each depth up to `k`: no run of at most `k` inputs, within the bounds, shows the
      -- target at its last step.
      | .search (.noModel k) =>
        unwrite
        printLine (.generate .unreached) (common ++ [("steps", Lean.toJson k), ("bounds", Json.arr job.scope.toArray),
          ("assumes", Json.arr (Step.Assumption.ofRuns.map (Json.str ·.text)).toArray)])
      -- Every kind's dead-target question is unsat, so no step shows the target, at any depth: of every run where no
      -- step can go past the slots and every input and the initial state fit (`unshown_sound`), else of every run
      -- within the slots (`unshown_within`).
      | .search .dead =>
        unwrite
        let fields := common ++ [("assumes", Json.arr (Step.Assumption.ofRuns.map (Json.str ·.text)).toArray)]
        match ← job.deadScope with
        | .error m => return ← internal m
        | .ok none => printLine (.generate .unreachable) fields
        | .ok (some bs) => printLine (.generate .unreachableWithinBounds) (fields ++ [("bounds", Json.arr bs.toArray)])
      | .brk (.found d (.ok (tr, f))) =>
        write tr
        printLine (.generate .violated) (common ++ [("file", Json.str job.file), ("steps", Lean.toJson d),
          ("outcome", Json.str (Outcome.fault f).summary)])
      | .brk (.found d (.error why)) =>
        unwrite
        printLine (.undecided .limit) (common ++ [("limit", Json.str s!"the run of {d} steps found {why}")])
      -- `noModel_breaks` at each depth up to `k`: no run of at most `k` inputs, within the bounds, whose steps before
      -- the last fault nowhere, breaks the target at its last step.
      | .brk (.noModel k) =>
        unwrite
        printLine (.generate .unsettled) (common ++ [("steps", Lean.toJson k), ("bounds", Json.arr job.scope.toArray),
          ("assumes", Json.arr #[Json.str Step.Assumption.validInputs.text, Json.str "no step before the last faults"])])
      | .search (.undecided kind fields) | .brk (.undecided kind fields) =>
        unwrite
        printLine kind (common ++ fields)
      | .settled | .brk .dead => unwrite

end Tazuna.Cli
