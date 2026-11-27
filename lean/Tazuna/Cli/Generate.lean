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
step takes (`mayShow`), or, at the last depth, where prove's dead-target question (`showsAsk`) of each kind of its last
pick is unsat. The targets of a service share each depth's run (`unrollBase`) and its cubes' prefixes, built once; only the goal differs, so an answer is looked up under a key read off the shared prefix's digest and the goal
(`ScriptPrefix.ask`), and a script's text is printed only for the solver. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace

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
    let mut jobs : Array (String × GenTarget × List Json × IO.Ref (Option (Except String (SearchResult TraceFile)))) := #[]
    for sv in c.services do
      let v := sv.v
      let L := sv.L
      let rules := ruleNamesOf v
      -- Each target once (a rule named `callers` repeats admission's), so with `targetFile_inj` no two share a file.
      let gs := dedupBy (· == ·) ((targets c.T v rules).filter fun g => opts.keeps (v.name ++ "/" ++ g.text))
      if gs.isEmpty then continue
      let (bs, ds) ← depthJobs solver sv pool v.bounds.stepsNat
      builds := builds ++ bs
      let asks := Thunk.mk fun _ => stepAsks c sv
      for g in gs do
        -- The picks some kind of which has a dead-target question that is not unsat: a step of any other pick never shows
        -- the target, so the last depth asks no cube whose last step takes one, and none at all where no pick is left.
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
        -- `generate_sound`: the decoded run's last step shows the target, so "misses the target" is unreachable unless the
        -- goal read z3's values for division by zero or a selector on another constructor (`lastHits`).
        let (j, r) ← Job.of (searchDepths solver cache sv g.text ds live (!mayShow c.P c.T g ·) (fun sts => .ok (genGoal L c.T rules g sts))
          (genTrace c.T v rules g (c.checked v sv.mem)))
        searches := searches.push j
        jobs := jobs.push (v.name, g, scopeBounds c.T L v, r)
    -- One pool: the builds first, so a search waits only on a build some worker runs. Its workers mostly wait on
    -- their cubes, so there are enough of them to keep every solver busy.
    runAll (opts.jobs * cubeChunk) (builds ++ searches)
    for (service, g, scope, r) in jobs do
      let file := System.FilePath.mk dir / targetFile service g
      let common := [("service", Json.str service), ("target", Json.str g.text)]
      match ← r.get with
      | none => return ← internal s!"service {service}, {g.text}: its search never ran"
      | some (.error m) => return ← internal m
      | some (.ok (.found d tr)) =>
        if let some d := file.parent then IO.FS.createDirAll d
        IO.FS.writeFile file (String.join (tr.wires.map (·.text ++ "\n")))
        printLine (.generate .reached) (common ++
          [("file", Json.str (targetFile service g)), ("steps", Lean.toJson d)])
      | some (.ok res) =>
        if ← file.pathExists then IO.FS.removeFile file
        match res with
        -- T6b (`noModel_cubes`) at each depth up to `k`, or a dead target (`unshown_within`): no run of at most `k`
        -- inputs, within the bounds, shows the target at its last step.
        | .noModel k =>
          printLine (.generate .unreached) (common ++ [("steps", Lean.toJson k), ("bounds", Json.arr scope.toArray),
            ("assumes", Json.arr (Step.Assumption.ofRuns.map (Json.str ·.text)).toArray)])
        | .undecided kind fields => printLine kind (common ++ fields)
        | .found .. => pure ()

end Tazuna.Cli
