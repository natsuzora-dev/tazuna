import Tazuna.Cli.Search
import Tazuna.Smt.GenGoal
import Tazuna.Trace.Verify

/-! The `generate` command: for each target of each service (`targets`), the shortest run from the initial state whose
last step shows the target's class of out line, found by deepening an unrolled run (`unrollBase` with `genGoal`) from one
step to the spec's `steps` bound. A model is played back in Lean: its inputs are decoded, written with the trace
writer scenarios use, read back and replayed by verify's own replay, and the trace is written only when that replay
passes and its last step shows the target (`generate_reaches`). A target with no model at any depth is unreached
within the steps (`generate_unreached`). The targets of a service share each depth's run (`unrollBase`), built once;
only the goal differs, so an answer is looked up under a key read off the shared prefix's digest and the goal
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

/-- A target's file: its text with every byte outside `[A-Za-z0-9 ._-]` percent-encoded, `%` too, so distinct targets
get distinct names on any file system. -/
def fileName (target : String) : String :=
  let hex := "0123456789ABCDEF".toList
  let byte (b : UInt8) : String :=
    let c := Char.ofNat b.toNat
    if b < 128 && (c.isAlphanum || c == ' ' || c == '.' || c == '_' || c == '-') then c.toString
    else "%" ++ String.ofList [hex[b.toNat / 16]!, hex[b.toNat % 16]!]
  String.join (target.toUTF8.toList.map byte) ++ ".jsonl"

section
variable (T : List TypeDecl) (v : ServiceV) (rules : RuleNames) (g : GenTarget)

/-- Whether the last step of the run on `xs` from the initial state shows a class the target aims at. -/
def lastHits (xs : List (Input v)) : Bool :=
  match xs.getLast? with
  | some x => (classes T v x (step T v (run T v (State.init v) xs.dropLast).1 x)).any (g.covers rules)
  | none => false

/-- The trace generate writes for the inputs: their trace, where verify replays it, read back from its text, as passed
and its last step shows the target; else what failed. -/
def genTrace (xs : List (Input v)) : Except String (List Wire) :=
  match traceOf T v xs with
  | .error (.fault k _) => .error s!"faults at step {k} when written as a trace"
  | .error (.badStep k m) => .error s!"does not write as a trace at step {k}: {m}"
  | .ok ws => match reread ws with
    | none => .error "does not read back from its trace"
    | some lines => match replay T v lines with
      | .passed => if lastHits T v rules g xs then .ok ws else .error "misses the target"
      | _ => .error "does not replay as passed"

/-- T6: a written trace reaches its target. Read back from its text, verify replays it as passed, and the last step of
its run from the initial state shows a class the target aims at. -/
theorem generate_reaches {xs : List (Input v)} {ws : List Wire} (h : genTrace T v rules g xs = .ok ws) :
    ∃ lines, reread ws = some lines ∧ replay T v lines = .passed ∧
      ∃ ys x, xs = ys ++ [x] ∧ Hits T v rules g x (step T v (run T v (State.init v) ys).1 x) := by
  unfold genTrace at h
  split at h
  · cases h
  · cases h
  · rename_i ws' hws
    split at h
    · cases h
    · rename_i lines hl
      split at h
      · rename_i hp
        split at h
        · rename_i hit
          cases h
          refine ⟨lines, hl, hp, ?_⟩
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
      · cases h

end

def generate (root dir path : String) (opts : Options) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok c =>
    let solver : Solver := {}
    let cache := opts.cache / Sha256.hex (← solver.version).toUTF8
    let internal (m : String) : IO UInt32 := do
      IO.eprintln s!"tazuna-engine: internal error: {m}"
      return 4
    -- Each target's search is one job; a service's depths are built once for all its targets (`depthJobs`). Lines and
    -- files are written in target order once all are done.
    let mut builds : Array Job := #[]
    let mut searches : Array Job := #[]
    let mut jobs : Array (String × GenTarget × List Json × IO.Ref (Option (Except String (SearchResult (List Wire))))) := #[]
    for sv in c.services do
      let v := sv.v
      let L := sv.L
      let senv := sv.senv
      let rules := ruleNamesOf v
      let gs := (targets c.T v rules).filter fun g => opts.keeps (v.name ++ "/" ++ g.text)
      if gs.isEmpty then continue
      let (bs, ds) ← depthJobs solver c v L senv v.bounds.steps.toNat
      builds := builds ++ bs
      for g in gs do
        -- `generate_sound`: the decoded run's last step shows the target, so "misses the target" is unreachable.
        let (j, r) ← Job.of (searchDepths solver cache c.T v L senv g.text ds sv.callerData (fun sts => .ok (genGoal L c.T rules g sts))
          (genTrace c.T v rules g))
        searches := searches.push j
        jobs := jobs.push (v.name, g, scopeBounds c.T L v, r)
    -- One pool: the builds first, so a search waits only on a build some worker runs.
    runAll opts.jobs (builds ++ searches)
    let mut undecided := false
    for (service, g, scope, r) in jobs do
      let file := System.FilePath.mk dir / service / fileName g.text
      let common := [("service", Json.str service), ("target", Json.str g.text)]
      match ← r.get with
      | none => return ← internal s!"service {service}, {g.text}: its search never ran"
      | some (.error m) => return ← internal m
      | some (.ok (.found d ws)) =>
        IO.FS.createDirAll (System.FilePath.mk dir / service)
        IO.FS.writeFile file (String.join (ws.map (·.text ++ "\n")))
        printLine (.generate .reached) (common ++
          [("file", Json.str (service ++ "/" ++ fileName g.text)), ("steps", Lean.toJson d)])
      | some (.ok res) =>
        if ← file.pathExists then IO.FS.removeFile file
        match res with
        -- T6b (`generate_unreached`) at each depth up to `k`: no run of at most `k` inputs, within the bounds, shows
        -- the target at its last step.
        | .noModel k =>
          printLine (.generate .unreached) (common ++ [("steps", Lean.toJson k), ("bounds", Json.arr scope.toArray),
            ("assumes", Json.arr #[Json.str Step.Assumption.validInputs.text])])
        | .undecided kind fields =>
          undecided := true
          printLine kind (common ++ fields)
        | .found .. => pure ()
    return if undecided then 2 else 0

end Tazuna.Cli
