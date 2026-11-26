import Tazuna.Cli.Search
import Tazuna.Smt.GenGoal
import Tazuna.Trace.Verify

/-! The `generate` command: for each target of each service (`targets`), the shortest run from the initial state whose
last step shows the target's class of out line, found by deepening an unrolled run (`unrollBase` with `genGoal`) from one
step to the spec's `steps` bound. A model is played back in Lean: its inputs are decoded, written with the trace
writer scenarios use and replayed by verify's own replay (`foundTrace`), and the trace is written only when that replay
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

/-- The trace generate writes for the inputs: their trace (`foundTrace`, which verify replays as passed) where the
last step shows the target. -/
def genTrace (xs : List (Input v)) : Except String TraceFile := do
  let tr ← foundTrace T v xs
  if lastHits T v rules g xs then .ok tr else .error "misses the target"

/-- T6: a written trace reaches its target. Verify replays its lines as passed, and the last step of its run from the
initial state shows a class the target aims at. -/
theorem generate_reaches {xs : List (Input v)} {tr : TraceFile} (h : genTrace T v rules g xs = .ok tr) :
    replay T v tr.numbered = .passed ∧
      ∃ ys x, xs = ys ++ [x] ∧ Hits T v rules g x (step T v (run T v (State.init v) ys).1 x) := by
  simp only [genTrace, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i tr' htr
    split at h
    · rename_i hit
      cases h
      refine ⟨?_, ?_⟩
      · unfold foundTrace at htr
        split at htr
        · cases htr
        · cases htr
        · split at htr
          · rename_i hp; cases htr; exact hp
          · cases htr
      · unfold lastHits at hit
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
    let mut jobs : Array (String × GenTarget × List Json × IO.Ref (Option (Except String (SearchResult TraceFile)))) := #[]
    for sv in c.services do
      let v := sv.v
      let L := sv.L
      let rules := ruleNamesOf v
      let gs := (targets c.T v rules).filter fun g => opts.keeps (v.name ++ "/" ++ g.text)
      if gs.isEmpty then continue
      let (bs, ds) ← depthJobs solver sv v.bounds.stepsNat
      builds := builds ++ bs
      for g in gs do
        -- `generate_sound`: the decoded run's last step shows the target, so "misses the target" is unreachable.
        let (j, r) ← Job.of (searchDepths solver cache sv g.text ds (fun sts => .ok (genGoal L c.T rules g sts))
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
      | some (.ok (.found d tr)) =>
        IO.FS.createDirAll (System.FilePath.mk dir / service)
        IO.FS.writeFile file (String.join (tr.wires.map (·.text ++ "\n")))
        printLine (.generate .reached) (common ++
          [("file", Json.str (service ++ "/" ++ fileName g.text)), ("steps", Lean.toJson d)])
      | some (.ok res) =>
        if ← file.pathExists then IO.FS.removeFile file
        match res with
        -- T6b (`generate_unreached`) at each depth up to `k`: no run of at most `k` inputs, within the bounds, shows
        -- the target at its last step.
        | .noModel k =>
          printLine (.generate .unreached) (common ++ [("steps", Lean.toJson k), ("bounds", Json.arr scope.toArray),
            ("assumes", Json.arr (Step.Assumption.ofRuns.map (Json.str ·.text)).toArray)])
        | .undecided kind fields =>
          undecided := true
          printLine kind (common ++ fields)
        | .found .. => pure ()
    return if undecided then 2 else 0

end Tazuna.Cli
