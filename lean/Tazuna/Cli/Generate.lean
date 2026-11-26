import Tazuna.Cli.Prove
import Tazuna.Smt.GenGoal
import Tazuna.Trace.Verify

/-! The `generate` command: for each target of each service (`targets`), the shortest run from the initial state whose
last step shows the target's class of out line, found by deepening an unrolled run (`unrollBase` with `genGoal`) from one
step to the spec's `steps` bound. A model is played back in Lean: its inputs are decoded, written with the trace
writer scenarios use, read back and replayed by verify's own replay, and the trace is written only when that replay
passes and its last step shows the target (`generate_reaches`). A target with no model at any depth is unreached
within the steps (`generate_unreached`). The targets of a service share each depth's run (`unrollBase`), built once;
only the goal differs, so an answer is looked up under a key read off the shared prefix's digest and the goal
(`ScriptPrefix.key`), and a script's text is printed only for the solver. -/

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

/-- The literal names of the rules a command's or query's `accepts` can break, read off its step's terms as prove
reads rule names; none for a rule whose name the model decides. -/
def ruleNamesOf (L : Layout) (c : CheckedSpec) (v : ServiceV) (senv : StepEnv L (shapes v)) : RuleNames := fun name =>
  let w := stateWidth v
  let cmds := (List.finRange v.commands.length).filterMap fun i =>
    if (v.commands.get i).name == name then
      match encodeStep L c.T c.P v senv (SymState.vars 0) (.command i (.var w) (.var (w + 1))) with
      | .ok ⟨.command o, _, _, _⟩ => some (ruleNames o.rules)
      | _ => none
    else none
  let qs := (List.finRange v.queries.length).filterMap fun i =>
    if (v.queries.get i).name == name then
      match encodeStep L c.T c.P v senv (SymState.vars 0) (.query i (.var w) (.var (w + 1))) with
      | .ok ⟨.query o, _, _, _⟩ => some (ruleNames o.rules)
      | _ => none
    else none
  dedup (cmds ++ qs).flatten

/-- What generate found for one target. -/
inductive GenResult where
  | reached (steps : Nat) (trace : List Wire)
  | unreached (steps : Nat)
  | undecided (kind : Kind) (fields : List (String × Json))

section
variable (solver : Solver) (cache : System.FilePath) (c : CheckedSpec) (v : ServiceV) (L : Layout)
  (senv : StepEnv L (shapes v)) (rules : RuleNames)

/-- The target's search over the depths 1, 2, ... (`ds`), stopping at the first model, which is played back. A refused
encoding of the run, or of an input kind (which the script then lacks), leaves the target undecided unless a model is
found. An error is an engine bug. -/
def searchTarget (ds : List (Depth v senv.nT)) (g : GenTarget) : IO (Except String GenResult) := do
  if hc : v.caller.isData = false then return .error "the caller type is no data" else
  have hc : v.caller.isData = true := by simpa using hc
  let mut refused : Option (SymInput v (shapes v) senv.nT × Refusal) := none
  for (t, i) in ds.zipIdx do
    let d := i + 1
    match t with
    | .error r =>
      match refusalLine c.T r with
      | some (kind, fields) => return .ok (.undecided kind fields)
      | none => return .error s!"service {v.name}, {g.text}: the encoding refused: {reprStr r}"
    | .ok (B, pre) =>
      let goal := genGoal L c.T rules g B.steps
      let U := B.withGoal goal
      if refused.isNone then refused := U.refused.head?
      let some pre := pre | return .ok (.undecided (.undecided .unknown) [("depth", Lean.toJson d),
        ("why", Json.str "a shared term of the script has no sort")])
      let some key := pre.key goal | return .ok (.undecided (.undecided .unknown)
        [("depth", Lean.toJson d), ("why", Json.str "a shared term of the script has no sort")])
      match ← solver.runKeyed cache key fun _ => U.ask.script.text solver.header with
      | .unsat => pure ()
      | .unknown why =>
        return .ok (.undecided (.undecided .unknown) [("depth", Lean.toJson d), ("why", Json.str why)])
      | .sat vs =>
        let M := modelOf vs
        -- `unroll_decode`: every model's steps decode to a run that faults nowhere.
        let some xs := U.steps.mapM (·.decode M L hc)
          | return .error s!"service {v.name}, {g.text}: a model of depth {d} does not decode"
        -- `generate_sound`: the decoded run's last step shows the target, so "misses the target" is unreachable.
        -- Writing, reading back and replaying the trace are checked here, not proved.
        match genTrace c.T v rules g xs with
        | .ok ws => return .ok (.reached d ws)
        | .error why => return .error s!"service {v.name}, {g.text}: a model of depth {d} {why}"
  match refused with
  | some (inp, r) => match refusalLine c.T r with
    | some (kind, fields) => return .ok (.undecided kind (("step", Json.str inp.text) :: fields))
    | none => return .error s!"service {v.name}, {inp.text}: the encoding refused: {reprStr r}"
  | none => return .ok (.unreached ds.length)

end

/-- `generate`'s options are `prove`'s: the prefix `--only` keeps targets by, how many solvers run at once, the
cache directory. -/
def generate (root dir path : String) (opts : ProveOptions) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok c =>
    let solver : Solver := {}
    let cache := opts.cache / Sha256.hex (← solver.version).toUTF8
    let keep (name : String) : Bool := match opts.only with
      | some p => p.isPrefixOf name
      | none => true
    -- Each job is one target's search; its lines and file are written in target order once all are done.
    let mut jobs : Array (String × GenTarget × List Json × IO (Except String GenResult)) := #[]
    let mut builds : Array (Nat × (Nat → IO Unit)) := #[]
    for v in c.spec.services do
      let L := Layout.ofService c.program.defs v
      let .ok senv := StepEnv.of L (shapes v)
        | IO.eprintln s!"tazuna-engine: internal error: service {v.name}: no step environment in its layout"
          return 4
      let rules := ruleNamesOf L c v senv
      let scope := scopeBounds c.T L v
      let gs := (targets c.T v rules).filter fun g => keep (v.name ++ "/" ++ g.text)
      if gs.isEmpty then continue
      -- Each depth's run is built once for every target of the service, before any search.
      let k := v.bounds.steps.toNat
      let built ← IO.mkRef (Array.replicate k (none : Option (Depth v senv.nT)))
      -- The depth is the job's argument, so building its run waits for the job.
      for d in List.range' 1 k do
        builds := builds.push (d, fun d => built.modify (·.set! (d - 1) (some (depthAt solver c v L senv d))))
      for g in gs do
        jobs := jobs.push (v.name, g, scope, do
          searchTarget solver cache c v L senv rules ((← built.get).toList.filterMap id) g)
    let _ ← runAll opts.jobs (fun (d, build) => build d) builds
    let results ← runAll opts.jobs (fun (_, _, _, job) => job) jobs
    let mut undecided := false
    for ((service, g, scope, _), res) in jobs.zip results do
      let file := System.FilePath.mk dir / service / fileName g.text
      let common := [("service", Json.str service), ("target", Json.str g.text)]
      match res with
      | .error m =>
        IO.eprintln s!"tazuna-engine: internal error: {m}"
        return 4
      | .ok (.reached d ws) =>
        IO.FS.createDirAll (System.FilePath.mk dir / service)
        IO.FS.writeFile file (String.join (ws.map (·.text ++ "\n")))
        printLine (.generate .reached) (common ++
          [("file", Json.str (service ++ "/" ++ fileName g.text)), ("steps", Lean.toJson d)])
      | .ok res =>
        if ← file.pathExists then IO.FS.removeFile file
        match res with
        | .unreached k =>
          printLine (.generate .unreached) (common ++ [("steps", Lean.toJson k), ("bounds", Json.arr scope.toArray),
            ("assumes", Json.arr #[Json.str Step.Assumption.validInputs.text])])
        | .undecided kind fields =>
          undecided := true
          printLine kind (common ++ fields)
        | .reached .. => pure ()
    return if undecided then 2 else 0

end Tazuna.Cli
