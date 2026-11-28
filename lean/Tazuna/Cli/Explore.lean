import Tazuna.Cli.Generate
import Tazuna.Explore.Search

/-! The `explore` command: for each service, breadth-first search over the states its model's scope reaches
(`Tazuna.Explore.search`), then one line per target. A behavior target is reached where some transition showed its
class of out line, a target a fault breaks is violated where some transition faulted by a fault it covers, and a
response is violated where some run broke it. The run of the first such transition is played back with the writers
generate uses, so the traces read as the spec and verify replays them (`generate_reaches`, `generate_breaks`,
`response_trace`); every other target's line names what the search covered. -/

namespace Tazuna.Explore

open Tazuna.Ir Tazuna.Ir.Step Tazuna.Trace Tazuna.Cli

section
variable {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}

/-- The trace explore writes for a run that breaks the response: the run's trace (`foundTrace`) where, run in Lean
from the initial state, its clock lines pass no waiting timer and its steps violate the response. -/
def responseTrace (chk : Smt.Checked P E T v) (resp : ResponseV v.records v.event) (xs : List (Input v)) :
    Except String TraceFile :=
  if TimelyRun T (State.init v) xs then
    if ResponseV.violatedBy T resp (State.init v) xs then foundTrace chk xs
    else .error "does not violate the response"
  else .error "has a clock line past a waiting timer"

/-- A trace explore writes for a response reads as the spec, so verify replays it as passed unless it runs out of
tries, and its run from the initial state has timely clock lines and violates the response as the semantics defines
it (`ResponseV.Violated`). -/
theorem response_trace {chk : Smt.Checked P E T v} (hv : v.Equivariant) {resp : ResponseV v.records v.event}
    {xs : List (Input v)} {tr : TraceFile} (h : responseTrace chk resp xs = .ok tr) :
    Reads T v (State.init v) {} tr.numbered ∧ TimelyRun T (State.init v) xs ∧
      resp.Violated ((run T v (State.init v) xs).2.map Result.moment) := by
  unfold responseTrace at h
  split at h
  · rename_i ht
    split at h
    · rename_i hvi
      exact ⟨foundTrace_reads hv h, ht, (resp.violated_iff _).1 hvi⟩
    · cases h
  · cases h

end

end Tazuna.Explore

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Ir.Step Tazuna.Smt Tazuna.Trace Tazuna.Explore

/-- The targets a fault breaks, read off the service's code: each rule name of its invariants and its machines'
invariants (none for a name the code computes), each rule name of each command's `ensures`, the cascade bound, and
each own command or query its sends can name. -/
def faultTargets (v : ServiceV) : List Target :=
  dedupBy (· == ·) <|
    (v.invariants.ruleNames.map (.invariant none ·)) ++
    (v.machines.flatMap fun m => m.invariants.ruleNames.map (.invariant (some m.name) ·)) ++
    (v.commands.flatMap fun c => c.ensures.ruleNames.map (.ensures c.name ·)) ++ [.cascade] ++
    (v.sentHandles.filterMap fun h => if h.kind == "command" || h.kind == "query" then h.name.map .effect else none)

/-- The earliest of the hits: fewest inputs, then first met. -/
def earliest (hs : List Hit) : Option Hit :=
  hs.foldl (fun best h => match best with
    | some b => if h.depth < b.depth || (h.depth == b.depth && h.order < b.order) then some h else some b
    | none => some h) none

/-- The scope fields of a service's explore lines: the model, what the search covered, and what its inputs try. -/
def exploreScope (name : String) (sc : ScopeV) (c : Coverage) : List (String × Json) :=
  [("model", Json.str name), ("depth", Lean.toJson c.depth), ("exhausted", Json.bool c.exhausted),
    ("capped", Json.bool c.capped), ("exploreDepth", Lean.toJson sc.exploreDepth),
    ("exploreStates", Lean.toJson sc.exploreStates), ("waits", Json.arr (sc.waits.map Lean.toJson).toArray),
    ("othersAtMost", Lean.toJson sc.items),
    ("values", Json.arr (sc.values.map fun vs => Json.mkObj [("input", Json.str (vs.input.kind ++ " " ++ vs.input.name)),
      ("ints", Json.arr (vs.ints.map Lean.toJson).toArray),
      ("strings", Json.arr (vs.strings.map (Json.str ·.1)).toArray)]).toArray)]

def explore (root dir path : String) (opts : Options) : Cmd Unit := do
  let start ← IO.monoMsNow
  match ← loadModel root path opts.model with
  | none => pure ()
  | some (cm, name) =>
    let c := cm.checked
    let deadline := opts.timeout.map (start + 1000 * ·)
    let mut unfinished : Array String := #[]
    for sv in cm.services do
      let v := sv.v
      let rules := ruleNamesOf v
      let gs := dedupBy (· == ·) ((targets c.T v rules).filter fun g => opts.keeps (v.name ++ "/" ++ g.text))
      let bs := (faultTargets v).filter fun g => opts.keeps (v.name ++ "/" ++ g.text)
      let rs := v.responses.zipIdx.filter fun (r, _) => opts.keeps (v.name ++ "/" ++ (Target.response r.name).text)
      let names := gs.map (·.text) ++ bs.map (·.text) ++ rs.map fun (r, _) => (Target.response r.name).text
      if names.isEmpty then continue
      let some sc := cm.model.scopeOf v | return ← internal s!"service {v.name}: no scope after check"
      -- The search is pure; past the deadline its service's lines are not printed, and the run ends.
      let task ← IO.asTask (prio := .dedicated) (pure (search c.T v sc sc.exploreDepth.toNat sc.exploreStates.toNat))
      let found ← match deadline with
        | none => IO.ofExcept (← IO.wait task)
        | some d =>
          let left := d - (← IO.monoMsNow)
          let timer ← IO.asTask (prio := .dedicated) (IO.sleep left.toUInt32)
          match ← IO.waitAny [task.map (·.map some), timer.map (·.map fun _ => none)] with
          | .ok (some f) => pure f
          | _ =>
            unfinished := unfinished ++ (names.map (v.name ++ "/" ++ ·)).toArray
            break
      let cov := found.coverage
      let scope := exploreScope name sc cov
      let common (target : String) := [("service", Json.str v.name), ("target", Json.str target)]
      let chk := c.checked v sv.mem
      let write (file : String) (tr : TraceFile) : IO Unit := do
        let path := System.FilePath.mk dir / file
        if let some d := path.parent then IO.FS.createDirAll d
        IO.FS.writeFile path (String.join (tr.wires.map (·.text ++ "\n")))
      let unwrite (file : String) : IO Unit := do
        let path := System.FilePath.mk dir / file
        if ← path.pathExists then IO.FS.removeFile path
      let assumes (as : List Assumption) := ("assumes", Json.arr (as.map (Json.str ·.text)).toArray)
      printLine (.explore .covered) [("service", Json.str v.name), ("scope", Json.mkObj scope),
        ("states", Json.arr (cov.levels.map Lean.toJson).toArray), ("transitions", Lean.toJson cov.transitions)]
      for g in gs do
        let file := targetFile v.name g
        match earliest (found.classes.filterMap fun (cl, h) => if g.covers rules cl then some h else none) with
        | some h =>
          match genTrace c.T v rules g chk (found.hitPath h) with
          | .ok tr =>
            write file tr
            printLine (.explore .reached) (common g.text ++ [("file", Json.str file), ("steps", Lean.toJson h.depth)])
          | .error m => return ← internal s!"service {v.name}, {g.text}: the run explore found {m}"
        | none =>
          unwrite file
          printLine (.explore .unreached) (common g.text ++ [("scope", Json.mkObj scope),
            assumes Assumption.ofRuns])
      for g in bs do
        let file := breakFile v.name g.text
        match earliest (found.faults.filterMap fun (_, f, h) => if g.covers f then some h else none) with
        | some h =>
          match breakTrace c.T v g (found.hitPath h) with
          | .ok (.ok (tr, f)) =>
            write file tr
            printLine (.explore .violated) (common g.text ++ [("file", Json.str file), ("steps", Lean.toJson h.depth),
              ("outcome", Json.str (Outcome.fault f).summary)])
          | .ok (.error m) | .error m => return ← internal s!"service {v.name}, {g.text}: the run explore found {m}"
        | none =>
          unwrite file
          printLine (.explore .notViolated) (common g.text ++ [("scope", Json.mkObj scope),
            ("assumes", Json.arr #[Json.str Assumption.validInputs.text, Json.str "no step before the last faults"])])
      for (resp, j) in rs do
        let text := (Target.response resp.name).text
        let file := breakFile v.name text
        match found.responses.lookup j with
        | some h =>
          match responseTrace chk resp (found.hitPath h) with
          | .ok tr =>
            write file tr
            printLine (.explore .violated) (common text ++ [("file", Json.str file), ("steps", Lean.toJson h.depth),
              ("outcome", Json.str "late")])
          | .error m => return ← internal s!"service {v.name}, {text}: the run explore found {m}"
        | none =>
          unwrite file
          printLine (.explore .notViolated) (common text ++ [("scope", Json.mkObj scope),
            assumes [.validInputs, .noFault, .timelyClock]])
    unless unfinished.isEmpty do
      printLine .unfinished [("targets", Json.arr (unfinished.map Json.str))]
      -- The search left running is pure and cannot be stopped; the process ends here, with the run's exit code.
      IO.Process.exit (← (← read).get).code.toUInt8

end Tazuna.Cli
