import Tazuna.Cli.Check
import Tazuna.Trace.Verify

/-! The `test` and `verify` commands. `test` runs each scenario and compares its trace with the snapshot
`snapshots/<service>/<scenario>.jsonl`, or writes the snapshot with `--update`. `verify` replays each trace in a
directory against the spec. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Trace

def faultFields : Fault → List (String × Json)
  | .invariant n | .ensures n => [("rule", Json.str n)]
  | .cascadeLimit => []
  | .answerUnmatched to => [("to", Json.str to)]
  | .invalidEffect n rs => [("request", Json.str n), ("rules", Json.arr (rs.map Json.str).toArray)]

/-- The scenario's steps, typed by its service, when the types agree; the structure rules have checked that they do. -/
def _root_.Tazuna.Ir.ScenarioV.stepsFor (sc : ScenarioV) (v : ServiceV) : Option (List (StepV v.records v.event v.caller)) :=
  match Ty.same sc.records v.records, Ty.same sc.event v.event, Ty.same sc.caller v.caller with
  | some ⟨h1⟩, some ⟨h2⟩, some ⟨h3⟩ => some (h1 ▸ h2 ▸ h3 ▸ sc.steps)
  | _, _, _ => none

def textLines (text : String) : List String := (text.splitOn "\n").filter (!·.isEmpty)

/-- Runs one scenario and compares or writes its snapshot; returns whether it passed. -/
def testScenario (T : List TypeDecl) (spec : SpecV) (sc : ScenarioV) (update : Bool) : IO Bool := do
  let at_ := [("service", Json.str sc.service), ("scenario", Json.str sc.name)]
  let some v := spec.services.find? (·.name == sc.service) | return false
  let some steps := sc.stepsFor v | return false
  match runScenario T v steps with
  | .error (.fault k f) =>
    printLine (.fault f.kind) (at_ ++ [("step", Json.num k)] ++ faultFields f)
    return false
  | .error (.badStep k m) =>
    printLine (.test .badStep) (at_ ++ [("step", Json.num k), ("message", Json.str m)])
    return false
  | .ok wires =>
    let lines := wires.map Wire.text
    let dir : System.FilePath := "snapshots" / sc.service
    let path := dir / (sc.name ++ ".jsonl")
    if update then
      IO.FS.createDirAll dir
      IO.FS.writeFile path (String.intercalate "\n" lines ++ "\n")
      printLine (.test .written) (at_ ++ [("path", Json.str path.toString)])
      return true
    let expected ← if ← path.pathExists then pure (some (textLines (← IO.FS.readFile path))) else pure none
    let some expected := expected | do
      printLine (.test .changed) (at_ ++ [("path", Json.str path.toString), ("line", Json.num 1),
        ("expected", Json.null), ("actual", Json.str (lines.headD ""))])
      return false
    let n := max expected.length lines.length
    match (List.range n).find? fun i => expected[i]? != lines[i]? with
    | none =>
      printLine (.test .passed) at_
      return true
    | some i =>
      let text (l : Option String) : Json := (l.map Json.str).getD Json.null
      printLine (.test .changed) (at_ ++ [("path", Json.str path.toString), ("line", Json.num ((i + 1 : Nat) : Int)),
        ("expected", text expected[i]?), ("actual", text lines[i]?)])
      return false

def test (root path : String) (update : Bool) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok (T, spec) =>
    let mut ok := true
    for sc in spec.scenarios do
      ok := (← testScenario T spec sc update) && ok
    return if ok then 0 else 1

/-- Reads the lines of a trace after its header, each with its line number, and the service it names. -/
def readTrace (spec : SpecV) (text : String) : Except (Nat × String) ((_ : ServiceV) × List (Nat × Line)) := do
  let raw := (text.splitOn "\n").zipIdx.filterMap fun (l, k) => if l.isEmpty then none else some (k + 1, l)
  let (n, first) :: rest := raw | throw (1, "the trace is empty")
  let service ← match Wire.parse first with
    | .ok (.obj kvs) => match kvs.lookup "trace", kvs.lookup "service" with
      | some (.num 1), some (.str s) => pure s
      | _, _ => throw (n, "the first line is no header {\"trace\":1,\"service\":...}")
    | _ => throw (n, "the first line is no header {\"trace\":1,\"service\":...}")
  let some v := spec.services.find? (·.name == service) | throw (n, s!"the spec has no service {service}")
  let lines ← rest.mapM fun (k, l) => match Wire.parse l with
    | .ok w => match Line.ofWire w with
      | some line => pure (k, line)
      | none => throw (k, "the line is no trace line")
    | .error e => throw (k, s!"the line is not JSON: {e}")
  pure ⟨v, lines⟩

def verify (root dir path : String) : IO UInt32 := do
  match ← loadSpec root path with
  | .error code => return code
  | .ok (T, spec) =>
    let entries ← System.FilePath.readDir dir
    let files := (entries.toList.map (·.path)).filter (·.extension == some "jsonl") |>.mergeSort
      fun a b => a.toString ≤ b.toString
    let mut ok := true
    for file in files do
      let at_ := ("trace", Json.str file.toString)
      let text ← IO.FS.readFile file
      match readTrace spec text with
      | .error (n, m) =>
        printLine .traceInvalid [at_, ("line", Json.num n), ("message", Json.str m)]
        ok := false
      | .ok ⟨v, lines⟩ =>
        match replay T v lines with
        | .passed => printLine .verifyPassed [at_]
        | .differs n expected actual =>
          let texts (ws : List Wire) := Json.arr (ws.map (Json.str ·.text)).toArray
          printLine .verifyDiffers [at_, ("line", Json.num n), ("expected", texts expected), ("actual", texts actual)]
          ok := false
        | .invalid n m =>
          printLine .traceInvalid [at_, ("line", Json.num n), ("message", Json.str m)]
          ok := false
        | .fault n f =>
          printLine (.fault f.kind) ([at_, ("line", Json.num n)] ++ faultFields f)
          ok := false
    return if ok then 0 else 1

end Tazuna.Cli
