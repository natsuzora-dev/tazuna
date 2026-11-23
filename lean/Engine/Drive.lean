import Engine.Verify
import Tazuna.Semantics.Sim.Given

/-!
What `drive` asks of the engine while it drives an implementation through a snapshot: the Given records that the
implementation starts from, and the snapshot's lines read by their schemas, whose key references it substitutes by the
bindings under which the log so far compares with the snapshot so far (bindingsOf). Comparing reads values by their
schemas alone, so drive needs no spec function.
-/

namespace Tazuna.Engine

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Verify

/-- A compared value as TS reads it: an object with one field, whose name tells the variant; fields as pairs. -/
partial def CValue.tagged : CValue → Value
  | .leaf v => .obj [("leaf", v)]
  | .ref e v => .obj [("ref", .arr [.str e, .str v])]
  | .arr xs => .obj [("arr", .arr (xs.map CValue.tagged))]
  | .bag xs => .obj [("bag", .arr (xs.map CValue.tagged))]
  | .runs xs => .obj [("runs", .arr (xs.map CValue.tagged))]
  | .obj fs => .obj [("obj", .arr (fs.map fun (k, x) => .arr [.str k, CValue.tagged x]))]

/-- The Given records of the running service `service` of `sc`, as its records hold them, valid and unclashing. -/
def givenRecordsOf (spec : Ir.Structure) (sc : Scenario) (service : String) : IO (List Scenario.GivenRecord) := do
  let st ← Service.ofStructure spec service
  let fs := Eval.functionsOf st (← IO.mkRef {})
  let (rows, _) ← Sim.givenRows st fs (fun _ => none) service (Sim.givenRecords sc service)
  pure (rows.map fun r => { entity := r.entity, key := r.key, value := r.value })

/-- A snapshot line as verify reads it: with its values compared, and its value tagged (CValue.tagged), if it has one. -/
structure ReadLine where
  line : TraceLine
  value : Option Value

derive_wire ReadLine serialize_only skip_serializing_none

/-- Each line as verify reads it, or none for a blank line. -/
def readSnapshotLines (spec : Ir.Structure) (service : String) (lines : List (Option TraceLine)) :
    IO (List (Option ReadLine)) := do
  let (read, _) ← Verify.readLines spec service (readIn spec) lines []
  pure (read.map (·.map fun l => { line := l.toTraceLine, value := l.value.map CValue.tagged }))

/--
The violations of comparing the log `trace` so far with the snapshot lines `snapshot` so far, and the pairs of each
binding that the comparison ends with, by which drive substitutes the snapshot's values.
-/
def bindingsOf (spec : Ir.Structure) (service : String) (snapshot : List (Option TraceLine))
    (trace : List (FileLine TraceLine)) : IO (List Verify.Finding × List (List (String × String))) := do
  let compared ← Verify.verifyLines spec service (readIn spec) snapshot trace id
  pure (compared.findings.filter (·.isViolation), compared.bindings.map (·.strings))

end Tazuna.Engine
