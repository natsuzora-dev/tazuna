import Tazuna.Data.Canonical
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Pairing

namespace Tazuna.Verify

open Tazuna.Data

/-- Each line that is not blank, with its file line number. -/
def numbered (snapshot : List (Option Value)) : List (Nat × Value) :=
  (snapshot.zipIdx 1).filterMap fun (v, n) => v.map (n, ·)

/--
The first difference between a snapshot and a run. Lines compare as values, ignoring field order. `none` is a blank
line. A line missing from the snapshot is at the line after the snapshot's last.
-/
def compareSnapshot (snapshot : List (Option Value)) (run : List Value) : Option Mismatch :=
  let lines := numbered snapshot
  ((List.range (max lines.length run.length)).find? fun i =>
      lines[i]?.map (·.2.canonical) ≠ run[i]?.map Value.canonical).map fun i =>
    .line ((lines[i]?.map (·.1)).getD (snapshot.length + 1)) (lines[i]?.map (·.2)) run[i]?

structure SnapshotPairing where
  /-- The compared scenarios that have a snapshot. -/
  compare : List Run
  violations : List (At × Uncomparable)

def snapshotPairing (expected : List Expected) (folders : List Folder) (service : String) : SnapshotPairing :=
  let entries := entriesIn folders service
  let p := pair Run.stem (comparedRuns expected service) entries
  { compare := p.paired
    violations :=
      p.missing.map (fun r => (.scenario r.ref, .missingSnapshot r.ref r.runner)) ++
        p.unknown.map (fun e => (.snapshotEntry service e, .unknownSnapshotEntry)) ++
        (pair Run.stem (runsOf expected service) entries).extra.map fun n =>
          (.snapshotEntry service (n ++ ".jsonl"), .obsoleteSnapshot) }

/--
The pairing of the compared scenarios with their snapshots. A snapshot of a scenario that is not compared is neither
compared nor reported.
-/
def pairSnapshots (services : List String) (expected : List Expected) (folders : List Folder) : SnapshotPairing :=
  let pairings := services.map (snapshotPairing expected folders)
  { compare := pairings.flatMap (·.compare), violations := pairings.flatMap (·.violations) }

end Tazuna.Verify
