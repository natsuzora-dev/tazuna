import Tazuna.Data.Group
import Tazuna.Syntax.Structure
import Tazuna.Verify.Mismatch

namespace Tazuna.Verify

open Tazuna.Data

/--
A line or file that verify cannot compare. `line` is 1-based in the violation's file, and `snapshotLine` is 1-based in
the snapshot.
-/
inductive Uncomparable where
  | lineSchema (line : Nat)
  | unknownRequest (line : Nat) (subject : Subject)
  /-- The answer line names no earlier request line. -/
  | unknownAnswer (line : Nat) (subject : Subject)
  | unknownEvent (line : Nat) (subject : Subject)
  | resultOfUnknownRequest (line : Nat) (event : Syntax.Ref) (requestId : String)
  | resultOfNonCommand (line : Nat) (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  /-- An id of the line's `after` names no earlier `out` line of its window. -/
  | unknownAfter (line : Nat) (lineId : String)
  /-- The trace has an `in` line where the snapshot has none. -/
  | unexpectedInput (line : Nat) (trace : Value)
  /-- The trace, at its last line `line`, has no `in` line for the snapshot's. -/
  | missingInput (line : Nat) (snapshot : Value) (snapshotLine : Nat)
  /-- The answer input answers another request than the snapshot's answer input does. -/
  | differentRequest (line : Nat) (subject : Subject) (snapshotLine : Nat)
  | differentInput (line snapshotLine : Nat) (snapshot trace : Value)
  /--
  The comparison takes more steps than verify searches, over all its tries: of the window after the `in` lines `line`
  and `snapshotLine` (1 for the first window), or of those `in` lines.
  -/
  | searchLimit (line snapshotLine : Nat)
  | unknownService (service : String)
  /-- A trace is named for no scenario of the service. -/
  | unknownScenario (scenario : Syntax.Ref)
  | missingTrace (scenario : Syntax.Ref)
  | unknownTraceEntry
  | missingSnapshot (scenario : Syntax.Ref)
  /-- A snapshot is named for no scenario of the service. -/
  | obsoleteSnapshot
  | unknownSnapshotEntry

derive_group Uncomparable

end Tazuna.Verify
