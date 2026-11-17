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
  /--
  The line is an `out` request line (a command, query or subscribe line) with the id of the earlier `out` request line
  `firstLine`, so the answers that name that id do not tell which request they answer.
  -/
  | duplicateId (line : Nat) (id : String) (firstLine : Nat)
  | unknownRequest (line : Nat) (subject : Subject)
  /-- The answer line names no earlier request line. -/
  | unknownAnswer (line : Nat) (subject : Subject)
  | unknownEvent (line : Nat) (subject : Subject)
  | resultOfUnknownRequest (line : Nat) (event : Syntax.Ref) (requestId : String)
  | resultOfNonCommand (line : Nat) (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  /-- An id of the line's `after` names no earlier `out` line of its group. -/
  | unknownAfter (line : Nat) (lineId : String)
  /-- The trace has an `in` line where the snapshot has none. -/
  | unexpectedInput (line : Nat) (trace : Value)
  /-- The trace, at its last line `line`, has no `in` line for the snapshot's. -/
  | missingInput (line : Nat) (snapshot : Value) (snapshotLine : Nat)
  | differentInput (line snapshotLine : Nat) (snapshot trace : Value)
  /--
  The `in` line names a value that the bindings that agree with the lines so far give different implementation values,
  `candidates` are the trace's `out` lines with those values as ids, and the snapshot's `in` lines do not use alike the
  values that may stand for them, so the route that the harness chose decides what the implementation got
  (Verify/Compare).
  -/
  | ambiguous (line : Nat) (subject : Subject) (snapshotLine : Nat) (candidates : List Nat)
  /--
  Comparing the snapshot line would keep more than `limit` bindings, or ways of pairing its group, that agree with the
  lines so far.
  -/
  | bindingLimit (line : Nat) (subject : Subject) (snapshotLine : Nat) (limit : Nat)
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
