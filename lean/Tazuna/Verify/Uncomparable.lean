import Tazuna.Data.Group
import Tazuna.Spec.Structure
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
  The line is a request line (a command, query or subscribe line) with the id of the earlier request line `firstLine`
  and another type, name or input, so the answers that name that id do not tell which request they answer: an `out`
  request in a trace that verify compares with a snapshot, an `in` request in an external service's trace
  (Verify/Compare's firstDuplicate).
  -/
  | duplicateId (line : Nat) (id : String) (firstLine : Nat)
  | unknownRequest (line : Nat) (subject : Subject)
  /-- The answer line names no earlier request line. -/
  | unknownAnswer (line : Nat) (subject : Subject)
  | unknownEvent (line : Nat) (subject : Subject)
  | resultOfUnknownRequest (line : Nat) (event : Spec.Ref) (requestId : String)
  | resultOfNonCommand (line : Nat) (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
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
  (Verify/Compare). Equal requests that get different answers cause it. Give them content that tells them apart, or
  equal answers.
  -/
  | ambiguous (line : Nat) (subject : Subject) (snapshotLine : Nat) (candidates : List Nat)
  /--
  Comparing the snapshot line would keep more than `limit` bindings, or ways of pairing its group, that agree with the
  lines so far.
  -/
  | bindingLimit (line : Nat) (subject : Subject) (snapshotLine : Nat) (limit : Nat)
  | unknownService (service : String)
  /-- A trace is named for no scenario of the service. -/
  | unknownScenario (scenario : Spec.Ref)
  /-- A snapshot of the run of `scenario` by `runner` has no trace. -/
  | missingTrace (scenario : Spec.Ref) (runner : String)
  | unknownTraceEntry
  /-- The run of `scenario` by `runner` did not halt and has no snapshot. -/
  | missingSnapshot (scenario : Spec.Ref) (runner : String)
  /-- A snapshot is named for no scenario of the service. -/
  | obsoleteSnapshot
  | unknownSnapshotEntry

derive_group Uncomparable

end Tazuna.Verify
