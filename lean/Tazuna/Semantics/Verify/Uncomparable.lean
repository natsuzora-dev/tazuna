import Tazuna.Ir.Group
import Tazuna.Ir.Structure
import Tazuna.Semantics.Verify.Mismatch

namespace Tazuna.Semantics.Verify

open Tazuna.Ir

/--
A line or file that verify cannot compare. `line` is 1-based in the violation's file, and `specLine` is 1-based in
the lines of the spec's replay.
-/
inductive Uncomparable where
  /-- The line is not a trace line that the trace line schema reads. -/
  | lineSchema (line : Nat)
  /--
  The line is a request line (a command, query or subscribe line) with the id of the earlier request line `firstLine`
  and another type, name or input, so the answers that name that id do not tell which request they answer: an `out`
  request in a trace that verify compares with a snapshot, an `in` request in an external service's trace
  (Verify/Compare's firstDuplicate).
  -/
  | duplicateId (line : Nat) (id : String) (firstLine : Nat)
  /-- The `in` request line of an external service's trace names a command or query that the service does not have. -/
  | unknownRequest (line : Nat) (subject : Subject)
  /-- The answer line names no earlier request line. -/
  | unknownAnswer (line : Nat) (subject : Subject)
  /-- The event line of an external service's trace names an event that the service does not have. -/
  | unknownEvent (line : Nat) (subject : Subject)
  /-- The event names as its cause (`resultOf`) `requestId`, which no earlier request line has as its id. -/
  | resultOfUnknownRequest (line : Nat) (event : Ir.Ref) (requestId : String)
  /-- The event names as its cause (`resultOf`) the request `requestId` to `target`, which is not a command. -/
  | resultOfNonCommand (line : Nat) (event : Ir.Ref) (requestId : String) (target : Ir.Ref)
  /-- An id of the line's `after` names no earlier `out` line of its group. -/
  | unknownAfter (line : Nat) (lineId : String)
  /--
  The `in` line differs from the `in` line `specLine` that the spec took from it: its time is earlier than the
  spec's clock, which never goes back. Where one side has no `in` line, its value is null, and `specLine` is 0 when
  the spec has none.
  -/
  | differentInput (line specLine : Nat) (spec trace : Value)
  /--
  The `in` line names a value that the bindings that agree with the lines so far give different implementation values,
  `candidates` are the trace's `out` lines with those values as ids, and the spec's `in` lines do not use alike the
  values that may stand for them, so the route that the harness chose decides what the implementation got
  (Verify/Compare). Equal requests that get different answers cause it. Give them content that tells them apart, or
  equal answers.
  -/
  | ambiguous (line : Nat) (subject : Subject) (specLine : Nat) (candidates : List Nat)
  /--
  Comparing the spec line would keep more than `limit` bindings, or ways of pairing its group, that agree with the
  lines so far.
  -/
  | bindingLimit (line : Nat) (subject : Subject) (specLine : Nat) (limit : Nat)
  /-- The traces folder has a folder `service` that names no service of the spec. -/
  | unknownService (service : String)
  /-- The traces folder has an entry that is not in a service's folder, or is neither a file nor a folder. -/
  | unknownTraceEntry
  /--
  The run of `scenario` by `runner` did not halt and has no snapshot, such as the run of a new scenario.
  `tazuna test --update` writes the snapshot.
  -/
  | missingSnapshot (scenario : Ir.Ref) (runner : String)
  /-- A snapshot is named for no scenario of the service. -/
  | obsoleteSnapshot
  /-- A snapshot folder has an entry that is not a `<scenario>.jsonl` or `<scenario>.<peer>.jsonl` snapshot. -/
  | unknownSnapshotEntry

derive_group Uncomparable

end Tazuna.Semantics.Verify
