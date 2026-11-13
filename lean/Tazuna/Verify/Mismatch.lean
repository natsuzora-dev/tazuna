import Tazuna.Data.Answer
import Tazuna.Data.Group
import Tazuna.Syntax.Structure

namespace Tazuna.Verify

open Tazuna.Data

inductive Subject where
  | reply (type to : String)
  | named (type : String) (name id : Option String)

derive_wire Subject untagged

/-- A snapshot value and the trace value that a pair of lines uses for it. -/
structure Use where
  snapshot : String
  trace : String
  line : Nat
  snapshotLine : Nat
deriving DecidableEq, Repr, Inhabited

derive_wire Use

/--
A difference between compared lines. `line` is 1-based in the trace. A line missing from the trace is at the
trace's `in` line before it, or at 1. `snapshotLine` is 1-based in the snapshot. Mismatch.line compares the run
of test, not a trace: `run` is the run's line compared with the snapshot line at `snapshotLine`, and a missing
line is null. `renaming` holds the uses of one connected group of values in which a value stands for two values,
when no line differs otherwise. TS decides rejectedAssumedRequires, failedAssumedRequires, failedAssumedEnsures,
answerOutputSchema and eventPayloadSchema, which need the spec's functions or Zod schemas.
-/
inductive Mismatch where
  | request (line : Nat) (id : Option String) (type name : String) (snapshot trace : Value)
  | event (line : Nat) (name : String) (snapshot trace : Value)
  | operation (line : Nat) (name : String) (snapshot trace : Value)
  | output (line : Nat) (to : String) (snapshot trace : Value)
  | result (line : Nat) (to : String) (snapshot trace : String)
  | rejection (line : Nat) (to : String) (snapshot trace : RejectionKind)
  | missingAnswer (line : Nat) (type to : String) (snapshotLine : Nat)
  | missingLine (line : Nat) (type name : String) (content : Value) (snapshotLine : Nat)
  | unopenedSubscription (line : Nat) (name : String) (input : Value) (snapshotLine : Nat)
  | unexpectedSubscription (line : Nat) (name : String) (input : Value) (id : String)
  | unexpectedLine (line : Nat) (subject : Subject)
  | lineOrder (line : Nat) (subject before : Subject)
  | time (line : Nat) (subject : Subject) (snapshot trace : String)
  | renaming (uses : List Use)
  | line (snapshotLine : Nat) (snapshot run : Option Value)
  | emittedNotInContract (line : Nat) (event : Syntax.Ref) (service : String)
  | resultOfUnacceptedRequest (line : Nat) (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | resultOfUnlistedEvent (line : Nat) (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | unlistedRejectionKind (line : Nat) (requestId : String) (target : Syntax.Ref) (rejection : Rejection)
  | rejectedAssumedRequires (line : Nat) (requestId : String) (target : Syntax.Ref)
  | failedAssumedRequires (line : Nat) (requestId : String) (target : Syntax.Ref) (condition : String)
  | failedAssumedEnsures (line : Nat) (requestId : String) (target : Syntax.Ref) (condition : String)
  | answerOutputSchema (line : Nat) (requestId : String) (target : Syntax.Ref)
  | eventPayloadSchema (line : Nat) (event : Syntax.Ref)

derive_group Mismatch

end Tazuna.Verify
