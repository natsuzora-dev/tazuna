import Tazuna.Data.Answer
import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Spec.Structure

namespace Tazuna.Verify

open Tazuna.Data

/--
A trace line as a violation names it: an answer or unsubscribe line by its `to`, and any other line by its name and
id.
-/
inductive Subject where
  | reply (type to : String)
  | named (type : String) (name : Option String) (id : String)

derive_wire Subject untagged

def Subject.of (l : TraceLine) : Subject :=
  match l.body with
  | .answer _ _ to _ | .unsubscribe _ _ to => .reply l.body.type to
  | _ => .named l.body.type l.body.name? l.body.id

/--
A difference between compared lines. `line` is 1-based in the trace; a line missing from the trace is at the trace's
`in` line before it, or at 1. `snapshotLine` is 1-based in the snapshot. TS decides rejectedAssumedRequires,
failedAssumedRequires, failedAssumedEnsures, answerOutputSchema and eventPayloadSchema, which need the spec's functions
or Zod schemas.
-/
inductive Mismatch where
  | request (line : Nat) (subject : Subject) (snapshot trace : Value)
  | event (line : Nat) (subject : Subject) (snapshot trace : Value)
  | operation (line : Nat) (subject : Subject) (snapshot trace : Value)
  /-- The output of an accepted or fulfilled answer, or the answer to a query. -/
  | output (line : Nat) (subject : Subject) (snapshot trace : Value)
  | result (line : Nat) (subject : Subject) (snapshot trace : String)
  | rejection (line : Nat) (subject : Subject) (snapshot trace : RejectionKind)
  | missingAnswer (line : Nat) (subject : Subject) (snapshotLine : Nat)
  | missingLine (line : Nat) (subject : Subject) (content : Value) (snapshotLine : Nat)
  /-- The trace does not open the subscription that the snapshot opens. -/
  | unopenedSubscription (line : Nat) (subject : Subject) (content : Value) (snapshotLine : Nat)
  /-- The trace opens a subscription that the snapshot does not. -/
  | unexpectedSubscription (line : Nat) (subject : Subject) (content : Value)
  | unexpectedLine (line : Nat) (subject : Subject)
  /-- The line comes before the line `before`, which its snapshot line must follow. -/
  | lineOrder (line : Nat) (subject before : Subject)
  | time (line : Nat) (subject : Subject) (snapshot trace : String)
  /-- The event results from another request than the snapshot's event (`resultOf`), or only one of them names one. -/
  | resultOf (line : Nat) (subject : Subject) (snapshot trace : Option String)
  /-- The run of test, not a trace, differs from the snapshot at its line `line`; a missing line is null. -/
  | line (line : Nat) (snapshot trace : Option Value)
  /-- No contract of another service lists the event that the external service emits. -/
  | unlistedEvent (line : Nat) (event : Spec.Ref)
  | resultOfUnacceptedRequest (line : Nat) (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  | resultOfUnlistedEvent (line : Nat) (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  | unlistedRejectionKind (line : Nat) (requestId : String) (target : Spec.Ref) (rejection : Rejection)
  | rejectedAssumedRequires (line : Nat) (requestId : String) (target : Spec.Ref)
  | failedAssumedRequires (line : Nat) (requestId : String) (target : Spec.Ref) (condition : String)
  | failedAssumedEnsures (line : Nat) (requestId : String) (target : Spec.Ref) (condition : String)
  | answerOutputSchema (line : Nat) (requestId : String) (target : Spec.Ref)
  | eventPayloadSchema (line : Nat) (event : Spec.Ref)

derive_group Mismatch

end Tazuna.Verify
