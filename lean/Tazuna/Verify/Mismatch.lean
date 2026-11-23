import Tazuna.Data.Answer
import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Spec.Structure

namespace Tazuna.Verify

open Tazuna.Data

/--
A difference between compared lines. `line` is 1-based in the trace. A line missing from the trace is at the trace's
`in` line before it, or at 1. `snapshotLine` is 1-based in the snapshot. TS decides rejectedAssumedRequires,
failedAssumedRequires, failedAssumedEnsures, answerOutputSchema, eventPayloadSchema and requestInputSchema, which need
the spec's functions or Zod schemas.
-/
inductive Mismatch where
  /-- The request line has another input than the snapshot's. -/
  | request (line : Nat) (subject : Subject) (snapshot trace : Value)
  /-- The request line has another caller than the snapshot's. -/
  | caller (line : Nat) (subject : Subject) (snapshot trace : Value)
  /-- The event line has another payload than the snapshot's. -/
  | event (line : Nat) (subject : Subject) (snapshot trace : Value)
  /-- The accepted or fulfilled answer, or the answer to a query, has another output than the snapshot's. -/
  | output (line : Nat) (subject : Subject) (snapshot trace : Value)
  /-- The answer has another result, accepted, fulfilled, or rejected, than the snapshot's. -/
  | result (line : Nat) (subject : Subject) (snapshot trace : String)
  /-- The answer rejects with another kind than the snapshot's. -/
  | rejection (line : Nat) (subject : Subject) (snapshot trace : RejectionKind)
  /-- The trace does not answer the request that the snapshot answers at `snapshotLine`. -/
  | missingAnswer (line : Nat) (subject : Subject) (snapshotLine : Nat)
  /-- The trace lacks the snapshot's line `snapshotLine`. -/
  | missingLine (line : Nat) (subject : Subject) (content : Value) (snapshotLine : Nat)
  /-- The trace does not open the subscription that the snapshot opens. -/
  | unopenedSubscription (line : Nat) (subject : Subject) (content : Value) (snapshotLine : Nat)
  /-- The trace opens a subscription that the snapshot does not. -/
  | unexpectedSubscription (line : Nat) (subject : Subject) (content : Value)
  /-- The trace has a line that the snapshot does not. -/
  | unexpectedLine (line : Nat) (subject : Subject)
  /-- The line comes before the line `before`, which its snapshot line must follow. -/
  | lineOrder (line : Nat) (subject before : Subject)
  /-- The line has another time than the snapshot's. -/
  | time (line : Nat) (subject : Subject) (snapshot trace : Time)
  /-- The event results from another request than the snapshot's event (`resultOf`), or only one of them names one. -/
  | resultOf (line : Nat) (subject : Subject) (snapshot trace : Option String)
  /-- The run of test, not a trace, differs from the snapshot at its line `line`. A missing line is null. -/
  | line (line : Nat) (snapshot trace : Option Value)
  /-- No contract of another service lists the event that the external service emits. -/
  | unlistedEvent (line : Nat) (event : Spec.Ref)
  /-- The external service emits `event` as a result of the request `requestId`, which it did not accept. -/
  | resultOfUnacceptedRequest (line : Nat) (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  /--
  The external service emits `event` as a result of the request `requestId`, whose target `target` does not list the
  event as a result.
  -/
  | resultOfUnlistedEvent (line : Nat) (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  | assumption (line : Nat) (requestId : String) (target : Spec.Ref) (mismatch : Spec.AssumptionMismatch)
  /-- The answer has a result that the target never answers with: `fulfilled` to a command or `accepted` to a query. -/
  | answerResult (line : Nat) (requestId : String) (target : Spec.Ref) (result : String)
  /-- The answer answers a request whose every send, the first and each resend, an earlier line answered. -/
  | repeatedAnswer (line : Nat) (requestId : String) (target : Spec.Ref)
  /-- The external service emits `event` with a payload that does not match the event's payload schema. -/
  | eventPayloadSchema (line : Nat) (event : Spec.Ref)
  /--
  The external service answers, without rejecting, the request `requestId` whose input does not match the target's input
  schema. Its assumed requires and ensures cannot read such an input.
  -/
  | requestInputSchema (line : Nat) (requestId : String) (target : Spec.Ref)

derive_group Mismatch flatten mismatch

end Tazuna.Verify
