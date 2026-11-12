import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Semantics.Note
import Tazuna.Syntax.Structure

namespace Tazuna.Semantics

open Tazuna.Data

/-- A scenario input that no caller or external service gives. The input is the subject, so `definition` is null. -/
inductive InvalidInput where
  | earlierAt («at» now : Time)
  | notOwned (target : Syntax.Ref)
  | notInContract (event : Syntax.Ref)
  | eventPayloadSchema (event : Syntax.Ref)
  | controlPayloadSchema (screen : Syntax.Ref) (control : String)
  | reusedEventId (id : String) (first delivered : Syntax.Ref)
  | changedRedeliveryPayload (id : String) (event : Syntax.Ref) (first delivered : Value)
  | subscriptionOpen (id : String)
  | subscriptionNotOpen (id : String)
  | unlistedRejectionKind (requestId : String) (target : Syntax.Ref) (rejection : Rejection)
  | unlistedRejectionReason (requestId : String) (target : Syntax.Ref) (rejection : Rejection)
  | answerOutputSchema (requestId : String) (target : Syntax.Ref)
  | rejectedAssumedRequires (requestId : String) (target : Syntax.Ref)
  | failedAssumedRequires (requestId : String) (target : Syntax.Ref) (condition : String)
  | failedAssumedEnsures (requestId : String) (target : Syntax.Ref) (condition : String)
  | resultOfNonCommand (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | resultOfUnacceptedRequest (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | resultOfUnlistedEvent (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | noWaitingRequest (sender target : Syntax.Ref)
  | noStaleRequest (sender target : Syntax.Ref)
  | unknownControl (screen : Syntax.Ref) (control : String)
  | screenNotOpen (screen : Syntax.Ref) (control : String)
  | coveredByModal (screen : Syntax.Ref) (control : String) (child : Syntax.Ref)
  | payloadNotOffered (screen : Syntax.Ref) (control : String) (payload : Value)
  | unexpectedlyAccepted (screen : Syntax.Ref) (control : String)
  | deadlineNotNext (named : DeadlineId) (deadlines : List DeadlineId)
  | unusedDeadlineOrder (entries : List DeadlineId)
  | stepNotNext (named : StepName) (ready : List StepName)
  | unusedStepOrder (entries : List StepName)
  /--
  A value of the input has the form of a createKey value of the service's entity `entity` that createKey has not given
  yet. An implementation makes its own keys, such as UUIDs, so no caller knows a key before the service gives it.
  -/
  | uncreatedKey (key : String) (entity : Syntax.Ref)

local instance : ToValue Time := ⟨fun t => .str (renderTime t)⟩

derive_group InvalidInput

/--
Whether the violation halts the run, which it does when the input cannot be written as a trace line. A trace writes an
implementation's own key in place of each createKey value, which an input cannot hold before the key exists
(uncreatedKey).
-/
def InvalidInput.halts : InvalidInput → Bool
  | .earlierAt .. | .notOwned .. | .notInContract .. | .eventPayloadSchema .. | .controlPayloadSchema ..
  | .unlistedRejectionKind .. | .unlistedRejectionReason .. | .answerOutputSchema .. | .unknownControl ..
  | .screenNotOpen .. | .coveredByModal .. | .payloadNotOffered .. | .unexpectedlyAccepted .. | .deadlineNotNext ..
  | .unusedDeadlineOrder .. | .stepNotNext .. | .unusedStepOrder .. | .uncreatedKey .. => true
  | .reusedEventId .. | .changedRedeliveryPayload .. | .subscriptionOpen .. | .subscriptionNotOpen ..
  | .rejectedAssumedRequires .. | .failedAssumedRequires .. | .failedAssumedEnsures .. | .resultOfNonCommand ..
  | .resultOfUnacceptedRequest .. | .resultOfUnlistedEvent .. | .noWaitingRequest .. | .noStaleRequest .. => false

end Tazuna.Semantics
