import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Service.Note
import Tazuna.Syntax.Structure

namespace Tazuna.Semantics

open Tazuna.Data

/-- A scenario input that no caller or external service gives. The input is the subject, so `definition` is null. -/
inductive InvalidInput where
  /-- The input names a command, query, or screen that the service does not own. -/
  | unownedTarget (target : Syntax.Ref)
  | eventPayloadSchema (event : Syntax.Ref)
  | controlPayloadSchema (screen : Syntax.Ref) (control : String)
  /-- The subscribe input has the id of a subscription that is open. -/
  | reusedSubscriptionId (subscriptionId : String)
  /-- The unsubscribe input names a subscription that is not open. -/
  | unopenedSubscription (subscriptionId : String)
  | unlistedRejectionKind (requestId : String) (target : Syntax.Ref) (rejection : Rejection)
  /-- The answer rejects the request for a requires reason that the target does not list. -/
  | unlistedRejectionReason (requestId : String) (target : Syntax.Ref) (rejection : Rejection)
  | answerOutputSchema (requestId : String) (target : Syntax.Ref)
  /-- The answer rejects the request for requires, although the input meets the target's assumed requires. -/
  | rejectedAssumedRequires (requestId : String) (target : Syntax.Ref)
  /-- The answer is no rejection, although the input fails the target's assumed requires `condition`. -/
  | failedAssumedRequires (requestId : String) (target : Syntax.Ref) (condition : String)
  /-- The answer, or the result events so far, fail the target's assumed ensures `condition`. -/
  | failedAssumedEnsures (requestId : String) (target : Syntax.Ref) (condition : String)
  /-- The resultOf of the event input names a request to a target that is not a command. -/
  | resultOfNonCommand (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  /-- The resultOf of the event input names a request that the answer did not accept. -/
  | resultOfUnacceptedRequest (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  /-- The resultOf of the event input names a request to a command whose emits do not list the event. -/
  | resultOfUnlistedEvent (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
  | unknownControl (screen : Syntax.Ref) (control : String)
  /-- The operation input operates a screen that is not open. -/
  | unopenedScreen (screen : Syntax.Ref) (control : String)
  /-- The modal screen `child` covers the operated screen. -/
  | coveredByModal (screen : Syntax.Ref) (control : String) (child : Syntax.Ref)
  /-- No active state of the screen offers the payload of the operation input. -/
  | unofferedPayload (screen : Syntax.Ref) (control : String) (payload : Value)
  /-- The deadlineOrder entry `named` is not among the deadlines due in the tie, `candidates`. -/
  | unreadyDeadline (named : DeadlineId) (candidates : List DeadlineId)
  /-- No entry of the clock line's order names which of the deadlines `candidates`, due at the same time, fires first. -/
  | unorderedDeadlines (candidates : List DeadlineId)
  /-- No tie during the input used the deadlineOrder `entries`. -/
  | unusedDeadlineOrder (entries : List DeadlineId)
  /-- The stepOrder entry `named` is not among the steps that can begin next, `candidates`. -/
  | unreadyStep (named : StepName) (candidates : List StepName)
  /-- No step choice during the input used the stepOrder `entries`. -/
  | unusedStepOrder (entries : List StepName)

local instance : ToValue Time := ⟨fun t => .str (renderTime t)⟩

derive_group InvalidInput

/--
Whether the violation halts the run, which it does when the input cannot be written as a trace line.
-/
def InvalidInput.halts : InvalidInput → Bool
  | .unownedTarget .. | .eventPayloadSchema .. | .controlPayloadSchema ..
  | .unlistedRejectionKind .. | .unlistedRejectionReason .. | .answerOutputSchema .. | .unknownControl ..
  | .unopenedScreen .. | .coveredByModal .. | .unofferedPayload .. | .unreadyDeadline ..
  | .unorderedDeadlines ..
  | .unusedDeadlineOrder .. | .unreadyStep .. | .unusedStepOrder .. => true
  | .reusedSubscriptionId .. | .unopenedSubscription ..
  | .rejectedAssumedRequires .. | .failedAssumedRequires .. | .failedAssumedEnsures .. | .resultOfNonCommand ..
  | .resultOfUnacceptedRequest .. | .resultOfUnlistedEvent .. => false

end Tazuna.Semantics
