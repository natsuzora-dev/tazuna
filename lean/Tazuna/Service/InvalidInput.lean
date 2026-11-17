import Tazuna.Data.Group
import Tazuna.Data.Trace
import Tazuna.Service.Note
import Tazuna.Spec.Structure

namespace Tazuna.Service

open Tazuna.Data

/--
An input that the service takes and that breaks what it may assume: a message that no sender could give it, or that
breaks the service's assumption about its sender, or an order that the scenario writes for the input. The input is the
subject, so `definition` is null.
-/
inductive InvalidInput where
  /-- The input names a command, query, or screen that the service does not own. -/
  | unownedTarget (target : Spec.Ref)
  | eventPayloadSchema (event : Spec.Ref)
  | controlPayloadSchema (screen : Spec.Ref) (control : String)
  /-- The subscribe input has the id of a subscription that is open. -/
  | reusedSubscriptionId (subscriptionId : String)
  /-- The unsubscribe input names a subscription that is not open. -/
  | unopenedSubscription (subscriptionId : String)
  | unlistedRejectionKind (requestId : String) (target : Spec.Ref) (rejection : Rejection)
  /-- The answer rejects the request for a requires reason that the target does not list. -/
  | unlistedRejectionReason (requestId : String) (target : Spec.Ref) (rejection : Rejection)
  | answerOutputSchema (requestId : String) (target : Spec.Ref)
  /-- The answer rejects the request for requires, although the input meets the target's assumed requires. -/
  | rejectedAssumedRequires (requestId : String) (target : Spec.Ref)
  /-- The answer is no rejection, although the input fails the target's assumed requires `condition`. -/
  | failedAssumedRequires (requestId : String) (target : Spec.Ref) (condition : String)
  /-- The answer, or the result events so far, fail the target's assumed ensures `condition`. -/
  | failedAssumedEnsures (requestId : String) (target : Spec.Ref) (condition : String)
  /-- The resultOf of the event input names a request to a target that is not a command. -/
  | resultOfNonCommand (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  /-- The resultOf of the event input names a request that the answer did not accept. -/
  | resultOfUnacceptedRequest (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  /-- The resultOf of the event input names a request to a command whose emits do not list the event. -/
  | resultOfUnlistedEvent (event : Spec.Ref) (requestId : String) (target : Spec.Ref)
  | unknownControl (screen : Spec.Ref) (control : String)
  /-- The operation input operates a screen that is not open. -/
  | unopenedScreen (screen : Spec.Ref) (control : String)
  /-- The modal screen `child` covers the operated screen. -/
  | coveredByModal (screen : Spec.Ref) (control : String) (child : Spec.Ref)
  /-- No active state of the screen offers the payload of the operation input. -/
  | unofferedPayload (screen : Spec.Ref) (control : String) (payload : Value)
  /-- The stepOrder entry `named` is not among the steps that can begin next, `candidates`. -/
  | unreadyStep (named : StepName) (candidates : List StepName)
  /-- No step choice during the input used the stepOrder `entries`. -/
  | unusedStepOrder (entries : List StepName)
  /-- The event input names as its resultOf the request `requestId`, whose answer the service has not taken. -/
  | resultOfUnansweredRequest (event : Spec.Ref) (requestId : String)
deriving Repr

local instance : ToValue Time := ⟨fun t => .str (renderTime t)⟩

derive_group InvalidInput

/--
Whether the violation halts the run, which it does when the scenario as written describes no run, or not one run, from
this input on, so that later inputs would build on a history no run has: the input is one that no sender could give
(it cannot be written as a trace line), it states a cause that did not occur (an event's resultOf naming a request that
cannot have the event as its result), or the step order written for it does not fit the run (an entry that names
nothing that can begin next, or an entry it leaves unused). An input that a sender can give, such as a subscription
id it reuses on a retry or an answer that breaks the receiver's assumption, is written as given and the run goes on.
-/
def InvalidInput.halts : InvalidInput → Bool
  | .unownedTarget .. | .eventPayloadSchema .. | .controlPayloadSchema ..
  | .unlistedRejectionKind .. | .unlistedRejectionReason .. | .answerOutputSchema .. | .unknownControl ..
  | .unopenedScreen .. | .coveredByModal .. | .unofferedPayload .. | .unreadyStep .. | .unusedStepOrder .. | .resultOfUnansweredRequest ..
  | .resultOfNonCommand .. | .resultOfUnacceptedRequest .. | .resultOfUnlistedEvent .. => true
  | .reusedSubscriptionId .. | .unopenedSubscription ..
  | .rejectedAssumedRequires .. | .failedAssumedRequires .. | .failedAssumedEnsures .. => false

end Tazuna.Service
