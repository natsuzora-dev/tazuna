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
  /-- The event input has a payload that does not match the payload schema of `event`. -/
  | eventPayloadSchema (event : Spec.Ref)
  /-- The operation input has a payload that does not match the payload schema of the control `control` of `screen`. -/
  | controlPayloadSchema (screen : Spec.Ref) (control : String)
  /-- The subscribe input has the id of a subscription that is open. -/
  | reusedSubscriptionId (subscriptionId : String)
  /-- The unsubscribe input names a subscription that is not open. -/
  | unopenedSubscription (subscriptionId : String)
  | assumption (requestId : String) (target : Spec.Ref) (mismatch : Spec.AssumptionMismatch)
  /-- The answer rejects the request for a requires reason that the target does not list. -/
  | unlistedRejectionReason (requestId : String) (target : Spec.Ref) (rejection : Rejection)
  | resultOf (event : Spec.Ref) (requestId : String) (target : Spec.Ref) (mismatch : Spec.ResultOfMismatch)
  /-- The operation input names the control `control`, which `screen` does not have. -/
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
deriving Repr


derive_group InvalidInput flatten mismatch

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
  | .assumption _ _ (.unlistedRejectionKind _) | .assumption _ _ .answerOutputSchema | .unlistedRejectionReason ..
  | .unknownControl .. | .unopenedScreen .. | .coveredByModal .. | .unofferedPayload .. | .unreadyStep ..
  | .unusedStepOrder .. | .resultOf .. => true
  | .reusedSubscriptionId .. | .unopenedSubscription .. | .assumption _ _ .rejectedAssumedRequires
  | .assumption _ _ (.failedAssumedRequires _) | .assumption _ _ (.failedAssumedEnsures _) => false

/-- Whether no spec that `tazuna check` passes can produce the violation, as InvalidScenario.internal says. -/
def InvalidInput.internal : InvalidInput → Bool
  | .unownedTarget .. | .unlistedRejectionReason .. | .unknownControl .. | .unreadyStep .. | .unusedStepOrder .. => true
  | .eventPayloadSchema .. | .controlPayloadSchema .. | .reusedSubscriptionId .. | .unopenedSubscription ..
  | .assumption .. | .resultOf .. | .unopenedScreen .. | .coveredByModal .. | .unofferedPayload .. => false

end Tazuna.Service
