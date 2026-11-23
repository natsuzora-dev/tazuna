import Tazuna.Ir.Group
import Tazuna.Ir.Trace
import Tazuna.Semantics.Service.Note
import Tazuna.Ir.Structure

namespace Tazuna.Semantics.Service

open Tazuna.Ir

/--
An input that the service takes and that breaks what it may assume: a message that no sender could give it, or that
breaks the service's assumption about its sender, or an order that the scenario writes for the input. The input is the
subject, so `definition` is null.
-/
inductive InvalidInput where
  /-- The input names a command, query, or screen that the service does not own. -/
  | unownedTarget (target : Ir.Ref)
  /-- The event input has a payload that does not match the payload schema of `event`. -/
  | eventPayloadSchema (event : Ir.Ref)
  /-- The operation input has a payload that does not match the payload schema of the control `control` of `screen`. -/
  | controlPayloadSchema (screen : Ir.Ref) (control : String)
  /-- The subscribe input has the id of a subscription that is open. -/
  | reusedSubscriptionId (subscriptionId : String)
  /-- The unsubscribe input names a subscription that is not open. -/
  | unopenedSubscription (subscriptionId : String)
  | assumption (requestId : String) (target : Ir.Ref) (mismatch : Ir.AssumptionMismatch)
  /-- The answer rejects the request for a requires reason that the target does not list. -/
  | unlistedRejectionReason (requestId : String) (target : Ir.Ref) (rejection : Rejection)
  | resultOf (event : Ir.Ref) (requestId : String) (target : Ir.Ref) (mismatch : Ir.ResultOfMismatch)
  /-- The operation input names the control `control`, which `screen` does not have. -/
  | unknownControl (screen : Ir.Ref) (control : String)
  /-- The operation input operates a screen that is not open. -/
  | unopenedScreen (screen : Ir.Ref) (control : String)
  /-- The modal screen `child` covers the operated screen. -/
  | coveredByModal (screen : Ir.Ref) (control : String) (child : Ir.Ref)
  /-- No active state of the screen offers the payload of the operation input. -/
  | unofferedPayload (screen : Ir.Ref) (control : String) (payload : Value)
deriving Repr


derive_group InvalidInput flatten mismatch

/--
Whether the violation halts the run, which it does when the scenario as written describes no run, or not one run, from
this input on, so that later inputs would build on a history no run has: the input is one that no sender could give
(it cannot be written as a trace line), it states a cause that did not occur (an event's resultOf naming a request that
cannot have the event as its result). An input that a sender can give, such as a subscription
id it reuses on a retry or an answer that breaks the receiver's assumption, is written as given and the run goes on.
-/
def InvalidInput.halts : InvalidInput → Bool
  | .unownedTarget .. | .eventPayloadSchema .. | .controlPayloadSchema ..
  | .assumption _ _ (.unlistedRejectionKind _) | .assumption _ _ .answerOutputSchema | .unlistedRejectionReason ..
  | .unknownControl .. | .unopenedScreen .. | .coveredByModal .. | .unofferedPayload .. | .resultOf .. => true
  | .reusedSubscriptionId .. | .unopenedSubscription .. | .assumption _ _ .rejectedAssumedRequires
  | .assumption _ _ (.failedAssumedRequires _) | .assumption _ _ (.failedAssumedEnsures _) => false

/-- Whether no spec that `tazuna check` passes can produce the violation, as InvalidScenario.internal says. -/
def InvalidInput.internal : InvalidInput → Bool
  | .unownedTarget .. | .unlistedRejectionReason .. | .unknownControl .. => true
  | .eventPayloadSchema .. | .controlPayloadSchema .. | .reusedSubscriptionId .. | .unopenedSubscription ..
  | .assumption .. | .resultOf .. | .unopenedScreen .. | .coveredByModal .. | .unofferedPayload .. => false

end Tazuna.Semantics.Service
