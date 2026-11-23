import Tazuna.Semantics.Service.State

namespace Tazuna.Semantics.Service

open Tazuna.Ir

/--
The state after the answer to an automation's command. As in sagas and Temporal, a rejected automation command is
neither retried nor compensated implicitly. An unavailable rejection is ignored, as the automation's `onRejected: []`
states; any other kind is a fault of the automation.
-/
def automationAnswer (st : Service) (automation : String) (answer : Answer) (s : State) : State :=
  match answer with
  | .rejected r =>
    if RejectionKind.byCaller r.kind then s.report (.fault (.rejectedAutomationCommand (st.ref automation) r)) else s
  | _ => s

end Tazuna.Semantics.Service
