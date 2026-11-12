import Tazuna.Semantics.Service.Automation
import Tazuna.Thm.Semantics.State

namespace Tazuna.Thm.Semantics.Service.Automation

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {st : Service} {s : State}

theorem automationAnswer_fixed (a : String) (answer : Answer) (t : State) :
    (automationAnswer st a answer t).fixed = t.fixed := by
  unfold automationAnswer; split <;> (try split) <;> simp

theorem automationAnswer_lines (a : String) (answer : Answer) (t : State) :
    (automationAnswer st a answer t).lines = t.lines := by
  unfold automationAnswer; split <;> (try split) <;> simp

theorem rejected_automation_command_reported (a : String) (r : Rejection) (t : State)
    (h : RejectionKind.byCaller r.kind) :
    automationAnswer st a (.rejected r) t =
      t.violate (Finding.fault (.rejectedAutomationCommand (st.ref a) r)).toViolation := by
  simp [automationAnswer, h, State.report, Fault.halts]

end Tazuna.Thm.Semantics.Service.Automation
