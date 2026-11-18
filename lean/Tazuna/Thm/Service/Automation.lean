import Tazuna.Service.Automation
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Automation

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {s : State}

theorem automationAnswer_fixed (a : String) (answer : Answer) (t : State) :
    (automationAnswer st a answer t).fixed = t.fixed := by
  unfold automationAnswer; split <;> (try split) <;> simp

theorem automationAnswer_lines (a : String) (answer : Answer) (t : State) :
    (automationAnswer st a answer t).lines = t.lines := by
  unfold automationAnswer; split <;> (try split) <;> simp

end Tazuna.Thm.Service.Automation
