import Tazuna.Semantics.Service.Automation
import Tazuna.Thm.Semantics.Service.State

namespace Tazuna.Thm.Semantics.Service.Automation

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic

variable {st : Service} {s : Service.State}

theorem automationAnswer_fixed (a : String) (answer : Answer) (t : Service.State) :
    (automationAnswer st a answer t).fixed = t.fixed := by
  unfold automationAnswer; split <;> (try split) <;> simp

theorem automationAnswer_lines (a : String) (answer : Answer) (t : Service.State) :
    (automationAnswer st a answer t).lines = t.lines := by
  unfold automationAnswer; split <;> (try split) <;> simp

end Tazuna.Thm.Semantics.Service.Automation
