import Tazuna.Semantics.Service.Clock
import Tazuna.Thm.Semantics.Service.Chart.Macrostep
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Service.Clock

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.Chart.Always Tazuna.Thm.Semantics.Service.Chart.Deadline Tazuna.Thm.Semantics.Service.Chart.Done Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Macrostep Tazuna.Thm.Semantics.Service.Chart.Map Tazuna.Thm.Semantics.Service.Chart.Microstep Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.Chart.Request Tazuna.Thm.Semantics.Service.Functions Tazuna.Thm.Semantics.Service.Automation Tazuna.Thm.Semantics.Service.Command Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic

variable {st : Service} {fs : Functions Id}

theorem keeps_fire (step : Nat) (t : Service.Deadline) : Keeps (fire fs st step t) := by
  intro r
  unfold fire
  simp only
  split
  · rfl
  · refine (keeps_withMachine (fun i r => ?_) _).trans (takeDeadline_fixed t)
    split
    · rfl
    · exact keeps_applyCompletion _ _ _ _ r

theorem growsBy_fire (step : Nat) (t : Service.Deadline) : GrowsBy (fire fs st step t) := by
  intro r
  unfold fire
  simp only
  split
  · exact Grows.of_lines rfl
  · refine Grows.after (growsBy_withMachine (fun i r => ?_)) rfl rfl
    split
    · exact Grows.refl _
    · exact growsBy_applyCompletion _ _ _ _ r

@[guarantee] theorem fires_only_in_active_state (step : Nat) (t : Service.Deadline) (r : Processing) (i : Instance)
    (hi : r.state.machine? t.machine = some i)
    (hn : (r.state.takeDeadline t).2 = false ∨ i.closed = true ∨ i.isIn t.state = false) :
    fire fs st step t r = ⟨(r.state.takeDeadline t).1, r.queue⟩ := by
  unfold fire withMachine
  simp only
  split
  · rfl
  · split
    · rfl
    · have hm : (r.state.takeDeadline t).1.machine? t.machine = some i := hi
      rcases hn with hn | hn | hn
      · simp_all
      · simp [hm, hn]
      · simp [hm, hn]

end Tazuna.Thm.Semantics.Service.Clock
