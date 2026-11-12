import Tazuna.Semantics.System.Clock
import Tazuna.Thm.Semantics.Chart.Macrostep

namespace Tazuna.Thm.Semantics.System.Clock

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.Chart.Always Tazuna.Thm.Semantics.Chart.Deadline Tazuna.Thm.Semantics.Chart.Done Tazuna.Thm.Semantics.Chart.Exit Tazuna.Thm.Semantics.Chart.Macrostep Tazuna.Thm.Semantics.Chart.Map Tazuna.Thm.Semantics.Chart.Microstep Tazuna.Thm.Semantics.Chart.Queue Tazuna.Thm.Semantics.Chart.Request Tazuna.Thm.Semantics.Functions Tazuna.Thm.Semantics.Service.Automation Tazuna.Thm.Semantics.Service.Command Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {st : Service} {fs : Functions Id}

theorem keeps_fire (step : Nat) (t : Deadline) : Keeps (fire fs st step t) := by
  intro r
  unfold fire
  simp only [Note.note_id, id_bind]
  split
  · rfl
  · refine (keeps_withMachine (fun i r => ?_) _).trans (takeDeadline_fixed t)
    split
    · rfl
    · exact keeps_applyCompletion _ _ _ _ r

theorem growsBy_fire (step : Nat) (t : Deadline) : GrowsBy (fire fs st step t) := by
  intro r
  unfold fire
  simp only [Note.note_id, id_bind]
  split
  · exact Grows.of_lines (takeDeadline_lines t)
  · refine (Grows.of_lines (takeDeadline_lines t)).trans rfl (growsBy_withMachine (fun i r => ?_) _)
    split
    · exact Grows.refl _
    · exact growsBy_applyCompletion _ _ _ _ r

theorem fires_only_in_active_state (step : Nat) (t : Deadline) (r : Processing) (i : Instance)
    (hi : r.state.machine? t.machine = some i)
    (hn : (r.state.takeDeadline t).2 = false ∨ i.closed = true ∨ i.isIn t.state = false) :
    fire fs st step t r = ⟨(r.state.takeDeadline t).1, r.queue⟩ := by
  unfold fire withMachine
  simp only [Note.note_id, id_bind]
  split
  · rfl
  · split
    · rfl
    · have hm : (r.state.takeDeadline t).1.machine? t.machine = some i := hi
      rcases hn with hn | hn | hn
      · simp_all
      · simp [hm, hn]
      · simp [hm, hn]

/-- Without a named order, deadlines due at one time fire in the default order, from the earliest one. -/
theorem chooseDeadline_default (first : Deadline) (due : List Deadline) (tied : Bool) :
    chooseDeadline first due tied [] = .ok (first, []) := by
  cases tied <;> rfl

/-- The next entry of the input's `deadlineOrder` chooses which of the tied deadlines fires. -/
theorem chooseDeadline_named (first t : Deadline) (due : List Deadline) (c : DeadlineId) (rest : List DeadlineId)
    (h : due.find? (·.id == c) = some t) : chooseDeadline first due true (c :: rest) = .ok (t, rest) := by
  simp [chooseDeadline, h]

end Tazuna.Thm.Semantics.System.Clock
