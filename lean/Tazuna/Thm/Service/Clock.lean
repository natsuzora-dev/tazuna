import Tazuna.Service.Clock
import Tazuna.Thm.Service.Chart.Macrostep

namespace Tazuna.Thm.Service.Clock

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id}

theorem keeps_fire (step : Nat) (t : Deadline) : Keeps (fire fs st step t) := by
  intro r
  unfold fire
  simp only [Tazuna.Thm.Service.Note.note_id, id_bind]
  split
  · rfl
  · refine (keeps_withMachine (fun i r => ?_) _).trans (takeDeadline_fixed t)
    split
    · rfl
    · exact keeps_applyCompletion _ _ _ _ r

theorem fires_only_in_active_state (step : Nat) (t : Deadline) (r : Processing) (i : Instance)
    (hi : r.state.machine? t.machine = some i)
    (hn : (r.state.takeDeadline t).2 = false ∨ i.closed = true ∨ i.isIn t.state = false) :
    fire fs st step t r = ⟨(r.state.takeDeadline t).1, r.queue⟩ := by
  unfold fire withMachine
  simp only [Tazuna.Thm.Service.Note.note_id, id_bind]
  split
  · rfl
  · split
    · rfl
    · have hm : (r.state.takeDeadline t).1.machine? t.machine = some i := hi
      rcases hn with hn | hn | hn
      · simp_all
      · simp [hm, hn]
      · simp [hm, hn]

/--
In a tie, whichever line advanced the time, the next entry of the input's `stepOrder` chooses which of the tied
deadlines fires, as it chooses the internal queue's next step.
-/
theorem chooseDeadline_stepOrder (s : State) (first t : Deadline) (due : List Deadline) (named : StepName)
    (rest : List StepName) (ho : s.stepOrder = named :: rest) (h : due.find? (·.step == named) = some t) :
    chooseDeadline s first due true = .ok (t, { s with stepOrder := rest }) := by
  simp [chooseDeadline, ho, h]

/-- Choosing a deadline changes only the step order entries left. -/
theorem chooseDeadline_orders {s s' : State} {tied : Bool} {first t : Deadline} {due : List Deadline}
    (h : chooseDeadline s first due tied = .ok (t, s')) :
    ∃ o, s' = { s with stepOrder := o } := by
  unfold chooseDeadline at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try obtain ⟨-, rfl⟩ := h)
  all_goals exact ⟨_, rfl⟩

end Tazuna.Thm.Service.Clock
