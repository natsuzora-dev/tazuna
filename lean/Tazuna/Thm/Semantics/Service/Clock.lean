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
  simp only [Tazuna.Thm.Semantics.Service.Note.note_id, id_bind]
  split
  · rfl
  · refine (keeps_withMachine (fun i r => ?_) _).trans (takeDeadline_fixed t)
    split
    · rfl
    · exact keeps_applyCompletion _ _ _ _ r

theorem growsBy_fire (step : Nat) (t : Service.Deadline) : GrowsBy (fire fs st step t) := by
  intro r
  unfold fire
  simp only [Tazuna.Thm.Semantics.Service.Note.note_id, id_bind]
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
  simp only [Tazuna.Thm.Semantics.Service.Note.note_id, id_bind]
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
@[guarantee] theorem chooseDeadline_stepOrder (s : Service.State) (first t : Service.Deadline) (due : List Service.Deadline) (named : StepName)
    (rest : List StepName) (ho : s.stepOrder = named :: rest) (h : due.find? (·.step == named) = some t) :
    chooseDeadline s first due true = .ok (t, { s with stepOrder := rest }) := by
  have hn : named.isArrival = false := by
    have := List.find?_some h
    simp only [beq_iff_eq] at this
    rw [← this]
    rfl
  simp [chooseDeadline, ho, h, hn]

/-- Choosing a deadline changes only the step order entries left. -/
theorem chooseDeadline_orders {s s' : Service.State} {tied : Bool} {first t : Service.Deadline} {due : List Service.Deadline}
    (h : chooseDeadline s first due tied = .ok (t, s')) :
    ∃ o, s' = { s with stepOrder := o } := by
  unfold chooseDeadline at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try obtain ⟨-, rfl⟩ := h)
  all_goals exact ⟨_, rfl⟩

end Tazuna.Thm.Semantics.Service.Clock
