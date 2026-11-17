import Tazuna.Service.Clock
import Tazuna.Thm.Service.Chart.Macrostep

namespace Tazuna.Thm.Service.Clock

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Service.Chart.Basic

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

theorem growsBy_fire (step : Nat) (t : Deadline) : GrowsBy (fire fs st step t) := by
  intro r
  unfold fire
  simp only [Tazuna.Thm.Service.Note.note_id, id_bind]
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

/-- Without a tie, the earliest deadline in entry order fires. -/
theorem chooseDeadline_untied (s : State) (clock : Bool) (first : Deadline) (due : List Deadline) :
    chooseDeadline st s clock first due false = .ok (first, s) := rfl

/-- In a tie during a clock line with no `order` entry left, the tie is reported instead of decided. -/
theorem chooseDeadline_required (s : State) (first : Deadline) (due : List Deadline) (h : s.deadlineOrder = []) :
    chooseDeadline st s true first due true = .error (.unorderedDeadlines (due.map Deadline.id)) := by
  simp [chooseDeadline, h]

/-- In a tie during a clock line, the next entry of the line's `order` chooses which of the tied deadlines fires. -/
theorem chooseDeadline_named (s : State) (first t : Deadline) (due : List Deadline) (c : DeadlineId)
    (rest : List DeadlineId) (ho : s.deadlineOrder = c :: rest) (h : due.find? (·.id == c) = some t) :
    chooseDeadline st s true first due true = .ok (t, { s with deadlineOrder := rest }) := by
  simp [chooseDeadline, ho, h]

/--
In a tie of any other processing, the next entry of the input's `stepOrder` chooses which of the tied deadlines fires,
as it chooses the internal queue's next step.
-/
theorem chooseDeadline_stepOrder (s : State) (first t : Deadline) (due : List Deadline) (named : StepName)
    (rest : List StepName) (ho : s.stepOrder = named :: rest) (h : due.find? (s.deadlineStep st · == named) = some t) :
    chooseDeadline st s false first due true = .ok (t, { s with stepOrder := rest }) := by
  simp [chooseDeadline, ho, h]

/-- Choosing a deadline changes only the order entries left. -/
theorem chooseDeadline_orders {s s' : State} {clock tied : Bool} {first t : Deadline} {due : List Deadline}
    (h : chooseDeadline st s clock first due tied = .ok (t, s')) :
    ∃ d o, s' = { s with deadlineOrder := d, stepOrder := o } := by
  unfold chooseDeadline at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try obtain ⟨-, rfl⟩ := h)
  all_goals exact ⟨_, _, rfl⟩

end Tazuna.Thm.Service.Clock
