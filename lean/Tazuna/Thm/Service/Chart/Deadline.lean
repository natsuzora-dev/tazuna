import Tazuna.Service.Chart.Deadline
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Chart.Deadline

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem addDeadlines_fixed (name n : String) (ds : List (String × DeadlineTime)) :
    (addDeadlines name n ds s).fixed = s.fixed := by
  unfold addDeadlines
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih => exact ih

theorem rearm_fixed : (rearm st fs s).fixed = s.fixed := by
  unfold rearm
  rw [foldlM_id]
  generalize s.deadlines = ts
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rfl
    · split
      · rfl
      · simp only [id_bind]
        split
        · simp [report_eq, State.fixed]
        · rfl

theorem addDeadlines_lines (name n : String) (ds : List (String × DeadlineTime)) :
    (addDeadlines name n ds s).lines = s.lines := by
  unfold addDeadlines
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih => exact ih

theorem rearm_lines : (rearm st fs s).lines = s.lines := by
  unfold rearm
  rw [foldlM_id]
  generalize s.deadlines = ts
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split
    · rfl
    · split
      · rfl
      · simp only [id_bind]
        split
        · simp
        · rfl

theorem addDeadlines_now (name n : String) (ds : List (String × DeadlineTime)) (s : State) :
    (addDeadlines name n ds s).now = s.now := by
  unfold addDeadlines
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih => exact ih _

theorem mem_addDeadlines_of_mem (name n : String) (ds : List (String × DeadlineTime)) (s : State) (t : Deadline)
    (ht : t ∈ s.deadlines) : t ∈ (addDeadlines name n ds s).deadlines := by
  unfold addDeadlines
  induction ds generalizing s with
  | nil => exact ht
  | cons d ds ih => exact ih _ (List.mem_append_left _ ht)

theorem entry_restarts_deadline (name n : String) (ds : List (String × DeadlineTime)) (s : State) (d : String)
    (delay : Time) (hd : (d, .delay delay) ∈ ds) :
    ∃ t ∈ (addDeadlines name n ds s).deadlines,
      t.machine = name ∧ t.state = n ∧ t.name = d ∧ t.time = some (s.now + delay) := by
  induction ds generalizing s with
  | nil => cases hd
  | cons e ds ih =>
    rcases List.mem_cons.mp hd with rfl | hd
    · refine ⟨{ time := some (s.now + delay), fromAt := false, order := s.deadlineCount + 1, machine := name,
                state := n, name := d }, ?_, rfl, rfl, rfl, rfl⟩
      show _ ∈ (addDeadlines name n ds _).deadlines
      exact mem_addDeadlines_of_mem name n ds _ _ (List.mem_append_right _ (List.mem_singleton_self _))
    · obtain ⟨t, ht, h⟩ := ih _ hd
      exact ⟨t, ht, by simpa [addDeadlines_now] using h⟩

theorem delay_counts_from_entry (name n : String) (ds : List (String × DeadlineTime)) (d : String) (delay : Time)
    (hd : (d, .delay delay) ∈ ds) :
    ∃ t ∈ (addDeadlines name n ds s).deadlines,
      t.machine = name ∧ t.state = n ∧ t.name = d ∧ t.time = some (s.now + delay) :=
  entry_restarts_deadline name n ds s d delay hd

theorem takeDeadline_fixed (t : Deadline) : (s.takeDeadline t).1.fixed = s.fixed := rfl

theorem takeDeadline_lines (t : Deadline) : (s.takeDeadline t).1.lines = s.lines := rfl

end Tazuna.Thm.Service.Chart.Deadline
