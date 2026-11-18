import Tazuna.Service.Chart.Deadline
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Chart.Deadline

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem addDeadlines_fixed (name : InstanceId) (n : String) (ds : List (String × DeadlineTime)) :
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

theorem addDeadlines_lines (name : InstanceId) (n : String) (ds : List (String × DeadlineTime)) :
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

theorem takeDeadline_fixed (t : Deadline) : (s.takeDeadline t).1.fixed = s.fixed := rfl

end Tazuna.Thm.Service.Chart.Deadline
