import Tazuna.Service.Chart.Deadline
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Chart.Deadline

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem addDeadlines_fixed (step : Nat) (name : InstanceId) (n : String) (ds : List (String × DeadlineTime)) :
    (addDeadlines st fs step name n ds s).fixed = s.fixed := by
  unfold addDeadlines
  split
  · rfl
  · rw [foldlM_id]
    clear ‹_ = some _›
    induction ds generalizing s with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [ih]
      split
      · rfl
      · split
        · simp [State.fixed]
        · generalize fs.deadlineAt _ _ _ = r
          rcases r with e | t <;> simp [Functor.map, report_eq, State.fixed]

theorem addDeadlines_lines (step : Nat) (name : InstanceId) (n : String) (ds : List (String × DeadlineTime)) :
    (addDeadlines st fs step name n ds s).lines = s.lines := by
  unfold addDeadlines
  split
  · rfl
  · rw [foldlM_id]
    clear ‹_ = some _›
    induction ds generalizing s with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [ih]
      split
      · rfl
      · split
        · simp
        · generalize fs.deadlineAt _ _ _ = r
          rcases r with e | t <;> simp [Functor.map]

theorem takeDeadline_fixed (t : Deadline) : (s.takeDeadline t).1.fixed = s.fixed := rfl

end Tazuna.Thm.Service.Chart.Deadline
