import Tazuna.Service.Chart.Deadline
import Tazuna.Thm.Service.State

namespace Tazuna.Thm.Service.Chart.Deadline

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem addDeadlines_fixed (step : Nat) (name : InstanceId) (n : String) (ds : List Spec.Deadline) :
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
        · generalize (expectFound _ _ : Id Int) = ms
          show State.fixed (if (s.now + Id.run ms).inRange = true then _ else _) = _
          split <;> simp [report_eq, State.fixed]
        · generalize fs.deadlineAt _ _ _ = r
          rcases r with e | (_ | t)
          · simp [report_eq, State.fixed]
          · simp [report_eq, State.fixed]
          · show State.fixed (match instantTime? t with | some _ => _ | none => _) = _
            split <;> simp [report_eq, State.fixed]

theorem addDeadlines_lines (step : Nat) (name : InstanceId) (n : String) (ds : List Spec.Deadline) :
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
        · generalize (expectFound _ _ : Id Int) = ms
          show State.lines (if (s.now + Id.run ms).inRange = true then _ else _) = _
          split <;> simp
        · generalize fs.deadlineAt _ _ _ = r
          rcases r with e | (_ | t)
          · simp
          · simp
          · show State.lines (match instantTime? t with | some _ => _ | none => _) = _
            split <;> simp

theorem takeDeadline_fixed (t : Deadline) : (s.takeDeadline t).1.fixed = s.fixed := rfl

end Tazuna.Thm.Service.Chart.Deadline
