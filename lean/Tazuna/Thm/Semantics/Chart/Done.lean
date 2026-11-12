import Tazuna.Semantics.Chart.Done
import Tazuna.Thm.Semantics.Chart.Exit

namespace Tazuna.Thm.Semantics.Chart.Done

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.Chart.Exit Tazuna.Thm.Semantics.Chart.Queue Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {fs : Functions Id}

theorem enterFinal_fixed (step : Nat) (name parent : String) (r : Processing) :
    (enterFinal step name parent r).1.fixed = r.state.fixed := by
  unfold enterFinal
  repeat' split
  all_goals rfl

theorem keeps_closeFinal (st : Service) (step : Nat) (name : String) : Keeps (closeFinal fs st step name) := by
  unfold closeFinal
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  have hc := keeps_endWith (fun c n => keeps_exitOne (st := st) (fs := fs) Limit.exitDepth.max c n) name
  split
  · simp [Processing.report]
  · repeat' split
    all_goals exact (hc _).trans (reportAll_fixed (s := r.state) _)

theorem enterFinal_lines (step : Nat) (name parent : String) (r : Processing) : (enterFinal step name parent r).1.lines = r.state.lines := by
  unfold enterFinal
  repeat' split
  all_goals rfl

theorem growsBy_closeFinal (st : Service) (step : Nat) (name : String) : GrowsBy (closeFinal fs st step name) := by
  unfold closeFinal
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  have hc := growsBy_endWith (fun c n => growsBy_exitOne (st := st) (fs := fs) Limit.exitDepth.max c n)
    (fun c n => keeps_exitOne (st := st) Limit.exitDepth.max c n) name
  split
  · exact Grows.of_lines (report_lines ..)
  · repeat' split
    all_goals exact (hc _).bridge (reportAll_lines (s := r.state) _) (reportAll_now (s := r.state) _)

end Tazuna.Thm.Semantics.Chart.Done
