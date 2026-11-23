import Tazuna.Semantics.Service.Chart.Done
import Tazuna.Thm.Semantics.Service.Chart.Exit

namespace Tazuna.Thm.Semantics.Service.Chart.Done

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic

variable {fs : Functions Id}

theorem enterFinal_fixed (step : Nat) (name : InstanceId) (parent : String) (r : Processing) :
    (enterFinal step name parent r).1.fixed = r.state.fixed := by
  unfold enterFinal
  repeat' split
  all_goals rfl

theorem keeps_closeFinal (st : Service) (step : Nat) (name : InstanceId) : Keeps (closeFinal fs st step name) := by
  unfold closeFinal
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  have hc := keeps_endWith (fun c n => keeps_exitOne (st := st) (fs := fs) st.exitFuel c n) name
  repeat' split
  all_goals first | exact (hc _).trans (reportAll_fixed (s := r.state) _) | simp [Processing.report]

theorem enterFinal_lines (step : Nat) (name : InstanceId) (parent : String) (r : Processing) : (enterFinal step name parent r).1.lines = r.state.lines := by
  unfold enterFinal
  repeat' split
  all_goals rfl

theorem growsBy_closeFinal (st : Service) (step : Nat) (name : InstanceId) : GrowsBy (closeFinal fs st step name) := by
  unfold closeFinal
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  have hc := growsBy_endWith (fun c n => growsBy_exitOne (st := st) (fs := fs) st.exitFuel c n)
    (fun c n => keeps_exitOne (st := st) st.exitFuel c n) name
  repeat' split
  all_goals first
    | exact Grows.of_lines (report_lines ..)
    | exact (hc _).bridge (reportAll_lines (s := r.state) _) (reportAll_now (s := r.state) _)

end Tazuna.Thm.Semantics.Service.Chart.Done
