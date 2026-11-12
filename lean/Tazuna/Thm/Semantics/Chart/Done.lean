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

theorem finished_awaits_in_order (step : Nat) (name parent : String) (r : Processing) (i : Instance)
    (waiting : List String) (hi : r.state.machine? name = some i) (hw : i.awaitingOnDone = some waiting) :
    enterFinal step name parent r =
      ⟨r.state.setMachine name fun i' => { i' with awaitingOnDone := some (waiting ++ i.chart.tree.finished i.active parent) },
       r.queue⟩ := by
  simp [enterFinal, hi, hw]

theorem first_finished_queues_onDone (step : Nat) (name parent : String) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) (hw : i.awaitingOnDone = none) :
    enterFinal step name parent r =
      ⟨r.state.setMachine name fun i' => { i' with awaitingOnDone := some (i.chart.tree.finished i.active parent) },
       { r.queue with tasks := r.queue.tasks ++ [.onDone name step] }⟩ := by
  simp [enterFinal, hi, hw]

theorem closeFinal_output_then_ends (st : Service) (step : Nat) (name : String) (r : Processing) (i : Instance)
    (hh : r.state.halted = none) (hi : r.state.machine? name = some i) (output : Value) (failed : Option String)
    (hc : fs.close (r.state.scopeOf i none) r.state.records = .ok (output, failed)) :
    closeFinal fs st step name r =
      let ended := endWith (exitOne fs st Limit.exitDepth.max) name
        ⟨r.state.reportAll (failed.toList.map (st.failedEnsures i.chart.name)), r.queue⟩
      if ended.halted then ended else
      match i.opener with
      | some o =>
        let (s, serial) := ended.state.startQueued o.parent o.state
        ⟨s, { ended.queue with tasks := ended.queue.tasks ++ [.opensDone o.parent o.state o.key output serial step] }⟩
      | none => ended := by
  simp only [closeFinal, withMachine, Processing.halted, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hi, hc,
    id_bind]
  rfl

end Tazuna.Thm.Semantics.Chart.Done
