import Tazuna.Semantics.Service.Chart.Map
import Tazuna.Thm.Semantics.Service.Chart.Microstep
import Tazuna.Thm.Semantics.Service.Note

namespace Tazuna.Thm.Semantics.Service.Chart.Map

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Ir.List Tazuna.Thm.Semantics.Service.Functions Tazuna.Thm.Semantics.Service.Note Tazuna.Thm.Semantics.Service.Chart.Deadline Tazuna.Thm.Semantics.Service.Chart.Done Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Microstep Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.Chart.Request Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : Service.State}

theorem keeps_startCopy (step : Nat) (owner : InstanceId) (map : String) (key : Value) :
    Keeps (startCopy fs st step owner map key) := by
  unfold startCopy
  apply keeps_withMachine
  intro o r
  simp only [id_bind, id_pure]
  split
  · exact keeps_enter _ _ _ _
  · rfl

theorem exitLeftCopy_fixed (owner : InstanceId) (map : String) (itemKeys : List Value) (r : Processing) (k : Value) :
    (exitLeftCopy fs st owner map itemKeys r k).1.fixed = r.state.fixed := by
  unfold exitLeftCopy
  split
  · rfl
  · exact keeps_unlessHalted (keeps_endWith (fun c n => keeps_exitOne st.exitFuel c n) _) _

theorem syncMap_fixed (step : Nat) (owner : InstanceId) (r : Processing) (map : String) :
    (syncMap fs st step owner r map).1.1.fixed = r.state.fixed := by
  unfold syncMap
  simp only [id_bind]
  split
  · rfl
  · split
    · rfl
    · split
      · simp [Processing.report]
      · split
        · rfl
        · split
          · rfl
          · rw [foldlM_id, foldlM_id]
            exact (foldl_fixed' _ (fun (r : Processing) (k : Value) =>
              keeps_unlessHalted (keeps_startCopy (fs := fs) (st := st) step owner map k) r) _ _).trans
              (foldl_fixed' _ (exitLeftCopy_fixed _ _ _) _ _)

theorem syncCopies_fixed (step : Nat) (owner : InstanceId) (r : Processing) :
    (syncCopies fs st step owner r).1.1.fixed = r.state.fixed := by
  unfold syncCopies
  split
  · rfl
  · rw [foldlM_id]
    exact foldl_pair_keeps (fun acc map => ((syncMap fs st step owner acc.1 map).1, acc.2 || (syncMap fs st step owner acc.1 map).2))
      (fun acc map => syncMap_fixed step owner acc.1 map) _ _

theorem growsBy_startCopy (step : Nat) (owner : InstanceId) (map : String) (key : Value) :
    GrowsBy (startCopy fs st step owner map key) := by
  unfold startCopy
  apply growsBy_withMachine
  intro o r
  simp only [id_bind, id_pure]
  split
  · exact (growsBy_enter _ _ _ _).bridge (by rfl) (by rfl)
  · exact Grows.of_lines rfl

theorem exitLeftCopy_grows (owner : InstanceId) (map : String) (itemKeys : List Value) (r : Processing) (k : Value) :
    Grows r.state (exitLeftCopy fs st owner map itemKeys r k).1 := by
  unfold exitLeftCopy
  split
  · exact Grows.refl _
  · exact growsBy_unlessHalted (growsBy_endWith (fun c n => growsBy_exitOne st.exitFuel c n)
      (fun c n => keeps_exitOne st.exitFuel c n) _) r

theorem syncMap_grows (step : Nat) (owner : InstanceId) (r : Processing) (map : String) :
    Grows r.state (syncMap fs st step owner r map).1.1 := by
  unfold syncMap
  simp only [id_bind]
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · split
      · exact Grows.of_lines (by simp [Processing.report])
      · split
        · exact Grows.of_lines rfl
        · split
          · exact Grows.refl _
          · rw [foldlM_id, foldlM_id]
            refine (foldl_run_grows _ (exitLeftCopy_grows _ _ _) (fun r c => congrArg Fixed.now (exitLeftCopy_fixed _ _ _ r c))
              _ _).trans ?_ ((foldl_run_grows _ (fun (r : Processing) (k : Value) =>
                growsBy_unlessHalted (growsBy_startCopy (fs := fs) (st := st) step owner map k) r)
                (fun (r : Processing) (k : Value) => congrArg Fixed.now
                  (keeps_unlessHalted (keeps_startCopy (fs := fs) (st := st) step owner map k) r)) _ _).bridge
                  (by rfl) (by rfl))
            exact congrArg Fixed.now (foldl_fixed' _ (exitLeftCopy_fixed _ _ _) _ _)

theorem syncCopies_grows (step : Nat) (owner : InstanceId) (r : Processing) :
    Grows r.state (syncCopies fs st step owner r).1.1 := by
  unfold syncCopies
  split
  · exact Grows.refl _
  · rw [foldlM_id]
    generalize (List.filter _ _) = maps
    suffices ∀ (acc : Processing × Bool), Grows acc.1.state (maps.foldl (fun acc map =>
        ((syncMap fs st step owner acc.1 map).1, acc.2 || (syncMap fs st step owner acc.1 map).2)) acc).1.1 from this _
    intro acc
    induction maps generalizing acc with
    | nil => exact Grows.refl _
    | cons x xs ih =>
      exact (syncMap_grows step owner acc.1 x).trans (congrArg Fixed.now (syncMap_fixed step owner acc.1 x)) (ih _)

end Tazuna.Thm.Semantics.Service.Chart.Map
