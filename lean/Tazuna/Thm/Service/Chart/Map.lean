import Tazuna.Service.Chart.Map
import Tazuna.Thm.Service.Chart.Microstep
import Tazuna.Thm.Service.Note

namespace Tazuna.Thm.Service.Chart.Map

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Data.List Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Note Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_startCopy (step : Nat) (owner : InstanceId) (map : String) (key : Value) (k : Value) :
    Keeps (startCopy fs st step owner map key k) := by
  unfold startCopy
  apply keeps_withMachine
  intro o r
  simp only [id_bind, note_id, id_pure]
  split
  · exact keeps_enter _ _ _ _
  · rfl

theorem exitLeftCopy_fixed (owner : InstanceId) (map : String) (itemKeys : List Value) (r : Processing) (k : Value) :
    (exitLeftCopy fs st owner map itemKeys r k).1.fixed = r.state.fixed := by
  unfold exitLeftCopy
  split
  · rfl
  · exact keeps_unlessHalted (keeps_endWith (fun c n => keeps_exitOne Limit.exitDepth.max c n) _) _

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
            exact (foldl_fixed' _ (fun (r : Processing) (k : Value × Value) =>
              keeps_unlessHalted (keeps_startCopy (fs := fs) (st := st) step owner map k.1 k.2) r) _ _).trans
              (foldl_fixed' _ (exitLeftCopy_fixed _ _ _) _ _)

theorem syncCopies_fixed (step : Nat) (owner : InstanceId) (r : Processing) :
    (syncCopies fs st step owner r).1.1.fixed = r.state.fixed := by
  unfold syncCopies
  split
  · rfl
  · rw [foldlM_id]
    exact foldl_pair_keeps (fun acc map => ((syncMap fs st step owner acc.1 map).1, acc.2 || (syncMap fs st step owner acc.1 map).2))
      (fun acc map => syncMap_fixed step owner acc.1 map) _ _

theorem syncMap_unchanged (step : Nat) (owner : InstanceId) (r : Processing) (map : String)
    (h : (syncMap fs st step owner r map).2 = false) : (syncMap fs st step owner r map).1 = r := by
  by_cases hr : r.halted = true
  · simp [syncMap, hr]
  · cases ho : r.state.machine? owner with
    | none => simp [syncMap, hr, ho]
    | some o =>
      cases hi : fs.items (r.state.scopeOf o (some map)) r.state.records with
      | error v => simp [syncMap, hr, ho, hi] at h
      | ok keys =>
        cases hd : firstDuplicate (·.2) (sortItemKeys keys) with
        | some k => simp [syncMap, hr, ho, hi, hd] at h
        | none =>
        by_cases he : o.copyKeysOf map = (sortItemKeys keys).map (·.2)
        · simp [syncMap, hr, ho, hi, hd, he]
        · simp [syncMap, hr, ho, hi, hd, he] at h

theorem foldl_unchanged {α : Type} (g : Processing → α → Processing × Bool) (hg : ∀ r x, (g r x).2 = false → (g r x).1 = r)
    (xs : List α) (acc : Processing × Bool)
    (h : (xs.foldl (fun acc x => ((g acc.1 x).1, acc.2 || (g acc.1 x).2)) acc).2 = false) :
    acc.2 = false ∧ (xs.foldl (fun acc x => ((g acc.1 x).1, acc.2 || (g acc.1 x).2)) acc).1 = acc.1 := by
  induction xs generalizing acc with
  | nil => exact ⟨h, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2⟩ := ih _ h
    simp only [Bool.or_eq_false_iff] at h1
    rw [h2, hg _ _ h1.2]
    exact ⟨h1.1, rfl⟩

theorem syncCopies_unchanged (step : Nat) (owner : InstanceId) (r : Processing)
    (h : (syncCopies fs st step owner r).2 = false) : (syncCopies fs st step owner r).1 = r := by
  unfold syncCopies at h ⊢
  split at h
  · rfl
  · rw [foldlM_id] at h ⊢
    exact (foldl_unchanged (fun r map => syncMap fs st step owner r map) (fun r map => syncMap_unchanged step owner r map)
      _ (r, false) h).2

theorem growsBy_startCopy (step : Nat) (owner : InstanceId) (map : String) (key : Value) (k : Value) :
    GrowsBy (startCopy fs st step owner map key k) := by
  unfold startCopy
  apply growsBy_withMachine
  intro o r
  simp only [id_bind, note_id, id_pure]
  split
  · exact (growsBy_enter _ _ _ _).bridge (by rfl) (by rfl)
  · exact Grows.of_lines rfl

theorem exitLeftCopy_grows (owner : InstanceId) (map : String) (itemKeys : List Value) (r : Processing) (k : Value) :
    Grows r.state (exitLeftCopy fs st owner map itemKeys r k).1 := by
  unfold exitLeftCopy
  split
  · exact Grows.refl _
  · exact growsBy_unlessHalted (growsBy_endWith (fun c n => growsBy_exitOne Limit.exitDepth.max c n)
      (fun c n => keeps_exitOne Limit.exitDepth.max c n) _) r

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
              _ _).trans ?_ ((foldl_run_grows _ (fun (r : Processing) (k : Value × Value) =>
                growsBy_unlessHalted (growsBy_startCopy (fs := fs) (st := st) step owner map k.1 k.2) r)
                (fun (r : Processing) (k : Value × Value) => congrArg Fixed.now
                  (keeps_unlessHalted (keeps_startCopy (fs := fs) (st := st) step owner map k.1 k.2) r)) _ _).bridge
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

end Tazuna.Thm.Service.Chart.Map
