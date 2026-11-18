import Tazuna.Service.Chart.Always
import Tazuna.Thm.Service.Chart.Map
import Tazuna.Thm.Service.Chart.Select

namespace Tazuna.Thm.Service.Chart.Always

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Chart.Select Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id}

theorem alwaysRound_fixed (step : Nat) (owner : InstanceId) (next : Instance → List (InstanceId × Transition) → Processing → Id Processing)
    (h : ∀ o c r, (next o c r).1.fixed = r.state.fixed) (r : Processing) :
    (alwaysRound fs st step owner next r).1.fixed = r.state.fixed := by
  have hs := syncCopies_fixed (fs := fs) (st := st) step owner r
  unfold alwaysRound
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · simp only [id_bind]
        split
        · exact hs
        · split
          · exact hs
          · split
            · exact (report_fixed ..).trans hs
            · split
              · exact hs
              · exact (h _ _ _).trans hs

theorem alwaysRound_grows (step : Nat) (owner : InstanceId) (next : Instance → List (InstanceId × Transition) → Processing → Id Processing)
    (h : ∀ o c r, Grows r.state (next o c r).1) (r : Processing) :
    Grows r.state (alwaysRound fs st step owner next r).1 := by
  have hs := syncCopies_grows (fs := fs) (st := st) step owner r
  have hn := congrArg Fixed.now (syncCopies_fixed (fs := fs) (st := st) step owner r)
  unfold alwaysRound
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · split
      · exact Grows.refl _
      · simp only [id_bind]
        split
        · exact hs
        · split
          · exact hs
          · split
            · exact hs.trans hn (Grows.of_lines (report_lines ..))
            · split
              · exact hs
              · exact hs.trans hn (h _ _ _)

theorem settleFrom_fixed (step : Nat) (owner : InstanceId) (roundsLeft : Nat) (r : Processing) :
    (settleFrom fs st step owner roundsLeft r).1.fixed = r.state.fixed := by
  induction roundsLeft generalizing r with
  | zero => rw [settleFrom]; apply alwaysRound_fixed; intro _ _ _; rfl
  | succ n ih =>
    rw [settleFrom]
    refine alwaysRound_fixed (fs := fs) (st := st) step owner _ (fun _ chosen r => ?_) r
    simp only [id_bind]
    split
    · exact ih _
    · rw [ih, keeps_microstep]

theorem settleFrom_grows (step : Nat) (owner : InstanceId) (roundsLeft : Nat) (r : Processing) :
    Grows r.state (settleFrom fs st step owner roundsLeft r).1 := by
  induction roundsLeft generalizing r with
  | zero => rw [settleFrom]; apply alwaysRound_grows; intro _ _ _; exact Grows.of_lines rfl
  | succ n ih =>
    rw [settleFrom]
    refine alwaysRound_grows (fs := fs) (st := st) step owner _ (fun _ chosen r => ?_) r
    simp only [id_bind]
    split
    · exact ih _
    · exact (growsBy_microstep step _ _ _ r).trans ((keeps_microstep step _ _ _).now r) (ih _)

def StableIfOpen (fs : Functions Id) (st : Service) (step : Nat) (owner : InstanceId) (R : Processing) (o : Instance) : Prop :=
  R.state.halted = none → R.state.machine? owner = some o → o.closed = false →
    syncCopies fs st step owner R = (R, false) ∧
      select fs st R.state o .always .none (leavesOf R.state o o.copyIds) = .ok []

theorem alwaysRound_stable (step : Nat) (owner : InstanceId) (o : Instance)
    (next : Instance → List (InstanceId × Transition) → Processing → Id Processing)
    (hnext : ∀ o' c r', StableIfOpen fs st step owner (next o' c r') o) (r : Processing) :
    StableIfOpen fs st step owner (alwaysRound fs st step owner next r) o := by
  intro hh ho hc
  generalize hR : alwaysRound fs st step owner next r = R at hh ho ⊢
  unfold alwaysRound at hR
  split at hR
  · subst hR; simp_all [Processing.halted]
  · split at hR
    · subst hR; simp_all
    · rename_i o₀ ho₀
      split at hR
      · subst hR; simp only [id_pure] at ho; rw [ho₀] at ho; cases ho; simp_all
      · simp only [id_bind] at hR
        split at hR
        · subst hR; simp_all [Processing.halted]
        · split at hR
          · subst hR; simp_all
          · rename_i o₁ ho₁
            split at hR
            · rename_i d reason hsel
              subst hR
              simp [Processing.report, report_halted (.fault _) (select_error_halts _ _ _ _ _ _ hsel)] at hh
            · rename_i chosen ht
              split at hR
              · rename_i he
                subst hR
                simp only [id_pure] at ho ⊢
                rw [ho₁] at ho; cases ho
                simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_eq_eq_not, Bool.not_true] at he
                have hu := syncCopies_unchanged step owner r he.2
                refine ⟨?_, he.1 ▸ ht⟩
                rw [hu]
                exact Prod.ext hu he.2
              · subst hR; exact hnext _ _ _ hh ho hc

theorem settle_result_stable (step : Nat) (owner : InstanceId) (roundsLeft : Nat) (r : Processing) (o : Instance)
    (hh : (settleFrom fs st step owner roundsLeft r).state.halted = none)
    (ho : (settleFrom fs st step owner roundsLeft r).state.machine? owner = some o) (hc : o.closed = false) :
    syncCopies fs st step owner (settleFrom fs st step owner roundsLeft r) = (settleFrom fs st step owner roundsLeft r, false) ∧
      select fs st (settleFrom fs st step owner roundsLeft r).state o .always .none
        (leavesOf (settleFrom fs st step owner roundsLeft r).state o o.copyIds) = .ok [] := by
  revert hh ho hc
  show StableIfOpen fs st step owner _ o
  induction roundsLeft generalizing r with
  | zero =>
    rw [settleFrom]
    exact alwaysRound_stable step owner o _ (fun _ _ _ hh => by simp [Processing.report, State.report, Fault.halts, State.halt] at hh) r
  | succ n ih =>
    rw [settleFrom]
    exact alwaysRound_stable step owner o _ (fun _ c r' => by
      simp only [id_bind]
      split
      · exact ih _
      · exact ih _) r

theorem syncMap_unchanged_any_step (a b : Nat) (owner : InstanceId) (r : Processing) (map : String)
    (h : (syncMap fs st a owner r map).2 = false) : syncMap fs st b owner r map = (r, false) := by
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

theorem foldl_unchanged_any_step {α : Type} (g k : Processing → α → Processing × Bool)
    (hg : ∀ r x, (g r x).2 = false → (g r x).1 = r) (hk : ∀ r x, (g r x).2 = false → k r x = (r, false))
    (xs : List α) (r : Processing)
    (h : (xs.foldl (fun acc x => ((g acc.1 x).1, acc.2 || (g acc.1 x).2)) (r, false)).2 = false) :
    xs.foldl (fun acc x => ((k acc.1 x).1, acc.2 || (k acc.1 x).2)) (r, false) = (r, false) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons] at h ⊢
    have h0 := (foldl_unchanged g hg xs _ h).1
    simp only [Bool.false_or] at h0
    rw [hg r x h0, h0] at h
    rw [hk r x h0]
    exact ih r h

theorem syncCopies_unchanged_any_step (a b : Nat) (owner : InstanceId) (r : Processing)
    (h : (syncCopies fs st a owner r).2 = false) : syncCopies fs st b owner r = (r, false) := by
  unfold syncCopies at h ⊢
  split at h
  · rfl
  · rw [foldlM_id] at h ⊢
    exact foldl_unchanged_any_step (fun r map => syncMap fs st a owner r map) (fun r map => syncMap fs st b owner r map)
      (fun r map => syncMap_unchanged a owner r map) (fun r map => syncMap_unchanged_any_step a b owner r map) _ r h

theorem settleFrom_idem (a b : Nat) (owner : InstanceId) (k k' : Nat) (r : Processing) :
    settleFrom fs st b owner k' (settleFrom fs st a owner k r) = settleFrom fs st a owner k r := by
  generalize hR : settleFrom fs st a owner k r = R
  have key : ∀ next, alwaysRound fs st b owner next R = R := by
    intro next
    unfold alwaysRound
    by_cases hh : R.halted = true
    · simp [hh]
    · cases ho : R.state.machine? owner with
      | none => simp [hh]
      | some o =>
        by_cases hc : o.closed = true
        · simp [hh, hc]
        · have hn : R.state.halted = none := by simpa [Processing.halted] using hh
          have hst := settle_result_stable a owner k r o (hR ▸ hn) (hR ▸ ho) (by simpa using hc)
          rw [hR] at hst
          have hs : syncCopies fs st b owner R = (R, false) :=
            syncCopies_unchanged_any_step a b owner R (by rw [hst.1])
          simp [hh, ho, hc, hs, hst.2]
  cases k' <;> simp only [settleFrom] <;> exact key _

theorem unlessHalted_pure (r : Processing) : unlessHalted (pure : Processing → Id Processing) r = r := by
  unfold unlessHalted; split <;> rfl

theorem always_step_independent (a b : Nat) (owner : InstanceId) (f : Processing → Id Processing) (r : Processing) :
    let H k := settleFrom fs st b owner Limit.alwaysRounds.max
      (unlessHalted f (settleFrom fs st k owner Limit.alwaysRounds.max r))
    settleAround fs st b owner f (settleAround fs st a owner pure r) = H a ∧
      settleAround fs st a owner pure (settleAround fs st b owner f r) = H b := by
  intro H
  simp only [H, settleAround, id_bind, unlessHalted_pure]
  rw [settleFrom_idem, settleFrom_idem, settleFrom_idem, settleFrom_idem]
  exact ⟨rfl, rfl⟩

theorem always_one_per_atomic (s : State) (o : Instance) (chosen : List (InstanceId × Transition))
    (h : select fs st s o .always .none (leavesOf s o o.copyIds) = .ok chosen) :
    ∃ f : InstanceId × Transition → InstanceId × Option String,
      (∀ c ∈ chosen, f c ∈ leavesOf s o o.copyIds ∧ ((f c).2 = none ∨ ∃ n, (f c).2 = some n ∧
        ((f c).1 = o.id ∧ n ∈ o.chart.tree.leaves o.active ∨
          ∃ ci, s.machine? (f c).1 = some ci ∧ n ∈ ci.chart.tree.leaves ci.active))) ∧
      ∀ c₁ ∈ chosen, ∀ c₂ ∈ chosen, f c₁ = f c₂ → c₁ = c₂ := by
  obtain ⟨f, hf, hinj⟩ := Tazuna.Thm.Service.Chart.Select.select_one_per_leaf s o .always .none _ chosen h
  exact ⟨f, fun c hc => ⟨hf c hc,
    Tazuna.Thm.Service.Chart.Select.leavesOf_atomic s o _ (f c) (hf c hc)⟩, hinj⟩

end Tazuna.Thm.Service.Chart.Always
