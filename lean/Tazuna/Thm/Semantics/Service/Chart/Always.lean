import Tazuna.Semantics.Service.Chart.Always
import Tazuna.Thm.Semantics.Service.Chart.Map
import Tazuna.Thm.Semantics.Service.Chart.Select
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Service.Chart.Always

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.Chart.Deadline Tazuna.Thm.Semantics.Service.Chart.Done Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Map Tazuna.Thm.Semantics.Service.Chart.Microstep Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.Chart.Request Tazuna.Thm.Semantics.Service.Chart.Select Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic

variable {st : Service} {fs : Functions Id}

theorem alwaysRound_fixed (step : Nat) (owner : InstanceId) (next : Instance → List (InstanceId × Service.Transition) → Processing → Id Processing)
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

theorem alwaysRound_grows (step : Nat) (owner : InstanceId) (next : Instance → List (InstanceId × Service.Transition) → Processing → Id Processing)
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

/--
A settle whose always transitions still select a transition, or change the copies, after Limit.alwaysRounds rounds
halts with exceededAlwaysRounds.
-/
@[guarantee] theorem always_rounds_limit_halts (step : Nat) (owner : InstanceId) (r r' : Processing) (o o' : Instance)
    (changed : Bool) (chosen : List (InstanceId × Service.Transition)) (hr : r.halted = false)
    (ho : r.state.machine? owner = some o) (hc : o.closed = false)
    (hs : syncCopies fs st step owner r = (r', changed)) (hr' : r'.halted = false)
    (ho' : r'.state.machine? owner = some o')
    (hsel : select fs st r'.state o' .always .none (leavesOf r'.state o' o'.copyIds) = .ok chosen)
    (hn : chosen.isEmpty = false ∨ changed = true) :
    (settleFrom fs st step owner 0 r).state.halted =
      some (.fault (.exceededAlwaysRounds (st.ref o'.chart.name) Limit.alwaysRounds.max)) := by
  have hn' : (chosen.isEmpty && !changed) = false := by cases hn <;> simp [*]
  simp only [settleFrom, alwaysRound, hr, ho, hc, Bool.false_eq_true, ite_false, id_bind]
  rw [hs]
  simp only [hr', ho', Bool.false_eq_true, ite_false, hsel, hn', Processing.report]
  exact report_halted _ rfl

end Tazuna.Thm.Semantics.Service.Chart.Always
