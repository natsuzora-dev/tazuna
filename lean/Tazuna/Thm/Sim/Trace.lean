import Tazuna.Sim.Trace
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Sim.Trace

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Data.Basic

variable {s : State}

/-- Only lines on one channel are ordered: lines on different channels, or on none, keep no order. -/
theorem ordered_same_channel (lineSteps : Array (Option (Nat × Nat))) (a b : Nat) (la lb : Line)
    (ha : s.lines[a]? = some la) (hb : s.lines[b]? = some lb) (h : ordered s lineSteps a b = true) :
    (channelOf la).isSome ∧ channelOf la = channelOf lb := by
  unfold ordered at h
  rw [ha, hb] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- Two lines of one group of a decide's emits are unordered. -/
theorem group_lines_unordered (lineSteps : Array (Option (Nat × Nat))) (a b sa sb g : Nat)
    (hla : lineSteps[a]? = some (some (sa, g))) (hlb : lineSteps[b]? = some (some (sb, g))) :
    ordered s lineSteps a b = false := by
  unfold ordered
  split
  · rw [hla, hlb]; simp
  · rfl

theorem created_listed_on_first_output (v : String) (i : Nat) :
    v ∈ createdAt s i ↔ v ∈ s.created.map (·.2) ∧ firstOut s v = some i := by
  simp [createdAt, List.mem_filter]

theorem leadsTo_of_lt (i : Nat) : ∀ k, k < i → leadsTo s i k = false := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    rw [leadsTo]
    have h1 : (k == i) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have h2 : decide (i < k) = false := by simp only [decide_eq_false_iff_not, Nat.not_lt]; omega
    simp only [h1, h2, Bool.false_and, Bool.false_or, Bool.and_false]
    split
    · split
      · split
        · rename_i hc
          exact ih _ hc (by omega)
        · rfl
      · rfl
    · rfl

theorem sibling_steps_unordered (c i j : Nat) (ii ij : StepInfo) (hij : i < j) (hi : s.steps[i]? = some ii)
    (hj : s.steps[j]? = some ij) (hcj : ij.cause = some c) (hc : c < i)
    (hbi : ii.barrier = false) (hbj : ij.barrier = false) : leadsTo s i j = false := by
  unfold leadsTo
  have hne : (j == i) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  simp only [hne, hi, hj, hbi, hbj, hcj, Bool.false_or, Bool.false_and, Bool.and_false, Option.any_some]
  have : c < j := by omega
  simp only [this, ↓reduceIte]
  exact leadsTo_of_lt i c hc

end Tazuna.Thm.Sim.Trace
