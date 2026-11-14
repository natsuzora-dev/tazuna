import Tazuna.Observe.Trace
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Observe.Trace

open Tazuna.Data Tazuna.Semantics Tazuna.Observe
open Tazuna.Thm.Data.Basic

variable {s : State}

theorem unrelated_steps_unordered (lineSteps : Array (Option (Nat × Nat))) (messages : List (Option Time))
    (a b sa sb ga gb : Nat) (ia ib : StepInfo) (hla : lineSteps[a]? = some (some (sa, ga)))
    (hlb : lineSteps[b]? = some (some (sb, gb))) (hia : s.steps[sa]? = some ia) (hib : s.steps[sb]? = some ib)
    (hscope : raceScopeOf messages ia.message = raceScopeOf messages ib.message) (hreach : leadsTo s sa sb = false) :
    ordered s lineSteps messages a b = false := by
  unfold ordered
  rw [hla, hlb]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq] at *
    rename_i hsa hsb
    obtain ⟨rfl, rfl⟩ := hsa
    obtain ⟨rfl, rfl⟩ := hsb
    rw [hia, hib]
    simp [hscope, hreach]
  · rfl

/-- Two lines of one group of a decide's emits are unordered. -/
theorem group_lines_unordered (lineSteps : Array (Option (Nat × Nat))) (messages : List (Option Time))
    (a b sa sb g : Nat) (hla : lineSteps[a]? = some (some (sa, g))) (hlb : lineSteps[b]? = some (some (sb, g))) :
    ordered s lineSteps messages a b = false := by
  unfold ordered
  rw [hla, hlb]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq] at *
    rename_i hsa hsb
    obtain ⟨-, rfl⟩ := hsa
    obtain ⟨-, h⟩ := hsb
    simp [h]
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

end Tazuna.Thm.Observe.Trace
