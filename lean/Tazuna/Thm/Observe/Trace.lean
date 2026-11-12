import Tazuna.Observe.Trace
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Observe.Trace

open Tazuna.Data Tazuna.Semantics Tazuna.Observe
open Tazuna.Thm.Data.Basic

variable {s : State}

theorem unrelated_steps_unordered (lineSteps : Array (Option Nat)) (messages : List (Option Time)) (a b sa sb : Nat)
    (ia ib : StepInfo) (hla : lineSteps[a]? = some (some sa)) (hlb : lineSteps[b]? = some (some sb))
    (hia : s.steps[sa]? = some ia) (hib : s.steps[sb]? = some ib)
    (hscope : raceScopeOf messages ia.message = raceScopeOf messages ib.message) (hreach : leadsTo s sa sb = false) :
    ordered s lineSteps messages a b = false := by
  unfold ordered
  rw [hla, hlb]
  split
  · simp only [Option.some.injEq] at *
    rename_i hsa hsb
    subst hsa hsb
    rw [hia, hib]
    simp [hscope, hreach]
  · rfl

theorem barrier_follows_earlier (a b : Nat) (ia ib : StepInfo) (ha : s.steps[a]? = some ia) (hb : s.steps[b]? = some ib)
    (hbar : ib.barrier = true) (hlt : a < b) (hm : ia.message = ib.message) : leadsTo s a b = true := by
  unfold leadsTo; simp [ha, hb, hbar, hlt, hm]

theorem barrier_precedes_later (a b : Nat) (ia ib : StepInfo) (ha : s.steps[a]? = some ia) (hb : s.steps[b]? = some ib)
    (hbar : ia.barrier = true) (hlt : a < b) (hm : ia.message = ib.message) : leadsTo s a b = true := by
  unfold leadsTo; simp [ha, hb, hbar, hlt, hm]

theorem first_output_containing (v : String) (i : Nat) (h : firstOut s v = some i) :
    ∃ l, s.lines[i]? = some l ∧ l.dir = .out ∧ v ∈ bodyStrings l.body ∧
      ∀ j < i, ∀ l', s.lines[j]? = some l' → l'.dir = .out → v ∉ bodyStrings l'.body := by
  unfold firstOut at h
  obtain ⟨⟨l, i'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hl, hp, hb⟩ := find?_zipIdx _ _ _ _ hf
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  refine ⟨l, by simpa using hl, hp.1, hp.2, fun j hj l' hl' hd hv => ?_⟩
  have := hb j hj l' (by simpa using hl')
  simp [hd, hv] at this

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

theorem mem_after (lineSteps : Array (Option Nat)) (messages : List (Option Time)) (i : Nat) (line : Line)
    (hl : s.lines[i]? = some line) (hd : line.dir = .out) (id : String) :
    id ∈ after s lineSteps messages i ↔
      ∃ a l, a ∈ window s i ∧ a < i ∧ s.lines[a]? = some l ∧ l.id = id ∧
        (ordered s lineSteps messages a i = true ∨ l.time ≠ line.time) := by
  unfold after
  simp only [hl, hd, beq_iff_eq, reduceCtorEq, ↓reduceIte, List.mem_filterMap, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq, Bool.or_eq_true, Option.map_eq_some_iff, ne_eq, exists_and_left]
  constructor
  · rintro ⟨a, ⟨hw, hi, ho⟩, l, hla, rfl⟩
    rw [hla] at ho
    exact ⟨a, hw, hi, l, hla, rfl, by simpa using ho⟩
  · rintro ⟨a, hw, hi, l, hla, rfl, ho⟩
    exact ⟨a, ⟨hw, hi, by rw [hla]; simpa using ho⟩, l, hla, rfl⟩

end Tazuna.Thm.Observe.Trace
