import Tazuna.Ir.Structure

namespace Tazuna.Thm.Ir.Structure

open Tazuna.Ir

theorem resultOfMismatch_eq_none_iff (s : Structure) (target : Ref) (answers : List Answer) (event : Ref) :
    s.resultOfMismatch target answers event = none ↔ answers.all (· matches .accepted _) = true ∧
      ∃ d ∈ s.definitions.find? (·.ref == target), match d.body with
        | .command c => event ∈ c.emits
        | _ => False := by
  unfold Structure.resultOfMismatch
  cases h : s.definitions.find? (·.ref == target) with
  | none => simp
  | some d =>
    cases hb : d.body <;> cases answers.all (· matches .accepted _) <;> simp [hb]

theorem resultOfMismatch_unaccepted (s : Structure) (target event : Ref) (answers : List Answer)
    (h : ∃ a ∈ answers, ¬ a matches .accepted _) : s.resultOfMismatch target answers event ≠ none := by
  rw [Ne, resultOfMismatch_eq_none_iff]
  obtain ⟨a, ha, hn⟩ := h
  simp only [List.all_eq_true, not_and]
  exact fun hall => absurd (hall a ha) (by simpa using hn)

theorem emitsOf_mem (s : Structure) (command r : Ref) (h : r ∈ s.emitsOf command) :
    ∃ d ∈ s.definitions, d.ref = command ∧ match d.body with
      | .command c => r ∈ c.emits
      | _ => False := by
  unfold Structure.emitsOf at h
  cases hf : s.definitions.find? (·.ref == command) with
  | none => simp [hf] at h
  | some d =>
    refine ⟨d, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, ?_⟩
    cases hb : d.body <;> simp [hf, hb] at h ⊢; exact h

end Tazuna.Thm.Ir.Structure
