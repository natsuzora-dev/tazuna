import Tazuna.Validation.Contracts

namespace Tazuna.Thm.Validation.Contracts

open Tazuna.Data Tazuna.Spec Tazuna.Validation

theorem members_of_own_service (s : Structure) :
    Contracts.check s = [] ↔ ∀ c ∈ s.contracts, ∀ key m, (key, some m) ∈ c.members → m.service = c.service := by
  simp only [Contracts.check, List.flatMap_eq_nil_iff]
  constructor
  · intro h c hc key m hm
    have := List.filterMap_eq_nil_iff.mp (h c hc) (key, some m) hm
    exact Classical.byContradiction fun hne => by simp [hne] at this
  · intro h c hc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨key, m⟩ hm => ?_
    cases m with
    | none => rfl
    | some m => simp [h c hc key m hm]

end Tazuna.Thm.Validation.Contracts
