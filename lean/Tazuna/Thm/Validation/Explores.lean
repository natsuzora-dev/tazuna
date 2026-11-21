import Tazuna.Thm.Spec.Domains
import Tazuna.Validation.Explores

namespace Tazuna.Thm.Validation.Explores

open Tazuna.Data Tazuna.Spec Tazuna.Spec.Domains Tazuna.Validation

/-- Explores.check reports nothing exactly when every node of a schema that a move of an explore may carry is declared. -/
theorem domains_declared (s : Structure) : Explores.check s = [] ↔ ∀ x ∈ s.explores, ∀ schema json,
    (schema, json) ∈ moveSchemas s x.service → ∃ t, rootTree (declared x.domains schema) json = .ok t := by
  simp only [Explores.check, Explores.undeclared, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]
  constructor
  · intro h x hx schema json hs
    have := h x hx (schema, json) hs
    revert this
    cases hr : rootTree (declared x.domains schema) json with
    | ok t => intro; exact ⟨t, rfl⟩
    | error paths => intro hp; exact absurd hp (Thm.Spec.Domains.treeOf_error _ _ _ _ _ hr)
  · intro h x hx ⟨schema, json⟩ hs
    obtain ⟨t, ht⟩ := h x hx schema json hs
    simp [ht, Except.undeclared]

end Tazuna.Thm.Validation.Explores
