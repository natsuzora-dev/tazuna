import Tazuna.Validation.Explores

namespace Tazuna.Thm.Validation.Explores

open Tazuna.Data Tazuna.Spec Tazuna.Spec.Domains Tazuna.Validation

/-- Explores.check reports nothing exactly when every node that a move of an explore may carry has a domain. -/
theorem domains_declared (s : Structure) : Explores.check s = [] ↔ ∀ x ∈ s.explores, ∀ schema ∈ moveSchemas s x.service,
    ∀ t, schemaTree? s x schema = some t → t.undeclaredPaths = [] := by
  simp only [Explores.check, Explores.undeclared, List.flatMap_eq_nil_iff]
  constructor
  · intro h x hx schema hs t ht
    have := h x hx schema hs
    simpa [ht] using this
  · intro h x hx schema hs
    split
    · rename_i t ht
      simp [h x hx schema hs t ht]
    · rfl

end Tazuna.Thm.Validation.Explores
