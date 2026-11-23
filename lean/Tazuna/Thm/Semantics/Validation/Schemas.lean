import Tazuna.Semantics.Validation.Schemas

namespace Tazuna.Thm.Semantics.Validation.Schemas

open Tazuna.Ir Tazuna.Semantics.Validation Tazuna.Semantics.Validation.Schemas

/--
check's schema rules report nothing exactly when no schema of any definition has either issue at any path and no map
state's key declares a default.
-/
theorem schemas_ordered (s : Structure) : Schemas.check s = [] ↔
    (∀ d ∈ s.definitions, ∀ x ∈ schemasOf d, ∀ path key, (path, .unorderedSortKey key) ∉ issues x.1 x.2) ∧
    (∀ d ∈ s.definitions, ∀ x ∈ schemasOf d, ∀ path, (path, .ambiguousUnion) ∉ issues x.1 x.2) ∧
    (∀ d ∈ s.definitions, ∀ x ∈ mapKeysOf d, defaultPaths x.1 x.2 = []) := by
  simp only [Schemas.check, List.flatMap_eq_nil_iff, List.append_eq_nil_iff, List.map_eq_nil_iff]
  constructor
  · intro h
    exact ⟨fun d hd x hx path key hm => by simp [(h d hd).1 x hx] at hm,
      fun d hd x hx path hm => by simp [(h d hd).1 x hx] at hm,
      fun d hd x hx => (h d hd).2 x hx⟩
  · intro ⟨h1, h2, h3⟩ d hd
    refine ⟨fun x hx => ?_, h3 d hd⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro ⟨path, i⟩ hm
    cases i with
    | unorderedSortKey key => exact h1 d hd x hx path key hm
    | ambiguousUnion => exact h2 d hd x hx path hm

end Tazuna.Thm.Semantics.Validation.Schemas
