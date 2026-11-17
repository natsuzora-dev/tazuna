import Tazuna.Spec.Structure

namespace Tazuna.Thm.Spec.Structure

open Tazuna.Data Tazuna.Spec

theorem resultOfMismatch_eq_none_iff (s : Structure) (target : Ref) (accepted : Bool) (event : Ref) :
    s.resultOfMismatch target accepted event = none ↔ accepted = true ∧
      ∃ d ∈ s.definitions.find? (·.ref == target), match d.body with
        | .command _ _ _ emits .. => some event ∈ emits
        | _ => False := by
  unfold Structure.resultOfMismatch
  cases h : s.definitions.find? (·.ref == target) with
  | none => simp
  | some d =>
    cases hb : d.body <;> cases accepted <;> simp [hb]

theorem resultOfMismatch_unaccepted (s : Structure) (target event : Ref) :
    s.resultOfMismatch target false event ≠ none := by
  rw [Ne, resultOfMismatch_eq_none_iff]
  simp

theorem emitsOf_mem (s : Structure) (command : Option Ref) (r : Ref) (h : some r ∈ s.emitsOf command) :
    ∃ d ∈ s.definitions, sameRef (some d.ref) command = true ∧ match d.body with
      | .command _ _ _ emits .. => some r ∈ emits
      | _ => False := by
  unfold Structure.emitsOf at h
  generalize hf : s.definitions.findSome? _ = found at h
  cases found with
  | none => simp at h
  | some es =>
    rw [Option.getD_some] at h
    obtain ⟨d, hd, hs⟩ := List.exists_of_findSome?_eq_some hf
    refine ⟨d, hd, ?_⟩
    cases hb : d.body <;> simp only [hb] at hs <;> try contradiction
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨by assumption, h⟩
    · contradiction

/-- A request to the own service is rejected with no kind but those its definition allows or declares. -/
theorem rejectionKinds_own (s : Structure) (r : Ref) (k : RejectionKind) (hk : k ∈ s.rejectionKinds r.service r) :
    k = .notFound ∨ k = .requires ∨ k = .alreadyExists ∨
      ∃ d ∈ s.definitions.find? (·.ref == r), match d.body with
        | .command (some kinds) .. | .query (some kinds) .. => k ∈ kinds
        | _ => False := by
  unfold Structure.rejectionKinds at hk
  cases h : s.definitions.find? (·.ref == r) with
  | none => simp [h] at hk
  | some d =>
    simp only [h, Option.map_some] at hk
    cases hb : d.body <;> simp only [hb, List.not_mem_nil] at hk
    case command rejects _ _ _ _ _ _ =>
      cases rejects
      · simp_all; grind
      · simp_all
    case query rejects _ _ _ =>
      cases rejects <;> simp_all

end Tazuna.Thm.Spec.Structure
