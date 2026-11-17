import Tazuna.Data.Value
import Tazuna.Spec.Shape

namespace Tazuna.Thm.Spec.Shape

open Tazuna.Data Tazuna.Spec

theorem preorder_split (stack seen : List String) (l : List Shape) (h : preorder stack seen l = true)
    (hs : ∀ a ∈ stack, a ∈ seen) :
    ∀ x ∈ l, ∃ A B, seen ++ l.map (·.name) = A ++ x.name :: B ∧ ∀ a ∈ x.path.dropLast, a ∈ A := by
  induction l generalizing stack seen with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
    simp only [preorder, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hpath, hpre⟩, _⟩, hrest⟩ := h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · refine ⟨seen, ys.map (·.name), by simp, fun a ha => hs a ?_⟩
      exact (List.isPrefixOf_iff_prefix.mp hpre).subset ha
    · have hs' : ∀ a ∈ x.path, a ∈ seen ++ [x.name] → True := fun _ _ _ => trivial
      obtain ⟨A, B, hAB, hA⟩ := ih y.path (seen ++ [y.name]) hrest (fun a ha => by
        rw [hpath] at ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (hs a ((List.isPrefixOf_iff_prefix.mp hpre).subset ha))
        · exact List.mem_append_right _ ha) x hx
      exact ⟨A, B, by simpa using hAB, hA⟩

end Tazuna.Thm.Spec.Shape
