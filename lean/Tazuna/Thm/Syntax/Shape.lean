import Tazuna.Data.Value
import Tazuna.Syntax.Shape

namespace Tazuna.Thm.Syntax.Shape

open Tazuna.Data Tazuna.Syntax

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

theorem preorder_nodup (stack seen : List String) (l : List Shape) (h : preorder stack seen l = true)
    (hs : seen.Nodup) : (seen ++ l.map (·.name)).Nodup := by
  induction l generalizing stack seen with
  | nil => simpa using hs
  | cons y ys ih =>
    simp only [preorder, Bool.and_eq_true] at h
    obtain ⟨⟨_, hn⟩, hrest⟩ := h
    have hn' : y.name ∉ seen := by simpa using hn
    have := ih y.path (seen ++ [y.name]) hrest
      (List.nodup_append.mpr ⟨hs, by simp, by simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact hn' ha⟩)
    simpa using this

def shapeOf (name : String) (path : List String) (kind : StateKind) (children : List String) : Shape :=
  { name, path, parent := path.dropLast.getLast?, initial := children.head?, children, kind, targets := [] }

theorem preorder_rejects_interleaved_regions : preorder [] []
    [shapeOf "p" ["p"] .parallel ["left", "right"], shapeOf "left" ["p", "left"] .compound ["l1"],
     shapeOf "right" ["p", "right"] .compound ["r1"], shapeOf "l1" ["p", "left", "l1"] .atomic [],
     shapeOf "r1" ["p", "right", "r1"] .atomic []] = false := by decide

theorem preorder_accepts_document_order : preorder [] []
    [shapeOf "p" ["p"] .parallel ["left", "right"], shapeOf "left" ["p", "left"] .compound ["l1"],
     shapeOf "l1" ["p", "left", "l1"] .atomic [], shapeOf "right" ["p", "right"] .compound ["r1"],
     shapeOf "r1" ["p", "right", "r1"] .atomic []] = true := by decide

theorem stateTree_rejects_copy_target_outside : stateTree
    [shapeOf "m" ["m"] .map ["c"], { shapeOf "c" ["m", "c"] .atomic [] with targets := ["x"] },
     shapeOf "x" ["x"] .atomic []] = false := by decide

theorem stateTree_rejects_final_in_map : stateTree
    [shapeOf "m" ["m"] .map ["c", "f"], shapeOf "c" ["m", "c"] .atomic [], shapeOf "f" ["m", "f"] .final []] = false := by
  decide

theorem chartTree_rejects_initial_outside_root : chartTree
    [shapeOf "a" ["a"] .compound ["b"], shapeOf "b" ["a", "b"] .atomic []] "b" [] = false := by decide

theorem chartTree_accepts_initial_at_root : chartTree
    [shapeOf "a" ["a"] .compound ["b"], shapeOf "b" ["a", "b"] .atomic []] "a" [] = true := by decide

theorem chartTree_rejects_reserved_character : chartTree [shapeOf "a@b" ["a@b"] .atomic []] "a@b" [] = false ∧
    chartTree [shapeOf "a[b" ["a[b"] .atomic []] "a[b" [] = false := by decide

theorem stateTree_accepts_copy_target_inside : stateTree
    [shapeOf "m" ["m"] .map ["c", "d"], { shapeOf "c" ["m", "c"] .atomic [] with targets := ["d"] },
     shapeOf "d" ["m", "d"] .atomic []] = true := by decide

end Tazuna.Thm.Syntax.Shape
