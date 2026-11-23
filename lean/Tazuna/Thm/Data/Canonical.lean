import Tazuna.Verify.Pairing
import Tazuna.Thm.Data.List
import Tazuna.Data.Binding
import Tazuna.Data.Canonical

namespace Tazuna.Thm.Data.Canonical

open Tazuna.Data Tazuna.Verify

mutual

/-- Whether the second value is the first with the fields of its objects, at any depth, in any order. -/
inductive Reordered : Value → Value → Prop
  | refl (v : Value) : Reordered v v
  | arr {xs ys : List Value} : ReorderedList xs ys → Reordered (.arr xs) (.arr ys)
  | obj {fs gs hs : List (String × Value)} :
      (fs.map (·.1)).Nodup → fs.Perm gs → ReorderedFields gs hs → Reordered (.obj fs) (.obj hs)

inductive ReorderedList : List Value → List Value → Prop
  | nil : ReorderedList [] []
  | cons {x y : Value} {xs ys : List Value} : Reordered x y → ReorderedList xs ys → ReorderedList (x :: xs) (y :: ys)

inductive ReorderedFields : List (String × Value) → List (String × Value) → Prop
  | nil : ReorderedFields [] []
  | cons {k : String} {v w : Value} {fs gs : List (String × Value)} :
      Reordered v w → ReorderedFields fs gs → ReorderedFields ((k, v) :: fs) ((k, w) :: gs)

end

theorem canonicalList_eq : ∀ vs : List Value, canonicalList vs = vs.map Value.canonical
  | [] => by rw [canonicalList]; rfl
  | v :: vs => by rw [canonicalList, canonicalList_eq vs]; rfl

theorem canonicalFields_eq : ∀ fs : List (String × Value), canonicalFields fs = fs.map fun p => (p.1, p.2.canonical)
  | [] => by rw [canonicalFields]; rfl
  | (k, v) :: fs => by rw [canonicalFields, canonicalFields_eq fs]; rfl

theorem objectText_perm {xs ys : List (String × String)} (hn : (xs.map (·.1)).Nodup) (hp : xs.Perm ys) :
    objectText xs = objectText ys := by
  have trans (a b c : String × String) (hab : decide (a.1 ≤ b.1) = true) (hbc : decide (b.1 ≤ c.1) = true) :
      decide (a.1 ≤ c.1) = true := by
    simp only [decide_eq_true_eq] at *; exact String.le_trans hab hbc
  have total (a b : String × String) : (decide (a.1 ≤ b.1) || decide (b.1 ≤ a.1)) = true := by
    simpa using String.le_total a.1 b.1
  unfold objectText
  rw [List.Perm.eq_of_pairwise _ (List.pairwise_mergeSort trans total xs) (List.pairwise_mergeSort trans total ys)
    ((List.mergeSort_perm _ _).trans (hp.trans (List.mergeSort_perm _ _).symm))]
  intro a b ha hb hab hba
  simp only [decide_eq_true_eq] at hab hba
  exact eq_of_map_nodup (f := (·.1)) hn ((List.mergeSort_perm _ _).mem_iff.mp ha)
    (hp.mem_iff.mpr ((List.mergeSort_perm _ _).mem_iff.mp hb)) (String.le_antisymm hab hba)

mutual

theorem Reordered.canonical_eq {v w : Value} : Reordered v w → v.canonical = w.canonical
  | .refl _ => rfl
  | .arr h => by rw [Value.canonical, Value.canonical, h.canonical_eq]
  | .obj hn hp h => by
    rw [Value.canonical, Value.canonical, ← h.canonical_eq]
    refine objectText_perm ?_ ?_
    · rwa [canonicalFields_eq, List.map_map]
    · rw [canonicalFields_eq, canonicalFields_eq]; exact hp.map _

theorem ReorderedList.canonical_eq {xs ys : List Value} : ReorderedList xs ys → canonicalList xs = canonicalList ys
  | .nil => rfl
  | .cons h t => by rw [canonicalList, canonicalList, h.canonical_eq, t.canonical_eq]

theorem ReorderedFields.canonical_eq {fs gs : List (String × Value)} :
    ReorderedFields fs gs → canonicalFields fs = canonicalFields gs
  | .nil => rfl
  | .cons h t => by rw [canonicalFields, canonicalFields, h.canonical_eq, t.canonical_eq]

end

end Tazuna.Thm.Data.Canonical
