import Tazuna.Data.Collections

namespace Tazuna.Thm.Data.Collections

open Tazuna.Data

theorem SortKey.lt_irrefl (k : SortKey) : k.lt k = false := by
  cases k <;> simp [SortKey.lt]

theorem sortByKey_keeps_equal_keys (key : String) (k : SortKey) (xs : List Value) :
    (sortByKey key xs).filter (keyOf key · == k) = xs.filter (keyOf key · == k) := by
  have hins : ∀ (c : Value) (l : List Value), (∀ d ∈ l, keyOf key d = k → (keyOf key d).lt (keyOf key c) = false) →
      (insertByKey key c l).filter (keyOf key · == k) = (c :: l).filter (keyOf key · == k) := by
    intro c l
    induction l with
    | nil => intro _; rfl
    | cons d ds ih =>
      intro hl
      simp only [insertByKey]
      split
      · rename_i hlt
        by_cases hd : keyOf key d = k
        · rw [hl d (List.mem_cons_self ..) hd] at hlt
          simp at hlt
        · rw [List.filter_cons_of_neg (by simpa using hd), ih (fun e he => hl e (List.mem_cons_of_mem _ he))]
          simp only [List.filter_cons]
          split <;> simp [hd]
      · rfl
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    simp only [sortByKey]
    by_cases hc : keyOf key c = k
    · rw [hins c _ (fun d _ hd => by rw [hd, ← hc]; exact SortKey.lt_irrefl _)]
      simp only [List.filter_cons, hc, beq_self_eq_true, ↓reduceIte, ih]
    · have : ∀ (l : List Value), (insertByKey key c l).filter (keyOf key · == k) = l.filter (keyOf key · == k) := by
        intro l
        induction l with
        | nil => simp [insertByKey, hc]
        | cons d ds ihl =>
          simp only [insertByKey]
          split
          · simp only [List.filter_cons, ihl]
          · simp [List.filter_cons, hc]
      rw [this, ih, List.filter_cons_of_neg (by simpa using hc)]

theorem bag_or_set_array_sorted (schema item : Value) (xs : List Value)
    (ha : unionOptions schema = none) (hi : schema.field? "items" = some item)
    (hk : schema.field? "x-tazuna-sorted-by" = none)
    (hb : schema.field? "x-tazuna-bag" = some (.bool true) ∨ schema.field? "x-tazuna-set" = some (.bool true)) :
    sortCollections schema (.arr xs) = .arr (sortCanonical (xs.map (sortCollections item))) := by
  rw [sortCollections]
  split
  · rename_i heq; rw [ha] at heq; cases heq
  · simp only [hk]
    rcases hb with hb | hb <;> split <;> simp_all <;> split <;> simp_all

theorem sortCanonical_in_order (xs : List Value) : (sortCanonical xs).Pairwise (·.canonical ≤ ·.canonical) := by
  have trans (a b c : Value) (hab : decide (a.canonical ≤ b.canonical) = true)
      (hbc : decide (b.canonical ≤ c.canonical) = true) : decide (a.canonical ≤ c.canonical) = true := by
    simp only [decide_eq_true_eq] at *; exact String.le_trans hab hbc
  have total (a b : Value) : (decide (a.canonical ≤ b.canonical) || decide (b.canonical ≤ a.canonical)) = true := by
    simpa using String.le_total a.canonical b.canonical
  simpa [sortCanonical] using List.pairwise_mergeSort trans total xs

/-- In an array sorted by a key, the elements with equal keys are in the order of their canonical text. -/
theorem sortByKey_equal_keys_in_canonical_order (key : String) (k : SortKey) (xs : List Value) :
    ((sortByKey key (sortCanonical xs)).filter (keyOf key · == k)).Pairwise (·.canonical ≤ ·.canonical) := by
  rw [sortByKey_keeps_equal_keys]
  exact (sortCanonical_in_order xs).filter _

/--
The canonical texts of the sorted elements of a bag or set do not depend on the order of its elements, so the order
in which spec code builds a bag leaves no trace in the values that tazuna keeps.
-/
theorem sortCanonical_perm {xs ys : List Value} (h : xs.Perm ys) :
    (sortCanonical xs).map Value.canonical = (sortCanonical ys).map Value.canonical := by
  have sorted (zs : List Value) : ((sortCanonical zs).map Value.canonical).Pairwise (· ≤ ·) :=
    List.pairwise_map.mpr (sortCanonical_in_order zs)
  have perm (zs : List Value) : ((sortCanonical zs).map Value.canonical).Perm (zs.map Value.canonical) :=
    (List.mergeSort_perm _ _).map _
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => String.le_antisymm hab hba) (sorted xs) (sorted ys)
    ((perm xs).trans ((h.map _).trans (perm ys).symm))

/--
When no two elements have the same canonical text unless they are equal, the canonical sort of a permutation is the
same list, and so is the sort by a key that follows it: a sortedBy array keeps no trace of the order in which spec code
built it.
-/
theorem sortByKey_perm (key : String) {xs ys : List Value} (h : xs.Perm ys)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, a.canonical = b.canonical → a = b) :
    sortByKey key (sortCanonical xs) = sortByKey key (sortCanonical ys) := by
  have perm (zs : List Value) : (sortCanonical zs).Perm zs := List.mergeSort_perm _ _
  have same : sortCanonical xs = sortCanonical ys := by
    refine List.Perm.eq_of_pairwise (le := fun a b => a.canonical ≤ b.canonical) (fun a b ha hb hab hba => ?_)
      (sortCanonical_in_order xs) (sortCanonical_in_order ys) ((perm xs).trans (h.trans (perm ys).symm))
    exact hc a ((perm xs).mem_iff.mp ha) b (h.mem_iff.mpr ((perm ys).mem_iff.mp hb)) (String.le_antisymm hab hba)
  rw [same]

end Tazuna.Thm.Data.Collections
