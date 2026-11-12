import Tazuna.Data.Collections

namespace Tazuna.Thm.Data.Collections

open Tazuna.Data

def InKeyOrder (key : String) : List Value → Prop
  | a :: b :: rest => (keyOf key b).lt (keyOf key a) = false ∧ InKeyOrder key (b :: rest)
  | _ => True

theorem SortKey.lt_irrefl (k : SortKey) : k.lt k = false := by
  cases k <;> simp [SortKey.lt]

theorem SortKey.lt_asymm {a b : SortKey} (h : a.lt b = true) : b.lt a = false := by
  cases a <;> cases b <;> simp only [SortKey.lt, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢ <;>
    exact Int.lt_asymm h

theorem insertByKey_head (key : String) (c d : Value) (ds : List Value) :
    (insertByKey key c (d :: ds)).head? = some c ∨ (insertByKey key c (d :: ds)).head? = some d := by
  simp only [insertByKey]
  split <;> simp

theorem insertByKey_in_order (key : String) (c : Value) (l : List Value) (h : InKeyOrder key l) :
    InKeyOrder key (insertByKey key c l) := by
  induction l with
  | nil => trivial
  | cons d ds ih =>
    simp only [insertByKey]
    split
    · rename_i hlt
      cases ds with
      | nil =>
        simp only [insertByKey, InKeyOrder]
        exact ⟨SortKey.lt_asymm hlt, trivial⟩
      | cons e es =>
        have hde : (keyOf key e).lt (keyOf key d) = false := h.1
        have ih' := ih h.2
        rcases insertByKey_head key c e es with hh | hh
        · revert ih'
          cases hi : insertByKey key c (e :: es) with
          | nil => simp only [insertByKey] at hi; split at hi <;> simp at hi
          | cons x xs =>
            intro ih'
            simp only [hi, List.head?_cons, Option.some.injEq] at hh
            subst hh
            exact ⟨SortKey.lt_asymm hlt, ih'⟩
        · revert ih'
          cases hi : insertByKey key c (e :: es) with
          | nil => simp only [insertByKey] at hi; split at hi <;> simp at hi
          | cons x xs =>
            intro ih'
            simp only [hi, List.head?_cons, Option.some.injEq] at hh
            subst hh
            exact ⟨hde, ih'⟩
    · rename_i hlt
      exact ⟨by simpa using hlt, h⟩

theorem sortByKey_in_order (key : String) (xs : List Value) : InKeyOrder key (sortByKey key xs) := by
  induction xs with
  | nil => trivial
  | cons c cs ih => exact insertByKey_in_order key c _ ih

theorem insertByKey_perm (key : String) (c : Value) (l : List Value) : (insertByKey key c l).Perm (c :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons d ds ih =>
    simp only [insertByKey]
    split
    · exact ((ih.cons d).trans (List.Perm.swap c d ds))
    · exact List.Perm.refl _

theorem sortByKey_perm (key : String) (xs : List Value) : (sortByKey key xs).Perm xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons c cs ih => exact (insertByKey_perm key c _).trans (ih.cons c)

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

theorem sorted_by_array_sorted (schema item : Value) (xs : List Value) (key : String)
    (ha : schema.field? "anyOf" = none) (hi : schema.field? "items" = some item)
    (hk : schema.field? "x-tazuna-sorted-by" = some (.str key)) :
    sortCollections schema (.arr xs) = .arr (sortByKey key (xs.map (sortCollections item))) := by
  rw [sortCollections]
  split
  · rename_i heq; rw [ha] at heq; cases heq
  · simp only [hk]
    split
    · rename_i item' hi' _
      rw [hi] at hi'
      cases Option.mem_def.mp hi'
      rfl
    · rename_i heq
      simp [hi] at heq

end Tazuna.Thm.Data.Collections
