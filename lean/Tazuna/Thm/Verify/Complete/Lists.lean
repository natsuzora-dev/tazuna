import Tazuna.Verify.Compare

/-! List facts that the completeness proof of the comparison uses. -/

namespace Tazuna.Thm.Verify.Complete.Lists

open Tazuna.Data Tazuna.Verify

/-- A list without duplicates inside another list that is not longer is a permutation of it. -/
theorem perm_of_nodup_subset {α : Type} : ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x ∈ l₁, x ∈ l₂) →
    l₂.length ≤ l₁.length → l₁.Perm l₂
  | [], l₂, _, _, hl => by cases l₂ with
    | nil => exact List.Perm.refl _
    | cons _ _ => simp at hl
  | a :: t, l₂, hn, hs, hl => by
    classical
    have ha : a ∈ l₂ := hs a List.mem_cons_self
    have hn' := List.nodup_cons.mp hn
    have ih : t.Perm (l₂.erase a) := perm_of_nodup_subset hn'.2
      (fun x hx => (List.mem_erase_of_ne (fun e => hn'.1 (by subst e; exact hx))).mpr
        (hs x (List.mem_cons_of_mem _ hx)))
      (by rw [List.length_erase_of_mem ha]; simp at hl; omega)
    exact ((List.perm_cons a).mpr ih).trans (List.perm_cons_erase ha).symm

theorem perm_cons_eraseIdx {α : Type} : ∀ {ys : List α} {i : Nat} {y : α}, ys[i]? = some y →
    ys.Perm (y :: ys.eraseIdx i)
  | [], _, _, h => by simp at h
  | z :: ys, 0, y, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; simp
  | z :: ys, i + 1, y, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.eraseIdx_cons_succ]
    exact ((List.perm_cons z).mpr (perm_cons_eraseIdx h)).trans (List.Perm.swap y z _)

theorem distinct_go_subset {α : Type} (key : α → Value) :
    ∀ (xs : List α) (seen : List Value), ∀ x ∈ distinct.go key xs seen, x ∈ xs
  | [], _, x, h => by simp [distinct.go] at h
  | y :: xs, seen, x, h => by
    simp only [distinct.go] at h
    split at h
    · exact List.mem_cons_of_mem _ (distinct_go_subset key xs seen x h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (distinct_go_subset key xs _ x h)

theorem mem_of_mem_distinct {α : Type} {key : α → Value} {xs : List α} {x : α} (h : x ∈ distinct key xs) : x ∈ xs :=
  distinct_go_subset key xs [] x h

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 a ha rfl, nodup_of_map f h.2⟩

theorem lookup_mem {β : Type} : ∀ {gs : List (String × β)} {k : String} {w : β}, gs.lookup k = some w → (k, w) ∈ gs
  | [], _, _, h => by simp at h
  | (a, b) :: rest, k, w, h => by
    by_cases e : k = a
    · subst e; simp only [List.lookup_cons, beq_self_eq_true] at h; cases h; simp
    · have : (k == a) = false := by simpa using e
      simp only [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- A pairwise relation that is symmetric holds between any two distinct members. -/
theorem pairwise_of_ne {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b
  | [], _, a, ha, _, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, ha, b, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ea | ha' <;> rcases List.mem_cons.mp hb with eb | hb'
    · exact absurd (ea.trans eb.symm) hne
    · subst ea; exact h.1 b hb'
    · subst eb; exact hs _ _ (h.1 a ha')
    · exact pairwise_of_ne hs h.2 a ha' b hb' hne

end Tazuna.Thm.Verify.Complete.Lists
