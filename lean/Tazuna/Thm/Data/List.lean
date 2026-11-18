import Tazuna.Data.List

namespace Tazuna.Thm.Data.List

open Tazuna.Data

theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] {c : List (α × β)} (hc : (c.map Prod.fst).Nodup) {t : α}
    {u : β} (h : (t, u) ∈ c) : c.lookup t = some u := by
  induction c with
  | nil => cases h
  | cons p c ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hc
    rcases List.mem_cons.mp h with he | hm
    · cases he; simp
    · have hne : (t == a) = false := by
        simp only [beq_eq_false_iff_ne]
        intro e; subst e; exact hc.1 ⟨(t, u), hm, rfl⟩
      rw [List.lookup_cons, hne]; exact ih hc.2 hm

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {c : List (α × β)} {t : α} {u : β} (h : c.lookup t = some u) :
    (t, u) ∈ c := by
  induction c with
  | nil => simp at h
  | cons p c ih =>
    obtain ⟨a, b⟩ := p
    rw [List.lookup_cons] at h
    split at h
    · rename_i he; cases h; have := beq_iff_eq.mp he; subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem mem_addName_self {α : Type} [DecidableEq α] (acc : List α) (n : α) : n ∈ addName acc n := by
  unfold addName
  split
  · assumption
  · simp

theorem mem_addName_of_mem {α : Type} [DecidableEq α] {acc : List α} {x : α} (n : α) (h : x ∈ acc) : x ∈ addName acc n := by
  unfold addName
  split
  · exact h
  · exact List.mem_append_left _ h

end Tazuna.Thm.Data.List
