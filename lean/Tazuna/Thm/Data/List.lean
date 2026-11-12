import Tazuna.Data.List

namespace Tazuna.Thm.Data.List

open Tazuna.Data

theorem mem_addName_self (acc : List String) (n : String) : n ∈ addName acc n := by
  unfold addName
  split
  · assumption
  · simp

theorem mem_addName_of_mem {acc : List String} {x : String} (n : String) (h : x ∈ acc) : x ∈ addName acc n := by
  unfold addName
  split
  · exact h
  · exact List.mem_append_left _ h

theorem mem_addName {acc : List String} {x n : String} (h : x ∈ addName acc n) : x ∈ acc ∨ x = n := by
  unfold addName at h
  split at h
  · exact Or.inl h
  · simpa using h

theorem not_mem_path_foldl (entered : List String) (n : String) (hn : n ∈ entered) (path : List String)
    (acc : List String) (ha : n ∉ acc) :
    n ∉ path.foldl (fun acc m => if m ∈ entered then acc else addName acc m) acc := by
  induction path generalizing acc with
  | nil => exact ha
  | cons m path ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact ha
    · rename_i hm
      intro h
      rcases mem_addName h with h | h
      · exact ha h
      · subst h; exact hm hn

theorem firstDuplicateFrom_eq_none_iff {α : Type} (key : α → String) : ∀ (seen : List String) (l : List α),
    firstDuplicateFrom key seen l = none ↔ (l.map key).Nodup ∧ ∀ x ∈ l, key x ∉ seen
  | seen, [] => by simp [firstDuplicateFrom]
  | seen, x :: xs => by
    rw [firstDuplicateFrom]
    by_cases hx : key x ∈ seen
    · simp only [hx, ↓reduceIte]
      constructor
      · intro h; cases h
      · rintro ⟨-, hs⟩; exact absurd hx (hs x List.mem_cons_self)
    · simp only [hx, ↓reduceIte]
      rw [firstDuplicateFrom_eq_none_iff key (key x :: seen) xs, List.map_cons, List.nodup_cons]
      constructor
      · rintro ⟨hn, hs⟩
        refine ⟨⟨fun h => ?_, hn⟩, fun y hy => ?_⟩
        · obtain ⟨y, hy, he⟩ := List.mem_map.mp h
          exact hs y hy (by rw [he]; exact List.mem_cons_self)
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact fun h => hs y hy (List.mem_cons_of_mem _ h)
      · rintro ⟨⟨hxs, hn⟩, hs⟩
        refine ⟨hn, fun y hy h => ?_⟩
        rcases List.mem_cons.mp h with h | h
        · exact hxs (by rw [← h]; exact List.mem_map_of_mem hy)
        · exact hs y (List.mem_cons_of_mem _ hy) h

theorem firstDuplicate_eq_none_iff {α : Type} (key : α → String) (l : List α) :
    firstDuplicate key l = none ↔ (l.map key).Nodup := by
  simp [firstDuplicate, firstDuplicateFrom_eq_none_iff]

theorem mem_foldl_addNew {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (l acc : List α) (x : α), x ∈ l.foldl addNew acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc, x => by simp
  | y :: ys, acc, x => by
    rw [List.foldl_cons, mem_foldl_addNew ys _ x]
    unfold addNew
    by_cases hy : y ∈ acc
    · simp only [List.contains_iff_mem.mpr hy, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hy
        · exact Or.inr h
    · have hn : acc.contains y = false := by simpa [List.contains_iff_mem] using hy
      simp only [hn, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ((h | rfl) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr h

end Tazuna.Thm.Data.List
