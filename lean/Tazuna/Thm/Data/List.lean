import Tazuna.Data.List

namespace Tazuna.Thm.Data.List

open Tazuna.Data

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
