import Tazuna.Data.Pairing

namespace Tazuna.Thm.Data.Pairing

open Tazuna.Data

theorem mem_names (es : List Entry) (n : String) : n ∈ names es ↔ ∃ e ∈ es, fileName e = some n := by
  simp [names, List.mem_filterMap]

variable {α : Type} (name : α → String)

theorem unknown_nil (ex : List α) (es : List Entry) :
    (pair name ex es).unknown = [] ↔ ∀ e ∈ es, (fileName e).isSome := by
  simp [pair, List.filter_eq_nil_iff, Option.isSome_iff_ne_none]

theorem extra_nil (ex : List α) (es : List Entry) :
    (pair name ex es).extra = [] ↔ ∀ e ∈ es, ∀ n, fileName e = some n → n ∈ ex.map name := by
  simp only [pair, List.filter_eq_nil_iff, mem_names, decide_eq_true_eq, Classical.not_not]
  constructor
  · intro h e he n hn; exact h n ⟨e, he, hn⟩
  · rintro h n ⟨e, he, hn⟩; exact h e he n hn

theorem missing_nil (ex : List α) (es : List Entry) :
    (pair name ex es).missing = [] ↔ ∀ x ∈ ex, ∃ e ∈ es, fileName e = some (name x) := by
  simp only [pair, List.filter_eq_nil_iff, mem_names, decide_eq_true_eq, Classical.not_not]

end Tazuna.Thm.Data.Pairing
