import Tazuna.Data.Pairing

namespace Tazuna.Thm.Data.Pairing

open Tazuna.Data

theorem mem_names (es : List Entry) (n : String) : n ∈ names es ↔ ∃ e ∈ es, fileName e = some n := by
  simp [names, List.mem_filterMap]

theorem unknown_nil (ex : List String) (es : List Entry) :
    (pair ex es).unknown = [] ↔ ∀ e ∈ es, (fileName e).isSome := by
  simp [pair, List.filter_eq_nil_iff, Option.isSome_iff_ne_none]

theorem extra_nil (ex : List String) (es : List Entry) :
    (pair ex es).extra = [] ↔ ∀ e ∈ es, ∀ n, fileName e = some n → n ∈ ex := by
  simp only [pair, List.filter_eq_nil_iff, mem_names, decide_eq_true_eq, Classical.not_not]
  constructor
  · intro h e he n hn; exact h n ⟨e, he, hn⟩
  · rintro h n ⟨e, he, hn⟩; exact h e he n hn

theorem missing_nil (ex : List String) (es : List Entry) :
    (pair ex es).missing = [] ↔ ∀ n ∈ ex, ∃ e ∈ es, fileName e = some n := by
  simp only [pair, List.filter_eq_nil_iff, mem_names, decide_eq_true_eq, Classical.not_not]

theorem pair_complete_iff (ex : List String) (es : List Entry) :
    (pair ex es).missing = [] ∧ (pair ex es).extra = [] ∧ (pair ex es).unknown = [] ↔
      (∀ e ∈ es, ∃ n ∈ ex, fileName e = some n) ∧ (∀ n ∈ ex, ∃ e ∈ es, fileName e = some n) := by
  rw [missing_nil, extra_nil, unknown_nil]
  constructor
  · rintro ⟨hm, hx, hu⟩
    refine ⟨fun e he => ?_, hm⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hu e he)
    exact ⟨n, hx e he n hn, hn⟩
  · rintro ⟨he, hm⟩
    refine ⟨hm, fun e h n hn => ?_, fun e h => ?_⟩
    · obtain ⟨n', hn', he'⟩ := he e h
      rw [hn] at he'; cases he'; exact hn'
    · obtain ⟨n, _, hn⟩ := he e h
      simp [hn]

end Tazuna.Thm.Data.Pairing
