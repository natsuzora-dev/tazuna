import Tazuna.Data.Trace

namespace Tazuna.Thm.Data.Trace

open Tazuna.Data

theorem untilMalformed_append_malformed {α : Type} (pre post : List (FileLine α)) :
    untilMalformed (pre ++ .malformed :: post) = untilMalformed (pre ++ [.malformed]) := by
  induction pre with
  | nil => rfl
  | cons l pre ih => cases l <;> simp only [List.cons_append, untilMalformed, ih]

theorem untilMalformed_line {α : Type} (lines : List (FileLine α)) {n : Nat}
    (h : (untilMalformed lines).2 = some n) : n = (untilMalformed lines).1.length + 1 := by
  induction lines generalizing n with
  | nil => simp [untilMalformed] at h
  | cons l ls ih =>
    cases l with
    | malformed => simp only [untilMalformed, Option.some.injEq, List.length_nil] at h ⊢; omega
    | blank | line =>
      simp only [untilMalformed, Prod.map, Option.map_eq_some_iff] at h ⊢
      obtain ⟨m, hm, rfl⟩ := h
      simp [ih hm]

end Tazuna.Thm.Data.Trace
