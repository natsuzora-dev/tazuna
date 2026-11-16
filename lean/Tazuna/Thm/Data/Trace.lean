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

/-- No string of the bindings is bound to two strings, and no two strings to one. -/
def OneToOne (bs : Bindings) : Prop := ∀ p ∈ bs, ∀ q ∈ bs, (p.1 = q.1 ↔ p.2 = q.2)

theorem lookup_append_of {bs rest : Bindings} {v w : String} (h : bs.lookup v = some w) :
    (bs ++ rest).lookup v = some w := by
  induction bs with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.lookup, List.cons_append] at h ⊢
    split at h <;> simp_all

theorem lookup_prefix {bs R : Bindings} (hp : bs <+: R) {v w : String} (h : bs.lookup v = some w) :
    R.lookup v = some w := by
  obtain ⟨rest, rfl⟩ := hp
  exact lookup_append_of h

theorem lookup_none {bs : Bindings} {v : String} (h : bs.lookup v = none) : ∀ q ∈ bs, q.1 ≠ v := by
  induction bs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.lookup] at h
    split at h
    · cases h
    · rename_i hne
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · intro he
        simp [he] at hne
      · exact ih h q hq

theorem lookup_append_none {bs rest : Bindings} {v : String} (h : bs.lookup v = none) :
    (bs ++ rest).lookup v = rest.lookup v := by
  induction bs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.lookup, List.cons_append] at h ⊢
    split at h <;> simp_all

end Tazuna.Thm.Data.Trace
