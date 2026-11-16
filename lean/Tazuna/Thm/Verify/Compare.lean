import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

/-- No value of the binding stands for two values, in either direction. -/
def OneToOne (b : Bindings) : Prop := ∀ u ∈ b, ∀ v ∈ b, (u.1 = v.1 ↔ u.2 = v.2)

theorem lookup_none {b : Bindings} {s : String} (h : b.lookup s = none) : ∀ v ∈ b, v.1 ≠ s := by
  induction b with
  | nil => simp
  | cons p rest ih =>
    intro v hv e
    by_cases ps : s = p.1
    · simp [List.lookup, ps] at h
    · have hr : rest.lookup s = none := by
        have : (s == p.1) = false := by simp [ps]
        simpa [List.lookup, this] using h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ps e.symm
      · exact ih hr v hv e

/-- Binding a string keeps the binding one-to-one, so a snapshot value stands for one implementation value. -/
theorem bindString_oneToOne {fresh : List String} {b b' : Bindings} {s t : String} (h : OneToOne b)
    (hb : bindString fresh b s t = some b') : OneToOne b' := by
  unfold bindString at hb
  cases hs : b.lookup s with
  | some bound =>
    rw [hs] at hb
    by_cases e : (bound == t) = true
    · simp only [e, ite_true, Option.some.injEq] at hb; subst hb; exact h
    · simp [e] at hb
  | none =>
    rw [hs] at hb
    by_cases hf : fresh.contains s = true
    · by_cases ht : b.any (·.2 == t) = true
      · simp [ht] at hb; simp at hf; exact absurd hf hb.1
      · simp only [hf, ht, Bool.false_eq_true, ite_true, ite_false, Option.some.injEq] at hb
        subst hb
        have ns := lookup_none hs
        have nt : ∀ v ∈ b, v.2 ≠ t := by
          intro v hv e
          simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at ht
          exact ht v hv e
        intro x hx y hy
        simp only [List.mem_append, List.mem_singleton] at hx hy
        rcases hx with hx | rfl <;> rcases hy with hy | rfl
        · exact h x hx y hy
        · exact ⟨fun e => absurd e (ns x hx), fun e => absurd e (nt x hx)⟩
        · exact ⟨fun e => absurd e.symm (ns y hy), fun e => absurd e.symm (nt y hy)⟩
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · by_cases e : (s == t) = true
      · simp only [hf, e, Bool.false_eq_true, ite_true, ite_false, Option.some.injEq] at hb; subst hb; exact h
      · simp [e] at hb; simp at hf; exact absurd hb.1 hf

end Tazuna.Thm.Verify.Compare
