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

theorem bind_spec {bs bs' : Bindings} {v w : String} (h : bs.bind v w = some bs') :
    bs <+: bs' ∧ bs'.lookup v = some w ∧ (OneToOne bs → OneToOne bs') := by
  unfold Bindings.bind at h
  cases hv : bs.lookup v with
  | some x =>
    rw [hv] at h
    by_cases e : (x == w) = true
    · simp only [e, ite_true, Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at e
      exact ⟨List.prefix_refl _, by rw [hv, e], id⟩
    · simp [e] at h
  | none =>
    rw [hv] at h
    by_cases hw : bs.any (·.2 == w) = true
    · simp [hw] at h
    · simp only [hw, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst h
      have hk := lookup_none hv
      have ht : ∀ q ∈ bs, q.2 ≠ w := by
        intro q hq he
        exact hw (List.any_eq_true.mpr ⟨q, hq, by simp [he]⟩)
      refine ⟨List.prefix_append _ _, ?_, fun ho p hp q hq => ?_⟩
      · rw [lookup_append_none hv]
        simp [List.lookup]
      · rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
        · exact ho p hp q hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨fun e => absurd e (hk p hp), fun e => absurd e (ht p hp)⟩
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨fun e => absurd e.symm (hk q hq), fun e => absurd e.symm (ht q hq)⟩
        · simp only [List.mem_singleton] at hp hq
          subst hp hq
          simp

theorem bindNew_bind {bs bs' : Bindings} {v w : String} (h : bs.bindNew v w = some bs') :
    bs.bind v w = some bs' ∧ bs.lookup v = none := by
  unfold Bindings.bindNew at h
  split at h
  · next hc =>
    cases h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    refine ⟨?_, hc.1⟩
    unfold Bindings.bind
    rw [hc.1]
    simp [hc.2]
  · cases h

end Tazuna.Thm.Data.Trace
