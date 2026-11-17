import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

/--
A value that compares equal enters the binding as a pair, unless it is a string of domain "" that equals its counterpart
and is not fresh, and what the binding held before stays.
-/
theorem bindString_binds {fresh : Bool} {b : Binding} {s t : Bound} {b' : { b' : Binding // b.Extends b' }}
    (h : b.bindString fresh s t = some b') :
    b.Extends b'.val ∧ ((s, t) ∈ b'.val.pairs ∨ (b'.val = b ∧ s = t ∧ s.1 = "" ∧ fresh = false)) := by
  refine ⟨b'.property, ?_⟩
  unfold Binding.bindString at h
  split at h
  · split at h
    · rename_i hst
      simp only [Option.some.injEq] at h
      subst h
      exact .inl hst
    · simp at h
  · split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hs
      exact .inr ⟨rfl, hs.1.2, hs.2, hs.1.1⟩
    · split at h
      · simp at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact .inl (List.mem_append_right _ (List.mem_singleton_self _))
        · simp at h

/--
Every binding that compare ends with is one-to-one within each domain: no snapshot value stands for two implementation
values, and no two snapshot values of one domain for one implementation value of it.
-/
theorem compare_oneToOne (snapshot lines : List (Option Line)) (cut : Option Uncomparable) (internal : Line → Bool)
    (renamed : Values → Values) : ∀ b ∈ (compare snapshot lines cut internal renamed).bindings, OneToOne b.pairs :=
  fun b _ => b.pairs_oneToOne

/--
Comparing the groups only adds pairs: every binding of the set that it ends with keeps every pair of `root`, and, step by
step, every pair that a compared line bound on its way (bindString_binds), so it agrees with every line that it
compared equal.
-/
theorem compareGroups_extends (lineCount : Nat) (internal : Line → Bool) (inputs : List Line) (outs : List Numbered)
    (expected actual : List Group) (cut : Bool) {root : Binding} (fuel : Nat) (v : Values) (set : List (From root)) :
    ∀ b ∈ (compareGroups lineCount internal inputs outs expected actual cut fuel v set).2, root.Extends b.val :=
  fun b _ => b.property

/-- A restart ends every subscription, so no answer after it is dropped as a repeat of an answer before it. -/
theorem restart_ends_subscriptions (l : Line) (id : String) (ls : List (Option Line)) (o : List (String × Option String))
    (h : l.body = .restart .in id) :
    withoutRepeatedAnswers.go (some l :: ls) o = some l :: withoutRepeatedAnswers.go ls [] := by
  simp [withoutRepeatedAnswers.go, h]

end Tazuna.Thm.Verify.Compare
