import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

theorem resolveIn_binds {s t : String} :
    ∀ {slots slots' : List Slot}, resolveIn s t slots = some slots' → ∃ k ∈ slots', s ∈ k.1 ∧ k.1.length = 1 ∧ t ∈ k.2
  | [], _, hr => by simp [resolveIn] at hr
  | k :: ks, slots', hr => by
    unfold resolveIn at hr
    by_cases hk : s ∈ k.1
    · by_cases ht : t ∈ k.2
      · by_cases h1 : k.1.length = 1
        · simp only [hk, ht, h1, ite_true, Option.some.injEq] at hr
          subst hr
          exact ⟨k, List.mem_cons_self .., hk, h1, ht⟩
        · simp only [hk, ht, h1, ite_true, ite_false, Option.some.injEq] at hr
          subst hr
          exact ⟨([s], [t]), List.mem_cons_self .., List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩
      · simp [hk, ht] at hr
    · simp only [hk, ite_false, Option.map_eq_some_iff] at hr
      obtain ⟨rest, hr, rfl⟩ := hr
      obtain ⟨k', hk', h⟩ := resolveIn_binds hr
      exact ⟨k', List.mem_cons_of_mem _ hk', h⟩

/-- A string that compares equal enters the binding as a bound pair, and what the binding bound before stays. -/
theorem bindString_binds {fresh : List String} {b : Binding} {s t : String} {b' : { b' : Binding // b.Extends b' }}
    (h : b.bindString fresh s t = some b') :
    b.Extends b'.val ∧ ∃ k ∈ b'.val.slots, s ∈ k.1 ∧ k.1.length = 1 ∧ t ∈ k.2 := by
  refine ⟨b'.property, ?_⟩
  unfold Binding.bindString at h
  split at h
  · split at h
    · rename_i slots' hr
      simp only [Option.some.injEq] at h
      subst h
      exact resolveIn_binds hr
    · simp at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨([s], [t]), List.mem_append_right _ (List.mem_singleton_self _), List.mem_singleton_self _, rfl,
          List.mem_singleton_self _⟩
      · simp at h
    · simp at h

/--
The binding that compare ends with is one-to-one: no snapshot string stands for two implementation strings, and no two
snapshot strings for one implementation string.
-/
theorem compare_oneToOne (snapshot lines : List (Option Line)) (malformed : Option Nat) (internal : Line → Bool) :
    OneToOne (compare snapshot lines malformed internal).bindings :=
  (compare snapshot lines malformed internal).binding.pairs_oneToOne

/--
Comparing the groups only refines the binding: the binding that it ends with keeps every pair that any step bound, so
every pair of strings that compared equal anywhere in the comparison is in that one one-to-one binding.
-/
theorem compareGroups_extends (lineCount : Nat) (internal : Line → Bool) (expected actual : List Group) (cut : Bool)
    (fuel : Nat) (fresh : List String) (b : Binding) :
    b.Extends (compareGroups lineCount internal expected actual cut fuel fresh b).2.val :=
  (compareGroups lineCount internal expected actual cut fuel fresh b).2.property

end Tazuna.Thm.Verify.Compare
