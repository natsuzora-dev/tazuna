import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

/--
Every binding that compare ends with is one-to-one within each domain: no snapshot value stands for two implementation
values, and no two snapshot values of one domain for one implementation value of it.
-/
theorem compare_oneToOne (snapshot lines : List (Option Line)) (cut : Option Uncomparable) (internal : Line → Bool)
    (renamed : Values → Values) : ∀ b ∈ (compare snapshot lines cut internal renamed).bindings, OneToOne b.pairs :=
  fun b _ => b.pairs_oneToOne

/--
Comparing the groups only adds pairs: every binding of the set that it ends with keeps every pair of `root`.
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
