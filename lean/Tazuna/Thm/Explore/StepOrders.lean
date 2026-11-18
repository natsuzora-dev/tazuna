import Tazuna.Explore.StepOrders
import Tazuna.Thm.Explore.ChoiceDependent
import Tazuna.Thm.Verify.Compare

/-!
The verdict of the step-order search: what a search that reports nothing says of the orders that it ran.
-/

namespace Tazuna.Thm.Explore.StepOrders

open Tazuna.Data Tazuna.Service Tazuna.Explore
open Tazuna.Thm.Verify.Compare (GroupsMatch compare_matches)

theorem untilMalformed_lines (ls : List TraceLine) : untilMalformed (ls.map FileLine.line) = (ls.map some, none) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [untilMalformed, ih]

/--
A comparison of the search that finds no violation pairs every group of the expected lines with the actual group at its
place through one pairing, `after` included (GroupsMatch with `relation`), under every binding that it returns, each one
to one within each domain. The lines are those that verify reads: by the schema of their definitions, and the actual
lines without repeated subscription answers.
-/
theorem compareTraces_ok {spec : Spec.Structure} {service : String}
    {ask : Spec.Definition → Verify.Part → Value → Id CValue} {renamed : Values → Values}
    {expected actual : List TraceLine} {set : List Binding}
    (h : (Verify.compareTraces spec service ask renamed expected actual : Id _) = .ok set) :
    let read := Verify.readLines spec service ask (expected.map some) []
    let e := read.1
    let a := Verify.withoutRepeatedAnswers (Verify.readLines spec service ask (actual.map some) read.2).1
    set ≠ [] ∧ ∀ b ∈ set, OneToOne b.pairs ∧
      GroupsMatch (renamed { domain := Verify.valueDomains e, fresh := [], image := fun _ _ => true }).domain
        (Verify.internalEvent spec service) true b (Verify.groups e) (Verify.groups a) := by
  intro read e a
  rcases hr : Verify.readLines spec service ask (expected.map some) [] with ⟨E, out⟩
  rcases hr' : Verify.readLines spec service ask (actual.map some) out with ⟨A, out'⟩
  have he : e = E := by simp only [e, read, hr]
  have ha : a = Verify.withoutRepeatedAnswers A := by simp only [a, read, hr, hr']
  rw [he, ha]
  cases hd : Verify.firstDuplicate (actual.map some) with
  | some p =>
    obtain ⟨i, u⟩ := p
    simp only [Verify.compareTraces, Verify.verifyLines, Verify.comparedLines, untilMalformed_lines, hd, hr, bind,
      pure] at h
    split at h
    · cases h
    · rename_i hnil
      rcases hr'' : Verify.readLines spec service ask ((actual.map some).take (i - 1)) out with ⟨A₂, out₂⟩
      simp only [hr''] at hnil
      have hf : (Verify.compare E (Verify.withoutRepeatedAnswers A₂) (some u) (Verify.internalEvent spec service)
          renamed true).findings = [] := by
        simpa [List.length_mergeSort] using congrArg List.length (List.head?_eq_none_iff.mp hnil)
      exact absurd (compare_matches _ _ _ _ _ _ hf).1 (by simp)
  | none =>
    simp only [Verify.compareTraces, Verify.verifyLines, Verify.comparedLines, untilMalformed_lines, hd, hr, hr',
      Option.map_none, bind, pure] at h
    split at h
    · cases h
    · rename_i hnil
      cases h
      have hf : (Verify.compare E (Verify.withoutRepeatedAnswers A) none (Verify.internalEvent spec service) renamed
          true).findings = [] := by
        simpa [List.length_mergeSort] using congrArg List.length (List.head?_eq_none_iff.mp hnil)
      obtain ⟨-, hne, hall⟩ := compare_matches _ _ _ _ _ _ hf
      exact ⟨hne, hall⟩

/--
Two outcomes that difference finds the same halt alike, and when neither halts, either the outputs compare under bindings
of which one makes the records equal (sameRecords), or the original outputs do not compare even with themselves, and the
records are equal (sameRecords under the empty binding).
-/
theorem difference_same {compare : Compare Id} {o a : Explore.Outcome} (h : (difference compare o a : Id _) = .same) :
    haltIdentity o.halted = haltIdentity a.halted ∧
    (o.halted = none →
      (∃ set, compare (o.renaming a) o.lines a.lines = .ok set ∧ sameRecords set o a = .same) ∨
      ((∃ v, compare (o.renaming a) o.lines a.lines = .error v) ∧
        (∃ v, compare (o.renaming o) o.lines o.lines = .error v) ∧ sameRecords [.empty] o a = .same)) := by
  unfold difference at h
  by_cases hh : (o.halted.isSome || a.halted.isSome) = true
  · simp only [hh, ↓reduceIte, pure] at h
    split at h
    · rename_i he
      refine ⟨beq_iff_eq.mp he, fun hn => ?_⟩
      rw [hn] at he
      cases ha : a.halted with
      | none => simp [hn, ha] at hh
      | some v => simp [ha, haltIdentity] at he
    · cases h
  · simp only [hh, Bool.false_eq_true, ↓reduceIte, bind, pure] at h
    simp only [Bool.or_eq_true, Option.isSome_iff_ne_none, not_or, Decidable.not_not] at hh
    refine ⟨by rw [hh.1, hh.2], fun _ => ?_⟩
    split at h
    · rename_i set hc
      refine .inl ⟨set, hc, ?_⟩
      split at h <;> first | rfl | assumption | cases h
    · rename_i v hc
      split at h
      · cases h
      · rename_i w hc'
        refine .inr ⟨⟨v, hc⟩, ⟨w, hc'⟩, ?_⟩
        split at h <;> first | rfl | assumption | cases h

theorem violation_none {d : Spec.Ref} {f : Difference → ChoiceDependent} {c : Comparison}
    (h : c.violation d f = none) : c = .same := by
  cases c <;> simp_all [Comparison.violation]

/-- stepOrder reports nothing only when difference finds the two outcomes the same, in one order or the other. -/
theorem stepOrder_none {compare : Compare Id} {service : String} {a b : StepName} {ao bo : List StepName}
    {x y : Explore.Outcome} (h : (stepOrder compare service a b ao bo x y : Id _) = none) :
    (difference compare x y : Id _) = .same ∨ (difference compare y x : Id _) = .same := by
  unfold stepOrder at h
  by_cases hc : (ToValue.toValue a).canonical ≤ (ToValue.toValue b).canonical
  · simp only [hc, ↓reduceIte, bind, pure] at h
    exact .inl (violation_none h)
  · simp only [hc, ↓reduceIte, bind, pure] at h
    exact .inr (violation_none h)

section Search

variable (compare : Compare Id) (executeWith : List StepName → Id Execution) (o : Scenario.Origin) (st : Service)

/--
A step order that the search ran: refused, or compared with an execution `parent` that the search had run, a verdict
without a violation meaning that difference finds the two outcomes the same, in one order or the other.
-/
def Ran (t : Tried) : Prop :=
  t.verdict = .refused ∨ ∃ (parent : Execution) (found : Option ChoiceDependent), t.verdict = .decided found ∧
    (found = none →
      (difference compare (parent.outcome st) (aligned o st parent (executeWith t.order)) : Id _) = .same ∨
      (difference compare (aligned o st parent (executeWith t.order)) (parent.outcome st) : Id _) = .same)

/-- What every state of a search holds: each order it ran is Ran, and while it found nothing, none had a violation. -/
def SearchInv (r : Searching) : Prop :=
  (∀ t ∈ r.search.tried, Ran compare executeWith o st t) ∧
    (r.search.found = [] → (∀ t ∈ r.search.tried, t.verdict = .refused ∨ ∃ f, t.verdict = .decided f ∧ f = none) ∧
      r.stopped = false)

omit compare executeWith o st in
theorem filter_none {α : Type} {x : Option α} {p : α → Bool} (h : (x.filter p).toList = [])
    (hp : ∀ v, p v = true) : x = none := by
  cases x with
  | none => rfl
  | some v => simp [Option.filter, hp v] at h

theorem inv_step {r r' : Searching} (hr : SearchInv compare executeWith o st r)
    (htried : ∀ t ∈ r'.search.tried, t ∈ r.search.tried ∨ (Ran compare executeWith o st t ∧
      (r'.search.found = [] → t.verdict = .refused ∨ ∃ f, t.verdict = .decided f ∧ f = none)))
    (hfound : r'.search.found = [] → r.search.found = [] ∧ r'.stopped = r.stopped) :
    SearchInv compare executeWith o st r' := by
  obtain ⟨hran, hnone⟩ := hr
  refine ⟨fun t ht => ?_, fun h => ?_⟩
  · rcases htried t ht with ht | ⟨hr, -⟩
    · exact hran t ht
    · exact hr
  · obtain ⟨hf, hs⟩ := hfound h
    obtain ⟨h₁, h₂⟩ := hnone hf
    refine ⟨fun t ht => ?_, hs ▸ h₂⟩
    rcases htried t ht with ht | ⟨-, hv⟩
    · exact h₁ t ht
    · exact hv h

theorem searchPair_inv (parent : Execution) (parentOrder : List StepName) (taken : List (Nat × StepName))
    (r : Searching) (pair : Nat × Nat) (hr : SearchInv compare executeWith o st r) :
    SearchInv compare executeWith o st
      (searchPair compare executeWith o st parent parentOrder (parent.outcome st) taken r pair : Id _) := by
  unfold searchPair
  simp only [bind, pure]
  repeat' split
  all_goals first
    | exact hr
    | refine inv_step compare executeWith o st hr (fun t ht => ?_) (fun h => ?_)
  · exact .inl ht
  · simp at h
  all_goals first
    | (simp only [List.mem_append, List.mem_singleton] at ht
       rcases ht with ht | rfl
       · exact .inl ht
       · refine .inr ⟨?_, fun h => ?_⟩
         · first
           | exact .inl rfl
           | exact .inr ⟨parent, _, rfl, fun hn => stepOrder_none hn⟩
         · first
           | exact .inl rfl
           | (refine .inr ⟨_, rfl, ?_⟩
              obtain ⟨h₁, h₂⟩ := List.append_eq_nil_iff.mp h
              rw [h₁] at h₂
              exact filter_none h₂ (fun v => by simp)))
    | exact ⟨h, rfl⟩
    | exact ⟨(List.append_eq_nil_iff.mp h).1, rfl⟩

theorem searchQueue_inv : ∀ (fuel : Nat) (r : Searching), SearchInv compare executeWith o st r →
    SearchInv compare executeWith o st (searchQueue compare executeWith o st fuel r : Id _)
  | 0, _, h => h
  | fuel + 1, r, h => by
    unfold searchQueue
    split
    · exact h
    · simp only [bind, pure]
      split
      · exact h
      · split
        · refine searchQueue_inv fuel _ ?_
          rw [Tazuna.Thm.Data.Basic.foldlM_id]
          exact Tazuna.Thm.Data.Basic.foldl_keeps _ _
            (fun r pair hr => searchPair_inv compare executeWith o st _ _ _ r pair hr) _ _ h
        · exact searchQueue_inv fuel _ h

/--
The verdict of the step-order search of one processing: when it reports nothing, each order that it ran was refused (no
queue could take it) or gives the same outcome as the execution that it came from, as difference finds outcomes the
same (difference_same, compareTraces_ok). The search reports searchLimit when it stops with orders left, so it ran
every order that it reached. That it reaches every order of dependent steps (dynamic partial-order reduction) has no
theorem.
-/
theorem stepOrderSearch_same (base : Execution)
    (h : (stepOrderSearch compare executeWith o st base : Id _).found = []) :
    ∀ t ∈ (stepOrderSearch compare executeWith o st base : Id _).tried,
      t.verdict = .refused ∨ (t.verdict = .decided none ∧ ∃ parent : Execution,
        (difference compare (parent.outcome st) (aligned o st parent (executeWith t.order)) : Id _) = .same ∨
        (difference compare (aligned o st parent (executeWith t.order)) (parent.outcome st) : Id _) = .same) := by
  unfold stepOrderSearch at h ⊢
  cases hs : base.span? o st.service with
  | none => simp
  | some span =>
    by_cases hc : (base.candidatesOf span).isEmpty = true
    · simp [hc]
    · simp only [hs, hc, Bool.false_eq_true, ↓reduceIte, bind, pure] at h ⊢
      obtain ⟨hran, hnone⟩ := searchQueue_inv compare executeWith o st (stepOrderLimit + 1)
        { reached := [(base.taken span).map (·.2)], queue := [(base, [])] }
        ⟨fun t ht => by simp at ht, fun _ => ⟨fun t ht => by simp at ht, rfl⟩⟩
      intro t ht
      obtain ⟨hv, -⟩ := hnone h
      rcases hran t ht with hr | ⟨parent, found, hf, hs⟩
      · exact .inl hr
      · rcases hv t ht with hv | ⟨f, hv, rfl⟩
        · exact .inl hv
        · rw [hf] at hv
          cases hv
          exact .inr ⟨hf, parent, hs rfl⟩

end Search

end Tazuna.Thm.Explore.StepOrders
