import Tazuna.Semantics.Validation.Canonical
import Tazuna.Thm.Guarantee

/-!
The verdict of check's structural NonCanonical part: the canonical forms that a spec without such a violation keeps.
-/

namespace Tazuna.Thm.Semantics.Validation.Canonical

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Validation Tazuna.Semantics.Validation.Canonical

/-- The canonical forms that Canonical.check enforces. -/
structure CanonicalForms (s : Structure) : Prop where
  /-- No machine is stateless: one state, no context, nothing to wait for, one event to one command. -/
  noStatelessMachine : ∀ d ∈ s.definitions, ∀ c, d.body = .machine c → stateless c = false
  /-- A transition has a `reenter` exactly when it leads to its source state or a descendant of it. -/
  reenterWhenWithin : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c →
    ∀ t ∈ c.on ++ c.states.flatMap (·.transitions), t.reenter.isSome = withinSource c t
  /-- An automation writes `onRejected` exactly when its command may be rejected with `unavailable`. -/
  automationOnRejected : ∀ d ∈ s.definitions, ∀ a, d.body = .automation a →
    a.onRejected = automationArrives s d.service a
  /-- A state's calls or sends writes `onRejected` exactly when an answer may be rejected. -/
  requestOnRejected : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states, ∀ a ∈ st.activities,
    ∀ trigger r written, requestOf a = some (trigger, r, written) →
      written = !(s.rejectionKinds d.service r).isEmpty
  /-- Each binding of a command's or automation's `binds` is read by a body that receives it as `bound`. -/
  bindingRead : ∀ x ∈ boundReaders s.program, ∀ b ∈ x.1.conditions, readsBinding x.2 b.name = true

/--
Canonical.check reports no violation exactly when the spec keeps every canonical form that the structure shows
(CanonicalForms).
-/
@[guarantee] theorem canonical_check_eq_nil_iff (s : Structure) : Canonical.check s = [] ↔ CanonicalForms s := by
  simp only [Canonical.check, List.append_eq_nil_iff]
  have machines : statelessMachines s = [] ↔
      ∀ d ∈ s.definitions, ∀ c, d.body = .machine c → stateless c = false := by
    simp only [statelessMachines, List.filterMap_eq_nil_iff]
    constructor
    · intro h d hd c hb
      have := h d hd
      simp only [hb] at this
      exact Classical.byContradiction fun hn => by simp [hn] at this
    · intro h d hd
      split
      · rename_i c hb
        simp [h d hd c hb]
      · rfl
  have reenter : reenters s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.chart? = some c →
      ∀ t ∈ c.on ++ c.states.flatMap (·.transitions), t.reenter.isSome = withinSource c t := by
    simp only [reenters, List.flatMap_eq_nil_iff]
    constructor
    · intro h d hd c hc t ht
      have := h d hd
      simp only [hc] at this
      have := List.filterMap_eq_nil_iff.mp this t ht
      exact Classical.byContradiction fun hn => by simp [hn] at this
    · intro h d hd
      cases hc : d.chart? with
      | none => rfl
      | some c => exact List.filterMap_eq_nil_iff.mpr fun t ht => by simp [h d hd c hc t ht]
  have automation : Canonical.automations s = [] ↔ ∀ d ∈ s.definitions, ∀ a, d.body = .automation a →
      a.onRejected = automationArrives s d.service a := by
    simp only [Canonical.automations, List.filterMap_eq_nil_iff]
    constructor
    · intro h d hd a hb
      have := h d hd
      simp only [hb] at this
      exact Classical.byContradiction fun hn => by simp [Ne.symm hn] at this
    · intro h d hd
      split
      · rename_i a hb
        simp [h d hd a hb]
      · rfl
  have request : Canonical.states s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states,
      ∀ a ∈ st.activities, ∀ trigger r written, requestOf a = some (trigger, r, written) →
        written = !(s.rejectionKinds d.service r).isEmpty := by
    simp only [Canonical.states, List.flatMap_eq_nil_iff]
    constructor
    · intro h d hd c hc st hst a ha trigger r written hr
      have := h d hd
      simp only [hc, List.flatMap_eq_nil_iff] at this
      have := List.filterMap_eq_nil_iff.mp (this st hst) a ha
      simp only [hr, Option.bind_some] at this
      exact Classical.byContradiction fun hn => by simp [Ne.symm hn] at this
    · intro h d hd
      cases hc : d.chart? with
      | none => rfl
      | some c =>
        refine List.flatMap_eq_nil_iff.mpr fun st hst => List.filterMap_eq_nil_iff.mpr fun a ha => ?_
        cases hr : requestOf a with
        | none => rfl
        | some x =>
          obtain ⟨trigger, r, written⟩ := x
          simp [h d hd c hc st hst a ha trigger r written hr]
  have binding : unreadBindings s = [] ↔
      ∀ x ∈ boundReaders s.program, ∀ b ∈ x.1.conditions, readsBinding x.2 b.name = true := by
    simp only [unreadBindings, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
    constructor
    · intro h x hx b hb
      have := h x hx b hb
      exact Classical.byContradiction fun hn => by simp [hn] at this
    · intro h x hx b hb
      simp [h x hx b hb]
  rw [machines, reenter, automation, request, binding]
  exact ⟨fun ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩⟩

end Tazuna.Thm.Semantics.Validation.Canonical
