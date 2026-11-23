import Tazuna.Validation.Check
import Tazuna.Thm.Validation.Automations
import Tazuna.Thm.Validation.Charts
import Tazuna.Thm.Validation.Commands
import Tazuna.Thm.Validation.Contracts
import Tazuna.Thm.Validation.Schemas
import Tazuna.Thm.Guarantee

/-!
The verdict of check's structural part (Illegal): the rules that a spec without such a violation keeps.
-/

namespace Tazuna.Thm.Validation.Check

open Tazuna.Data Tazuna.Spec Tazuna.Validation
open Tazuna.Validation.Automations (automations)
open Tazuna.Thm.Validation.Automations (Chain)

/-- The structural rules of a spec that Validation.check enforces, one per kind of Illegal violation. -/
structure Checked (s : Structure) : Prop where
  /-- No automation that sends a command to its own service is triggered, through a chain, by its own command. -/
  noReturningAutomation : ∀ a ∈ automations s, ¬ Chain s a a
  /-- A screen with an input, requires, output, or ensures is opened by a screen. -/
  parentsOpened : ∀ d ∈ s.definitions, ∀ c, d.body = .screen c → (Charts.parentKeys c).isEmpty = false →
    s.isOpenedByScreen d.ref = true
  /-- A chart queries only other services. -/
  noOwnQuery : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ key q, (key, q) ∈ c.queries →
    q.service ≠ d.service
  /-- Each control of a chart is one that it offers. -/
  controlsListed : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ k x, (k, x) ∈ c.controls →
    c.offers.any (·.1 == k) = true
  /-- An unguarded always transition does not lead back to its source. -/
  alwaysEnds : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states, ∀ t ∈ st.transitions,
    t.trigger = .always → t.guarded = false → ¬ Charts.Reaches c (Charts.lands c st.name t) st.name
  /-- A command emits only events of its own service. -/
  ownEvents : ∀ d ∈ s.definitions, ∀ c, d.body = .command c → ∀ e ∈ c.emits, e.service = d.service
  /-- No rejection reason is an array index, which a JavaScript object would reorder. -/
  reasonsNotIndices : ∀ d ∈ s.definitions, ∀ r ∈ s.rejectionReasons d.ref, Commands.isArrayIndex r = false
  /-- No history state restores a state with parameters, which a restore would enter without filling them. -/
  heldNotRestored : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → Charts.restoredHeldOf c = []
  /-- A contract lists only members of its own service. -/
  ownMembers : ∀ c ∈ s.contracts, ∀ key m, (key, some m) ∈ c.members → m.service = c.service
  /-- Every deadline's delay has a length in milliseconds, which the run adds to an instant. -/
  delaysExact : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states, ∀ t ∈ st.deadlines,
    t.time.isExact = true
  /-- No deadline's delay is below zero. -/
  delaysNonNegative : ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states, ∀ t ∈ st.deadlines,
    t.time.isNegative = false
  /-- Every sortedBy array of a schema sorts by a key whose encoded value SortKey orders. -/
  sortKeysOrdered : ∀ d ∈ s.definitions, ∀ x ∈ Schemas.schemasOf d, ∀ path key,
    (path, .unorderedSortKey key) ∉ Schemas.issues x.1 x.2
  /-- Every two options of a union that holds a collection are `apart`, so no value fits both (`apart_disjoint`). -/
  unionsApart : ∀ d ∈ s.definitions, ∀ x ∈ Schemas.schemasOf d, ∀ path, (path, .ambiguousUnion) ∉ Schemas.issues x.1 x.2
  /-- No map state's key declares a default, which items, typed by the key's output type, never leaves to fill. -/
  mapKeysUndefaulted : ∀ d ∈ s.definitions, ∀ x ∈ Schemas.mapKeysOf d, Schemas.defaultPaths x.1 x.2 = []
  /-- Every command or query that an automation or chart sends lists its sender among its callers. -/
  callersListed : ∀ d ∈ s.definitions, ∀ r ∈ Commands.sentBy d, ∀ callers, s.callersOf? r = some callers →
    Commands.admitsSender callers d = true

/-- check reports no Illegal violation exactly when the spec keeps every structural rule (Checked). -/
@[guarantee] theorem check_eq_nil_iff (s : Structure) : Validation.check s = [] ↔ Checked s := by
  simp only [Validation.check, Charts.check, Commands.check, List.append_eq_nil_iff,
    Tazuna.Thm.Validation.Automations.no_automation_returns,
    Tazuna.Thm.Validation.Charts.queries_of_other_services,
    Tazuna.Thm.Validation.Charts.unguarded_always_does_not_return,
    Tazuna.Thm.Validation.Commands.commands_emit_own_events,
    Tazuna.Thm.Validation.Contracts.members_of_own_service]
  have parents : Charts.missingParents s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.body = .screen c →
      (Charts.parentKeys c).isEmpty = false → s.isOpenedByScreen d.ref = true := by
    simp only [Charts.missingParents, List.filterMap_eq_nil_iff]
    constructor
    · intro h d hd c hb hk
      have := h d hd
      simp only [hb, hk, Bool.not_false, Bool.true_and] at this
      exact Classical.byContradiction fun hn => by simp [hn] at this
    · intro h d hd
      split
      · rename_i c hb
        split
        · rename_i hk
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
          have := h d hd c hb hk.1
          simp [hk.2] at this
        · rfl
      · rfl
  have controls : Charts.unlistedControls s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ k x,
      (k, x) ∈ c.controls → c.offers.any (·.1 == k) = true := by
    simp only [Charts.unlistedControls, List.flatMap_eq_nil_iff]
    constructor
    · intro h d hd c hc k x hk
      have := h d hd
      simp only [hc, List.map_eq_nil_iff, List.filter_eq_nil_iff] at this
      simpa using this (k, x) hk
    · intro h d hd
      split
      · rename_i c hc
        simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro ⟨k, x⟩ hk
        simpa using h d hd c hc k x hk
      · rfl
  have reasons : Commands.indexReasons s = [] ↔
      ∀ d ∈ s.definitions, ∀ r ∈ s.rejectionReasons d.ref, Commands.isArrayIndex r = false := by
    simp only [Commands.indexReasons, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    constructor
    · intro h d hd r hr; simpa using h d hd r hr
    · intro h d hd r hr; simpa using h d hd r hr
  have callers : Commands.unlistedCallers s = [] ↔ ∀ d ∈ s.definitions, ∀ r ∈ Commands.sentBy d, ∀ callers,
      s.callersOf? r = some callers → Commands.admitsSender callers d = true := by
    simp only [Commands.unlistedCallers, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
    constructor
    · intro h d hd r hr callers hc
      have := h d hd r hr
      simp only [hc] at this
      exact Classical.byContradiction fun hn => by simp [hn] at this
    · intro h d hd r hr
      split
      · rename_i callers hc
        simp [h d hd r hr callers hc]
      · rfl
  have restored : Charts.restoredHeld s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.chart? = some c →
      Charts.restoredHeldOf c = [] := by
    simp only [Charts.restoredHeld, List.flatMap_eq_nil_iff]
    constructor
    · intro h d hd c hc
      have := h d hd
      simpa [hc] using this
    · intro h d hd
      split
      · rename_i c hc
        simp [h d hd c hc]
      · rfl
  have delays : Charts.inexactDelays s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.chart? = some c → ∀ st ∈ c.states,
      ∀ t ∈ st.deadlines, t.time.isExact = true := by
    simp only [Charts.inexactDelays, List.flatMap_eq_nil_iff]
    constructor
    · intro h d hd c hc st hst t ht
      have := h d hd
      simp only [hc, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at this
      simpa using this st hst t ht
    · intro h d hd
      split
      · rename_i c hc
        simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro st hst t ht
        simpa using h d hd c hc st hst t ht
      · rfl
  have negative : Charts.negativeDelays s = [] ↔ ∀ d ∈ s.definitions, ∀ c, d.chart? = some c →
      ∀ st ∈ c.states, ∀ t ∈ st.deadlines, t.time.isNegative = false := by
    simp only [Charts.negativeDelays, List.flatMap_eq_nil_iff]
    constructor
    · intro h d hd c hc st hst t ht
      have := h d hd
      simp only [hc, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at this
      simpa using this st hst t ht
    · intro h d hd
      split
      · rename_i c hc
        simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro st hst t ht
        simpa using h d hd c hc st hst t ht
      · rfl
  have schemas := Tazuna.Thm.Validation.Schemas.schemas_ordered s
  rw [parents, controls, reasons, callers, restored, delays, negative, schemas]
  simp only [and_assoc]
  constructor
  · intro ⟨a, p, q, c, al, hr, dl, ng, e, r, u, m, sk, ua, mk⟩
    exact ⟨a, p, q, c, al, e, r, hr, m, dl, ng, sk, ua, mk, u⟩
  · intro h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.8, h.10, h.11, h.6, h.7, h.15, h.9, h.12, h.13, h.14⟩

end Tazuna.Thm.Validation.Check
