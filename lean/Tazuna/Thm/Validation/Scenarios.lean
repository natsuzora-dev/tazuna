import Tazuna.Validation.Scenarios
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Validation.Scenarios

open Tazuna.Data Tazuna.Syntax Tazuna.Validation Tazuna.Validation.Scenarios
open Tazuna.Thm.Data.Basic

def Requests (d : Definition) (target : Ref) : Prop :=
  (∃ receives binds guard, d.body = .automation receives (some target) binds guard) ∨
    ∃ c, d.chart? = some c ∧ ((∃ key, (key, some target) ∈ c.commands) ∨ ∃ key, (key, some target) ∈ c.queries)

theorem requests_iff (d : Definition) (target : Ref) : requests d target = true ↔ Requests d target := by
  unfold requests Requests Definition.chart?
  split <;> simp_all [List.any_eq_true]

theorem answers_requested (s : Structure) :
    unrequestedAnswers s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ l ∈ sc.inputs, ∀ sender target, l.input = .answer (some sender) (some target) →
        ∃ d ∈ s.definitions, d.ref = sender ∧ Requests d target := by
  simp only [unrequestedAnswers, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc l hl sender target hin
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hl
    have := List.filterMap_eq_nil_iff.mp (h sc hsc) _ hi
    simp only [hin] at this
    have hany : s.definitions.any (fun d => d.ref == sender && requests d target) = true := by
      cases hc : s.definitions.any (fun d => d.ref == sender && requests d target)
      · simp [hc] at this
      · rfl
    obtain ⟨d, hd, hdr⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hdr
    exact ⟨d, hd, hdr.1, (requests_iff d target).mp hdr.2⟩
  · intro h sc hsc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨l, i⟩ hi => ?_
    have hl := List.fst_mem_of_mem_zipIdx hi
    simp only
    split
    · rename_i sender target hin
      obtain ⟨d, hd, hr, hreq⟩ := h sc hsc l hl sender target hin
      have : s.definitions.any (fun d => d.ref == sender && requests d target) = true :=
        List.any_eq_true.mpr ⟨d, hd, by simp [hr, (requests_iff d target).mpr hreq]⟩
      simp [this]
    · rfl

/--
A check over scopedLines finds nothing exactly when it finds nothing at each line `(l, some i)` at place `k` of each
run's lines, with the lines before place `k` and all lines of the run.
-/
theorem scoped_nil {sc : Scenario} {s : Structure}
    (P : Nat → ScenarioLine → List ScenarioLine → List ScenarioLine → Option Illegal) :
    (scopedLines s sc).filterMap (fun (i, l, before, all) => P i l before all) = [] ↔
      ∀ r ∈ runsOf sc, ∀ k l i, (runLines s sc r)[k]? = some (l, some i) →
        P i l (((runLines s sc r).take k).map (·.1)) ((runLines s sc r).map (·.1)) = none := by
  simp only [scopedLines, List.filterMap_flatMap, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff,
    List.filterMap_filterMap]
  constructor
  · intro h r hr k l i hk
    have := h r hr ((l, some i), k) (List.mem_zipIdx_iff_getElem?.mpr hk)
    simpa using this
  · intro h r hr ⟨⟨l, o⟩, k⟩ hk
    have hk' := List.mem_zipIdx_iff_getElem?.mp hk
    cases o with
    | none => simp
    | some i => simpa using h r hr k l i hk'

/-- Each input that names another names one that its run takes at most once. -/
theorem named_inputs_placed_at_most_once (s : Structure) :
    namedInputsPlacedTwice s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ r ∈ runsOf sc, ∀ (k : Nat) (l : ScenarioLine) (i h : Nat), (runLines s sc r)[k]? = some (l, some i) → l.names = some h →
        ((runLines s sc r).filter (·.1.handle == some h)).length ≤ 1 := by
  simp only [namedInputsPlacedTwice, List.flatMap_eq_nil_iff]
  refine forall_congr' fun sc => forall_congr' fun _ => (scoped_nil (fun i l _ all => l.names.bind fun h =>
        if 1 < (all.filter (·.handle == some h)).length then some (.namedInputPlacedTwice sc.ref (i + 1)) else none)).trans ?_
  refine forall_congr' fun r => forall_congr' fun _ => forall_congr' fun k => forall_congr' fun l => ?_
  refine forall_congr' fun i => ⟨fun h hm hk hn => ?_, fun h hk => ?_⟩
  · have := h hk
    simp only [hn, Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false, Nat.not_lt] at this
    simpa [List.filter_map, Function.comp_def] using this
  · cases hn : l.names with
    | none => simp
    | some m =>
      have := h m hk hn
      simp only [Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false, Nat.not_lt]
      simpa [List.filter_map, Function.comp_def] using this

/-- Each input that names another names one that its run takes before it, from the same sender. -/
theorem named_inputs_placed_before (s : Structure) :
    namedInputsUnplaced s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ r ∈ runsOf sc, ∀ (k : Nat) (l : ScenarioLine) (i h : Nat), (runLines s sc r)[k]? = some (l, some i) → l.names = some h →
        ∃ b ∈ ((runLines s sc r).take k).map (·.1), b.handle = some h ∧ b.sentBy = l.sentBy := by
  simp only [namedInputsUnplaced, List.flatMap_eq_nil_iff]
  refine forall_congr' fun sc => forall_congr' fun _ => (scoped_nil (fun i l before _ => l.names.bind fun h =>
        if before.any fun b => b.handle == some h && b.sentBy == l.sentBy then none
        else some (.namedInputUnplaced sc.ref (i + 1)))).trans ?_
  refine forall_congr' fun r => forall_congr' fun _ => forall_congr' fun k => forall_congr' fun l => ?_
  refine forall_congr' fun i => ⟨fun h hm hk hn => ?_, fun h hk => ?_⟩
  · have := h hk
    simp only [hn, Option.bind_some, ite_eq_left_iff, reduceCtorEq, imp_false, Bool.not_eq_false,
      List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at this
    exact Classical.not_not.mp this
  · cases hn : l.names with
    | none => simp
    | some m =>
      obtain ⟨b, hb, h₁, h₂⟩ := h m hk hn
      have : (((runLines s sc r).take k).map (·.1)).any (fun b => b.handle == some m && b.sentBy == l.sentBy) :=
        List.any_eq_true.mpr ⟨b, hb, by simp [h₁, h₂]⟩
      simp only [Option.bind_some, this, ↓reduceIte]

/-- No input's `keys` gives a name to a createKey value of an entity that an earlier line of its run, or itself, named. -/
theorem keys_named_once (s : Structure) :
    keysNamedTwice s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ r ∈ runsOf sc, ∀ (k : Nat) (l : ScenarioLine) (i : Nat), (runLines s sc r)[k]? = some (l, some i) →
        ∀ j p, l.keyNames[j]? = some p → (∀ b ∈ ((runLines s sc r).take k).map (·.1), p ∉ b.keyNames) ∧
          p ∉ l.keyNames.take j := by
  simp only [keysNamedTwice, List.flatMap_eq_nil_iff]
  refine forall_congr' fun sc => forall_congr' fun _ => (scoped_nil (fun i l before _ =>
        (l.keyNames.zipIdx.find? fun (p, j) => before.any (p ∈ ·.keyNames) || p ∈ l.keyNames.take j).map
          fun ((e, n), _) => .keyNamedTwice sc.ref (i + 1) e n)).trans ?_
  refine forall_congr' fun r => forall_congr' fun _ => forall_congr' fun k => forall_congr' fun l => ?_
  refine forall_congr' fun i => forall_congr' fun _ => ?_
  simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
    not_or, not_exists, not_and]
  constructor
  · intro h j p hj
    have := h (p, j) (List.mem_zipIdx_iff_getElem?.mpr hj)
    exact ⟨fun b hb hp => this.1 b hb hp, this.2⟩
  · intro h ⟨p, j⟩ hj
    have := h j p (List.mem_zipIdx_iff_getElem?.mp hj)
    exact ⟨fun b hb hp => this.1 b hb hp, this.2⟩

/-- No input has a value that a later line's `keys` gives as a name. -/
theorem keys_named_before_use (s : Structure) :
    keysUsedBeforeNamed s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ i l, sc.inputs[i]? = some l → ∀ v ∈ l.strings, ∀ m ∈ sc.inputs.drop (i + 1),
        ∀ p ∈ m.keyNames, p.2 ≠ v := by
  simp only [keysUsedBeforeNamed, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
    List.find?_eq_none, List.any_eq_true, beq_iff_eq, not_exists, not_and, decide_eq_true_eq]
  refine forall_congr' fun sc => forall_congr' fun _ => ?_
  constructor
  · intro h i l hi v hv m hm p hp hpv
    exact h (l, i) (List.mem_zipIdx_iff_getElem?.mpr hi) v hv m hm p hp hpv
  · intro h ⟨l, i⟩ hi v hv m hm p hp hpv
    exact h i l (List.mem_zipIdx_iff_getElem?.mp hi) v hv m hm p hp hpv

theorem scenarios_of_internal_services (s : Structure) :
    scenariosOfExternalServices s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ sv ∈ s.services, sv.name = sc.service → sv.external = false := by
  simp only [scenariosOfExternalServices, List.filterMap_eq_nil_iff]
  constructor
  · intro h sc hsc sv hsv hn
    have := h sc hsc
    simp only [ite_eq_right_iff, reduceCtorEq, imp_false, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      not_exists, not_and] at this
    cases he : sv.external
    · rfl
    · exact absurd he (by simpa using this sv hsv hn)
  · intro h sc hsc
    have : s.services.any (fun sv => sv.name == sc.service && sv.external) = false := by
      simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
      intro sv hsv hn
      simp [h sc hsc sv hsv hn]
    simp [this]

/-- No value or `keys` name of an input has the form of a counted key of an entity of the scenario's service or a peer. -/
theorem keys_uncounted (s : Structure) :
    countedKeys s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ l ∈ sc.inputs, ∀ v ∈ l.strings ++ l.keyNames.map (·.2), ∀ e ∈ keyedEntities s,
        (e.service = sc.service ∨ e.service ∈ sc.peers) → isKeyOf e.name v = false := by
  simp only [countedKeys, checkedValues, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
    List.find?_eq_none, List.mem_eraseDups, List.mem_filter, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem,
    Bool.not_eq_true, and_imp]
  constructor
  · intro h sc hsc l hl v hv e he hs
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hl
    exact h sc hsc _ hi v hv e he (by simpa using hs)
  · intro h sc hsc p hp v hv e he hs
    exact h sc hsc p.1 (List.fst_mem_of_mem_zipIdx hp) v hv e he (by simpa using hs)

end Tazuna.Thm.Validation.Scenarios
