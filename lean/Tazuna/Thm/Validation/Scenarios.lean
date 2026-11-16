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
      ∀ sc ∈ s.scenarios, ∀ sender target strings, ScenarioInput.answer (some sender) (some target) strings ∈ sc.inputs →
        ∃ d ∈ s.definitions, d.ref = sender ∧ Requests d target := by
  simp only [unrequestedAnswers, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc sender target strings hin
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hin
    have := List.filterMap_eq_nil_iff.mp (h sc hsc) _ hi
    have hany : s.definitions.any (fun d => d.ref == sender && requests d target) = true := by
      cases hc : s.definitions.any (fun d => d.ref == sender && requests d target)
      · simp [hc] at this
      · rfl
    obtain ⟨d, hd, hdr⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hdr
    exact ⟨d, hd, hdr.1, (requests_iff d target).mp hdr.2⟩
  · intro h sc hsc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨input, i⟩ hi => ?_
    have hin := List.fst_mem_of_mem_zipIdx hi
    match input, hin with
    | .answer (some sender) (some target) strings, hin =>
      obtain ⟨d, hd, hr, hreq⟩ := h sc hsc sender target strings hin
      have : s.definitions.any (fun d => d.ref == sender && requests d target) = true :=
        List.any_eq_true.mpr ⟨d, hd, by simp [hr, (requests_iff d target).mpr hreq]⟩
      simp [this]
    | .answer none _ _, _ | .answer (some _) none _, _ | .at, _ | .command _, _ | .query _, _ | .subscribe _, _ | .unsubscribe _, _
    | .restart, _ | .event _ _, _ | .operation _, _ | .unacceptedOperation _, _ | .elsewhere _, _ => rfl

theorem named_inputs_placed_at_most_once (s : Structure) :
    namedInputsPlacedTwice s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ input ∈ sc.inputs, ∀ positions, input.named = some positions → positions.length ≤ 1 := by
  simp only [namedInputsPlacedTwice, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc input hin positions hp
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hin
    have := List.filterMap_eq_nil_iff.mp (h sc hsc) _ hi
    simp only [hp] at this
    simpa using this
  · intro h sc hsc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨input, i⟩ hi => ?_
    have hin := List.fst_mem_of_mem_zipIdx hi
    cases hp : input.named with
    | none => simp
    | some positions => simpa [hp] using h sc hsc input hin positions hp

theorem named_inputs_placed_before (s : Structure) :
    namedInputsUnplaced s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ i (input : ScenarioInput) positions, sc.inputs[i]? = some input → input.named = some positions →
        ∃ p ∈ positions, p < i := by
  simp only [namedInputsUnplaced, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc i input positions hi hp
    have hz : (input, i) ∈ sc.inputs.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    have := List.filterMap_eq_nil_iff.mp (h sc hsc) _ hz
    simp only [hp] at this
    simpa using this
  · intro h sc hsc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨input, i⟩ hz => ?_
    have hi : sc.inputs[i]? = some input := List.mem_zipIdx_iff_getElem?.mp hz
    cases hp : input.named with
    | none => simp
    | some positions => simpa [hp] using h sc hsc i input positions hi hp

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

theorem keys_uncounted (s : Structure) :
    countedKeys s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ input ∈ sc.inputs, ∀ v ∈ input.strings, ∀ e ∈ keyedEntities s, isKeyOf e.name v = false := by
  simp only [countedKeys, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
    List.find?_eq_none, List.mem_eraseDups, Bool.not_eq_true]
  constructor
  · intro h sc hsc input hin v hv e he
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hin
    exact h sc hsc _ hi v hv e he
  · intro h sc hsc p hp v hv e he
    exact h sc hsc p.1 (List.fst_mem_of_mem_zipIdx hp) v hv e he

end Tazuna.Thm.Validation.Scenarios
