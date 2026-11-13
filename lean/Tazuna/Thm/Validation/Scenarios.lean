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
      ∀ sc ∈ s.scenarios, ∀ sender target, ScenarioInput.answer (some sender) (some target) ∈ sc.inputs →
        ∃ d ∈ s.definitions, d.ref = sender ∧ Requests d target := by
  simp only [unrequestedAnswers, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc sender target hin
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
    | .answer (some sender) (some target), hin =>
      obtain ⟨d, hd, hr, hreq⟩ := h sc hsc sender target hin
      have : s.definitions.any (fun d => d.ref == sender && requests d target) = true :=
        List.any_eq_true.mpr ⟨d, hd, by simp [hr, (requests_iff d target).mpr hreq]⟩
      simp [this]
    | .answer none _, _ | .answer (some _) none, _ | .at, _ | .command, _ | .query, _ | .subscribe, _ | .unsubscribe, _ | .restart, _
    | .event _, _ | .operation, _ | .unacceptedOperation, _ => rfl

theorem results_placed_at_most_once (s : Structure) :
    resultsOfPlacedTwice s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ positions, ScenarioInput.event (some positions) ∈ sc.inputs → positions.length ≤ 1 := by
  simp only [resultsOfPlacedTwice, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc positions hin
    obtain ⟨i, hi⟩ := mem_zipIdx_of_mem hin
    have := List.filterMap_eq_nil_iff.mp (h sc hsc) _ hi
    simpa using this
  · intro h sc hsc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨input, i⟩ hi => ?_
    have hin := List.fst_mem_of_mem_zipIdx hi
    match input, hin with
    | .event (some positions), hin => simpa using h sc hsc positions hin
    | .event none, _ | .at, _ | .command, _ | .query, _ | .subscribe, _ | .unsubscribe, _ | .restart, _ | .operation, _
    | .unacceptedOperation, _ | .answer _ _, _ => rfl

theorem results_placed_before (s : Structure) :
    resultsOfUnplaced s = [] ↔
      ∀ sc ∈ s.scenarios, ∀ i positions, sc.inputs[i]? = some (ScenarioInput.event (some positions)) →
        ∃ p ∈ positions, p < i := by
  simp only [resultsOfUnplaced, List.flatMap_eq_nil_iff]
  constructor
  · intro h sc hsc i positions hi
    have hz : (ScenarioInput.event (some positions), i) ∈ sc.inputs.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
    have := List.filterMap_eq_nil_iff.mp (h sc hsc) _ hz
    simpa using this
  · intro h sc hsc
    refine List.filterMap_eq_nil_iff.mpr fun ⟨input, i⟩ hz => ?_
    have hi : sc.inputs[i]? = some input := List.mem_zipIdx_iff_getElem?.mp hz
    match input, hi with
    | .event (some positions), hi => simpa using h sc hsc i positions hi
    | .event none, _ | .at, _ | .command, _ | .query, _ | .subscribe, _ | .unsubscribe, _ | .restart, _ | .operation, _
    | .unacceptedOperation, _ | .answer _ _, _ => rfl

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

end Tazuna.Thm.Validation.Scenarios
