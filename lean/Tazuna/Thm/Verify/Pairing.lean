import Tazuna.Thm.Data.Pairing
import Tazuna.Verify.Pairing
import Tazuna.Thm.Data.List
import Tazuna.Data.Binding

namespace Tazuna.Thm.Verify.Pairing

open Tazuna.Data Tazuna.Thm.Data.Pairing Tazuna.Verify
open Tazuna.Thm.Data.List (lookup_of_mem mem_of_lookup)

/-- Whether entry `e` of the subfolder `service` is a trace of an external service, or a trace of a scenario of a
service that is not external. -/
def Paired (services : List (String × Bool)) (scenarios : List Scenario) (service : String) (e : Entry) : Prop :=
  ∃ n, fileName e = some n ∧
    (services.lookup service = some true ∨
      services.lookup service = some false ∧ ∃ s ∈ scenarios, s.service = service ∧ s.name = n)

theorem entriesIn_of_mem (folders : List Folder) (unique : (folders.map (·.service)).Nodup) (f : Folder)
    (hf : f ∈ folders) : entriesIn folders f.service = f.entries := by
  unfold entriesIn
  cases h : folders.find? (·.service == f.service) with
  | none => have := List.find?_eq_none.mp h f hf; simp at this
  | some g =>
    have hg := List.mem_of_find?_eq_some h
    have hs : g.service = f.service := by simpa using List.find?_some h
    have : g = f := eq_of_map_nodup (f := (·.service)) unique hg hf hs
    simp [this]

theorem entriesIn_cases (folders : List Folder) (s : String) :
    entriesIn folders s = [] ∨ ∃ f ∈ folders, f.service = s ∧ entriesIn folders s = f.entries := by
  unfold entriesIn
  cases h : folders.find? (·.service == s) with
  | none => simp
  | some f =>
    right
    exact ⟨f, List.mem_of_find?_eq_some h, by simpa using List.find?_some h, by simp⟩

theorem mem_comparedNames (scenarios : List Scenario) (service n : String) :
    n ∈ comparedNames scenarios service ↔ ∃ s ∈ scenarios, s.service = service ∧ s.name = n ∧ s.compared = true := by
  simp only [comparedNames, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨s, ⟨hs, h1, h2⟩, h3⟩; exact ⟨s, hs, h1, h3, h2⟩
  · rintro ⟨s, hs, h1, h3, h2⟩; exact ⟨s, ⟨hs, h1, h2⟩, h3⟩

theorem mem_scenarioNames (scenarios : List Scenario) (service n : String) :
    n ∈ scenarioNames scenarios service ↔ ∃ s ∈ scenarios, s.service = service ∧ s.name = n := by
  simp only [scenarioNames, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨s, ⟨hs, h1⟩, h2⟩; exact ⟨s, hs, h1, h2⟩
  · rintro ⟨s, hs, h1, h2⟩; exact ⟨s, ⟨hs, h1⟩, h2⟩

theorem unknownServiceViolations_nil (f : Folder) : unknownServiceViolations f = [] ↔ f.entries = [] := by
  unfold unknownServiceViolations
  simp only [List.append_eq_nil_iff, List.map_eq_nil_iff]
  rw [extra_nil, unknown_nil]
  constructor
  · rintro ⟨hx, hu⟩
    cases hes : f.entries with
    | nil => rfl
    | cons e _ =>
      have he : e ∈ f.entries := by simp [hes]
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hu e he)
      exact absurd (hx e he n hn) List.not_mem_nil
  · intro h; simp [h]

theorem servicePairing_nil (scenarios : List Scenario) (folders : List Folder) (s : String) (b : Bool) :
    (servicePairing scenarios folders (s, b)).violations = [] ↔
      (∀ e ∈ entriesIn folders s, (fileName e).isSome) ∧
        (b = false →
          (∀ e ∈ entriesIn folders s, ∀ n, fileName e = some n → n ∈ scenarioNames scenarios s) ∧
            ∀ n ∈ comparedNames scenarios s, ∃ e ∈ entriesIn folders s, fileName e = some n) := by
  cases b <;>
    simp only [servicePairing, List.append_eq_nil_iff, List.map_eq_nil_iff, Bool.false_eq_true, ite_false,
      ite_true, and_true, forall_const, reduceCtorEq, false_implies, unknown_nil, extra_nil, missing_nil,
      and_assoc]

theorem pairTraces_nil (services : List (String × Bool)) (scenarios : List Scenario) (others : List String)
    (folders : List Folder) :
    (pairTraces services scenarios others folders).violations = [] ↔
      others = [] ∧ (∀ f ∈ folders, services.lookup f.service = none → f.entries = []) ∧
        ∀ p ∈ services, (servicePairing scenarios folders p).violations = [] := by
  unfold pairTraces
  simp only [List.append_eq_nil_iff, List.map_eq_nil_iff, List.flatMap_eq_nil_iff, List.mem_filter,
    Option.isNone_iff_eq_none, unknownServiceViolations_nil, and_imp, and_assoc]

/-- The theorem leaves out scenarios of external services because check rejects them (scenarioOfExternalService). -/
theorem no_violation_iff (services : List (String × Bool)) (scenarios : List Scenario) (others : List String)
    (folders : List Folder) (uniqueServices : (services.map (·.1)).Nodup)
    (uniqueFolders : (folders.map (·.service)).Nodup) :
    (pairTraces services scenarios others folders).violations = [] ↔
      others = [] ∧ (∀ f ∈ folders, ∀ e ∈ f.entries, Paired services scenarios f.service e) ∧
        ∀ s ∈ scenarios, s.compared = true → services.lookup s.service = some false →
          ∃ f ∈ folders, f.service = s.service ∧ ∃ e ∈ f.entries, fileName e = some s.name := by
  rw [pairTraces_nil]
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨hu, hs⟩
    refine ⟨fun f hf e he => ?_, fun sc hsc hsn hl => ?_⟩
    · have hin := entriesIn_of_mem folders uniqueFolders f hf
      cases hl : services.lookup f.service with
      | none => rw [hu f hf hl] at he; exact absurd he List.not_mem_nil
      | some b =>
        have h := (servicePairing_nil scenarios folders f.service b).mp (hs _ (mem_of_lookup hl))
        rw [hin] at h
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (h.1 e he)
        refine ⟨n, hn, ?_⟩
        cases b
        · exact Or.inr ⟨hl, (mem_scenarioNames scenarios f.service n).mp ((h.2 rfl).1 e he n hn)⟩
        · exact Or.inl hl
    · have h := (servicePairing_nil scenarios folders sc.service false).mp (hs _ (mem_of_lookup hl))
      obtain ⟨e, he, hn⟩ :=
        (h.2 rfl).2 sc.name ((mem_comparedNames scenarios sc.service sc.name).mpr ⟨sc, hsc, rfl, rfl, hsn⟩)
      rcases entriesIn_cases folders sc.service with h0 | ⟨f, hf, hfs, hfe⟩
      · rw [h0] at he; exact absurd he List.not_mem_nil
      · exact ⟨f, hf, hfs, e, hfe ▸ he, hn⟩
  · rintro ⟨hp, hs⟩
    refine ⟨fun f hf hl => ?_, fun ⟨s, b⟩ hsb => ?_⟩
    · cases hes : f.entries with
      | nil => rfl
      | cons e _ =>
        obtain ⟨_, _, hl' | hl'⟩ := hp f hf e (by simp [hes])
        · rw [hl] at hl'; cases hl'
        · rw [hl] at hl'; cases hl'.1
    · have hl := lookup_of_mem uniqueServices hsb
      rw [servicePairing_nil]
      rcases entriesIn_cases folders s with h0 | ⟨f, hf, hfs, hfe⟩
      · rw [h0]
        refine ⟨by simp, fun hb => ⟨by simp, fun n hn => ?_⟩⟩
        subst hb
        obtain ⟨sc, hsc, h1, h2, h3⟩ := (mem_comparedNames scenarios s n).mp hn
        obtain ⟨f, hf, hfs, e, he, _⟩ := hs sc hsc h3 (h1 ▸ hl)
        have := entriesIn_of_mem folders uniqueFolders f hf
        rw [hfs, h1, h0] at this
        rw [← this] at he
        exact absurd he List.not_mem_nil
      · rw [hfe]
        subst hfs
        refine ⟨fun e he => ?_, fun hb => ⟨fun e he n hn => ?_, fun n hn => ?_⟩⟩
        · obtain ⟨n, hn, _⟩ := hp f hf e he
          simp [hn]
        · subst hb
          obtain ⟨n', hn', hl' | ⟨_, hsc⟩⟩ := hp f hf e he
          · rw [hl] at hl'; cases hl'
          · rw [hn] at hn'; cases hn'
            exact (mem_scenarioNames scenarios f.service n).mpr hsc
        · subst hb
          obtain ⟨sc, hsc, h1, h2, h3⟩ := (mem_comparedNames scenarios f.service n).mp hn
          obtain ⟨f', hf', hfs', e, he, hen⟩ := hs sc hsc h3 (h1 ▸ hl)
          have h' := entriesIn_of_mem folders uniqueFolders f' hf'
          rw [hfs', h1, hfe] at h'
          exact ⟨e, h' ▸ he, h2 ▸ hen⟩

end Tazuna.Thm.Verify.Pairing
