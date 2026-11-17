import Tazuna.Thm.Data.Pairing
import Tazuna.Thm.Verify.Canonical
import Tazuna.Thm.Verify.Pairing
import Tazuna.Verify.Snapshot

namespace Tazuna.Thm.Verify.Snapshot

open Tazuna.Data Tazuna.Thm.Data.Pairing Tazuna.Thm.Verify.Canonical Tazuna.Thm.Verify.Pairing Tazuna.Verify

theorem numbered_values (snapshot : List (Option Value)) :
    (numbered snapshot).map (·.2) = snapshot.filterMap id := by
  unfold numbered
  suffices h : ∀ n, ((snapshot.zipIdx n).filterMap fun (v, k) => v.map (k, ·)).map (·.2) = snapshot.filterMap id from
    h 1
  induction snapshot with
  | nil => intro n; rfl
  | cons v vs ih => intro n; cases v <;> simp [List.zipIdx_cons, ih]

theorem compareSnapshot_eq_none_iff (snapshot : List (Option Value)) (run : List Value) :
    compareSnapshot snapshot run = none ↔ (snapshot.filterMap id).map Value.canonical = run.map Value.canonical := by
  rw [← numbered_values, List.map_map]
  simp only [compareSnapshot, Option.map_eq_none_iff, List.find?_eq_none, List.mem_range, decide_eq_true_eq,
    Classical.not_not]
  constructor
  · intro h
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hi : i < max (numbered snapshot).length run.length
    · exact h i hi
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      rfl
  · intro h i _
    have := congrArg (·[i]?) h
    simp only [List.getElem?_map] at this
    exact this

theorem compareSnapshot_reordered (snapshot : List (Option Value)) (run : List Value)
    (h : ReorderedList (snapshot.filterMap id) run) : compareSnapshot snapshot run = none := by
  rw [compareSnapshot_eq_none_iff, ← canonicalList_eq, ← canonicalList_eq]
  exact h.canonical_eq

theorem pairSnapshots_nil_iff (services : List String) (scenarios : List Scenario) (folders : List Folder) :
    (pairSnapshots services scenarios folders).violations = [] ↔
      ∀ s ∈ services,
        (∀ e ∈ entriesIn folders s, ∃ sc ∈ scenarios, sc.service = s ∧ fileName e = some sc.name) ∧
          ∀ sc ∈ scenarios, sc.service = s → sc.compared = true →
            ∃ e ∈ entriesIn folders s, fileName e = some sc.name := by
  simp only [pairSnapshots, List.flatMap_eq_nil_iff, List.forall_mem_map]
  refine forall_congr' fun s => imp_congr_right fun _ => ?_
  simp only [snapshotPairing, List.append_eq_nil_iff, List.map_eq_nil_iff, missing_nil, unknown_nil, extra_nil,
    mem_comparedNames, mem_scenarioNames]
  constructor
  · rintro ⟨⟨hm, hu⟩, hx⟩
    refine ⟨fun e he => ?_, fun sc hs h1 h2 => hm sc.name ⟨sc, hs, h1, rfl, h2⟩⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hu e he)
    obtain ⟨sc, hs, h1, h2⟩ := hx e he n hn
    exact ⟨sc, hs, h1, h2 ▸ hn⟩
  · rintro ⟨he, hm⟩
    refine ⟨⟨fun n ⟨sc, hs, h1, h2, h3⟩ => h2 ▸ hm sc hs h1 h3, fun e h => ?_⟩, fun e h n hn => ?_⟩
    · obtain ⟨sc, _, _, hn⟩ := he e h
      simp [hn]
    · obtain ⟨sc, hs, h1, h2⟩ := he e h
      rw [hn] at h2
      cases h2
      exact ⟨sc, hs, h1, rfl⟩

end Tazuna.Thm.Verify.Snapshot
