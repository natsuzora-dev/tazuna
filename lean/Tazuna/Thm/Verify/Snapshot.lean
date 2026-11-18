import Tazuna.Thm.Data.Pairing
import Tazuna.Thm.Data.Canonical
import Tazuna.Thm.Verify.Pairing
import Tazuna.Verify.Snapshot

namespace Tazuna.Thm.Verify.Snapshot

open Tazuna.Data Tazuna.Thm.Data.Pairing Tazuna.Thm.Data.Canonical Tazuna.Thm.Verify.Pairing Tazuna.Verify

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

end Tazuna.Thm.Verify.Snapshot
