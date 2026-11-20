import Tazuna.Explore.Coverage
import Tazuna.Thm.Guarantee

/-! What `test --coverage` reports: only parts outside the reached parts that the runs collect. -/

namespace Tazuna.Thm.Explore.Coverage

open Tazuna.Data Tazuna.Service Tazuna.Explore

theorem requestsUncovered_unreached (reached : List Uncovered) (d : Spec.Definition) (u : Uncovered)
    (h : u ∈ requestsUncovered reached d) : u ∉ reached := by
  unfold requestsUncovered at h
  split at h <;> simp_all [List.mem_filter]

theorem automationUncovered_unreached (reached : List Uncovered) (d : Spec.Definition) (u : Uncovered)
    (h : u ∈ automationUncovered reached d) : u ∉ reached := by
  unfold automationUncovered at h
  split at h <;> simp_all [List.mem_filter]

theorem chartUncovered_unreached (reached : List Uncovered) (d : Spec.Definition) (u : Uncovered)
    (h : u ∈ chartUncovered reached d) : u ∉ reached := by
  unfold chartUncovered at h
  split at h
  · simpa using (List.mem_filter.mp h).2
  · simpa using (List.mem_filter.mp h).2
  · simp at h

/-- `test --coverage` reports only parts outside `reached`, the parts that the runs collect. -/
@[guarantee] theorem uncovered_unreached (spec : Spec.Structure) (reached : List Uncovered) (u : Uncovered)
    (h : u ∈ uncovered spec reached) : u ∉ reached := by
  simp only [uncovered, List.mem_append, List.mem_flatMap] at h
  rcases h with (⟨d, -, h⟩ | ⟨d, -, h⟩) | ⟨d, -, h⟩
  · exact requestsUncovered_unreached reached d u h
  · exact automationUncovered_unreached reached d u h
  · exact chartUncovered_unreached reached d u h

end Tazuna.Thm.Explore.Coverage
