import Tazuna.Semantics.Instrument.Coverage
import Tazuna.Thm.Guarantee

/-! What `verify --coverage` reports: only parts outside the reached parts that the runs collect. -/

namespace Tazuna.Thm.Semantics.Instrument.Coverage

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Instrument

/-- `verify --coverage` reports only parts outside `reached`, the parts that the runs collect. -/
@[guarantee] theorem uncovered_unreached (spec : Ir.Structure) (reached : List Uncovered) (u : Uncovered)
    (h : u ∈ uncovered spec reached) : u ∉ reached := by
  simp only [uncovered, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨t, ⟨-, hr, -⟩, rfl⟩ := h
  simpa using hr

end Tazuna.Thm.Semantics.Instrument.Coverage
