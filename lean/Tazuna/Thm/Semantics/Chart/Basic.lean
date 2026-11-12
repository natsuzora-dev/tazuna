import Tazuna.Semantics.Chart.Basic
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Syntax.Shape

namespace Tazuna.Thm.Semantics.Chart.Basic

open Tazuna.Data Tazuna.Semantics
open Tazuna.Syntax (chartTree plainName stateTree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Syntax.Shape

theorem tree_names (c : Chart) : c.tree.states.map (·.name) = c.states.map (·.name) := by
  simp [Chart.tree, List.map_map, Function.comp_def, ChartState.shape]

theorem toExec_ok (c : Syntax.Chart) (service name : String) (order : Nat) (screen opened : Bool)
    (x : Tazuna.Semantics.Chart) (h : c.toExec service name order screen opened = .ok x) :
    x.name = name ∧ x.screen = screen ∧ x.opened = opened := by
  unfold Syntax.Chart.toExec at h
  dsimp only at h
  split at h
  · obtain ⟨_, ha, _⟩ := except_bind_ok h
    cases ha
  · obtain ⟨_, _, h⟩ := except_bind_ok h
    obtain ⟨_, _, h⟩ := except_bind_ok h
    cases h
    exact ⟨rfl, rfl, rfl⟩

end Tazuna.Thm.Semantics.Chart.Basic
