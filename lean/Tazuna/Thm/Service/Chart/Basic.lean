import Tazuna.Service.Chart.Basic
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Spec.Shape

namespace Tazuna.Thm.Service.Chart.Basic

open Tazuna.Data Tazuna.Service
open Tazuna.Spec (chartTree stateTree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Spec.Shape

theorem tree_names (c : Chart) : c.tree.states.map (·.name) = c.states.map (·.name) := by
  simp [Chart.tree, List.map_map, Function.comp_def, ChartState.shape]

theorem ofSpec_ok (c : Spec.Chart) (service name : String) (order : Nat) (screen opened : Bool)
    (x : Tazuna.Service.Chart) (h : Chart.ofSpec c service name order screen opened = .ok x) :
    x.name = name ∧ x.screen = screen ∧ x.opened = opened := by
  unfold Chart.ofSpec at h
  dsimp only at h
  split at h
  · obtain ⟨_, ha, _⟩ := except_bind_ok h
    cases ha
  · obtain ⟨_, _, h⟩ := except_bind_ok h
    obtain ⟨_, _, h⟩ := except_bind_ok h
    cases h
    exact ⟨rfl, rfl, rfl⟩

end Tazuna.Thm.Service.Chart.Basic
