import Tazuna.Service.Chart.Basic
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Spec.Shape

namespace Tazuna.Thm.Service.Chart.Basic

open Tazuna.Data Tazuna.Service
open Tazuna.Spec (chartTree stateTree)
open Tazuna.Thm.Data.Basic Tazuna.Thm.Spec.Shape

theorem tree_names (c : Chart) : c.tree.states.map (·.name) = c.states.map (·.name) := by
  simp [Chart.tree, List.map_map, Function.comp_def, ChartState.shape]

end Tazuna.Thm.Service.Chart.Basic
