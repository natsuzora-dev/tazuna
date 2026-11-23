import Tazuna.Semantics.Service.Chart.Basic
import Tazuna.Thm.Semantics.Value.Basic
import Tazuna.Thm.Ir.Shape

namespace Tazuna.Thm.Semantics.Service.Chart.Basic

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Ir (chartTree stateTree)
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Ir.Shape

theorem tree_names (c : Service.Chart) : c.tree.states.map (·.name) = c.states.map (·.spec.name) := by
  simp [Service.Chart.tree, List.map_map, Function.comp_def, ChartState.shape, Ir.State.shape]

end Tazuna.Thm.Semantics.Service.Chart.Basic
