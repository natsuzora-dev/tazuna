import Tazuna.Semantics.Service.Chart.Basic

namespace Tazuna.Semantics.Service

open Tazuna.Ir

def Chart.exitsOf (c : Chart) (entered : List String) (t : Transition) : List String :=
  match t.target with
  | none => []
  | some target => c.tree.exitSet entered t.source target t.reenter

def Chart.slots (c : Chart) : List String :=
  c.states.foldl (fun acc st => (st.activities.filter (·.isShows)).foldl (fun acc a => addName acc a.key) acc) []

end Tazuna.Semantics.Service
