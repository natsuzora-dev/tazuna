import Tazuna.Ir.Group
import Tazuna.Semantics.Service.Message

namespace Tazuna.Semantics.Instrument

open Tazuna.Ir Tazuna.Semantics.Service

/--
A result, found while the run evaluates, that depends on an order the spec does not fix: the order of parallel regions.
No `RegionOrderDependent` violation halts the run. `definition` is the chart of the conflicting transitions.
-/
inductive RegionOrderDependent where
  /--
  Two transitions in parallel regions of `state`, taken on one event, both assign the context field `field`, so the
  result depends on the order of the regions.
  -/
  | bothAssign (definition : Ir.Ref) (state : String) (firstTransition secondTransition : Ir.TransitionRef)
      (field : String)
  /--
  The transition `writer` in one parallel region of `state` assigns the context field `field`, which the transition
  `reader` in another region, taken on the same event, reads, so the result depends on the order of the regions.
  -/
  | assignRead (definition : Ir.Ref) (state : String) (writer reader : Ir.TransitionRef) (field : String)
deriving DecidableEq, Repr, Inhabited

derive_group RegionOrderDependent

end Tazuna.Semantics.Instrument
