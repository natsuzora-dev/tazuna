import Tazuna.Data.Group
import Tazuna.Service.Message

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/--
A result, found while the run evaluates, that depends on an order the spec does not fix: the order of parallel regions.
No `BagOrderDependent` violation halts the run. `definition` is the chart of the conflicting transitions.
-/
inductive BagOrderDependent where
  /--
  Two transitions in parallel regions of `state`, taken on one event, both assign the context field `field`, so the
  result depends on the order of the regions.
  -/
  | bothAssign (definition : Spec.Ref) (state : String) (firstTransition secondTransition : Spec.TransitionRef)
      (field : String)
  /--
  The transition `writer` in one parallel region of `state` assigns the context field `field`, which the transition
  `reader` in another region, taken on the same event, reads, so the result depends on the order of the regions.
  -/
  | assignRead (definition : Spec.Ref) (state : String) (writer reader : Spec.TransitionRef) (field : String)
deriving DecidableEq, Repr, Inhabited

derive_group BagOrderDependent

end Tazuna.Explore
