import Tazuna.Data.Group
import Tazuna.Service.Message

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/--
A result, found while the run evaluates, that depends on an order the spec does not fix. No `BagOrderDependent`
violation halts the run. In `reversedException`, `reversedResult`, and `uncomparable`, `test` ran the spec function
`function` again with every `Bag` visiting its values in reverse order. `definition` is the definition whose code holds
the function: the command, query, automation, entity, or chart. In `bothAssign` and `assignRead`, `definition` is the
chart of the conflicting transitions.
-/
inductive BagOrderDependent where
  /--
  The second run of the function, or the check of a query's output or of its comparable value after it, failed. It
  threw, gave a value that does not match its schema, read a held value that its state does not hold, or called
  `only()` on more than one value.
  -/
  | reversedException (definition : Spec.Ref) (function : String)
  /-- The result of the second run differs from the first. -/
  | reversedResult (definition : Spec.Ref) (function : String)
  /--
  Comparing the second result with the first held more than `limit` (`bindingLimit`) bindings of the keys that the
  results created, so whether they differ is not known.
  -/
  | uncomparable (definition : Spec.Ref) (function : String) (limit : Nat)
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
