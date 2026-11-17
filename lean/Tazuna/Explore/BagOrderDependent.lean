import Tazuna.Data.Group
import Tazuna.Service.Message

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/--
A result, found while the run evaluates, that depends on an order the spec does not fix. No BagOrderDependent violation
halts the run. In reversedException and reversedResult, orderAudit asked the question `function` of Functions again,
with every Bag visiting its values in reverse order, and `definition` is the definition whose code answers it: the
command, query, automation, entity, or chart; so too in uncomparable. In bothAssign and assignRead, it is the chart of the conflicting
transitions.
-/
inductive BagOrderDependent where
  /-- An Issue stopped the second answer, or the check of a query's output or its comparable value. -/
  | reversedException (definition : Spec.Ref) (function : String)
  /-- The second answer differs from the first. -/
  | reversedResult (definition : Spec.Ref) (function : String)
  /--
  Comparing the second answer with the first held more than `limit` (bindingLimit) renamings of the keys that the
  answers created: too many renaming candidates to compare, so whether they differ is not known.
  -/
  | uncomparable (definition : Spec.Ref) (function : String) (limit : Nat)
  | bothAssign (definition : Spec.Ref) (state : String) (firstTransition secondTransition : Spec.TransitionRef)
      (field : String)
  | assignRead (definition : Spec.Ref) (state : String) (writer reader : Spec.TransitionRef) (field : String)
deriving DecidableEq, Repr, Inhabited

derive_group BagOrderDependent

end Tazuna.Explore
