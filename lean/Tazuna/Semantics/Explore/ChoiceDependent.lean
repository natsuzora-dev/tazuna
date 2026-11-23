import Tazuna.Ir.Group
import Tazuna.Semantics.Service.Step

namespace Tazuna.Semantics.Explore

open Tazuna.Ir Tazuna.Semantics.Service

/--
A result that depends on an order that no line writes, which prove finds: the order of two steps that can be pending
together, of two deadlines due at one time, or of two messages that arrive at once.
-/
inductive ChoiceDependent where
  /--
  Taking `firstStep` then `secondStep` from one state ends with `original`, and taking `secondStep` first ends with
  `alternative`. `definition` is the definition of the first step.
  -/
  | stepOrder (definition : Ir.Ref) (firstStep secondStep : StepName) (original alternative : Value)
deriving Repr, Inhabited

derive_group ChoiceDependent

end Tazuna.Semantics.Explore
