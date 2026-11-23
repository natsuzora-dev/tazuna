import Tazuna.Ir.Group
import Tazuna.Ir.Structure

namespace Tazuna.Semantics.Explore

open Tazuna.Ir

/--
A check of `test` that reached a limit that tazuna sets before it could decide, so it neither reports the violation
that the check looks for nor rules it out, as an SMT solver answers unknown. `definition` is where the check stopped.
-/
inductive Undecided where
  /--
  The search of the step orders of one processing ran `limit` (`stepOrderLimit`) orders and stopped with orders left,
  so a `ChoiceDependent` violation that only those orders show is not reported. `definition` is the definition of the
  first step of the first pair that the search swapped.
  -/
  | stepOrderLimit (definition : Ir.Ref) (limit : Nat)
  /--
  Comparing the states of two step orders whose first steps run `definition` held more than `limit` (`bindingLimit`)
  bindings of created keys at one step, so whether the order changes the state is not known.
  -/
  | stepOrderBindings (definition : Ir.Ref) (limit : Nat)
deriving Repr, Inhabited

derive_group Undecided

end Tazuna.Semantics.Explore
