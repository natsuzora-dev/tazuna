import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Tazuna.Cli.Check
import Tazuna.Ir.Examples
import Tazuna.Semantics.Eval
import Tazuna.Semantics.StepExamples

/-! Every declaration of the engine rests on Lean's standard axioms only, so no `sorry` or added axiom hides a gap. The
build fails otherwise. -/

open Lean Elab Command in
elab "#check_tazuna_axioms" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (n, _) in env.constants.toList do
    unless (`Tazuna).isPrefixOf n do continue
    checked := checked + 1
    for a in ← liftCoreM (collectAxioms n) do
      unless allowed.contains a do throwError "{n} depends on the axiom {a}"
  if checked == 0 then throwError "no Tazuna declarations found"

#check_tazuna_axioms
