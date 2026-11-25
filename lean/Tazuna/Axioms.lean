import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Meta.Tactic.Simp.SimpTheorems
import Tazuna.Cli.Test
import Tazuna.Ir.Examples
import Tazuna.Semantics.Eval
import Tazuna.Semantics.StepExamples
import Tazuna.Semantics.Reach
import Tazuna.Semantics.PendingInv
import Tazuna.Semantics.PendingPerm
import Tazuna.Semantics.Settle
import Tazuna.Semantics.Fire
import Tazuna.Smt.Step
import Tazuna.Smt.Bounds
import Tazuna.Smt.ServiceLayout
import Tazuna.Smt.Solver
import Tazuna.Trace.Line
import Tazuna.Trace.WireThm

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
  -- The theorems the engine's answers rest on: a double-backquoted name that no longer exists fails to elaborate.
  for n in [``Tazuna.Smt.step_encode, ``Tazuna.Smt.boundReached_iff] do
    unless env.contains n do throwError "{n} is missing"

#check_tazuna_axioms

/-- Whether a theorem is one Lean generates for a definition or a structure, rather than one written in the source. -/
def generatedTheorem (env : Lean.Environment) : Lean.Name → Bool
  | n@(.str p s) => s.startsWith "eq_" || s ∈ ["eq", "inj", "injEq", "sizeOf_spec", "congr_simp"] || n.isInternal ||
    (Lean.getStructureInfo? env p).any (·.fieldNames.contains (.mkSimple s))
  | _ => true

/-! Every theorem of the SMT layer is used by a root: a theorem the engine's answers rest on, or one listed below for
what U10 will use. A theorem nothing uses is dead or has lost its user, as the step's exactness did when per-kind
theorems were deleted without notice. `simp` uses a lemma proved by `rfl` without naming it in the proof, so those
are not checked. -/

open Lean Elab Command in
elab "#check_tazuna_reach" : command => do
  let env ← getEnv
  let roots := [
    -- T2 for every step kind, and the bound-reached condition the step scripts ask.
    ``Tazuna.Smt.step_encode, ``Tazuna.Smt.boundReached_iff,
    -- T3: a model's values decode to a state a run reaches, and the well-formedness holds of decoded values.
    ``Tazuna.Smt.decode_run, ``Tazuna.Smt.wf_decode,
    -- What check hands prove: `Checked` of every service from a check with no finding.
    ``Tazuna.Smt.check_ok,
    -- SMT-LIB text: printing then parsing gives the terms and values back, and shared definitions keep the meaning.
    ``Tazuna.Smt.Term.parse_print, ``Tazuna.Smt.Val.parse_print, ``Tazuna.Smt.shared_agrees,
    ``Tazuna.Smt.shared_conservative,
    -- The service's layout, derived from its program: the step environment and the wire-id invariant's term are found,
    -- and every create fits its table's slots.
    ``Tazuna.Smt.stepEnv_ofService, ``Tazuna.Smt.pendingBelowT_ofService, ``Tazuna.Smt.atMost_le_count,
    -- For U10, which asserts well-formedness, the wire-id invariant and the create bounds: each loses no model.
    ``Tazuna.Smt.wf_of_decode, ``Tazuna.Smt.wf_of_decodeState, ``Tazuna.Smt.pendingBelow_iff]
  let mut used : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if used.contains n then continue
    used := used.insert n
    let some ci := env.find? n | throwError "{n} is missing"
    let next := match ci with
      | .thmInfo t => ci.getUsedConstantsAsSet.toList ++ t.all
      | _ => ci.getUsedConstantsAsSet.toList
    todo := next.filter (!used.contains ·) ++ todo
  let mut unused := #[]
  for (n, ci) in env.constants.toList do
    unless (`Tazuna.Smt).isPrefixOf n && ci matches .thmInfo _ do continue
    if used.contains n || generatedTheorem env n then continue
    if (← liftCoreM (Meta.isRflTheorem n)) then continue
    unused := unused.push n
  unless unused.isEmpty do
    throwError "no root uses these theorems; delete them or name their user: {unused.qsort (·.toString < ·.toString)}"

#check_tazuna_reach
