import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Meta.Tactic.Simp.SimpTheorems
import Tazuna.Cli.Test
import Tazuna.Cli.Prove
import Tazuna.Semantics.After
import Tazuna.Smt.Prove
import Tazuna.Smt.Cover
import Tazuna.Smt.Cti
import Tazuna.Ir.Examples
import Tazuna.Semantics.Eval
import Tazuna.Semantics.StepExamples
import Tazuna.Semantics.Reach
import Tazuna.Semantics.PendingInv
import Tazuna.Semantics.PendingPerm
import Tazuna.Semantics.Settle
import Tazuna.Semantics.Interleave
import Tazuna.Semantics.NoTimer
import Tazuna.Semantics.StepRename
import Tazuna.Smt.Commute
import Tazuna.Smt.Pairs
import Tazuna.Smt.FiresForward
import Tazuna.Smt.Pair
import Tazuna.Semantics.Fire
import Tazuna.Smt.Step
import Tazuna.Smt.Bounds
import Tazuna.Smt.ServiceLayout
import Tazuna.Smt.CheckedState
import Tazuna.Smt.NoGap
import Tazuna.Smt.StepNoGap
import Tazuna.Smt.StepSites
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
  for n in [``Tazuna.Smt.step_encode, ``Tazuna.Smt.boundReached_iff, ``Tazuna.Smt.verdict_sound,
      ``Tazuna.Smt.within_sound, ``Tazuna.Smt.cti_sound, ``Tazuna.Smt.diamond_confluent,
      ``Tazuna.Smt.runs_confluent, ``Tazuna.Smt.ownPairs_complete, ``Tazuna.Smt.pairs_sound,
      ``Tazuna.Ir.Step.timerForward_of_noTimer] do
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
    -- The cascade's codes condition `step_encode` assumes holds exactly when every own kind's functions fit.
    ``Tazuna.Smt.step_sites,
    -- T3: a model's values decode to a state a run reaches, and the well-formedness holds of decoded values.
    ``Tazuna.Smt.decode_run, ``Tazuna.Smt.wf_decode,
    -- What check hands prove: `Checked` of every service and a named, declared handle from a check with no finding.
    ``Tazuna.Smt.check_ok, ``Tazuna.Smt.handles_ok,
    -- SMT-LIB text: printing then parsing gives the terms and values back, and shared definitions keep the meaning.
    ``Tazuna.Smt.Term.parse_print, ``Tazuna.Smt.Val.parse_print, ``Tazuna.Smt.shared_agrees,
    ``Tazuna.Smt.shared_conservative,
    -- The compiled printer appends to a string in place; it is the printer the theorems above are about.
    ``Tazuna.Smt.SExp.print_eq_printFast,
    -- The service's layout, derived from its program: the step environment and the wire-id invariant's term are found,
    -- and every create fits its table's slots.
    ``Tazuna.Smt.stepEnv_ofService, ``Tazuna.Smt.pendingBelowT_ofService, ``Tazuna.Smt.atMost_le_count,
    -- In a checked service's layout, a state within the slots embeds, so a script without a model has no state within
    -- the bounds, and the state's well-formedness term is always built.
    ``Tazuna.Smt.embedState_ofService, ``Tazuna.Smt.wf_ofService,
    -- In each service's layout, the step encoding meets no layout gap: refusals are the spec's, never the builder's.
    ``Tazuna.Smt.encodeStep_ofService,
    -- T4: unsat answers to every input kind's bound question and its questions about the rules named n mean no step
    -- within the slots of a run from an initial state whose invariants hold faults naming n.
    ``Tazuna.Smt.verdict_sound,
    -- What Prove.withinBounds says: unsat questions about the rules named n, whatever the bound questions answer, mean
    -- no step of such a run that stays within the slots faults naming n.
    ``Tazuna.Smt.within_sound,
    -- A counterexample is honest: a model of a target question decodes to a state with the step invariant and every
    -- invariant holding, whose step in Lean is the one the terms say.
    ``Tazuna.Smt.cti_sound,
    -- T5: where every two waiting own effects commute in the canonical sense and timers fire forward, every order of
    -- a cascade and of a clock line's timers ends as the semantics' order does, up to renaming, or both fault.
    ``Tazuna.Smt.diamond_confluent,
    -- T5 for runs: those cascades are every cascade a run on valid inputs starts, since valid inputs keep every name
    -- of a state below its counter.
    ``Tazuna.Smt.runs_confluent,
    -- T5's pair questions, one per ordered pair of own kinds: unsat answers to a pair's two questions mean its two
    -- effects commute in the canonical sense from every state a model decodes to whose names are below its counter;
    -- over every listed pair, any two own effects a model codes (T5b, `ownPairs_complete`).
    ``Tazuna.Smt.pairs_sound,
    -- A pair question's condition holds exactly when every internal step its two orders run fits the slots, so its
    -- bound question decides proved against within the bounds honestly. For the per-line soundness of pair lines
    -- (not yet built), as the reach check's own precedent for a theorem whose user is the next unit.
    ``Tazuna.Smt.pair_fits,
    -- T5's timer questions, one per timer machine: a model is a context whose timer falls back, so timers do not fire
    -- forward; unsat answers mean no context within the slots has one.
    ``Tazuna.Smt.back_violates, ``Tazuna.Smt.back_sound]
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
