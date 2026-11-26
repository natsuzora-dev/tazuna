import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Meta.Tactic.Simp.SimpTheorems
import Tazuna.Cli.Test
import Tazuna.Cli.Prove
import Tazuna.Cli.Generate
import Tazuna.Semantics.After
import Tazuna.Smt.Prove
import Tazuna.Smt.Cover
import Tazuna.Smt.Cti
import Tazuna.Ir.Examples
import Tazuna.Semantics.Eval
import Tazuna.Semantics.StepExamples
import Tazuna.Semantics.RunExamples
import Tazuna.Semantics.Reach
import Tazuna.Semantics.PendingInv
import Tazuna.Semantics.Settle
import Tazuna.Semantics.Interleave
import Tazuna.Semantics.NoTimer
import Tazuna.Semantics.StepRename
import Tazuna.Smt.Timer
import Tazuna.Smt.Pair
import Tazuna.Smt.PairLine
import Tazuna.Smt.Lines
import Tazuna.Smt.Runs
import Tazuna.Smt.Sorts
import Tazuna.Smt.DecodeTotal
import Tazuna.Smt.GenGoal
import Tazuna.Smt.RespGoal
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
import Tazuna.Trace.Examples

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

/-- Whether a theorem is one Lean generates for a definition, an inductive type or a structure, rather than one written
in the source. -/
def generatedTheorem (env : Lean.Environment) : Lean.Name → Bool
  | n@(.str p s) => s.startsWith "eq_" ||
    s ∈ ["eq", "inj", "injEq", "sizeOf_spec", "congr_simp", "brecOn", "ofNat_ctorIdx"] || n.isInternal ||
    (Lean.getStructureInfo? env p).any (·.fieldNames.contains (.mkSimple s))
  | _ => true

/-! Every theorem of tazuna is used by a root: what the engine runs, a theorem its answers rest on, or a statement of
meaning a reader checks the definitions against. A theorem nothing uses is dead or has lost its user, as the step's
exactness did when per-kind theorems were deleted without notice. A root another root uses is not a root: listing it
would keep it alive after the top statement stops using it, so the check fails on it too. `simp` uses a lemma proved
by `rfl` without naming it in the proof, so those are not checked. -/

open Lean Elab Command in
elab "#check_tazuna_reach" : command => do
  let env ← getEnv
  let roots := [
    -- What the engine runs: each command, and the lists the e2e harness and gen-dsl print, which hold every output
    -- kind, built-in and DSL type.
    ``Tazuna.Cli.check, ``Tazuna.Cli.test, ``Tazuna.Cli.verify, ``Tazuna.Cli.prove, ``Tazuna.Cli.optionsOf,
    ``Tazuna.Cli.generate,
    ``Tazuna.Kind.mem_all, ``Tazuna.Ir.Prim.mem_all, ``Tazuna.Ir.Dsl.mem_all,
    -- Gleam's meaning where languages differ, and literals: reading back a printed literal gives it back.
    ``Tazuna.Gleam.div_zero, ``Tazuna.Gleam.mod_zero, ``Tazuna.Gleam.div_add_mod, ``Tazuna.Gleam.mod_neg_left,
    ``Tazuna.Gleam.mod_neg_right, ``Tazuna.Gleam.div_neg_right, ``Tazuna.Gleam.length_eq_codepoints,
    ``Tazuna.Ir.Ty.deq_bag_perm, ``Tazuna.Ir.Literal.parseInt_printInt, ``Tazuna.Ir.Literal.parseStr_printStr,
    -- Traces: reading back a written trace's header and lines, or a written value, gives it back, and a date label and
    -- its day number are one value, every day having a label.
    ``Tazuna.Trace.TraceFile.read_wires, ``Tazuna.Trace.dec_enc, ``Tazuna.Trace.DateThm.render_parse,
    -- The trace writer's names: a fresh id is never called by an outside id's name the run carries, and an outside id
    -- the writer was told of always has its own name.
    ``Tazuna.Trace.Names.bind_ok, ``Tazuna.Trace.Names.ok_avoid,
    -- A counterexample's `after` is the state the step reaches before its invariant check.
    ``Tazuna.Ir.step_settled,
    -- generate's targets, from the checked IR's rule names, miss no class of out line a step can show.
    ``Tazuna.Ir.targets_cover,
    -- generate writes distinct targets of distinct services to distinct files, so none overwrites or removes another's.
    ``Tazuna.Cli.targetFile_inj,
    -- The layout's roots read every kept function of a service: its structures are matched whole, field by field.
    ``Tazuna.Ir.rootUses_eq,
    -- The bound-reached condition the step scripts ask. T2 (`step_encode`) is what the verdict theorems below rest on.
    ``Tazuna.Smt.boundReached_iff,
    -- T3: a model's values decode to a state a run reaches.
    ``Tazuna.Smt.decode_run,
    -- SMT-LIB text: printing then parsing gives the values back (and the terms, which values rest on), and shared
    -- definitions keep the meaning.
    ``Tazuna.Smt.Val.parse_print, ``Tazuna.Smt.shared_agrees,
    ``Tazuna.Smt.shared_conservative,
    -- The compiled printer appends to a string in place; it is the printer the theorems above are about.
    ``Tazuna.Smt.SExp.print_eq_printFast,
    -- Compiled code evaluates a term with each shared term once, and compares terms stopping at shared terms that are
    -- one object; they are the evaluation and equality the theorems are about.
    ``Tazuna.Smt.Term.denote_eq_denoteFast, ``Tazuna.Smt.Term.beq_eq_beqFast,
    -- Compiled code extends a script's shared definitions in place; it is the extension the sharing theorems are about.
    ``Tazuna.Smt.Defs.add_eq_addFast,
    -- The service's layout, derived from its program: every create fits its table's slots. (The commands read every
    -- script builder through `Sound.get` with its no-gap theorem, so those are the commands' own: `unrollBase_ofService`,
    -- `questions_ofService`, `timerQuestions_ofService`, `pairQuestions_ofService`, `respGoalE_ofService`.)
    ``Tazuna.Smt.atMost_le_count,
    -- In a checked service's layout, a state within the slots embeds, so a script without a model has no state within
    -- the bounds.
    ``Tazuna.Smt.embedState_ofService,
    -- T4: where every input kind's questions about the rules named n are unsat, and its bound question is unsat or
    -- the step fits the slots (Prove.withinBounds), no step within the slots of a run from an initial state whose
    -- invariants hold faults naming n.
    ``Tazuna.Smt.fault_sound,
    -- A counterexample is honest: a model of a target question decodes to a state with the step invariant and every
    -- invariant holding, whose step in Lean is the one the terms say.
    ``Tazuna.Smt.cti_sound,
    -- T5 for runs, scoped to the slots: from the initial state on valid inputs, where each step and pair line reads
    -- proved, or within the bounds where the steps it names fit, and each timer line reads proved, every order of every
    -- cascade a step starts, and of every clock line's timers, ends as the semantics' order does, up to renaming, or
    -- both fault. Its chain: `cascade_lines` and `timers_lines` (Smt/Lines), `Step.cascade_agrees` and
    -- `Step.timers_agree` (Semantics), `Diamond.runs_agree` (Semantics/Diamond).
    ``Tazuna.Smt.run_lines,
    -- A timer line's counterexample is honest: a model is a context whose timer falls back, so timers do not fire
    -- forward.
    ``Tazuna.Smt.timer_violates,
    -- A pair line's counterexample whose orders show a disabling or a fault in one order only is honest: the pair does
    -- not commute. Orders that end differently under every renaming searched are not covered.
    ``Tazuna.Smt.pair_violates,
    -- No unsat answer is free and none is out of reach: `Unsat` asks that the sorts hold values, and the sorts of every
    -- question an encoder builds in a layout whose datatypes have sorts (as `Layout.ofParts`'s, `sorted_ofParts`) do.
    ``Tazuna.Smt.questions_sorts, ``Tazuna.Smt.pair_sorts, ``Tazuna.Smt.timer_sorts,
    -- Every model a question family's report reads decodes: a model of the family's context whose variables hold values
    -- of their sorts decodes to the state, input, effects or instance context the report shows, so prove's "does not
    -- decode" lines are unreachable.
    ``Tazuna.Smt.questions_decode, ``Tazuna.Smt.pair_decode, ``Tazuna.Smt.timer_decode,
    -- A model generate finds is a run to its target: every model's steps decode to inputs whose run from the
    -- initial state takes the kinds the model picks and faults nowhere (`unroll_decode`), and its last step answers
    -- in the target's class.
    ``Tazuna.Smt.generate_sound,
    -- T6: a trace generate writes reaches its target: verify replays its lines as passed, and its last step answers
    -- in the target's class.
    ``Tazuna.Cli.generate_reaches,
    -- T6b: generate's "unreached within k steps": where its script at a depth has no model, no run of that many valid
    -- inputs within the slots that faults nowhere answers at its last step in the target's class (from
    -- `runs_covered`: every such run is a model of every assertion but the goal).
    ``Tazuna.Smt.generate_unreached,
    -- T7: a bounded response "within the bounds": where prove's script for it at a depth has no model, no run of that
    -- many valid inputs within the slots, faulting nowhere, with timely clock lines and the response's functions
    -- fitting at its events, violates it (from `runs_covered`).
    ``Tazuna.Smt.response_within,
    -- A response's model decodes to a run from the initial state with timely clock lines that violates it.
    ``Tazuna.Smt.response_sound]
  let mut used : NameSet := {}
  let mut usedByOther : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if used.contains n then continue
    used := used.insert n
    let some ci := env.find? n | throwError "{n} is missing"
    -- A theorem proved in a mutual block uses the block's other theorems; that use is not another root's.
    let block := match ci with
      | .thmInfo t => t.all
      | _ => [n]
    let uses := ci.getUsedConstantsAsSet.toList
    usedByOther := uses.foldl (fun acc m => if !block.contains m && roots.contains m then acc.insert m else acc)
      usedByOther
    todo := (uses ++ block).filter (!used.contains ·) ++ todo
  let inner := roots.filter usedByOther.contains
  unless inner.isEmpty do
    throwError "another root uses these roots, so they are not tops; drop them from the roots: {inner}"
  let mut unused := #[]
  for (n, ci) in env.constants.toList do
    unless (`Tazuna).isPrefixOf n && ci matches .thmInfo _ do continue
    if used.contains n || generatedTheorem env n then continue
    if (← liftCoreM (Meta.isRflTheorem n)) then continue
    unused := unused.push n
  unless unused.isEmpty do
    throwError "no root uses these theorems; delete them or name their user: {unused.qsort (·.toString < ·.toString)}"

#check_tazuna_reach
