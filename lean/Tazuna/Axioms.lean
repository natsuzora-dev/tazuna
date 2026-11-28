import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Meta.Tactic.Simp.SimpTheorems
import Tazuna.Cli.Test
import Tazuna.Cli.Prove
import Tazuna.Cli.Generate
import Tazuna.Cli.Explore
import Tazuna.Explore.Link
import Tazuna.Cli.Explain
import Tazuna.Semantics.After
import Tazuna.Smt.Prove
import Tazuna.Smt.Reached
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
import Tazuna.Semantics.StepSame
import Tazuna.Smt.Timer
import Tazuna.Smt.Pair
import Tazuna.Smt.PairLine
import Tazuna.Smt.Lines
import Tazuna.Smt.Runs
import Tazuna.Smt.Sorts
import Tazuna.Smt.DecodeTotal
import Tazuna.Smt.GenGoal
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
    ``Tazuna.Cli.generate, ``Tazuna.Cli.explore, ``Tazuna.Cli.explain,
    ``Tazuna.Kind.mem_all, ``Tazuna.Ir.Prim.mem_all, ``Tazuna.Ir.Dsl.mem_all,
    -- Gleam's meaning where languages differ, and literals: reading back a printed literal gives it back.
    ``Tazuna.Gleam.div_zero, ``Tazuna.Gleam.mod_zero, ``Tazuna.Gleam.div_add_mod, ``Tazuna.Gleam.mod_neg_left,
    ``Tazuna.Gleam.mod_neg_right, ``Tazuna.Gleam.div_neg_right, ``Tazuna.Gleam.length_eq_codepoints,
    ``Tazuna.Ir.Ty.deq_bag_perm, ``Tazuna.Ir.Literal.parseInt_printInt, ``Tazuna.Ir.Literal.parseStr_printStr,
    -- Traces: reading back a written trace's header and lines gives them back. (Reading back a written value,
    -- `dec_enc`, is T6's.)
    ``Tazuna.Trace.TraceFile.read_wires,
    -- verify, unless out of tries, passes a trace exactly when one bijection of ids reads every window as the spec's,
    -- each out line decoding to the spec's (a date label and its day number being one value, `render_parse`).
    ``Tazuna.Trace.replay_iff,
    -- A counterexample's `after` is the state the step reaches before its invariant check.
    ``Tazuna.Ir.step_settled,
    -- generate's targets, from the checked IR's rule names and the rejections each `decide`'s source may return, miss
    -- no class of out line a step can show.
    ``Tazuna.Ir.targets_cover,
    -- generate writes distinct targets of distinct services to distinct files, so none overwrites or removes another's.
    ``Tazuna.Cli.targetFile_inj,
    -- The layout's roots read every kept function of a service: its structures are matched whole, field by field.
    ``Tazuna.Ir.rootUses_eq,
    -- The bound-reached condition the step scripts ask. T2 (`step_encode`) is what the verdict theorems below rest on.
    ``Tazuna.Smt.boundReached_iff,
    -- T3: a model's values decode to a state a run reaches.
    ``Tazuna.Smt.decode_run,
    -- The solver reads names of ids from outside as codes (an unsat answer is the script's: `Unsat.noModel`); a model's
    -- codes read back as names in the codes' order, so the names keep what `<` said and stay distinct.
    ``Tazuna.Smt.nameOf_lt,
    -- SMT-LIB text: printing then parsing gives the values back (and the terms, which values rest on), and shared
    -- definitions keep the meaning.
    ``Tazuna.Smt.Val.parse_print, ``Tazuna.Smt.shared_agrees,
    -- The compiled printer appends to a string in place; it is the printer the theorems above are about.
    ``Tazuna.Smt.SExp.print_eq_printFast,
    -- Compiled code evaluates a term and checks assertions for references with each shared term once, and compares
    -- terms stopping at shared terms that are one object; they are the evaluation, check and equality the theorems
    -- are about.
    ``Tazuna.Smt.Term.denote_eq_denoteFast, ``Tazuna.Smt.Term.refFrees_eq_refFreesFast,
    ``Tazuna.Smt.Term.beq_eq_beqFast,
    -- Compiled code extends a script's shared definitions in place; it is the extension the sharing theorems are about.
    ``Tazuna.Smt.Defs.add_eq_addFast,
    -- Compiled code compares terms of the canonical order without serializing them; it is the order the theorems are
    -- about.
    ``Tazuna.Ir.Erl.cmp_eq_cmpFast,
    -- The service's layout, derived from its program: every create fits its table's slots. (The commands read every
    -- script builder through `Sound.get` with its no-gap theorem, so those are the commands' own: `unrollBase_ofService`,
    -- `questions_ofService`, `timerQuestions_ofService`, `pairQuestions_ofService`, `respStep_ofService`.)
    ``Tazuna.Smt.atMost_le_count,
    -- In a checked service's layout, a state within the slots embeds, so a script without a model has no state within
    -- the bounds.
    ``Tazuna.Smt.embedState_ofService,
    -- T4: where every input kind's questions about the rules named n are unsat, and its bound question is unsat or
    -- the step fits the slots (Prove.withinBounds), no step within the slots of a run on valid inputs from an initial
    -- state whose invariants hold faults naming n. Valid inputs keep every name below the counter (`Step.run_supp`),
    -- and every step keeps each machine's instances at the keys `instances` gives at the records (`Step.KeysOk`), as
    -- the questions assume of their state.
    ``Tazuna.Smt.fault_sound,
    -- A question whose goal is false in every model (a target of an own kind the step cannot queue) has no model, so
    -- prove reads it as unsat without the solver.
    ``Tazuna.Smt.questions_decided,
    -- T4 for every run (Prove.proved): where every input kind's lines about the rules named n read proved, the
    -- initial state fits the slots and every value an input carries does, no step of any run on valid inputs from an
    -- initial state whose invariants hold faults naming n. The bound questions keep every reached state within the slots
    -- (`run_within`, by induction over the run).
    ``Tazuna.Smt.proved_sound,
    -- Dead targets: where every input kind's question whether its step, from a state of the right shape whose
    -- invariants hold, shows a generate target's class is unsat, no step of a run on valid inputs that faults nowhere
    -- shows it: within the slots (Prove.unreachableWithinBounds), and at any depth where the bound questions read
    -- proved and every input and the initial state fit (Prove.unreachable).
    ``Tazuna.Smt.unshown_within, ``Tazuna.Smt.unshown_sound,
    -- A counterexample is honest: a model of a target question decodes to a state with the step invariant and every
    -- invariant holding, whose step in Lean is the one the terms say.
    ``Tazuna.Smt.cti_sound,
    -- T5 for runs, scoped to the slots: from the initial state on valid inputs, where each step and pair line reads
    -- proved, or within the bounds where the steps it names fit (a pair of own kinds no input kind's cascade can have
    -- waiting together reads proved with no question), and each timer line reads proved, every order of every
    -- cascade a step starts, and of every clock line's timers, ends as the semantics' order does, up to renaming, or
    -- both fault. Its chain: `cascade_lines` and `timers_lines` (Smt/Lines), `Step.cascade_agrees` and
    -- `Step.timers_agree` (Semantics), `Diamond.runs_agree` (Semantics/Diamond).
    ``Tazuna.Smt.run_lines,
    -- A timer line's counterexample is honest: a model is a context whose timer falls back, so timers do not fire
    -- forward.
    ``Tazuna.Smt.timer_violates,
    -- A pair line's counterexample is honest: the pair does not commute. Its orders show a disabling, a fault in one
    -- order only, or different data under every renaming the search tries, which is every renaming `Same` allows
    -- (`data_of_same`); a search past its cap is no violation.
    ``Tazuna.Smt.pair_violates,
    -- No unsat answer is free and none is out of reach: `Unsat` asks that the sorts hold values, and the sorts of every
    -- question an encoder builds in a layout whose datatypes have sorts (as `Layout.ofParts`'s, `sorted_ofParts`) do.
    ``Tazuna.Smt.questions_sorts, ``Tazuna.Smt.pair_sorts, ``Tazuna.Smt.timer_sorts,
    -- Every model a question family's report reads decodes: a model of the family's context whose variables hold values
    -- of their sorts decodes to the state, input, effects or instance context the report shows, so prove's "does not
    -- decode" lines are unreachable.
    ``Tazuna.Smt.questions_decode, ``Tazuna.Smt.pair_decode, ``Tazuna.Smt.timer_decode, ``Tazuna.Smt.resp_decode,
    -- A model generate finds is a run to its target: every model's steps decode to inputs whose run from the
    -- initial state takes the kinds the model picks and faults nowhere, each input carrying only ids from outside or
    -- ones an earlier out line showed (`unroll_decode`, `Step.ShownRun`), and its last step answers in the target's
    -- class.
    ``Tazuna.Smt.generate_sound,
    -- T6: a trace generate writes reaches its target: its lines read as the spec, so verify replays them as passed
    -- unless out of tries, and its last step answers in the target's class. Its chain: `traceOf_reads` (Trace/ReplayOk),
    -- on `dec_enc` and `Step.step_same`.
    ``Tazuna.Cli.generate_reaches,
    -- T6b: generate's "unreached within k steps": where its cubes at a depth cover it and have no model, no run of
    -- that many valid inputs within the slots that faults nowhere answers at its last step in the target's class
    -- (`generate_unreached` per cube, from `runs_covered`: every such run of the cube's kinds is a model of every
    -- assertion but the goal; `extendBase_ok`: a cube's script is the run on its picks).
    ``Tazuna.Smt.noModel_cubes,
    -- A run generate reports as breaking one of prove's targets does (Generate.violated): run in Lean, it faults
    -- nowhere before its last step and faults there by a fault the target covers, and verify replays the written
    -- trace to such a fault at its last line.
    ``Tazuna.Cli.generate_breaks,
    -- A run explore reports as breaking a response does (Explore.violated): its trace reads as the spec, its clock
    -- lines pass no waiting timer, and its steps violate the response as `ResponseV.Violated` defines it.
    ``Tazuna.Explore.response_trace,
    -- explore keeps one state per key: nodes of reachable states with equal keys are related by a renaming that keeps
    -- the counters' order and moves every instant alike, which `step_ren` takes. (Until explore's coverage theorem uses
    -- it.)
    ``Tazuna.Explore.key_link,
    -- generate's "unsettled within k steps" (Generate.unsettled): where its break cubes at a depth cover it with no
    -- model, or the step question whether a step breaks the target is unsat for every kind of a cube's last pick, no
    -- run of that many valid inputs within the slots whose steps before the last fault nowhere faults at its last step
    -- by a fault the target covers (`breakOne_covers`: the break step of such a run holds its assertions).
    ``Tazuna.Smt.noModel_breaks,
    -- T7, a response by induction over steps (Lamport sec 3.3): where every input kind's response question is unsat, no
    -- run on valid inputs with timely clock lines whose steps stay within the slots violates it (Prove.withinBounds);
    -- where every bound question is unsat too and every input and the initial state fit, no such run at all, at any
    -- length (Prove.proved). The question asks whether a step opens a trigger with no deadline in time, lets a waiting
    -- deadline go or move later without its answer, or is a timely clock line past one; `not_violated` turns
    -- those one-step facts into the run's.
    ``Tazuna.Smt.response_scoped, ``Tazuna.Smt.response_holds,
    -- Check's wireType rule reads every wire type, so a user's spec never fails `Checked.wire`: a function on the wire
    -- is Illegal.wireType, and only a loader bug is left to break it (exit 4).
    ``Tazuna.Smt.wireTys_wire]
  -- explain names the theorems a line rests on; each must be a root, so a renamed or demoted theorem fails here.
  let backing ← match unsafe env.evalConst (List Name) (← getOptions) ``Tazuna.Kind.backing with
    | .ok b => pure b
    | .error e => throwError "could not read the theorems explain names: {e}"
  let notRoots := backing.eraseDups.filter (!roots.contains ·)
  unless notRoots.isEmpty do throwError "explain names theorems that are no roots: {notRoots}"
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
