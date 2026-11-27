import Tazuna.Smt.GenGoal
import Tazuna.Smt.Reached

/-! Dead targets: prove asks of each of generate's targets whether a step of each input kind, from a state of the right
shape whose invariants hold, shows a class the target aims at (`showsAsk`), the T4 step question with generate's goal
for one step (`kindHitT`) in place of a broken rule. Every state a run on valid inputs reaches is such a state
(`run_invariants`, `Step.run_supp`), so where every kind's question has no model, no step of such a run that faults
nowhere shows the class: within the slots where some step can leave them (`unshown_within`), at any depth where none
can and every input and the initial state fit them (`unshown_sound`). A model says nothing: its state may be one no run
reaches. Only a query's answer shows an `answered` class or a query's `invalid` one, and a query changes nothing, so no
step question is about it and such a target gets no question (`GenTarget.byQuery`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Whether only a query's answer shows the target's class. -/
def _root_.Tazuna.Ir.GenTarget.byQuery (v : ServiceV) : GenTarget → Bool
  | .answered _ => true
  | .invalid c _ => v.queries.any (·.name == c)
  | _ => false

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV} (rules : RuleNames) (g : GenTarget)

/-- The question whether a step of the input kind shows a class the target aims at; none where the kind's terms say
it never does. -/
def showsAsk {n : Nat} (a : StepAsk v) (inp : SymInput v (shapes v) n) : Option TypedScript :=
  let hit := kindHitT L T rules g inp a.t.out
  if hit.const?.map Val.toBool == some false then none else some (a.ask hit)

/-- What an input kind's dead-target answers say: its questions' context is built, its question about the target is
unsat or not asked, and its bound question is unsat (any depth) or `F` holds, the fit of the step the scope names. -/
def ShowsLine (P : List AnySite) (senv : StepEnv L (shapes v)) (F : Prop) (inp : SymInput v (shapes v) senv.nT) :
    Prop :=
  ∃ a, stepAsk L T P v senv inp = .ok a ∧ (∀ q, showsAsk L T rules g a inp = some q → Unsat L q) ∧
    (Unsat L a.bound ∨ F)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

/-- A query's step shows only its own answer, so it shows no class of a target that not only a query shows. -/
theorem query_unshown {rules : RuleNames} {g : GenTarget} (hg : g.byQuery v = false) (s : State v)
    (i : Fin v.queries.length) (c : v.caller.den0) (y : (v.queries.get i).input.den0) :
    ¬ Hits T v rules g (.query i c y) (step T v s (.query i c y)) := by
  rintro ⟨cl, hcl, hcov⟩
  have hq : (v.queries.get i).name ∈ v.queries.map (·.name) := List.mem_map_of_mem (List.get_mem _ _)
  simp only [step] at hcl
  split at hcl <;>
  · simp only [classes, answerClasses, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hcl
    first
    | (subst hcl
       cases g <;> simp_all [GenTarget.covers, GenTarget.byQuery])
    | (obtain ⟨r, -, rfl⟩ := hcl
       cases g with
       | invalid q r' =>
         cases r' <;> simp only [GenTarget.covers, Bool.and_eq_true, beq_iff_eq] at hcov <;>
           (obtain ⟨rfl, -⟩ := hcov; simp [GenTarget.byQuery] at hg
            exact hg _ (List.get_mem _ _) rfl)
       | _ => simp [GenTarget.covers] at hcov)

/-- The dead-target question in one model: where the symbolic state and input decode to a state of the right shape
whose names are below its counter and whose invariants hold and to an input of the kind, the model satisfies the
kind's question about the target nowhere, and its bound question nowhere or the step fits the slots, the step faults
or shows no class the target aims at. -/
theorem step_unshown (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {rules : RuleNames} {g : GenTarget}
    {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v} (ha : stepAsk L T P v senv inp = .ok a)
    (hshow : ∀ q, showsAsk L T rules g a inp = some q → ∃ c ∈ q.script.asserts, ¬ Holds M c)
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hheld : Step.invariants s = [])
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    (hcase : ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case)
    (hb : (∃ c ∈ a.bound.script.asserts, ¬ Holds M c) ∨ StepFits L T P v s x)
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) : ¬ Hits T v rules g x (step T v s x) := by
  intro hhit
  obtain ⟨hside, hheldH, hcond, hrel⟩ := stepAsk_step chk senv ha hS hinv hsupp hheld hx hcase hb
  have hh := kindHitT_holds hx hrel hno hhit
  simp only [showsAsk] at hshow
  split at hshow
  · rename_i hk
    cases hw : (kindHitT L T rules g inp a.t.out).const? with
    | none => simp [hw] at hk
    | some w =>
      simp only [hw, Option.map_some, beq_iff_eq, Option.some.injEq] at hk
      simp only [Holds, Term.const?_denote M _ hw, hk] at hh
      cases hh
  · exact stepAsk_goal chk senv ha hS hinv hsupp hx hcase hside hheldH hcond (hshow _ rfl) hh

theorem boundUnsat_of_ask {senv : StepEnv L (shapes v)} {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v}
    (ha : stepAsk L T P v senv inp = .ok a) (hb : Unsat L a.bound) : BoundUnsat L T P v senv inp := by
  refine ⟨_, _, by simp only [questions, ha, bind, Except.bind, pure, Except.pure]; rfl, fun q hq hn => ?_⟩
  simp only [List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨_, -, rfl⟩
  · exact hb
  · cases hn

/-- The step of a run within the slots, where every input kind's dead-target answers read unsat with each bound
question unsat or `F`, which makes the step fit the slots. -/
theorem unshown_at (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v)) {rules : RuleNames}
    {g : GenTarget} (hg : g.byQuery v = false) (hinit : Step.invariants (Step.State.init v) = [])
    (is : List (Input v)) (hvalid : Step.ValidRun T (Step.State.init v) is) (x : Input v)
    {F : Prop} (hF : F → StepFits L T P v (run T v (Step.State.init v) is).1 x)
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ShowsLine L T rules g P senv F inp)
    (hs : Within L (shapes v) (run T v (Step.State.init v) is).1) (hx : (inputVals L chk.callerData x).isSome)
    (hno : ∀ f, (step T v (run T v (Step.State.init v) is).1 x).outcome ≠ .fault f) :
    ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) is).1 x) := by
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  have hsupp := Step.run_supp T he chk.reach _ Step.init_inv (Step.init_supp he) is hvalid
  rcases covered chk senv (run_keys T _ (Step.init_keys T hord) is) hs x hivs with
    ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | ⟨-, -, -, hq | hf⟩
  · obtain ⟨a, ha, hshow, hor⟩ := hl inp hmem
    have hun : ∀ q : TypedScript, q.tys = stateTys v (shapes v) ++ inp.tys → L.datatypes? = some q.datatypes →
        Unsat L q → ∃ c ∈ q.script.asserts, ¬ Holds M c := fun q ht hd hu =>
      hu.noModel_at ht hd M (fun n h => varSorted_of_sorted (hM n h)) hsel
    refine step_unshown chk senv ha (fun q hq => hun q ?_ ?_ (hshow q hq)) hS (run_inv T chk.reach _ Step.init_inv is)
      hsupp (Tazuna.Ir.run_invariants T _ is hinit) hxd hcase
      (hor.imp (fun hu => hun _ (stepAsk_tys L T P v senv ha _) (stepAsk_dts L T P v senv ha _) hu) hF) hno
    all_goals
      simp only [showsAsk] at hq
      split at hq
      · cases hq
      · cases hq
        first | exact stepAsk_tys L T P v senv ha _ | exact stepAsk_dts L T P v senv ha _
  · obtain ⟨i, c, y, rfl⟩ := hq
    exact query_unshown hg _ i c y
  · exact (hno _ hf).elim

/-- Dead targets within the slots: where every input kind's dead-target answers about a target that not only a query
shows read unsat, with each bound question unsat or the step fitting the slots, no step of a run on valid inputs from
an initial state whose invariants hold that faults nowhere shows a class the target aims at, wherever the state the
run reached and the input fit the slots. -/
theorem unshown_within (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v)) {rules : RuleNames}
    {g : GenTarget} (hg : g.byQuery v = false) (hinit : Step.invariants (Step.State.init v) = [])
    (is : List (Input v)) (hvalid : Step.ValidRun T (Step.State.init v) is) (x : Input v)
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v),
      ShowsLine L T rules g P senv (StepFits L T P v (run T v (Step.State.init v) is).1 x) inp)
    (hs : Within L (shapes v) (run T v (Step.State.init v) is).1) (hx : (inputVals L chk.callerData x).isSome)
    (hno : ∀ f, (step T v (run T v (Step.State.init v) is).1 x).outcome ≠ .fault f) :
    ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) is).1 x) :=
  unshown_at chk he senv hg hinit is hvalid x id hl hs hx hno

/-- Dead targets at any depth: where every input kind's dead-target answers about a target that not only a query
shows read unsat, every bound question too, and the initial state and every value an input can carry fit the slots,
no step of any run on valid inputs from an initial state whose invariants hold that faults nowhere shows a class the
target aims at. -/
theorem unshown_sound (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v)) {rules : RuleNames}
    {g : GenTarget} (hg : g.byQuery v = false) (hinit : Step.invariants (Step.State.init v) = [])
    (h0 : initFits L v = true) (hin : inputsFit L v = true)
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ShowsLine L T rules g P senv False inp)
    (is : List (Input v)) (hvalid : Step.ValidRun T (Step.State.init v) is) (x : Input v)
    (hno : ∀ f, (step T v (run T v (Step.State.init v) is).1 x).outcome ≠ .fault f) :
    ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) is).1 x) := by
  have hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp := fun inp hm => by
    obtain ⟨a, ha, -, hor⟩ := hl inp hm
    exact boundUnsat_of_ask ha (hor.resolve_right id)
  have hW := run_within chk he senv hin hb hinit h0 is hvalid
  rcases inputs_fit chk hin hW x with hx | ⟨hu, -⟩
  · exact unshown_at chk he senv hg hinit is hvalid x False.elim hl hW hx hno
  · exact (hno _ hu).elim

end

end Tazuna.Smt
