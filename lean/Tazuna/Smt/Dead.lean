import Tazuna.Smt.GenGoal
import Tazuna.Smt.Reached
import Tazuna.Smt.Cone

/-! Dead targets: prove asks of each behavior target whether a step of each input kind, from a state of the right
shape whose invariants hold, shows a class the target aims at (`showsAsk`), the T4 step question with search's goal
for one step (`kindHitT`) in place of a broken rule. Every state a run on valid inputs reaches is such a state
(`run_invariants`, `Step.run_supp`), so where every kind's question has no model, no step of such a run that faults
nowhere shows the class: within the slots where some step can leave them (`unshown_within`), at any depth where none
can and every input and the initial state fit them (`unshown_sound`). A model says nothing: its state may be one no run
reaches. Only a query's answer shows an `answered` class or a query's `invalid` one, and a query changes nothing, so no
step question is about it and such a target gets no question (`GenTarget.byQuery`).

Before any question, the code answers where it can (`mayShow`, the cone of influence of a step): a query and a command
no outside caller may send apply no event and send nothing, a step whose functions build no constructor of the
target's event applies no such event (`Step.step_events`), and a step that applies no event and is no clock line sends
no request. Such a kind gets no question; where no kind may show the class, the target is dead without one. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Whether only a query's answer shows the target's class. -/
def _root_.Tazuna.Ir.GenTarget.byQuery (v : ServiceV) : GenTarget → Bool
  | .answered _ => true
  | .invalid c _ => v.queries.any (·.name == c)
  | _ => false

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- Whether a step of the kind applies no event and sends nothing: a query, or a command no outside caller may send. -/
def SymInput.silent : SymInput v shs n → Bool
  | .query .. => true
  | .command k _ _ => !(v.commands.get k).callers.any isOutside
  | _ => false

/-- Whether the code leaves it possible that a step of the kind shows a class of an event or request target: an event
built with the target's constructor, a request at all. Other targets are left to the questions. -/
def mayShow (P : List AnySite) (T : List TypeDecl) : GenTarget → SymInput v shs n → Bool
  | .event V, inp => !inp.silent && match eventDecl v with
    | some i => match inp.evs P i with
      | some ns => ns.any fun k => variantName T i k == V
      | none => true
    | none => true
  | .request _ _, inp => !inp.silent && (inp.isClock || match eventDecl v with
    | some i => inp.evs P i != some []
    | none => true)
  | _, _ => true

end

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV} (rules : RuleNames) (g : GenTarget)

/-- The question whether a step of the input kind shows a class the target aims at; none where the code (`mayShow`) or
the kind's terms say it never does. -/
def showsAsk (P : List AnySite) {n : Nat} (a : StepAsk v) (inp : SymInput v (shapes v) n) : Option TypedScript :=
  if mayShow P T g inp then
    let hit := kindHitT L T rules g inp a.t.out
    if hit.const?.map Val.toBool == some false then none else some (a.ask hit)
  else none

/-- What an input kind's dead-target answers say: its questions' context is built, its question about the target is
unsat or not asked, and its bound question is unsat (any depth) or `F` holds, the fit of the step the scope names. -/
def ShowsLine (P : List AnySite) (senv : StepEnv L (shapes v)) (F : Prop) (inp : SymInput v (shapes v) senv.nT) :
    Prop :=
  ∃ a, stepAsk L T P v senv inp = .ok a ∧ (∀ q, showsAsk L T rules g P a inp = some q → Unsat L q) ∧
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

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat} {M : Model} {L : Layout} (T : List TypeDecl)

theorem silent_step {inp : SymInput v shs n} (h : inp.silent = true) {hc : v.caller.isData = true} {x : Input v}
    (hx : inp.decode M L hc = some x) (s : State v) : (step T v s x).events = [] ∧ (step T v s x).out = [] := by
  cases inp with
  | query k caller input =>
    simp only [SymInput.decode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨c, -, y, -, rfl⟩ := hx
    simp only [step]
    split <;> exact ⟨rfl, rfl⟩
  | command k caller input =>
    simp only [SymInput.silent, Bool.not_eq_true'] at h
    simp only [SymInput.decode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
    obtain ⟨c, -, y, -, rfl⟩ := hx
    simp only [step, Step.execCommand, Step.admit, Step.any_outside _ h]
    exact ⟨rfl, rfl⟩
  | _ => simp [SymInput.silent] at h

/-- Where the code rules a kind out (`mayShow`), no step of the kind from a state whose pending requests hold the
program's sites shows a class of the target: the cone of influence of the step's events. -/
theorem mayShow_sound {P : List AnySite} {rules : RuleNames} {g : GenTarget} {inp : SymInput v shs n}
    (h : mayShow P T g inp = false) {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    {s : State v} (hs : Step.Inv P s) : ¬ Hits T v rules g x (step T v s x) := by
  have hed : v.event.isData = true := by
    have := v.apply.ht; simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at this; exact this.1.2.1
  have noEvents : ∀ i, eventDecl v = some i → inp.evs P i = some [] → (step T v s x).events = [] := by
    intro i hi hns
    obtain ⟨hi15, a, vs, hev⟩ := eventDecl_some hi
    obtain ⟨hq, hcas, hent, -⟩ := evs_entry hns hx
    have hst := Step.step_events T hi15 hq hcas s hs x hent
    cases he : (step T v s x).events with
    | nil => rfl
    | cons ev _ =>
      exact (ok_variant T (V := variantOf T v.event ev) v.event hed ev ⟨a, vs, hev⟩
        (hst.1 ev (by simp [he]) hed) rfl rfl).elim
  cases g with
  | event V =>
    simp only [mayShow, Bool.and_eq_false_iff, Bool.not_eq_false'] at h
    rw [hits_event]
    rintro ⟨ev, hev, hv⟩
    rcases h with hsil | hm
    · rw [(silent_step T hsil hx s).1] at hev; cases hev
    · split at hm
      · rename_i i hi
        split at hm
        · rename_i ns hns
          obtain ⟨hi15, a, vs, hevt⟩ := eventDecl_some hi
          obtain ⟨hq, hcas, hent, -⟩ := evs_entry hns hx
          exact ok_variant T v.event hed ev ⟨a, vs, hevt⟩
            ((Step.step_events T hi15 hq hcas s hs x hent).1 ev hev hed) hm hv
        · cases hm
      · cases hm
  | request e m =>
    simp only [mayShow, Bool.and_eq_false_iff, Bool.not_eq_false', Bool.or_eq_false_iff] at h
    rw [hits_request]
    rintro ⟨o, ho, -⟩
    rcases h with hsil | ⟨hcl, hm⟩
    · rw [(silent_step T hsil hx s).2] at ho; cases ho
    · split at hm
      · rename_i i hi
        have hns : inp.evs P i = some [] := by simpa using hm
        obtain ⟨hi15, -, -, -⟩ := eventDecl_some hi
        obtain ⟨hq, hcas, hent, hclk⟩ := evs_entry hns hx
        have hout := (Step.step_events T hi15 hq hcas s hs x hent).2 (by rw [hclk, hcl])
        rcases hout with hout | hout
        · rw [hout] at ho; cases ho
        · exact hout (noEvents i hi hns)
      · cases hm
  | _ => simp [mayShow] at h

end

/-- The dead-target question in one model: where the symbolic state and input decode to a state of the right shape
whose names are below its counter and whose invariants hold and to an input of the kind, the model satisfies the
kind's question about the target nowhere, and its bound question nowhere or the step fits the slots, the step faults
or shows no class the target aims at. -/
theorem step_unshown (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {rules : RuleNames} {g : GenTarget}
    {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v} (ha : stepAsk L T P v senv inp = .ok a)
    (hshow : ∀ q, showsAsk L T rules g P a inp = some q → ∃ c ∈ q.script.asserts, ¬ Holds M c)
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hkeys : Step.KeysOk T s) (hheld : Step.invariants s = [])
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    (hcase : ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case)
    (hb : (∃ c ∈ a.bound.script.asserts, ¬ Holds M c) ∨ StepFits L T P v s x)
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) : ¬ Hits T v rules g x (step T v s x) := by
  cases hmay : mayShow P T g inp
  · exact mayShow_sound T hmay hx hinv
  intro hhit
  obtain ⟨hside, hheldH, hcond, hrel⟩ := stepAsk_step chk senv ha hS hinv hsupp hkeys hheld hx hcase hb
  have hh := kindHitT_holds hx hrel hno hhit
  simp only [showsAsk, hmay, ite_true] at hshow
  split at hshow
  · rename_i hk
    cases hw : (kindHitT L T rules g inp a.t.out).const? with
    | none => simp [hw] at hk
    | some w =>
      simp only [hw, Option.map_some, beq_iff_eq, Option.some.injEq] at hk
      simp only [Holds, Term.const?_denote M _ hw, hk] at hh
      cases hh
  · exact stepAsk_goal chk senv ha hS hinv hsupp hkeys hx hcase hside hheldH hcond (hshow _ rfl) hh

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
  have hkeys := run_keys T _ (Step.init_keys T hord chk.idle) is
  rcases covered chk senv hkeys hs x hivs with
    ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | ⟨-, -, -, hq | hf⟩
  · obtain ⟨a, ha, hshow, hor⟩ := hl inp hmem
    have hun : ∀ q : TypedScript, q.tys = stateTys v (shapes v) ++ inp.tys → L.datatypes? = some q.datatypes →
        q.tys.mapM L.srt? = some q.vars → Unsat L q → ∃ c ∈ q.script.asserts, ¬ Holds M c := fun q ht hd hv hu =>
      hu.noModel_at ht hd hv M (fun n h => varSorted_of_sorted (hM n h)) hsel
    refine step_unshown chk senv ha (fun q hq => hun q ?_ ?_ ?_ (hshow q hq)) hS (run_inv T chk.reach _ Step.init_inv is)
      hsupp hkeys (Tazuna.Ir.run_invariants T _ is hinit) hxd hcase
      (hor.imp (fun hu => hun _ (stepAsk_tys L T P v senv ha _) (stepAsk_dts L T P v senv ha _)
        (stepAsk_vars L T P v senv ha _) hu) hF) hno
    all_goals
      simp only [showsAsk] at hq
      split at hq
      · split at hq
        · cases hq
        · cases hq
          first
            | exact stepAsk_tys L T P v senv ha _
            | exact stepAsk_dts L T P v senv ha _
            | exact stepAsk_vars L T P v senv ha _
      · cases hq
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
