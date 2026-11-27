import Tazuna.Smt.Dead

/-! generate's split of a depth into cubes (cube and conquer, Heule, Kullmann, Wieringa and Biere 2011). A cube fixes
the input kinds of the last steps of a depth-`d` run (`cubeFilters`); its steps encode only those kinds
(`unrollOne`'s pick), so its script is smaller and easier than the whole depth's. A cube the solver leaves undecided
splits on the step before it, one cube per pick (`pickCount`), until the first step. A cube is asked as the run of
its unfixed steps, shared by every cube and target on that many steps, then its fixed steps and the goal as one
assertion (`cubeGoal`, `extendBase`). Every input's pick is one the split lists, so cubes that cover the depth and
have no model leave no run of `d` inputs that reaches the target (`noModel_cubes`, T6b at depth `d`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))

-- With no step in `B`, the steps start at the initial state `S0`.
set_option linter.tazuna.silentDefault false in
/-- The run `B` with one step per pick of `fs` after its steps, from the state its last step leaves (`S0`, the
initial state, where it has none); `extendBase_ok` shows it is the run on `B`'s picks then `fs`. -/
def extendBase (S0 : SymState v) (B : UnrollBase v senv.nT) (fs : List (Option Nat)) :
    Except Refusal (UnrollBase v senv.nT) := do
  let r := unrollSteps L T P v senv ((B.steps.getLast?.map (·.after)).getD S0) (B.steps.flatMap (·.shows))
    B.steps.length B.tys.length fs
  let vars ← r.1.mapM fun ty => need (lacks ty) (L.srt? ty)
  pure ⟨B.datatypes, B.tys ++ r.1, B.vars ++ vars, B.asserts ++ r.2.1, B.steps ++ r.2.2.1, B.refused ++ r.2.2.2⟩

end

/-- A term no model satisfies by its shape alone: false, a conjunction with such a part, or a choice whose branches
both are. A cube whose goal is one is settled without the solver (a step whose fixed pick has no kind, or a goal no
kind of the last step can meet). -/
def Term.falsy : Term → Bool
  | .bool false => true
  | .and a b => a.falsy || b.falsy
  | .ite _ a b => a.falsy && b.falsy
  | _ => false

theorem Term.not_holds_of_falsy {M : Model} : (t : Term) → t.falsy = true → ¬ Holds M t
  | .bool false, _ => by simp [Holds, Term.denote, Val.toBool]
  | .and a b, h => by
    simp only [Term.falsy, Bool.or_eq_true] at h
    rw [holds_and]
    intro hab
    rcases h with h | h
    · exact Term.not_holds_of_falsy a h hab.1
    · exact Term.not_holds_of_falsy b h hab.2
  | .ite c a b, h => by
    simp only [Term.falsy, Bool.and_eq_true] at h
    rw [holds_ite]
    split
    · exact Term.not_holds_of_falsy a h.1
    · exact Term.not_holds_of_falsy b h.2

/-- An assertion that always holds and names the literals `ls`, so a prefix shared by cubes holds every literal their
goals may read, as the abstract variant of a prefix needs (`Solver.askGoal`). -/
def litsFact (ls : List String) : Term := .or tt (allT (ls.map fun l => .eq (.str l) (.str l)))

/-- What a cube asks after the run of its unfixed steps `Bj`: the assertions of its fixed steps, which `B` adds to
`Bj` (`extendBase`), and the goal. -/
def cubeGoal {v : ServiceV} {n : Nat} (Bj B : UnrollBase v n) (goal : Term) : Term :=
  andT (allT (B.asserts.drop Bj.asserts.length)) goal

/-- A cube's question: the depth's declarations (`Bd`, the whole depth's run, whose constants are the cube's), the
run of the unfixed steps `Bj` and the literals' fact as the prefix shared by every cube and target on those steps,
then the cube's goal `q` (`cubeGoal`). -/
def cubeAsk {v : ServiceV} {n : Nat} (Bj Bd : UnrollBase v n) (ls : List String) (q : Term) : TypedScript :=
  ⟨Bd.datatypes, Bd.tys, Bd.vars, [], Bj.asserts ++ [litsFact ls, q]⟩

/-- The values a step's selector tells apart: every input's pick is below it. -/
def pickCount (v : ServiceV) : Nat := v.commands.length + v.queries.length + 1 + v.subscribes.length + 1

theorem Input.pick_lt {v : ServiceV} (x : Input v) : x.pick < pickCount v := by
  cases x <;> simp only [Input.pick, Input.kind, PickKind.pick, pickCount] <;> omega

/-- The steps of a depth-`d` run whose last `ps.length` steps take the kinds `ps` picks, in step order. -/
def cubeFilters (d : Nat) (ps : List Nat) : List (Option Nat) := List.replicate (d - ps.length) none ++ ps.map some

section
variable {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV} {senv : StepEnv L (shapes v)}

theorem unrollSteps_length (S : SymState v) (shown : List (Term × Term)) (i b : Nat) :
    (fs : List (Option Nat)) → (unrollSteps L T P v senv S shown i b fs).2.2.1.length = fs.length
  | [] => rfl
  | f :: fs => by
    rcases h1 : unrollOne L T P v senv S shown i b f with ⟨tys, asserts, st, refused, b'⟩
    have ih := unrollSteps_length st.after (shown ++ st.shows) (i + 1) b' fs
    simp only [unrollSteps, h1, List.length_cons, ih]

/-- An unrolled step's constants are its kinds', whatever its state, shown ids and fixed pick. -/
theorem unrollOne_tys (S S' : SymState v) (shown shown' : List (Term × Term)) (i b : Nat) (f f' : Option Nat) :
    (unrollOne L T P v senv S shown i b f).1 = (unrollOne L T P v senv S' shown' i b f').1 ∧
      (unrollOne L T P v senv S shown i b f).2.2.2.2 = (unrollOne L T P v senv S' shown' i b f').2.2.2.2 := by
  exact ⟨rfl, rfl⟩

/-- An unrolled run's constants depend only on its number of steps. -/
theorem unrollSteps_tys : (fs fs' : List (Option Nat)) → fs.length = fs'.length → (S S' : SymState v) →
    (shown shown' : List (Term × Term)) → (i b : Nat) →
    (unrollSteps L T P v senv S shown i b fs).1 = (unrollSteps L T P v senv S' shown' i b fs').1
  | [], [], _, _, _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _ => by simp at h
  | f :: fs, f' :: fs', h, S, S', shown, shown', i, b => by
    have ht := unrollOne_tys (T := T) (P := P) (senv := senv) S S' shown shown' i b f f'
    rcases h1 : unrollOne L T P v senv S shown i b f with ⟨tys, asserts, st, refused, b1⟩
    rcases h2 : unrollOne L T P v senv S' shown' i b f' with ⟨tys', asserts', st', refused', b2⟩
    rw [h1, h2] at ht
    obtain ⟨rfl, rfl⟩ := ht
    have ih := unrollSteps_tys fs fs' (by simpa using h) st.after st'.after (shown ++ st.shows) (shown' ++ st'.shows)
      (i + 1) b1
    simp only [unrollSteps, h1, h2, ih]

-- With no step on `fs1`, the run on `fs2` starts at `S`.
set_option linter.tazuna.silentDefault false in
/-- An unrolled run on `fs1 ++ fs2` is the run on `fs1` and then, from the state its last step leaves and after the
ids its steps show, the run on `fs2`. -/
theorem unrollSteps_append : (fs1 fs2 : List (Option Nat)) → (S : SymState v) → (shown : List (Term × Term)) →
    (i b : Nat) → unrollSteps L T P v senv S shown i b (fs1 ++ fs2) =
      ((unrollSteps L T P v senv S shown i b fs1).1 ++
          (unrollSteps L T P v senv (((unrollSteps L T P v senv S shown i b fs1).2.2.1.getLast?.map (·.after)).getD S)
            (shown ++ (unrollSteps L T P v senv S shown i b fs1).2.2.1.flatMap (·.shows)) (i + fs1.length)
            (b + (unrollSteps L T P v senv S shown i b fs1).1.length) fs2).1,
        (unrollSteps L T P v senv S shown i b fs1).2.1 ++
          (unrollSteps L T P v senv (((unrollSteps L T P v senv S shown i b fs1).2.2.1.getLast?.map (·.after)).getD S)
            (shown ++ (unrollSteps L T P v senv S shown i b fs1).2.2.1.flatMap (·.shows)) (i + fs1.length)
            (b + (unrollSteps L T P v senv S shown i b fs1).1.length) fs2).2.1,
        (unrollSteps L T P v senv S shown i b fs1).2.2.1 ++
          (unrollSteps L T P v senv (((unrollSteps L T P v senv S shown i b fs1).2.2.1.getLast?.map (·.after)).getD S)
            (shown ++ (unrollSteps L T P v senv S shown i b fs1).2.2.1.flatMap (·.shows)) (i + fs1.length)
            (b + (unrollSteps L T P v senv S shown i b fs1).1.length) fs2).2.2.1,
        (unrollSteps L T P v senv S shown i b fs1).2.2.2 ++
          (unrollSteps L T P v senv (((unrollSteps L T P v senv S shown i b fs1).2.2.1.getLast?.map (·.after)).getD S)
            (shown ++ (unrollSteps L T P v senv S shown i b fs1).2.2.1.flatMap (·.shows)) (i + fs1.length)
            (b + (unrollSteps L T P v senv S shown i b fs1).1.length) fs2).2.2.2)
  | [], fs2, S, shown, i, b => by simp [unrollSteps]
  | f :: fs1, fs2, S, shown, i, b => by
    have hn := unrollOne_next (T := T) (P := P) senv S shown i b f
    rcases h1 : unrollOne L T P v senv S shown i b f with ⟨tys, asserts, st, refused, b'⟩
    rw [h1] at hn
    simp only at hn
    have ih := unrollSteps_append fs1 fs2 st.after (shown ++ st.shows) (i + 1) b'
    rcases h2 : unrollSteps L T P v senv st.after (shown ++ st.shows) (i + 1) b' fs1 with ⟨tys1, as1, sts1, r1⟩
    rw [h2] at ih
    simp only [List.cons_append, unrollSteps, h1, h2, ih]
    rw [getLast?_cons_getD]
    simp only [List.flatMap_cons, List.append_assoc, List.length_cons, List.length_append, hn, Nat.add_assoc,
      Nat.add_comm 1]

/-- Runs on as many steps have the same constants. -/
theorem unrollBase_tys {fs fs' : List (Option Nat)} {B B' : UnrollBase v senv.nT}
    (hB : unrollBase L T P v senv fs = .ok B) (hB' : unrollBase L T P v senv fs' = .ok B')
    (hl : fs.length = fs'.length) : B.tys = B'.tys := by
  simp only [unrollBase] at hB hB'
  obtain ⟨S, -, hB⟩ := bind_ok.1 hB
  obtain ⟨_, -, hB⟩ := bind_ok.1 hB
  obtain ⟨_, -, hB⟩ := bind_ok.1 hB
  cases pure_ok.1 hB
  obtain ⟨S', -, hB'⟩ := bind_ok.1 hB'
  obtain ⟨_, -, hB'⟩ := bind_ok.1 hB'
  obtain ⟨_, -, hB'⟩ := bind_ok.1 hB'
  cases pure_ok.1 hB'
  exact unrollSteps_tys fs fs' hl S S' [] [] 0 0

/-- `extendBase` is the run on the base's picks then `fs`. -/
theorem extendBase_ok {fs1 fs2 : List (Option Nat)} {S0 : SymState v} {B B' : UnrollBase v senv.nT}
    (hB : unrollBase L T P v senv fs1 = .ok B) (hS0 : initState L v = some S0)
    (hB' : extendBase L T P v senv S0 B fs2 = .ok B') : unrollBase L T P v senv (fs1 ++ fs2) = .ok B' := by
  simp only [unrollBase] at hB ⊢
  obtain ⟨S0', hS0', hB⟩ := bind_ok.1 hB
  obtain ⟨dts, hdts, hB⟩ := bind_ok.1 hB
  obtain ⟨vars, hvars, hB⟩ := bind_ok.1 hB
  cases pure_ok.1 hB
  have e0 : S0' = S0 := by rw [need_ok.1 hS0'] at hS0; exact Option.some.inj hS0
  subst e0
  simp only [extendBase] at hB'
  obtain ⟨vars', hvars', hB'⟩ := bind_ok.1 hB'
  cases pure_ok.1 hB'
  refine bind_ok.2 ⟨S0', hS0', bind_ok.2 ⟨dts, hdts, ?_⟩⟩
  rw [unrollSteps_append, List.mapM_append, hvars]
  simp only [Nat.zero_add, List.nil_append, unrollSteps_length] at hvars' ⊢
  rw [hvars']
  rfl

end

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

theorem eachStep_last {p : State v → Input v → Prop} {x : Input v} : (ys : List (Input v)) → (s : State v) →
    Step.EachStep T p s (ys ++ [x]) → Step.EachStep T p s ys ∧ p (run T v s ys).1 x
  | [], _, h => ⟨trivial, by simpa [run] using h.1⟩
  | _ :: ys, _, ⟨h1, h2⟩ => by
    have ih := eachStep_last ys _ h2
    exact ⟨⟨h1, ih.1⟩, by simpa [run] using ih.2⟩

theorem inputVals_isSome {hc : v.caller.isData = true} {x : Input v} (h : (unrollVals L hc x).isSome) :
    (inputVals L hc x).isSome := by
  cases x <;> first | rfl | exact h

/-- A step that fits the slots from a state within them leaves a state within them, where every input kind's step
question is built (`stepAsk`): the question's terms say what the step is. -/
theorem within_fits (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hasks : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ∃ a, stepAsk L T P v senv inp = .ok a)
    {s : State v} (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hheld : Step.invariants s = [])
    (hkeys : Step.KeysOk T s) (hW : Within L (shapes v) s) {x : Input v} (hx : (inputVals L chk.callerData x).isSome)
    (hfit : StepFits L T P v s x) : Within L (shapes v) (step T v s x).state := by
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
  rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | h
  · obtain ⟨a, ha⟩ := hasks inp hmem
    exact within_stepRel chk.embeddable (stepAsk_step chk senv ha hS hinv hsupp hkeys hheld hxd hcase (.inr hfit)).2.2.2
      hW
  · rw [h.2.2.1]; exact hW

/-- Every state a run within the slots on valid inputs reaches from the initial state is within the slots, where the
initial state is and every input kind's step question is built. -/
theorem within_runIn (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    (hasks : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ∃ a, stepAsk L T P v senv inp = .ok a)
    (hinit : Step.invariants (Step.State.init v) = []) (h0 : initFits L v = true) (ys : List (Input v))
    (hvalid : Step.ValidRun T (Step.State.init v) ys) (hin : RunIn L T P v chk.callerData (Step.State.init v) ys) :
    Within L (shapes v) (run T v (Step.State.init v) ys).1 := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  suffices h : ∀ (xs : List (Input v)) (s : State v), Step.Inv P s → Step.StateSupp s →
      Step.invariants s = [] → Step.KeysOk T s → Step.ValidRun T s xs → RunIn L T P v chk.callerData s xs →
      Within L (shapes v) s → Within L (shapes v) (run T v s xs).1 from
    h ys _ Step.init_inv (Step.init_supp he) hinit (Step.init_keys T hord chk.idle) hvalid hin (within_init h0)
  intro xs
  induction xs with
  | nil => intro s _ _ _ _ _ _ hW; exact hW
  | cons x xs ih =>
    intro s hinv hsupp hheld hkeys ⟨hx, hxs⟩ ⟨⟨hvals, hfit⟩, hins⟩ hW
    exact ih _ (step_inv T chk.reach s hinv x) (Step.step_supp T he hsupp hinv.below x hx) (step_invariants T s x hheld)
      (step_keys T s hkeys x) hxs hins
      (within_fits chk senv hasks hinv hsupp hheld hkeys hW (inputVals_isSome hvals) hfit)

theorem SymInput.pick_of_decode {shs : List (PendingShape v.event)} {n : Nat} {M : Model}
    {hc : v.caller.isData = true} {inp : SymInput v shs n} {x : Input v} (h : inp.decode M L hc = some x) :
    inp.pick = x.pick := by
  cases inp with
  | command => obtain ⟨_, _, rfl, -, -⟩ := decode_command h; rfl
  | query => obtain ⟨_, _, rfl, -, -⟩ := decode_query h; rfl
  | answer => obtain ⟨_, _, _, rfl, -, -⟩ := decode_answer h; rfl
  | unmatched => obtain ⟨_, _, _, rfl, -, -⟩ := decode_answer h; rfl
  | event => obtain ⟨_, rfl, -⟩ := decode_event h; rfl
  | clock => obtain ⟨_, rfl, -⟩ := decode_clock h; rfl

/-- What generate's search shows of the cube `ps` at depth `d` (`ps.length` at most `d`): it has no model, as an unsat
answer to its question (`cubeAsk`) or a goal false by its shape says, and refuses no input kind; or the code rules out
that any kind its last step takes shows the target (`mayShow`), or prove's dead-target question (`showsAsk`) of every
kind of its last step's pick is unsat; or it splits on the step before its fixed ones, into
one cube per pick. -/
inductive CubesCover (senv : StepEnv L (shapes v)) (rules : RuleNames) (g : GenTarget) (d : Nat) : List Nat → Prop
  | leaf {ps : List Nat} {Bj Bd B : UnrollBase v senv.nT} {S0 : SymState v} {ls : List String} :
    ps.length ≤ d → unrollBase L T P v senv (List.replicate (d - ps.length) none) = .ok Bj →
    unrollBase L T P v senv (List.replicate d none) = .ok Bd → initState L v = some S0 →
    extendBase L T P v senv S0 Bj (ps.map some) = .ok B → B.refused = [] →
    Unsat L (cubeAsk Bj Bd ls (cubeGoal Bj B (genGoal L T rules g B.steps))) ∨
      (cubeGoal Bj B (genGoal L T rules g B.steps)).falsy = true →
    CubesCover senv rules g d ps
  | ruledOut {ps : List Nat} {Bj B : UnrollBase v senv.nT} {S0 : SymState v} :
    ps.length ≤ d → unrollBase L T P v senv (List.replicate (d - ps.length) none) = .ok Bj →
    initState L v = some S0 → extendBase L T P v senv S0 Bj (ps.map some) = .ok B → B.refused = [] →
    (∀ st, B.steps.getLast? = some st → ∀ k ∈ st.kinds, mayShow P T g k.1 = false) →
    CubesCover senv rules g d ps
  | deadLast {ps : List Nat} {k : Nat} :
    ps.getLast? = some k → g.byQuery v = false → v.Equivariant → Step.invariants (Step.State.init v) = [] →
    initFits L v = true →
    (∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ∃ a, stepAsk L T P v senv inp = .ok a ∧
      (inp.pick = k → ∀ q, showsAsk L T rules g P a inp = some q → Unsat L q)) →
    CubesCover senv rules g d ps
  | split {ps : List Nat} : ps.length < d → (∀ k < pickCount v, CubesCover senv rules g d (k :: ps)) →
    CubesCover senv rules g d ps

theorem picksFit_none : (ys : List (Input v)) → PicksFit (List.replicate ys.length none) ys
  | [] => trivial
  | _ :: ys => ⟨by simp, picksFit_none ys⟩

theorem picksFit_some : (ys : List (Input v)) → PicksFit ((ys.map (·.pick)).map some) ys
  | [] => trivial
  | _ :: ys => ⟨by simp, picksFit_some ys⟩

theorem picksFit_cube {d : Nat} {ps : List Nat} {xs : List (Input v)} (hlen : xs.length = d)
    (hx : (xs.drop (d - ps.length)).map (·.pick) = ps) : PicksFit (cubeFilters d ps) xs := by
  have hl : (xs.take (d - ps.length)).length = d - ps.length := by rw [List.length_take, hlen]; omega
  have e := List.take_append_drop (d - ps.length) xs
  generalize xs.take (d - ps.length) = pre at e hl
  generalize xs.drop (d - ps.length) = post at e hx
  subst hx e
  rw [cubeFilters, ← hl]
  exact forall2_append (picksFit_none _) (picksFit_some _)

/-- T6b at depth `d`: where generate's cubes cover the depth (`CubesCover` from no fixed step) with no model, no run from
the initial state of `d` inputs that fit the slots and are valid, whose steps stay within the slots and fault
nowhere, answers at its last step in a class the target aims at. generate's "unreached within k steps" is this at
every depth up to k, so no such run of at most k inputs answers in that class at any step. -/
theorem noModel_cubes (chk : Checked P E T v) (senv : StepEnv L (shapes v)) (hL : SortedLayout L)
    {rules : RuleNames} {g : GenTarget} {d : Nat} (hc : CubesCover (T := T) (P := P) senv rules g d [])
    {ys : List (Input v)} {x : Input v} (hlen : ys.length + 1 = d)
    (hin : RunIn L T P v chk.callerData (Step.State.init v) (ys ++ [x]))
    (has : ∀ a ∈ Step.Assumption.ofRuns, a.Holds T (Step.State.init v) (ys ++ [x])) :
    ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) ys).1 x) := by
  have hxl : (ys ++ [x]).length = d := by simp [hlen]
  suffices h : ∀ ps, CubesCover (T := T) (P := P) senv rules g d ps →
      ((ys ++ [x]).drop (d - ps.length)).map (·.pick) = ps →
      ¬ Hits T v rules g x (step T v (run T v (Step.State.init v) ys).1 x) from
    h [] hc (by simp; omega)
  intro ps hcov
  induction hcov with
  | @leaf ps Bj Bd B S0 ls hp hBj hBd hS0 hB hnr hno =>
    intro hx
    have hBc : unrollBase L T P v senv (cubeFilters d ps) = .ok B := extendBase_ok hBj hS0 hB
    refine generate_unreached chk senv hL hBc hnr (fun M hM hS => ?_) (picksFit_cube hxl hx) hin has
    -- The cube's constants are the depth's, and its assertions hold exactly where the question's do.
    have htys : Bd.tys = B.tys := unrollBase_tys hBd hBc (by simp [cubeFilters, hp])
    have hBa : B.asserts = Bj.asserts ++ B.asserts.drop Bj.asserts.length := by
      simp only [extendBase] at hB
      obtain ⟨_, -, hB⟩ := bind_ok.1 hB
      cases pure_ok.1 hB
      simp
    have hall : ¬ ∀ a ∈ Bj.asserts ++ [litsFact ls, cubeGoal Bj B (genGoal L T rules g B.steps)], Holds M a := by
      rcases hno with hun | hf
      · intro hh
        obtain ⟨a, ha, hna⟩ := hun.noModel_at (tys := B.tys) (by simp [cubeAsk, htys])
          (unrollBase_dts L T P v senv hBd) (unrollBase_vars L T P v senv hBd) M hM hS
        exact hna (hh a (by simpa [cubeAsk, TypedScript.script] using ha))
      · intro hh
        exact Term.not_holds_of_falsy _ hf (hh _ (by simp))
    refine Classical.byContradiction fun hne => hall fun a ha => ?_
    have hA : ∀ a ∈ (B.withGoal (genGoal L T rules g B.steps)).ask.script.asserts, Holds M a :=
      fun a ha => Classical.byContradiction fun hna => hne ⟨a, ha, hna⟩
    rw [UnrollBase.holds_withGoal] at hA
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl
    · exact hA.1 a (hBa ▸ List.mem_append_left _ ha)
    · simp [litsFact, Holds, Term.denote, Val.toBool, tt]
    · rw [cubeGoal, holds_andT, holds_allT]
      exact ⟨fun c hc => hA.1 c (hBa ▸ List.mem_append_right _ hc), hA.2⟩
  | @ruledOut ps Bj B S0 hp hBj hS0 hB hnr hrule =>
    intro hx hhit
    have hBc : unrollBase L T P v senv (cubeFilters d ps) = .ok B := extendBase_ok hBj hS0 hB
    obtain ⟨M, -, -, hrun, -⟩ := runs_covered chk senv hL hBc hnr (picksFit_cube hxl hx) (runFits_of _ _ _ _ _ _ _ hin has)
    obtain ⟨st, hlast, ⟨k, hk, hdec, -⟩, -, -⟩ := unrollRun_last x ys _ _ hrun
    have hmem : k ∈ st.kinds := List.mem_of_find?_eq_some hk
    exact mayShow_sound T (hrule st hlast k hmem) hdec (run_inv T chk.reach _ Step.init_inv ys) hhit
  | @deadLast ps k hk hg he hinit h0 hasks =>
    intro hx hhit
    have hne : ps ≠ [] := by rintro rfl; cases hk
    have hxk : x.pick = k := by
      have h1 := congrArg List.getLast? hx
      rw [List.getLast?_map, hk, List.getLast?_drop, List.getLast?_concat] at h1
      split at h1
      · simp at h1
      · simpa using h1
    obtain ⟨hinYs, hinX⟩ := eachStep_last ys _ hin
    have hshown : Step.ShownRun T [] (Step.State.init v) (ys ++ [x]) := has .validInputs (by simp [Step.Assumption.ofRuns])
    obtain ⟨hvalidYs, -⟩ := eachStep_last ys _ hshown.valid
    obtain ⟨-, hnoX⟩ := eachStep_last ys _ (has .noFault (by simp [Step.Assumption.ofRuns]))
    have hasks' := fun inp hm => (hasks inp hm).imp fun _ h => h.1
    have hW := within_runIn chk he senv hasks' hinit h0 ys hvalidYs hinYs
    have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
    have hsupp := Step.run_supp T he chk.reach _ Step.init_inv (Step.init_supp he) ys hvalidYs
    have hkeys := run_keys T _ (Step.init_keys T hord chk.idle) ys
    obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 (inputVals_isSome hinX.1)
    rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | ⟨-, -, -, hq | hf⟩
    · obtain ⟨a, ha, hshow⟩ := hasks inp hmem
      have hpk : inp.pick = k := (SymInput.pick_of_decode hxd).trans hxk
      refine step_unshown chk senv ha (fun q hq => ?_) hS (run_inv T chk.reach _ Step.init_inv ys) hsupp hkeys
        (Tazuna.Ir.run_invariants T _ ys hinit) hxd hcase (.inr hinX.2) hnoX hhit
      have hq' := hq
      simp only [showsAsk] at hq'
      split at hq'
      · split at hq'
        · cases hq'
        · cases hq'
          exact (hshow hpk _ hq).noModel_at (stepAsk_tys L T P v senv ha _) (stepAsk_dts L T P v senv ha _)
            (stepAsk_vars L T P v senv ha _) M (fun n h => varSorted_of_sorted (hM n h)) hsel
      · cases hq'
    · obtain ⟨i, c, y, rfl⟩ := hq
      exact query_unshown hg _ i c y hhit
    · exact hnoX _ hf
  | @split ps hp _ ih =>
    intro hx
    have hj : 0 < d - ps.length := by omega
    have hk : ((ys ++ [x])[d - ps.length - 1]'(by omega)).pick < pickCount v := Input.pick_lt _
    refine ih _ hk ?_
    rw [List.length_cons, show d - (ps.length + 1) = d - ps.length - 1 by omega,
      List.drop_eq_getElem_cons (by omega), List.map_cons, show d - ps.length - 1 + 1 = d - ps.length by omega, hx]

end

end Tazuna.Smt
