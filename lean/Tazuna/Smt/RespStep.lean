import Tazuna.Smt.RespGoal
import Tazuna.Smt.Reached

/-! A bounded response proved in one step: prove asks of each input kind whether its step, from a state of the right
shape whose invariants hold, applies a trigger that no event of the same step answers, or the response's functions
miss their slots (`respStep`). Where every kind's question and bound question has no model and every input and the
initial state fit the slots, every step of every run on valid inputs answers each trigger it applies in its own step,
which no later step can undo, so no run violates the response, whatever its `within` (`response_proved`). A model says
nothing: a later step at the same time may answer, or its state may be one no run reaches; the response is then
searched by BMC as before. prove asks it of `within 0` responses, the ones it can hold for. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {v : ServiceV}

/-- Whether the trigger term `tr` is opened by `after` and answered by no event of the step, and the condition that
the functions' terms are exact there. -/
def unansweredAt (fa : Code (Ty.fn [v.event] Ty.bool)) (fq : Code (Ty.fn [v.event, v.event] Ty.bool))
    (out : StepOut v) (tr : Term) : Except Refusal (Term × Term) := do
  let (o, co) ← predT fa tr
  let (an, can) ← kindHitsT (pred2T fq tr) out
  pure (andT o (.not an), andT co can)

/-- Whether a step of the kind applies a trigger that `after` opens and no event of the step answers, and the
condition that the functions' terms are exact at its events. -/
def unansweredT (fa : Code (Ty.fn [v.event] Ty.bool)) (fq : Code (Ty.fn [v.event, v.event] Ty.bool))
    (out : StepOut v) : Except Refusal (Term × Term) :=
  kindHitsT (unansweredAt fa fq out) out

/-- The question whether a step of the kind applies a trigger it does not answer, or the response's functions miss
their slots there. -/
def respStep (resp : ResponseV v.event) (a : StepAsk v) : Except Refusal TypedScript := do
  let (fa, ca) ← resp.after.code L
  let (fq, cq) ← resp.then_.code L
  let (h, c) ← unansweredT fa fq a.t.out
  pure (a.ask (.or (.not (andT (andT ca cq) c)) h))

/-- What an input kind's one-step answers for the response say: its questions' context is built, and its response
question and bound question are unsat. -/
def RespLine (T : List TypeDecl) (P : List AnySite) (senv : StepEnv L (shapes v)) (resp : ResponseV v.event)
    (inp : SymInput v (shapes v) senv.nT) : Prop :=
  ∃ a q, stepAsk L T P v senv inp = .ok a ∧ respStep L resp a = .ok q ∧ Unsat L q ∧ Unsat L a.bound

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

/-- The one-step question in one model: where the symbolic state and input decode to a state of the right shape
whose names are below its counter and whose invariants hold and to an input of the kind, and the model satisfies the
kind's response question and bound question nowhere, a step that faults nowhere answers each trigger it applies. -/
theorem step_answers (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {resp : ResponseV v.event}
    {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v} {q : TypedScript} (ha : stepAsk L T P v senv inp = .ok a)
    (hq : respStep L resp a = .ok q) (hun : ∃ c ∈ q.script.asserts, ¬ Holds M c)
    (hb : ∃ c ∈ a.bound.script.asserts, ¬ Holds M c)
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hheld : Step.invariants s = [])
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    (hcase : ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case)
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) :
    ∀ tv ∈ (step T v s x).events, resp.opens tv = true → resp.answers tv (step T v s x).moment = true := by
  obtain ⟨hside, hheldH, hcond, hrel⟩ := stepAsk_step chk senv ha hS hinv hsupp hheld hx hcase (.inl hb)
  obtain ⟨⟨fa, ca⟩, hfa, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨fq, cq⟩, hfq, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨h, c⟩, hh, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hgoal := stepAsk_goal chk senv ha hS hinv hsupp hx hcase hside hheldH hcond hun
  simp only [holds_or, holds_not, not_or, Classical.not_not, holds_andT] at hgoal
  obtain ⟨⟨⟨hca, hcq⟩, hc⟩, hnh⟩ := hgoal
  have hp : PredExact M L v (unansweredAt fa fq a.t.out)
      (fun tv => resp.opens tv && !resp.answers tv (step T v s x).moment)
      (fun tv => resp.after.appFits L.count (tv, ()) ∧
        ∀ ev ∈ (step T v s x).events, resp.then_.appFits L.count (tv, ev, ())) := by
    intro tr t c' henc tv hr
    obtain ⟨⟨o, co⟩, e1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨an, can⟩, e2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have x1 := predT_encode v.event_data resp.after hfa hca tv hr e1
    have x2 := kindHitsT_iff (ansT_exact hfq hcq hr) hx hrel hno e2
    simp only [holds_andT, holds_not]
    refine ⟨by rw [x1.1, x2.1], fun ⟨hc1, hc2⟩ => ?_⟩
    rw [x1.2 hc1, x2.2 hc2]
    simp [ResponseV.opens, ResponseV.answers, Result.moment]
  have e := kindHitsT_iff hp hx hrel hno hh
  intro tv htv hop
  cases hans : resp.answers tv (step T v s x).moment
  · exact absurd ((e.2 hc).2 ⟨tv, htv, by simp [hop, hans]⟩) hnh
  · rfl

/-- Every step from a state a run on valid inputs reaches, within the slots, answers each trigger it applies, where
every input kind's one-step answers for the response read unsat and every input fits the slots. -/
theorem state_answers (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {resp : ResponseV v.event}
    (hin : inputsFit L v = true)
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), RespLine L T P senv resp inp)
    {s : State v} (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hheld : Step.invariants s = [])
    (hkeys : Step.KeysOk T s) (hW : Within L (shapes v) s) (x : Input v) :
    ∀ tv ∈ (step T v s x).events, resp.opens tv = true → resp.answers tv (step T v s x).moment = true := by
  by_cases hacc : (step T v s x).outcome = .accepted
  · have hno : ∀ f, (step T v s x).outcome ≠ .fault f := fun f h => by rw [hacc] at h; cases h
    rcases inputs_fit chk hin hW x with hx | ⟨hu, -⟩
    · obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
      rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | ⟨-, -, -, hq | hf⟩
      · obtain ⟨a, q, ha, hq, hu, hb⟩ := hl inp hmem
        have hun : ∀ q' : TypedScript, q'.tys = stateTys v (shapes v) ++ inp.tys → L.datatypes? = some q'.datatypes →
            q'.tys.mapM L.srt? = some q'.vars → Unsat L q' → ∃ c ∈ q'.script.asserts, ¬ Holds M c :=
          fun q' ht hd hv hu' => hu'.noModel_at ht hd hv M (fun n h => varSorted_of_sorted (hM n h)) hsel
        have hqt : q.tys = stateTys v (shapes v) ++ inp.tys ∧ L.datatypes? = some q.datatypes ∧
            q.tys.mapM L.srt? = some q.vars := by
          obtain ⟨_, -, hq'⟩ := bind_ok.1 hq
          obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
          obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
          cases pure_ok.1 hq'
          exact ⟨stepAsk_tys L T P v senv ha _, stepAsk_dts L T P v senv ha _, stepAsk_vars L T P v senv ha _⟩
        exact step_answers chk senv ha hq (hun q hqt.1 hqt.2.1 hqt.2.2 hu)
          (hun _ (stepAsk_tys L T P v senv ha _) (stepAsk_dts L T P v senv ha _) (stepAsk_vars L T P v senv ha _) hb)
          hS hinv hsupp hheld hxd hcase hno
      · obtain ⟨i, c, y, rfl⟩ := hq
        exact absurd hacc (by simp only [step]; split <;> simp)
      · exact absurd hf (hno _)
    · exact absurd hu (hno _)
  · rw [(step_quiet s x hacc).1]
    intro _ h
    cases h

/-- A bounded response proved in one step: where every input kind's response question and bound question read unsat
and the initial state and every value an input can carry fit the slots, no run on valid inputs from an initial state
whose invariants hold violates the response, at any depth. Each trigger is answered in its own step, which is in the
range of steps the violation needs unanswered. -/
theorem response_proved (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    {resp : ResponseV v.event} (hinit : Step.invariants (Step.State.init v) = []) (h0 : initFits L v = true)
    (hin : inputsFit L v = true)
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), RespLine L T P senv resp inp)
    (xs : List (Input v)) (hvalid : Step.ValidRun T (Step.State.init v) xs) :
    ¬ resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  have hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp := fun inp hm => by
    obtain ⟨a, q, ha, -, -, hb⟩ := hl inp hm
    exact ⟨_, _, by simp only [questions, ha, bind, Except.bind, pure, Except.pure]; rfl, fun q hq hn => by
      simp only [List.mem_cons, List.mem_map] at hq
      rcases hq with rfl | ⟨_, -, rfl⟩
      · exact hb
      · cases hn⟩
  suffices h : ∀ (ys : List (Input v)) (s : State v), Step.Inv P s → Step.StateSupp s → Step.invariants s = [] →
      Step.KeysOk T s → Step.ValidRun T s ys → Within L (shapes v) s →
      ∀ r ∈ (run T v s ys).2, ∀ tv ∈ r.events, resp.opens tv = true → resp.answers tv r.moment = true by
    rintro ⟨i, j, tv, hij, hj, htv, hop, -, hm⟩
    have hi : i < ((run T v (Step.State.init v) xs).2.map Result.moment).length := by omega
    have hr := h xs _ Step.init_inv (Step.init_supp he) hinit (Step.init_keys T hord) hvalid (within_init h0)
      _ (List.getElem_mem (l := (run T v (Step.State.init v) xs).2) (by simpa using hi))
    simp only [List.getElem_map] at htv hm
    have := hm i (Nat.le_refl _) hij
    rw [hr tv htv hop] at this
    cases this
  intro ys
  induction ys with
  | nil => intro _ _ _ _ _ _ _ r hr; cases hr
  | cons x ys ih =>
    intro s hinv hsupp hheld hkeys ⟨hx, hys⟩ hW r hr
    rw [show (run T v s (x :: ys)).2 = step T v s x :: (run T v (step T v s x).state ys).2 from rfl,
      List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact state_answers chk senv hin hl hinv hsupp hheld hkeys hW x
    · exact ih _ (step_inv T chk.reach s hinv x) (Step.step_supp T he hsupp hinv.below x hx)
        (step_invariants T s x hheld) (step_keys T s hkeys x) hys (within_step chk senv hin hb hinv hsupp hheld hkeys hW x)
        r hr

end

/-- In each service's layout, a response's one-step question never refuses with a layout gap. -/
theorem respStep_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) {resp : ResponseV v.event}
    (hr : resp ∈ v.responses) (a : StepAsk v) : Sound (fun _ => True) (respStep (Layout.ofService c.program.defs v) resp a) := by
  have h := serviceGot_ofService hv
  have chk := c.checked v hv
  have hev := avail_of_got h.event
  refine sound_bind (Fun.code_ofService c hv _ (chk.reach.responses resp hr).1 (root_response hr).1)
    fun ⟨fa, _⟩ ha => sound_bind (Fun.code_ofService c hv _ (chk.reach.responses resp hr).2 (root_response hr).2)
    fun ⟨fq, _⟩ hq => sound_bind (kindHitsT_sound (pred := unansweredAt fa fq a.t.out) (fun tr =>
      sound_bind (predT_sound ha hev tr) fun _ _ =>
        sound_bind (kindHitsT_sound (pred2T_sound hq hev tr) a.t.out) fun _ _ => trivial) a.t.out)
      fun _ _ => trivial

end Tazuna.Smt
