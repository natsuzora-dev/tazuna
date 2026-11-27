import Tazuna.Smt.GenGoal
import Tazuna.Smt.StepNoGap
import Tazuna.Semantics.Response

/-! A bounded response's goal on an unrolled run: the run violates the response (`respGoalE`). A trigger is an event
a step applies, read off the event slots of the step's end where the step reaches it, as generate's event goal reads
them, for the kind the step takes. For each slot the goal keeps the slot's term as the trigger and asks whether it
satisfies `after`, whether the step or a later one applies an event that `then` ties to it (`ansT`, `then` applied to
the trigger's term and each later slot's), and whether a later step comes past the trigger's time plus `within` first
(`lateT`). Time is the state's after each step; a clock line must pass no timer that waits (`Step.timely`, the stated
assumption `timelyClock`). The goal is `ResponseV.violated` written as terms (`violT`), so its exactness is the
computed form's. The response's functions are encoded as every kept function is, with conditions: the goal asks that
`after` holds at every event a step applies and `then` at every trigger with every event from its step on, so a
model's terms say what the functions return.

With `runs_covered` this gives T7 (`response_within`): a depth with no model has no run of that many valid inputs,
within the slots, faulting nowhere and with timely clock lines, that violates the response. Every model decodes to a
run that violates it (`response_sound`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {v : ServiceV} {n : Nat}

/-- A response function's code applied to the event term `ev`: whether it holds, and its condition. -/
def predT {e : Ty} (f : Code (Ty.fn [e] Ty.bool)) (ev : Term) : Except Refusal (Term × Term) := do
  let ec ← Code.ofDataE e ev
  f (ec, ())

/-- Over event slots: whether some occupied slot's event satisfies `pred`, and the condition that `pred`'s terms are
exact at every occupied slot. -/
def slotHitsT (pred : Term → Except Refusal (Term × Term)) : List (Slot 1) → Except Refusal (Term × Term)
  | [] => pure (ff, tt)
  | (f, xs) :: S => do
    let (t, c) ← pred xs[0]
    let (h, k) ← slotHitsT pred S
    pure (.or (andT f t) h, andT (.or (.not f) c) k)

/-- Over the events a step of the kind applies, where it reaches its end: `slotHitsT` of its end's event slots. A kind
with no end applies none. -/
def kindHitsT (pred : Term → Except Refusal (Term × Term)) (out : StepOut v) : Except Refusal (Term × Term) :=
  match out.finish? with
  | some fo => do
    let (h, c) ← slotHitsT pred fo.events
    pure (andT out.reached h, .or (.not out.reached) c)
  | none => pure (ff, tt)

section
variable (L : Layout)

/-- A clock line at `time` from `S` passes no timer that waits: no timer is due at `time - 1`. Other kinds ask
nothing. -/
def kindTimelyT (S : SymState v) : SymInput v (shapes v) n → Except Refusal Term
  | .clock time => do
    let dues ← dueAll L v.machines S.machines (.sub time (.int 1))
    pure (.not (minDueT dues).1)
  | _ => pure tt

end

/-- A response's `then` code applied to the trigger term `tr` and the event term `ev`: whether it holds, and its
condition. -/
def pred2T {e : Ty} (f : Code (Ty.fn [e, e] Ty.bool)) (tr ev : Term) : Except Refusal (Term × Term) := do
  let tc ← Code.ofDataE e tr
  let ec ← Code.ofDataE e ev
  f (tc, ec, ())

/-- `kindHitsT pred` of the kind the step takes: whether some event it applies satisfies `pred`, and the condition. -/
def pickHitsT (pred : Term → Except Refusal (Term × Term)) (st : UnrollStep v n) : Except Refusal (Term × Term) := do
  let hs ← st.kindTerms fun k => kindHitsT pred k.2.out
  pure (st.pickedT ff (hs.map fun p => (p.1, p.2.1)), st.pickedT tt (hs.map fun p => (p.1, p.2.2)))

section
variable (fa : Code (Ty.fn [v.event] Ty.bool)) (fq : Code (Ty.fn [v.event, v.event] Ty.bool)) (within : Int)

/-- Whether the step applies an event that `then` ties to the trigger term `tr` (`ResponseV.answers`). -/
def ansT (tr : Term) (st : UnrollStep v n) : Except Refusal (Term × Term) := pickHitsT (pred2T fq tr) st

/-- From the trigger `tr` at time `t0`, some later step comes past `t0 + within` with no step before it answering
`tr` (`ResponseV.late`). -/
def lateT (tr t0 : Term) : List (UnrollStep v n) → Except Refusal (Term × Term)
  | [] => pure (ff, tt)
  | st :: sts => do
    let (a, ca) ← ansT fq tr st
    let (l, cl) ← lateT tr t0 sts
    pure (.or (.lt (.add t0 (.int within)) st.after.now) (andT (.not a) l), andT ca cl)

/-- The event term `tr` of the step `st`, followed by `sts`, is a trigger that its step does not answer and that
comes late. -/
def trigT (st : UnrollStep v n) (sts : List (UnrollStep v n)) (tr : Term) : Except Refusal (Term × Term) := do
  let (o, co) ← predT fa tr
  let (a, ca) ← ansT fq tr st
  let (l, cl) ← lateT fq within tr st.after.now sts
  pure (andT o (andT (.not a) l), andT co (andT ca cl))

/-- The steps violate the response (`ResponseV.violated`): some step applies a trigger as `trigT` reads it. -/
def violT : List (UnrollStep v n) → Except Refusal (Term × Term)
  | [] => pure (ff, tt)
  | st :: sts => do
    let (h, c) ← pickHitsT (trigT fa fq within st sts) st
    let (h', c') ← violT sts
    pure (.or h h', andT c c')

end

section
variable (L : Layout) (T : List TypeDecl) (v : ServiceV)

/-- A clock line the step takes is timely. -/
def timelyT (st : UnrollStep v n) : Except Refusal Term := do
  let tms ← st.kindTerms fun k => kindTimelyT L st.before k.1
  pure (st.pickedT tt (tms.map fun p => (p.1, p.2)))

/-- The response's goal on an unrolled run's steps: the functions' sources fit, the conditions hold, every clock line
is timely, and the steps violate the response. -/
def respGoalE (resp : ResponseV v.event) (sts : List (UnrollStep v n)) : Except Refusal Term := do
  let (fa, ca) ← resp.after.code L
  let (fq, cq) ← resp.then_.code L
  let (h, c) ← violT fa fq (resp.withinNat : Int) sts
  let tms ← sts.mapM (timelyT L v)
  pure (andT (andT ca cq) (andT c (andT (allT tms) h)))

end

end

/-! The semantic side. -/

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV}

/-- The response's functions fit the slots on the moments: `after` at every event, and `then` at every event as the
trigger with every event of its step and of the steps after. -/
def _root_.Tazuna.Ir.ResponseV.FitsOn {e : Ty} (resp : ResponseV e) : List (Moment e) → Prop
  | [] => True
  | m :: ms => (∀ ev ∈ m.events, resp.after.appFits L.count (ev, ()) ∧
      ∀ m' ∈ m :: ms, ∀ ev' ∈ m'.events, resp.then_.appFits L.count (ev, ev', ())) ∧ resp.FitsOn ms

/-- The response's functions fit the slots on the run's moments. -/
abbrev RespFits (resp : ResponseV v.event) (s : State v) (xs : List (Input v)) : Prop :=
  resp.FitsOn L ((run T v s xs).2.map Result.moment)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {n : Nat}

theorem predT_encode {e : Ty} (he : e.isData = true) (f : Fun (Ty.fn [e] Ty.bool)) {s : Code (Ty.fn [e] Ty.bool)}
    {c1 : Term} (hf : f.code L = .ok (s, c1)) (hc1 : Holds M c1) (x : e.den0) {ev : Term}
    (hx : RelV L e (Ty.up e he x) (ev.denote M)) {t c : Term} (h : predT s ev = .ok (t, c)) :
    (Holds M c ↔ f.appFits L.count (x, ())) ∧ (Holds M c → (Holds M t ↔ Step.toB (f.fn (x, ())) = true)) := by
  obtain ⟨ec, h1, h⟩ := bind_ok.1 h
  have hrc : Smt.Rel M L e (Ty.up e he x) ec := (rel_ofTerm (need_ok.1 h1) _).2 hx
  have hargs1 : (Ty.tuple [e]).isData = true := by simp [Ty.isData, Ty.isDatas, he]
  have hnf : ∀ t ∈ [e], t.isFn = false := by simpa using ofTerm_notFn (need_ok.1 h1)
  refine ⟨f.app_exact hf hc1 hnf _ _ (rels1 he hargs1 hrc) h, fun hc => ?_⟩
  have hfn := f.code_fn f.ht hf hc1
  have hb := hfn _ _ (rels1 he hargs1 hrc) t c h hc
  erw [Ty.up_fn _ Ty.bool _ hargs1 rfl] at hb
  have hb' := (rel_bool _ _).1 hb
  simp only [Holds, hb', Val.toBool]
  generalize f.fn (x, ()) = y
  rcases y with _ | _ | e <;> rfl

theorem pred2T_encode {e : Ty} (he : e.isData = true) (f : Fun (Ty.fn [e, e] Ty.bool))
    {s : Code (Ty.fn [e, e] Ty.bool)} {c1 : Term} (hf : f.code L = .ok (s, c1)) (hc1 : Holds M c1) (x y : e.den0)
    {tr ev : Term} (hx : RelV L e (Ty.up e he x) (tr.denote M)) (hy : RelV L e (Ty.up e he y) (ev.denote M))
    {t c : Term} (h : pred2T s tr ev = .ok (t, c)) :
    (Holds M c ↔ f.appFits L.count (x, y, ())) ∧ (Holds M c → (Holds M t ↔ Step.toB (f.fn (x, y, ())) = true)) := by
  obtain ⟨tc, h1, h⟩ := bind_ok.1 h
  obtain ⟨ec, h2, h⟩ := bind_ok.1 h
  have hrt : Smt.Rel M L e (Ty.up e he x) tc := (rel_ofTerm (need_ok.1 h1) _).2 hx
  have hre : Smt.Rel M L e (Ty.up e he y) ec := (rel_ofTerm (need_ok.1 h2) _).2 hy
  have hargs : (Ty.tuple [e, e]).isData = true := by simp [Ty.isData, Ty.isDatas, he]
  have hnf : ∀ t ∈ [e, e], t.isFn = false := by simpa using ofTerm_notFn (need_ok.1 h1)
  refine ⟨f.app_exact hf hc1 hnf _ _ (rels2 he he hargs hrt hre) h, fun hc => ?_⟩
  have hfn := f.code_fn f.ht hf hc1
  have hb := hfn _ _ (rels2 he he hargs hrt hre) t c h hc
  erw [Ty.up_fn _ Ty.bool _ hargs rfl] at hb
  have hb' := (rel_bool _ _).1 hb
  simp only [Holds, hb', Val.toBool]
  generalize f.fn (x, y, ()) = y
  rcases y with _ | _ | e <;> rfl

/-- What `pred` says of an event term that denotes `ev`: its condition holds exactly when `F ev`, and then it holds
exactly when `p ev`. -/
def PredExact (M : Model) (L : Layout) (v : ServiceV) (pred : Term → Except Refusal (Term × Term))
    (p : v.event.den0 → Bool) (F : v.event.den0 → Prop) : Prop :=
  ∀ a t c, pred a = .ok (t, c) → ∀ ev, RelV L v.event (Ty.up _ v.event_data ev) (a.denote M) →
    (Holds M c ↔ F ev) ∧ (Holds M c → (Holds M t ↔ p ev = true))

theorem slotHitsT_iff {pred : Term → Except Refusal (Term × Term)} {p : v.event.den0 → Bool} {F : v.event.den0 → Prop}
    (hp : PredExact M L v pred p F) : (S : List (Slot 1)) → (sv : List (Bool × List Val)) → (evs : List v.event.den0) →
    SlotsDen M S sv → Holds2 (EBag L v.event) (evs.map (Ty.up _ v.event_data)) sv → ∀ {h c : Term},
    slotHitsT pred S = .ok (h, c) → (Holds M c ↔ ∀ ev ∈ evs, F ev) ∧ (Holds M c → (Holds M h ↔ ∃ ev ∈ evs, p ev = true))
  | [], [], evs, _, he, h, c, henc => by
    cases pure_ok.1 henc
    have : evs = [] := by
      cases evs with
      | nil => rfl
      | cons _ _ => simp [Holds2, occupied, Forall2] at he
    subst this
    simp [tt, ff, Holds, Term.denote, Val.toBool]
  | (f, xs) :: S, (b, vs) :: sv, evs, ⟨hf, hx, hS⟩, he, h, c, henc => by
    obtain ⟨⟨t, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨h', k⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hfb : Holds M f ↔ b = true := by simp [Holds, hf, Val.toBool]
    simp only [holds_or, holds_andT, holds_not, hfb]
    cases b with
    | false =>
      have ih := slotHitsT_iff hp S sv evs hS (by simpa [Holds2, occupied] using he) h2
      simpa using ih
    | true =>
      simp only [Holds2, occupied, ite_true, List.filterMap_cons] at he
      match evs, he with
      | ev :: evs', ⟨⟨z, hz, hr⟩, he'⟩ =>
        have ih := slotHitsT_iff hp S sv evs' hS he' h2
        obtain ⟨a, rfl⟩ := SlotItems.one xs
        simp only [Term.denotes] at hx
        subst hx
        simp only [List.cons.injEq, and_true] at hz
        subst hz
        have e1 := hp a t c1 h1 ev hr
        simp only [true_and, not_true_eq_false, false_or, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
        rw [e1.1, ih.1]
        refine ⟨Iff.rfl, fun ⟨hc, hk⟩ => ?_⟩
        rw [e1.2 ((e1.1).2 hc), ih.2 ((ih.1).2 hk)]

/-- A step of the kind applies no event where it has no end or does not reach it. -/
theorem events_nil {hc : v.caller.isData = true} {inp : SymInput v (shapes v) n} {out : StepOut v}
    {s : State v} {x : Input v} (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x))
    (hno : ∀ f, (step T v s x).outcome ≠ .fault f) (h : ∀ fo, out.finish? = some fo → ¬ Holds M out.reached) :
    (step T v s x).events = [] := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨fo, hfo, hre⟩ := (rel_end hx hrel hno).2 (.inl hne)
  exact h fo hfo hre

theorem kindHitsT_iff {pred : Term → Except Refusal (Term × Term)} {p : v.event.den0 → Bool}
    {F : v.event.den0 → Prop} (hp : PredExact M L v pred p F) {hc : v.caller.isData = true}
    {inp : SymInput v (shapes v) n} {out : StepOut v} {s : State v} {x : Input v} (hx : inp.decode M L hc = some x)
    (hrel : out.Rel M L T (shapes v) s x (step T v s x)) (hno : ∀ f, (step T v s x).outcome ≠ .fault f) {h c : Term}
    (henc : kindHitsT pred out = .ok (h, c)) :
    (Holds M c ↔ ∀ ev ∈ (step T v s x).events, F ev) ∧
      (Holds M c → (Holds M h ↔ ∃ ev ∈ (step T v s x).events, p ev = true)) := by
  unfold kindHitsT at henc
  split at henc
  · rename_i fo hfo
    obtain ⟨⟨h', c'⟩, h1, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    simp only [holds_or, holds_not, holds_andT]
    by_cases hre : Holds M out.reached
    · obtain ⟨s0, a, hae, -, hf⟩ := (rel_end hx hrel hno).1 fo hfo hre
      obtain ⟨evs, hevs, sv, hS, h2⟩ := finished_events hf hno
      rw [hevs, hae, List.nil_append]
      have e := slotHitsT_iff hp fo.events sv evs hS h2 h1
      simpa [hre] using e
    · have hnil := events_nil hx hrel hno fun fo' hfo' => by rw [hfo] at hfo'; cases hfo'; exact hre
      rw [hnil]
      simp [hre]
  · cases pure_ok.1 henc
    have hnil := events_nil hx hrel hno fun fo' hfo' => by rename_i hn; rw [hn] at hfo'; cases hfo'
    rw [hnil]
    simp [tt, ff, Holds, Term.denote, Val.toBool]

theorem timely_iff_dues (s : State v) (time : Int) :
    Step.timely s time = true ↔ Step.dues s.machines.toSigma (time - 1) = [] := by
  simp only [Step.timely, Step.dues, List.all_eq_true, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine forall_congr' fun ⟨m, insts⟩ => imp_congr_right fun _ => forall_congr' fun i => imp_congr_right fun _ => ?_
  cases i.timer with
  | none => simp
  | some p => obtain ⟨d, _⟩ := p; simp; omega

theorem kindTimelyT_iff {hc : v.caller.isData = true} {S : SymState v} {s : State v}
    (hR : StateRel M L T (shapes v) S s) {inp : SymInput v (shapes v) n} {x : Input v} (hx : inp.decode M L hc = some x)
    {t : Term} (henc : kindTimelyT L S inp = .ok t) :
    Holds M t ↔ Step.timelyAt s x = true := by
  cases inp with
  | clock tm =>
    obtain ⟨time, rfl, htm⟩ := decode_clock hx
    obtain ⟨dues, h1, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hnow : (Term.sub tm (.int 1)).denote M = .int (time - 1) := by simp [Term.denote, htm, Val.toInt]
    obtain ⟨os, hF, hP⟩ := dueAll_rel (T := T) hnow v.machines S.machines s.machines hR.machines h1
    obtain ⟨hhas, -⟩ := minDue_den hF
    rw [min?_perm hP] at hhas
    show Holds M (Term.not _) ↔ Step.timely s time = true
    rw [holds_not, timely_iff_dues]
    simp only [Holds, hhas, Val.toBool, Option.isSome_iff_ne_none, ne_eq, List.min?_eq_none_iff, Decidable.not_not]
  | command i a b =>
    obtain ⟨_, _, rfl, -⟩ := decode_command hx; cases pure_ok.1 henc; exact iff_of_true holds_tt rfl
  | query i a b =>
    obtain ⟨_, _, rfl, -⟩ := decode_query hx; cases pure_ok.1 henc; exact iff_of_true holds_tt rfl
  | event i a =>
    obtain ⟨_, rfl, -⟩ := decode_event hx; cases pure_ok.1 henc; exact iff_of_true holds_tt rfl
  | answer k j to w =>
    obtain ⟨_, _, _, rfl, -⟩ := decode_answer hx; cases pure_ok.1 henc; exact iff_of_true holds_tt rfl
  | unmatched t' to w =>
    obtain ⟨_, _, _, rfl, -⟩ := decode_answer hx; cases pure_ok.1 henc; exact iff_of_true holds_tt rfl

/-- At a step a model takes, `pickHitsT` reads the kind it takes as `kindHitsT_iff` says. -/
theorem pickHitsT_iff {pred : Term → Except Refusal (Term × Term)} {p : v.event.den0 → Bool}
    {F : v.event.den0 → Prop} (hp : PredExact M L v pred p F) {hc : v.caller.isData = true} {st : UnrollStep v n}
    {s : State v} {x : Input v} (hat : StepAt L T M hc st s x) {h c : Term} (henc : pickHitsT pred st = .ok (h, c)) :
    (Holds M c ↔ ∀ ev ∈ (step T v s x).events, F ev) ∧
      (Holds M c → (Holds M h ↔ ∃ ev ∈ (step T v s x).events, p ev = true)) := by
  obtain ⟨⟨k, hk, hdec, hrel⟩, hno, -, -⟩ := hat
  obtain ⟨hs, e1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨⟨h1, c1⟩, f1, hh⟩ := kindTerms_taken st e1 hk (fun p => p.1) ff
  obtain ⟨⟨_, _⟩, f1', hcc⟩ := kindTerms_taken st e1 hk (fun p => p.2) tt
  rw [f1] at f1'; cases f1'
  rw [hcc, hh]
  exact kindHitsT_iff hp hdec hrel hno f1

theorem timelyT_iff {hc : v.caller.isData = true} {st : UnrollStep v n} {s : State v} {x : Input v}
    (hat : StepAt L T M hc st s x) {t : Term} (henc : timelyT L v st = .ok t) : Holds M t ↔ Step.timelyAt s x = true := by
  obtain ⟨⟨k, hk, hdec, -⟩, -, -, hbefore⟩ := hat
  obtain ⟨tms, e1, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨tk, f1, htm⟩ := kindTerms_taken st e1 hk (fun t => t) tt
  rw [htm]
  exact kindTimelyT_iff hbefore hdec f1

theorem timelysT_iff {hc : v.caller.isData = true} : (s : State v) → (sts : List (UnrollStep v n)) →
    (xs : List (Input v)) → UnrollRun L T M hc s sts xs → {ts : List Term} → sts.mapM (timelyT L v) = .ok ts →
    (Holds M (allT ts) ↔ Step.TimelyRun T s xs)
  | _, [], [], _, ts, h => by cases pure_ok.1 h; simp [holds_allT, Step.EachStep]
  | _, [], _ :: _, h, _, _ => h.elim
  | _, _ :: _, [], h, _, _ => h.elim
  | s, st :: sts, x :: xs, ⟨_, hat, hrun⟩, ts, h => by
    rw [List.mapM_cons] at h
    obtain ⟨t, e1, h⟩ := bind_ok.1 h
    obtain ⟨ts', e2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have ih := timelysT_iff _ sts xs hrun e2
    simp only [holds_allT, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [timelyT_iff hat e1, ih]
    rfl

section
variable {resp : ResponseV v.event} {fa : Code (Ty.fn [v.event] Ty.bool)}
  {fq : Code (Ty.fn [v.event, v.event] Ty.bool)} {ca cq : Term}
  (ha : resp.after.code L = .ok (fa, ca)) (hq : resp.then_.code L = .ok (fq, cq)) (hca : Holds M ca)
  (hcq : Holds M cq)

include hq hcq in
theorem ansT_exact {tv : v.event.den0} {tr : Term} (hr : RelV L v.event (Ty.up _ v.event_data tv) (tr.denote M)) :
    PredExact M L v (pred2T fq tr) (fun ev => Step.toB (resp.then_.fn (tv, ev, ())))
      (fun ev => resp.then_.appFits L.count (tv, ev, ())) :=
  fun _ _ _ h ev hr' => pred2T_encode v.event_data resp.then_ hq hcq tv ev hr hr' h

include hq hcq in
theorem lateT_iff {hc : v.caller.isData = true} {tv : v.event.den0} {tr : Term}
    (hr : RelV L v.event (Ty.up _ v.event_data tv) (tr.denote M)) {t0 : Term} {x0 : Int} (h0 : t0.denote M = .int x0) :
    (s : State v) → (sts : List (UnrollStep v n)) → (xs : List (Input v)) → UnrollRun L T M hc s sts xs →
    {l cl : Term} → lateT fq (resp.withinNat : Int) tr t0 sts = .ok (l, cl) →
    (Holds M cl ↔ ∀ m ∈ (run T v s xs).2.map Result.moment, ∀ ev ∈ m.events, resp.then_.appFits L.count (tv, ev, ())) ∧
      (Holds M cl → (Holds M l ↔ resp.late tv x0 ((run T v s xs).2.map Result.moment) = true))
  | _, [], [], _, l, cl, h => by
    cases pure_ok.1 h
    simp [run, ResponseV.late, tt, ff, Holds, Term.denote, Val.toBool]
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
  | s, st :: sts, x :: xs, ⟨_, hat, hrun⟩, l, cl, h => by
    obtain ⟨⟨a, ca'⟩, e1, h⟩ := bind_ok.1 h
    obtain ⟨⟨l', cl'⟩, e2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have x1 := pickHitsT_iff (ansT_exact hq hcq hr) hat e1
    have ih := lateT_iff hr h0 _ sts xs hrun e2
    have hnow := hat.2.2.1.now
    simp only [run, List.map_cons, Result.moment, List.mem_cons, forall_eq_or_imp, holds_andT, holds_or, holds_not]
    refine ⟨by rw [x1.1, ih.1], fun ⟨hc1, hc2⟩ => ?_⟩
    rw [x1.2 hc1, ih.2 hc2]
    simp only [ResponseV.late, ResponseV.answers, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq]
    simp only [Holds, Term.denote, h0, hnow, Val.toInt, Val.toBool, decide_eq_true_eq]
    simp

include ha hq hca hcq in
theorem trigT_exact {hc : v.caller.isData = true} {st : UnrollStep v n} {sts : List (UnrollStep v n)} {s : State v}
    {x : Input v} {xs : List (Input v)} (hat : StepAt L T M hc st s x)
    (hrun : UnrollRun L T M hc (step T v s x).state sts xs) :
    PredExact M L v (trigT fa fq (resp.withinNat : Int) st sts)
      (fun ev => resp.opens ev && !resp.answers ev (step T v s x).moment &&
        resp.late ev (step T v s x).moment.time ((run T v (step T v s x).state xs).2.map Result.moment))
      (fun ev => resp.after.appFits L.count (ev, ()) ∧ ∀ m ∈ (step T v s x).moment ::
        (run T v (step T v s x).state xs).2.map Result.moment, ∀ ev' ∈ m.events,
          resp.then_.appFits L.count (ev, ev', ())) := by
  intro a t c h ev hr
  obtain ⟨⟨o, co⟩, e1, h⟩ := bind_ok.1 h
  obtain ⟨⟨an, can⟩, e2, h⟩ := bind_ok.1 h
  obtain ⟨⟨l, cl⟩, e3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have x1 := predT_encode v.event_data resp.after ha hca ev hr e1
  have x2 := pickHitsT_iff (ansT_exact hq hcq hr) hat e2
  have x3 := lateT_iff hq hcq hr hat.2.2.1.now _ sts xs hrun e3
  simp only [holds_andT, holds_not, List.mem_cons, forall_eq_or_imp, Result.moment]
  refine ⟨by rw [x1.1, x2.1, x3.1], fun ⟨hc1, hc2, hc3⟩ => ?_⟩
  rw [x1.2 hc1, x2.2 hc2, x3.2 hc3]
  simp [ResponseV.opens, ResponseV.answers, and_assoc]

include ha hq hca hcq in
/-- Over a model's run: the violation's condition holds exactly when the response's functions fit on the run's
moments, and then its term holds exactly when the run violates the response. -/
theorem violT_iff {hc : v.caller.isData = true} : (s : State v) → (sts : List (UnrollStep v n)) →
    (xs : List (Input v)) → UnrollRun L T M hc s sts xs → {h c : Term} →
    violT fa fq (resp.withinNat : Int) sts = .ok (h, c) →
    (Holds M c ↔ RespFits L T resp s xs) ∧ (Holds M c → (Holds M h ↔ resp.violated ((run T v s xs).2.map Result.moment)))
  | _, [], [], _, h, c, henc => by
    cases pure_ok.1 henc
    simp [RespFits, run, ResponseV.FitsOn, ResponseV.violated, tt, ff, Holds, Term.denote, Val.toBool]
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim
  | s, st :: sts, x :: xs, ⟨_, hat, hrun⟩, h, c, henc => by
    obtain ⟨⟨h1, c1⟩, e1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨h2, c2⟩, e2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have x1 := pickHitsT_iff (trigT_exact ha hq hca hcq hat hrun) hat e1
    have ih := violT_iff _ sts xs hrun e2
    simp only [RespFits, run, List.map_cons, ResponseV.FitsOn, ResponseV.violated, holds_andT, holds_or] at ih ⊢
    refine ⟨by rw [x1.1, ih.1]; exact Iff.rfl, fun ⟨hc1, hc2⟩ => ?_⟩
    rw [x1.2 hc1, ih.2 hc2]
    simp [Result.moment, List.any_eq_true]

end

/-- The goal on a model's run: it holds exactly when the response's functions fit (their sources, and on the run's
moments), every clock line is timely and the run violates the response. -/
theorem respGoal_iff {resp : ResponseV v.event} {hc : v.caller.isData = true} {s : State v}
    {sts : List (UnrollStep v n)} {xs : List (Input v)} (hrun : UnrollRun L T M hc s sts xs) {g : Term}
    (hg : respGoalE L v resp sts = .ok g) :
    Holds M g ↔ ((resp.after.fits L.count).1 ∧ (resp.then_.fits L.count).1) ∧ RespFits L T resp s xs ∧
      Step.TimelyRun T s xs ∧ resp.Violated ((run T v s xs).2.map Result.moment) := by
  obtain ⟨⟨fa, ca⟩, ha, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨fq, cq⟩, hq, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨h, c⟩, hv, hg⟩ := bind_ok.1 hg
  obtain ⟨tms, ht, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  have ea := (resp.after.code_exact (M := M) ha).1
  have eq := (resp.then_.code_exact (M := M) hq).1
  rw [holds_andT, holds_andT, holds_andT, holds_andT, ea, eq, timelysT_iff s sts xs hrun ht, ← resp.violated_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have x := violT_iff ha hq (ea.2 h1) (eq.2 h2) s sts xs hrun hv
    exact ⟨⟨h1, h2⟩, x.1.1 h3, h4, (x.2 h3).1 h5⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have x := violT_iff ha hq (ea.2 h1) (eq.2 h2) s sts xs hrun hv
    exact ⟨⟨h1, h2⟩, x.1.2 h3, h4, (x.2 (x.1.2 h3)).2 h5⟩

variable {P : List AnySite} {E : List AnyEffectSite}

/-- T7: where prove's script for the response at depth `d` has no input kind refused, its goal is encoded and it has
no model, no run from the initial state of `d` inputs that fit the slots and are valid, whose steps stay within the
slots and fault nowhere, whose clock lines are timely and at whose events the response's functions fit, violates the
response. prove's "within the bounds" for a response is this at every depth up to the spec's steps, so no such run of
at most that many inputs violates it. -/
theorem response_within (chk : Checked P E T v) (senv : StepEnv L (shapes v)) (hL : SortedLayout L)
    {resp : ResponseV v.event} {d : Nat} {B : UnrollBase v senv.nT} (hB : unrollBase L T P v senv d = .ok B)
    {g : Term} (hg : respGoalE L v resp B.steps = .ok g) (hnr : B.refused = []) (hun : Unsat L (B.withGoal g).ask)
    {xs : List (Input v)} (hlen : xs.length = d) (hin : RunIn L T P v chk.callerData (Step.State.init v) xs)
    (hsrc : (resp.after.fits L.count).1 ∧ (resp.then_.fits L.count).1)
    (hrf : RespFits L T resp (Step.State.init v) xs)
    (has : ∀ a ∈ Step.Assumption.ofResponses, a.Holds T (Step.State.init v) xs) :
    ¬ resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  intro hviol
  have htime : Step.TimelyRun T (Step.State.init v) xs := has .timelyClock (by simp [Step.Assumption.ofResponses])
  obtain ⟨M, hM, hsel, hrun, hA⟩ := runs_covered chk senv hL hB hnr hlen
    (runFits_of _ _ _ _ _ _ _ hin fun a ha => has a (List.mem_append_left _ ha))
  obtain ⟨a, ha, hna⟩ := hun.noModel M hM (hsel _ (unrollBase_dts L T P v senv hB))
  exact hna (((B.holds_withGoal g).2 ⟨hA, (respGoal_iff hrun hg).2 ⟨hsrc, hrf, htime, hviol⟩⟩) a ha)

/-- Goal soundness: in every model of prove's script for the response whose variables hold values of their sorts, the
steps decode to inputs that `validInputs` allows whose run from the initial state has timely clock lines and violates
the response. So a found
model always replays to a violation; prove's check of that is never the one that fails. -/
theorem response_sound (chk : Checked P E T v) (senv : StepEnv L (shapes v)) (hL : SortedLayout L) {M : Model}
    {resp : ResponseV v.event} {d : Nat} {B : UnrollBase v senv.nT} (hB : unrollBase L T P v senv d = .ok B)
    {g : Term} (hg : respGoalE L v resp B.steps = .ok g)
    (hM : ∀ n (h : n < B.tys.length), VarSorted L B.tys[n] (M.vars n))
    (hA : ∀ a ∈ (B.withGoal g).ask.script.asserts, Holds M a) :
    ∃ xs, B.steps.mapM (·.decode M L chk.callerData) = some xs ∧ Step.ShownRun T [] (Step.State.init v) xs ∧
      Step.TimelyRun T (Step.State.init v) xs ∧ resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  obtain ⟨hA, hgoal⟩ := (B.holds_withGoal g).1 hA
  obtain ⟨xs, hrun, hshown⟩ := unroll_decode chk senv hL hB hM hA
  obtain ⟨-, -, ht, hv⟩ := (respGoal_iff hrun hg).1 hgoal
  exact ⟨xs, unrollRun_decode _ _ _ hrun, hshown, ht, hv⟩

end

/-! No layout gap in a response's goal: the service's layout holds every type and kind the goal's codes need, since
the response's functions are among the functions the layout is built from (`rootUses`), so a refusal is the spec's,
never the builder's, and prove never reads one as an engine bug. -/

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV} {n : Nat}

theorem predT_sound {e : Ty} {f : Code (Ty.fn [e] Ty.bool)} (hf : CodeOk L P ds H _ f) (he : Avail L e) (ev : Term) :
    Sound (fun _ => True) (predT f ev) :=
  sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) ev he) fun _ hec =>
    sound_mono (apply_sound hf ⟨hec, trivial⟩ avail_bool) fun _ _ => trivial

theorem pred2T_sound {e : Ty} {f : Code (Ty.fn [e, e] Ty.bool)} (hf : CodeOk L P ds H _ f) (he : Avail L e)
    (tr ev : Term) : Sound (fun _ => True) (pred2T f tr ev) :=
  sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) tr he) fun _ htc =>
    sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) ev he) fun _ hec =>
    sound_mono (apply_sound hf ⟨htc, hec, trivial⟩ avail_bool) fun _ _ => trivial

variable {pred : Term → Except Refusal (Term × Term)} (hp : ∀ ev, Sound (fun _ => True) (pred ev))
include hp

theorem slotHitsT_sound : (S : List (Slot 1)) → Sound (fun _ => True) (slotHitsT pred S)
  | [] => trivial
  | (_, xs) :: S => sound_bind (hp xs[0]) fun _ _ => sound_bind (slotHitsT_sound S) fun _ _ => trivial

theorem kindHitsT_sound (out : StepOut v) : Sound (fun _ => True) (kindHitsT pred out) := by
  unfold kindHitsT
  split
  · exact sound_bind (slotHitsT_sound hp _) fun _ _ => trivial
  · trivial

end

theorem kindTimelyT_sound {L : Layout} {v : ServiceV} {n : Nat} (hL : SortedLayout L)
    (hm : ∀ m ∈ v.machines, MachineGot L m) (S : SymState v) :
    (inp : SymInput v (shapes v) n) → Sound (fun _ => True) (kindTimelyT L S inp)
  | .clock _ => sound_bind (dueAll_sound hL _ hm _ _) fun _ _ => trivial
  | .command .. | .query .. | .answer .. | .unmatched .. | .event .. => trivial

/-- `kindTerms` refuses only where `h` does. -/
theorem kindTerms_sound {v : ServiceV} {n : Nat} {α : Type} (st : UnrollStep v n)
    {h : SymInput v (shapes v) n × EncodedStep v → Except Refusal α} (hh : ∀ k, Sound (fun _ => True) (h k)) :
    Sound (fun _ => True) (st.kindTerms h) :=
  sound_mapM _ fun k _ => sound_bind (hh k) fun _ _ => trivial

theorem pickHitsT_sound {v : ServiceV} {n : Nat} {pred : Term → Except Refusal (Term × Term)}
    (hp : ∀ ev, Sound (fun _ => True) (pred ev)) (st : UnrollStep v n) : Sound (fun _ => True) (pickHitsT pred st) :=
  sound_bind (kindTerms_sound st fun k => kindHitsT_sound hp k.2.out) fun _ _ => trivial

section
variable {v : ServiceV} {n : Nat} {fa : Code (Ty.fn [v.event] Ty.bool)} {fq : Code (Ty.fn [v.event, v.event] Ty.bool)}
  {w : Int} (ha : ∀ tr, Sound (fun _ => True) (predT fa tr)) (hq : ∀ tr ev, Sound (fun _ => True) (pred2T fq tr ev))

include hq in
theorem lateT_sound (tr t0 : Term) : (sts : List (UnrollStep v n)) → Sound (fun _ => True) (lateT fq w tr t0 sts)
  | [] => trivial
  | st :: sts => sound_bind (pickHitsT_sound (hq tr) st) fun _ _ => sound_bind (lateT_sound tr t0 sts) fun _ _ => trivial

include ha hq in
theorem trigT_sound (st : UnrollStep v n) (sts : List (UnrollStep v n)) (tr : Term) :
    Sound (fun _ => True) (trigT fa fq w st sts tr) :=
  sound_bind (ha tr) fun _ _ => sound_bind (pickHitsT_sound (hq tr) st) fun _ _ =>
    sound_bind (lateT_sound hq tr _ sts) fun _ _ => trivial

include ha hq in
theorem violT_sound : (sts : List (UnrollStep v n)) → Sound (fun _ => True) (violT fa fq w sts)
  | [] => trivial
  | st :: sts => sound_bind (pickHitsT_sound (trigT_sound ha hq st sts) st) fun _ _ =>
    sound_bind (violT_sound sts) fun _ _ => trivial

end

/-- In each service's layout, built from a checked spec's program, a response's goal never refuses with a layout gap,
on any unrolled run: every refusal is the spec's (a limit, a string outside SMT-LIB's). -/
theorem respGoalE_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) {resp : ResponseV v.event}
    (hr : resp ∈ v.responses) {n : Nat} (sts : List (UnrollStep v n)) :
    Sound (fun _ => True) (respGoalE (Layout.ofService c.program.defs v) v resp sts) := by
  have h := serviceGot_ofService hv
  have chk := c.checked v hv
  have hev := avail_of_got h.event
  have hm : ∀ m ∈ v.machines, MachineGot _ m := fun m hm => (h.machines m hm).1.1
  refine sound_bind (Fun.code_ofService c hv _ (chk.reach.responses resp hr).1 (root_response hr).1)
    fun ⟨fa, _⟩ ha => sound_bind (Fun.code_ofService c hv _ (chk.reach.responses resp hr).2 (root_response hr).2)
    fun ⟨fq, _⟩ hq => sound_bind (violT_sound (predT_sound ha hev) (pred2T_sound hq hev) sts) fun _ _ =>
    sound_bind (sound_mapM sts fun st _ => ?_) fun _ _ => trivial
  exact sound_bind (kindTerms_sound st fun k => kindTimelyT_sound h.sorted hm st.before k.1) fun _ _ => trivial

end Tazuna.Smt
