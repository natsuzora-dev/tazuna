import Tazuna.Smt.GenGoal
import Tazuna.Smt.StepNoGap
import Tazuna.Semantics.Response

/-! A bounded response's goal on an unrolled run: the run violates the response (`respGoalE`). Per step it reads the
kind the step takes: whether some event the step applies satisfies `after` (opens) or `then` (answers), read off the
event slots of the step's end where the step reaches it, as generate's event goal reads them; the time the state after
the step holds; and, for a clock line, that it passes no timer that waits (`Step.timely`, the stated assumption
`timelyClock`). Over those moments the goal is `ResponseV.violated` written as terms (`violT`), so its exactness is
the computed form's. The response's functions are encoded as every kept function is, with conditions: the goal asks
that they hold for every event a step applies, so a model's terms say what the functions return.

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

/-- `kindHitsT` of the first kind the step picks, as `UnrollStep.takenT` reads. -/
def kindsHitsT (pred : Term → Except Refusal (Term × Term)) (picks : SymInput v (shapes v) n × EncodedStep v → Term) :
    List (SymInput v (shapes v) n × EncodedStep v) → Except Refusal (Term × Term)
  | [] => pure (ff, tt)
  | k :: ks => do
    let (h, c) ← kindHitsT pred k.2.out
    let (h', c') ← kindsHitsT pred picks ks
    pure (.ite (picks k) h h', .ite (picks k) c c')

section
variable (L : Layout)

/-- A clock line at `time` from `S` passes no timer that waits: no timer is due at `time - 1`. Other kinds ask
nothing. -/
def kindTimelyT (S : SymState v) : SymInput v (shapes v) n → Except Refusal Term
  | .clock time => do
    let dues ← dueAll L v.machines S.machines (.sub time (.int 1))
    pure (.not (minDueT dues).1)
  | _ => pure tt

/-- `kindTimelyT` of the first kind the step picks. -/
def kindsTimelyT (st : UnrollStep v n) : List (SymInput v (shapes v) n × EncodedStep v) → Except Refusal Term
  | [] => pure tt
  | k :: ks => do
    let t ← kindTimelyT L st.before k.1
    let t' ← kindsTimelyT st ks
    pure (.ite (st.picks k) t t')

end

/-- From the moment `t0`, some later moment comes past `t0 + within` with no moment before it answering
(`ResponseV.late`); each moment is whether it opens, whether it answers, and its time. -/
def lateT (within : Int) (t0 : Term) : List (Term × Term × Term) → Term
  | [] => ff
  | (_, a, t) :: ms => .or (.lt (.add t0 (.int within)) t) (andT (.not a) (lateT within t0 ms))

/-- The moments violate the response (`ResponseV.violated`). -/
def violT (within : Int) : List (Term × Term × Term) → Term
  | [] => ff
  | (o, a, t) :: ms => .or (andT o (andT (.not a) (lateT within t ms))) (violT within ms)

section
variable (L : Layout) (T : List TypeDecl) (v : ServiceV)

/-- One step's part of the goal: its moment (opens, answers, the time after it) and its condition (the response's
functions are exact at every event it applies, and a clock line is timely). -/
def stepRespT (fa fq : Code (Ty.fn [v.event] Ty.bool)) (st : UnrollStep v n) :
    Except Refusal ((Term × Term × Term) × Term) := do
  let (o, co) ← kindsHitsT (predT fa) st.picks st.kinds
  let (a, ca) ← kindsHitsT (predT fq) st.picks st.kinds
  let tm ← kindsTimelyT L st st.kinds
  pure ((o, a, st.after.now), andT co (andT ca tm))

/-- The response's goal on an unrolled run's steps: the functions' sources fit, every step's condition holds, and the
moments violate the response. -/
def respGoalE (resp : ResponseV v.event) (sts : List (UnrollStep v n)) : Except Refusal Term := do
  let (fa, ca) ← resp.after.code L
  let (fq, cq) ← resp.then_.code L
  let ms ← sts.mapM (stepRespT L v fa fq)
  pure (andT (andT ca cq) (andT (allT (ms.map (·.2))) (violT resp.within (ms.map (·.1)))))

end

end

/-! The semantic side. -/

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV}

/-- The response's functions fit the slots at every event each step of the run applies. -/
def RespFits (resp : ResponseV v.event) : State v → List (Input v) → Prop
  | _, [] => True
  | s, x :: xs => (∀ ev ∈ (step T v s x).events, resp.after.appFits L.count (ev, ()) ∧
      resp.then_.appFits L.count (ev, ())) ∧ RespFits resp (step T v s x).state xs

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

/-- `kindsHitsT` is the first picked kind's `kindHitsT`. -/
theorem kindsHitsT_find {pred : Term → Except Refusal (Term × Term)}
    {picks : SymInput v (shapes v) n × EncodedStep v → Term} :
    (ks : List (SymInput v (shapes v) n × EncodedStep v)) → {k : SymInput v (shapes v) n × EncodedStep v} →
    ks.find? (fun k => (picks k).denote M |>.toBool) = some k → {h c : Term} → kindsHitsT pred picks ks = .ok (h, c) →
    ∃ hk ck, kindHitsT pred k.2.out = .ok (hk, ck) ∧ (Holds M h ↔ Holds M hk) ∧ (Holds M c ↔ Holds M ck)
  | [], _, hf, _, _, _ => by cases hf
  | k' :: ks, k, hf, h, c, henc => by
    obtain ⟨⟨h1, c1⟩, e1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨h2, c2⟩, e2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    simp only [List.find?_cons] at hf
    simp only [holds_ite]
    cases hb : (picks k').denote M |>.toBool
    · rw [hb] at hf
      simpa using kindsHitsT_find ks hf e2
    · rw [hb] at hf
      cases hf
      exact ⟨h1, c1, e1, by simp, by simp⟩

theorem timely_iff_dues (s : State v) (time : Int) :
    Step.timely s time = true ↔ Step.dues s.machines.toSigma (time - 1) = [] := by
  simp only [Step.timely, Step.dues, List.all_eq_true, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine forall_congr' fun ⟨m, insts⟩ => imp_congr_right fun _ => forall_congr' fun i => imp_congr_right fun _ => ?_
  cases i.timer with
  | none => simp
  | some p => obtain ⟨d, _⟩ := p; simp; omega

/-- Whether a clock line of the run's step is timely (`Step.TimelyRun`'s per-step part). -/
def stepTimely (s : State v) : Input v → Prop
  | .clock time => Step.timely s time = true
  | _ => True

theorem timelyRun_cons (s : State v) (x : Input v) (xs : List (Input v)) :
    Step.TimelyRun T s (x :: xs) ↔ stepTimely s x ∧ Step.TimelyRun T (step T v s x).state xs := by
  cases x <;> exact Iff.rfl

theorem kindTimelyT_iff {hc : v.caller.isData = true} {S : SymState v} {s : State v}
    (hR : StateRel M L T (shapes v) S s) {inp : SymInput v (shapes v) n} {x : Input v} (hx : inp.decode M L hc = some x)
    {t : Term} (henc : kindTimelyT L S inp = .ok t) :
    Holds M t ↔ stepTimely s x := by
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
    obtain ⟨_, _, rfl, -⟩ := decode_command hx; cases pure_ok.1 henc; exact iff_of_true holds_tt trivial
  | query i a b =>
    obtain ⟨_, _, rfl, -⟩ := decode_query hx; cases pure_ok.1 henc; exact iff_of_true holds_tt trivial
  | event i a =>
    obtain ⟨_, rfl, -⟩ := decode_event hx; cases pure_ok.1 henc; exact iff_of_true holds_tt trivial
  | answer k j to w =>
    obtain ⟨_, _, _, rfl, -⟩ := decode_answer hx; cases pure_ok.1 henc; exact iff_of_true holds_tt trivial
  | unmatched t' to w =>
    obtain ⟨_, _, _, rfl, -⟩ := decode_answer hx; cases pure_ok.1 henc; exact iff_of_true holds_tt trivial

theorem kindsTimelyT_find {st : UnrollStep v n} :
    (ks : List (SymInput v (shapes v) n × EncodedStep v)) → {k : SymInput v (shapes v) n × EncodedStep v} →
    ks.find? (fun k => (st.picks k).denote M |>.toBool) = some k → {t : Term} → kindsTimelyT L st ks = .ok t →
    ∃ tk, kindTimelyT L st.before k.1 = .ok tk ∧ (Holds M t ↔ Holds M tk)
  | [], _, hf, _, _ => by cases hf
  | k' :: ks, k, hf, t, henc => by
    obtain ⟨t1, e1, henc⟩ := bind_ok.1 henc
    obtain ⟨t2, e2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    simp only [List.find?_cons] at hf
    simp only [holds_ite]
    cases hb : (st.picks k').denote M |>.toBool
    · rw [hb] at hf
      simpa using kindsTimelyT_find ks hf e2
    · rw [hb] at hf
      cases hf
      exact ⟨t1, e1, by simp⟩

/-- A step's moment terms relate to its moment: opens and answers as the response reads them, and its time. -/
def MomentRel (M : Model) (resp : ResponseV v.event) (t : Term × Term × Term) (m : Moment v.event) : Prop :=
  (Holds M t.1 ↔ resp.opens m = true) ∧ (Holds M t.2.1 ↔ resp.answers m = true) ∧ t.2.2.denote M = .int m.time

theorem lateT_iff (resp : ResponseV v.event) {t0 : Term} {x : Int} (h0 : t0.denote M = .int x) :
    {ts : List (Term × Term × Term)} → {ms : List (Moment v.event)} → Forall2 (MomentRel M resp) ts ms →
    (Holds M (lateT resp.within t0 ts) ↔ resp.late x ms = true)
  | [], [], _ => by simp [lateT, ResponseV.late, ff, Holds, Term.denote, Val.toBool]
  | (o, a, t) :: ts, m :: ms, ⟨⟨_, ha, ht⟩, hr⟩ => by
    simp only [lateT, ResponseV.late, holds_or, holds_andT, holds_not, lateT_iff resp h0 hr, ha, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
    simp only [Holds, Term.denote, h0, ht, Val.toInt, Val.toBool, decide_eq_true_eq, Bool.not_eq_true]

theorem violT_iff (resp : ResponseV v.event) : {ts : List (Term × Term × Term)} → {ms : List (Moment v.event)} →
    Forall2 (MomentRel M resp) ts ms → (Holds M (violT resp.within ts) ↔ resp.violated ms = true)
  | [], [], _ => by simp [violT, ResponseV.violated, ff, Holds, Term.denote, Val.toBool]
  | (o, a, t) :: ts, m :: ms, ⟨⟨ho, ha, ht⟩, hr⟩ => by
    simp only [violT, ResponseV.violated, holds_or, holds_andT, holds_not, violT_iff resp hr,
      lateT_iff resp ht hr, ho, ha, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', and_assoc, Bool.not_eq_true]

section
variable {resp : ResponseV v.event} {fa fq : Code (Ty.fn [v.event] Ty.bool)} {ca cq : Term}

/-- One step's part of the goal, at a step a model takes: its condition holds exactly when the response's functions
fit at every event the step applies and a clock line is timely, and then its moment terms relate to the step's
moment. -/
theorem stepRespT_iff (ha : resp.after.code L = .ok (fa, ca)) (hq : resp.then_.code L = .ok (fq, cq))
    (hca : Holds M ca) (hcq : Holds M cq) {hc : v.caller.isData = true} {st : UnrollStep v n} {s : State v}
    {x : Input v} (hat : StepAt L T M hc st s x) {mt : Term × Term × Term} {cond : Term}
    (henc : stepRespT L v fa fq st = .ok (mt, cond)) :
    (Holds M cond ↔ (∀ ev ∈ (step T v s x).events, resp.after.appFits L.count (ev, ()) ∧
        resp.then_.appFits L.count (ev, ())) ∧ stepTimely s x) ∧
      (Holds M cond → MomentRel M resp mt (step T v s x).moment) := by
  obtain ⟨⟨k, hk, hdec, hrel⟩, hno, hafter, hbefore⟩ := hat
  obtain ⟨⟨o, co⟩, e1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨a, cA⟩, e2, henc⟩ := bind_ok.1 henc
  obtain ⟨tm, e3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hfind : st.kinds.find? (fun k => (st.picks k).denote M |>.toBool) = some k := hk
  have hpA : PredExact M L v (predT fa) (fun ev => Step.toB (resp.after.fn (ev, ())))
      (fun ev => resp.after.appFits L.count (ev, ())) := fun _ _ _ h ev hr =>
    predT_encode v.event_data resp.after ha hca ev hr h
  have hpQ : PredExact M L v (predT fq) (fun ev => Step.toB (resp.then_.fn (ev, ())))
      (fun ev => resp.then_.appFits L.count (ev, ())) := fun _ _ _ h ev hr =>
    predT_encode v.event_data resp.then_ hq hcq ev hr h
  obtain ⟨hk1, ck1, f1, ho, hco⟩ := kindsHitsT_find st.kinds hfind e1
  obtain ⟨hk2, ck2, f2, hA, hcA⟩ := kindsHitsT_find st.kinds hfind e2
  obtain ⟨tk, f3, htm⟩ := kindsTimelyT_find st.kinds hfind e3
  have x1 := kindHitsT_iff hpA hdec hrel hno f1
  have x2 := kindHitsT_iff hpQ hdec hrel hno f2
  have x3 := kindTimelyT_iff hbefore hdec f3
  rw [holds_andT, holds_andT, hco, hcA, htm, x1.1, x2.1, x3]
  refine ⟨⟨fun ⟨h1, h2, h3⟩ => ⟨fun ev hev => ⟨h1 ev hev, h2 ev hev⟩, h3⟩,
    fun ⟨h12, h3⟩ => ⟨fun ev hev => (h12 ev hev).1, fun ev hev => (h12 ev hev).2, h3⟩⟩, fun ⟨h1, h2, _⟩ => ?_⟩
  refine ⟨?_, ?_, hafter.now⟩
  · rw [ho, x1.2 (x1.1.2 h1)]
    simp [ResponseV.opens, Result.moment, List.any_eq_true]
  · rw [hA, x2.2 (x2.1.2 h2)]
    simp [ResponseV.answers, Result.moment, List.any_eq_true]

/-- Over a model's run: the steps' conditions all hold exactly when the response's functions fit at every event the
run applies and every clock line is timely, and then the moment terms relate to the run's moments. -/
theorem stepsRespT_iff (ha : resp.after.code L = .ok (fa, ca)) (hq : resp.then_.code L = .ok (fq, cq))
    (hca : Holds M ca) (hcq : Holds M cq) {hc : v.caller.isData = true} :
    (s : State v) → (sts : List (UnrollStep v n)) → (xs : List (Input v)) → UnrollRun L T M hc s sts xs →
    {ms : List ((Term × Term × Term) × Term)} → sts.mapM (stepRespT L v fa fq) = .ok ms →
    (Holds M (allT (ms.map (·.2))) ↔ RespFits L T resp s xs ∧ Step.TimelyRun T s xs) ∧
      (Holds M (allT (ms.map (·.2))) →
        Forall2 (MomentRel M resp) (ms.map (·.1)) ((run T v s xs).2.map Result.moment))
  | _, [], [], _, ms, h => by
    cases pure_ok.1 h
    simp [holds_allT, RespFits, Step.TimelyRun, run, Forall2]
  | _, [], _ :: _, h, _, _ => h.elim
  | _, _ :: _, [], h, _, _ => h.elim
  | s, st :: sts, x :: xs, ⟨_, hat, hrun⟩, ms, h => by
    rw [List.mapM_cons] at h
    obtain ⟨m1, e1, h⟩ := bind_ok.1 h
    obtain ⟨ms', e2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have x1 := stepRespT_iff ha hq hca hcq hat e1
    have ih := stepsRespT_iff ha hq hca hcq _ sts xs hrun e2
    simp only [List.map_cons, holds_allT, List.mem_cons, forall_eq_or_imp] at ih ⊢
    refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
    · rw [x1.1, ih.1, timelyRun_cons]
      simp only [RespFits]
      constructor
      · rintro ⟨⟨hf, ht⟩, hf', ht'⟩; exact ⟨⟨hf, hf'⟩, ht, ht'⟩
      · rintro ⟨⟨hf, hf'⟩, ht, ht'⟩; exact ⟨⟨hf, ht⟩, hf', ht'⟩
    · simp only [run, List.map_cons]
      exact ⟨x1.2 h1, ih.2 h2⟩

/-- The goal on a model's run: it holds exactly when the response's functions fit (their sources, and at every event
the run applies), every clock line is timely and the run violates the response. -/
theorem respGoal_iff {hc : v.caller.isData = true} {s : State v} {sts : List (UnrollStep v n)}
    {xs : List (Input v)} (hrun : UnrollRun L T M hc s sts xs) {g : Term} (hg : respGoalE L v resp sts = .ok g) :
    Holds M g ↔ ((resp.after.fits L.count).1 ∧ (resp.then_.fits L.count).1) ∧ RespFits L T resp s xs ∧
      Step.TimelyRun T s xs ∧ resp.Violated ((run T v s xs).2.map Result.moment) := by
  obtain ⟨⟨fa', ca'⟩, ha, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨fq', cq'⟩, hq, hg⟩ := bind_ok.1 hg
  obtain ⟨ms, hms, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  have ea := (resp.after.code_exact (M := M) ha).1
  have eq := (resp.then_.code_exact (M := M) hq).1
  rw [holds_andT, holds_andT, holds_andT, ea, eq, ← resp.violated_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have x := stepsRespT_iff ha hq (ea.2 h1) (eq.2 h2) s sts xs hrun hms
    exact ⟨⟨h1, h2⟩, (x.1.1 h3).1, (x.1.1 h3).2, (violT_iff resp (x.2 h3)).1 h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have x := stepsRespT_iff ha hq (ea.2 h1) (eq.2 h2) s sts xs hrun hms
    have hc3 := x.1.2 ⟨h3, h4⟩
    exact ⟨⟨h1, h2⟩, hc3, (violT_iff resp (x.2 hc3)).2 h5⟩

end

variable {P : List AnySite} {E : List AnyEffectSite}

/-- T7: where prove's script for the response at depth `d` has no input kind refused, its goal is encoded and it has
no model, no run from the initial state of `d` inputs that fit the slots and are valid, whose steps stay within the
slots and fault nowhere, whose clock lines are timely and at whose events the response's functions fit, violates the
response. prove's "within the bounds" for a response is this at every depth up to the spec's steps, so no such run of
at most that many inputs violates it. -/
theorem response_within (chk : Checked P E T v) (senv : StepEnv L (shapes v)) (hL : SortedLayout L)
    {resp : ResponseV v.event} {d : Nat} {B : UnrollBase v senv.nT} (hB : unrollBase L T P v senv d = .ok B)
    {g : Term} (hg : respGoalE L v resp B.steps = .ok g) (hnr : B.refused = []) (hun : Unsat L (B.withGoal g).ask)
    {xs : List (Input v)} (hlen : xs.length = d) (hfits : RunFits L T P v chk.callerData (Step.State.init v) xs)
    (hsrc : (resp.after.fits L.count).1 ∧ (resp.then_.fits L.count).1)
    (hrf : RespFits L T resp (Step.State.init v) xs) (htime : Step.TimelyRun T (Step.State.init v) xs) :
    ¬ resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  intro hviol
  obtain ⟨M, hM, hrun, hA⟩ := runs_covered chk senv hL hB hnr hlen hfits
  obtain ⟨a, ha, hna⟩ := hun.noModel M hM
  exact hna (((B.holds_withGoal g).2 ⟨hA, (respGoal_iff hrun hg).2 ⟨hsrc, hrf, htime, hviol⟩⟩) a ha)

/-- Goal soundness: in every model of prove's script for the response whose variables hold values of their sorts, the
steps decode to inputs whose run from the initial state has timely clock lines and violates the response. So a found
model always replays to a violation; prove's check of that is never the one that fails. -/
theorem response_sound (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {M : Model}
    {resp : ResponseV v.event} {d : Nat} {B : UnrollBase v senv.nT} (hB : unrollBase L T P v senv d = .ok B)
    {g : Term} (hg : respGoalE L v resp B.steps = .ok g)
    (hM : ∀ n (h : n < B.tys.length), VarSorted L B.tys[n] (M.vars n))
    (hA : ∀ a ∈ (B.withGoal g).ask.script.asserts, Holds M a) :
    ∃ xs, B.steps.mapM (·.decode M L chk.callerData) = some xs ∧ Step.TimelyRun T (Step.State.init v) xs ∧
      resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  obtain ⟨hA, hgoal⟩ := (B.holds_withGoal g).1 hA
  obtain ⟨xs, hrun⟩ := unroll_decode chk senv hB hM hA
  obtain ⟨-, -, ht, hv⟩ := (respGoal_iff hrun hg).1 hgoal
  exact ⟨xs, unrollRun_decode _ _ _ hrun, ht, hv⟩

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

variable {pred : Term → Except Refusal (Term × Term)} (hp : ∀ ev, Sound (fun _ => True) (pred ev))
include hp

theorem slotHitsT_sound : (S : List (Slot 1)) → Sound (fun _ => True) (slotHitsT pred S)
  | [] => trivial
  | (_, xs) :: S => sound_bind (hp xs[0]) fun _ _ => sound_bind (slotHitsT_sound S) fun _ _ => trivial

theorem kindsHitsT_sound (picks : SymInput v (shapes v) n × EncodedStep v → Term) :
    (ks : List (SymInput v (shapes v) n × EncodedStep v)) → Sound (fun _ => True) (kindsHitsT pred picks ks)
  | [] => trivial
  | k :: ks => by
    refine sound_bind (p := fun _ => True) ?_ fun _ _ => sound_bind (kindsHitsT_sound picks ks) fun _ _ => trivial
    unfold kindHitsT
    split
    · exact sound_bind (slotHitsT_sound hp _) fun _ _ => trivial
    · trivial

end

theorem kindsTimelyT_sound {L : Layout} {v : ServiceV} {n : Nat} (hL : SortedLayout L)
    (hm : ∀ m ∈ v.machines, MachineGot L m) (st : UnrollStep v n) :
    (ks : List (SymInput v (shapes v) n × EncodedStep v)) → Sound (fun _ => True) (kindsTimelyT L st ks)
  | [] => trivial
  | (inp, _) :: ks => by
    refine sound_bind (p := fun _ => True) ?_ fun _ _ => sound_bind (kindsTimelyT_sound hL hm st ks) fun _ _ => trivial
    cases inp with
    | clock time => exact sound_bind (dueAll_sound hL _ hm _ _) fun _ _ => trivial
    | _ => trivial

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
    fun ⟨fq, _⟩ hq => sound_bind (sound_mapM sts fun st _ => ?_) fun _ _ => trivial
  exact sound_bind (kindsHitsT_sound (predT_sound ha hev) _ _) fun _ _ =>
    sound_bind (kindsHitsT_sound (predT_sound hq hev) _ _) fun _ _ =>
    sound_bind (kindsTimelyT_sound h.sorted hm st _) fun _ _ => trivial

end Tazuna.Smt
