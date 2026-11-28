import Tazuna.Smt.GenGoal
import Tazuna.Smt.Reached
import Tazuna.Smt.Boundary
import Tazuna.Semantics.Response
import Tazuna.Smt.DecodeTotal

/-! A response proved by induction over steps (Lamport, "Real Time is Really Simple", sec 3.3): the response names the
deadline the records keep for each trigger (`deadline`), and prove asks of each input kind one question whether its
step, from a state of the right shape whose invariants hold, does one of three things:

* applies a trigger that no event of the same step answers and whose deadline, after the step, is missing or later
  than the step's time plus `within` (the trigger opens an item in time);
* closes the item of a trigger `tr`, whose deadline was `d` before the step, with no event of the step answering
  `tr`, or leaves it open with a deadline later than `d` (an open item waits for its answer, and its deadline never
  moves later);
* is a timely clock line past `d` while the item of `tr` is open with the deadline `d` (the clock cannot pass a
  deadline that waits).

`tr` is a free variable after the state's and the input's: a question speaks of every trigger value at once. The
last two are asked only where every machine's `instances` fits at the records, so the instance shape holds in full; a
step within the slots leaves records where it does (`Ended.fits`), and they are needed only after the trigger's step.
Where every kind's question has no model, no run on valid inputs with timely clock lines violates the response,
whatever its length (`response_scoped`, `response_holds`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-! The terms a response question reads of a step: its events against a predicate, and the timely-clock term. -/

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

/-- A clock line at `time` from `S` passes no timer that waits: no timer is due at `time - 1`, where every `timer`
fits. Other kinds ask nothing. -/
def kindTimelyT (S : SymState v) : SymInput v (shapes v) n → Except Refusal Term
  | .clock time => do
    let (tmss, ct) ← timersAll L v.machines S.machines S.records
    let dues ← dueAll L v.machines S.machines tmss (.sub time (.int 1))
    pure (andT ct (.not (minDueT dues).1))
  | _ => pure tt

end

/-- A response's `then` code applied to the trigger term `tr` and the event term `ev`: whether it holds, and its
condition. -/
def pred2T {e : Ty} (f : Code (Ty.fn [e, e] Ty.bool)) (tr ev : Term) : Except Refusal (Term × Term) := do
  let tc ← Code.ofDataE e tr
  let ec ← Code.ofDataE e ev
  f (tc, ec, ())

end

/-! The semantic side of the terms. -/

section
variable (L : Layout) {v : ServiceV}

/-- Every `timer` fits at the state a clock line comes to, which the timely-clock term reads. -/
def ClockFits (s : State v) : Input v → Prop
  | .clock _ => timersFit L.count s.records s.machines
  | _ => True

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
    Step.timely s time = true ↔ Step.dues s.records s.machines.toSigma (time - 1) = [] := by
  simp only [Step.timely, Step.dues, List.all_eq_true, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff]
  refine forall_congr' fun ⟨m, insts⟩ => imp_congr_right fun _ => forall_congr' fun i => imp_congr_right fun _ => ?_
  cases Step.timerOf s.records i with
  | none => simp
  | some p => obtain ⟨d, _⟩ := p; simp; omega

theorem kindTimelyT_iff {hc : v.caller.isData = true} {S : SymState v} {s : State v}
    (hR : StateRel M L T (shapes v) S s) {inp : SymInput v (shapes v) n} {x : Input v} (hx : inp.decode M L hc = some x)
    {t : Term} (henc : kindTimelyT L S inp = .ok t) :
    Holds M t ↔ ClockFits L s x ∧ Step.timelyAt s x = true := by
  cases inp with
  | clock tm =>
    obtain ⟨time, rfl, htm⟩ := decode_clock hx
    obtain ⟨⟨tmss, ct⟩, h0, henc⟩ := bind_ok.1 henc
    obtain ⟨dues, h1, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have ET := timersAll_encode (T := T) s.records hR.records v.machines S.machines s.machines hR.machines h0
    show Holds M (andT ct (Term.not _)) ↔ timersFit L.count s.records s.machines ∧ Step.timely s time = true
    rw [holds_andT, ET.1]
    refine and_congr_right fun htf => ?_
    have hnow : (Term.sub tm (.int 1)).denote M = .int (time - 1) := by simp [Term.denote, htm, Val.toInt]
    obtain ⟨os, hF, hP⟩ := dueAll_rel (T := T) s.records hnow v.machines S.machines s.machines hR.machines
      (ET.2 (ET.1.2 htf)) h1
    obtain ⟨hhas, -⟩ := minDue_den hF
    rw [min?_perm hP] at hhas
    rw [holds_not, timely_iff_dues]
    simp only [Holds, hhas, Val.toBool, Option.isSome_iff_ne_none, ne_eq, List.min?_eq_none_iff, Decidable.not_not]
  | command i a b =>
    obtain ⟨_, _, rfl, -⟩ := decode_command hx; cases pure_ok.1 henc
    exact iff_of_true holds_tt ⟨trivial, rfl⟩
  | query i a b =>
    obtain ⟨_, _, rfl, -⟩ := decode_query hx; cases pure_ok.1 henc
    exact iff_of_true holds_tt ⟨trivial, rfl⟩
  | event i a =>
    obtain ⟨_, rfl, -⟩ := decode_event hx; cases pure_ok.1 henc
    exact iff_of_true holds_tt ⟨trivial, rfl⟩
  | answer k j to w =>
    obtain ⟨_, _, _, rfl, -⟩ := decode_answer hx; cases pure_ok.1 henc
    exact iff_of_true holds_tt ⟨trivial, rfl⟩
  | unmatched t' to w =>
    obtain ⟨_, _, _, rfl, -⟩ := decode_answer hx; cases pure_ok.1 henc
    exact iff_of_true holds_tt ⟨trivial, rfl⟩

section
variable {resp : ResponseV v.records v.event} {fa : Code (Ty.fn [v.event] Ty.bool)}
  {fq : Code (Ty.fn [v.event, v.event] Ty.bool)} {ca cq : Term}
  (ha : resp.after.code L = .ok (fa, ca)) (hq : resp.then_.code L = .ok (fq, cq)) (hca : Holds M ca)
  (hcq : Holds M cq)

include hq hcq in
theorem ansT_exact {tv : v.event.den0} {tr : Term} (hr : RelV L v.event (Ty.up _ v.event_data tv) (tr.denote M)) :
    PredExact M L v (pred2T fq tr) (fun ev => Step.toB (resp.then_.fn (tv, ev, ())))
      (fun ev => resp.then_.appFits L.count (tv, ev, ())) :=
  fun _ _ _ h ev hr' => pred2T_encode v.event_data resp.then_ hq hcq tv ev hr hr' h

end

end

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

theorem kindTimelyT_sound {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite}
    {v : ServiceV} {n : Nat} (hL : SortedLayout L)
    (hm : ∀ m ∈ v.machines, MachineGot L m ∧ MachineCodes L P ds H m) (S : SymState v) :
    (inp : SymInput v (shapes v) n) → Sound (fun _ => True) (kindTimelyT L S inp)
  | .clock _ => sound_bind (timersAll_sound hL _ hm _ _) fun _ _ =>
      sound_bind (dueAll_sound hL _ (fun m h => (hm m h).1) _ _ _) fun _ _ => trivial
  | .command .. | .query .. | .answer .. | .unmatched .. | .event .. => trivial

/-! The response question. -/

section
variable (L : Layout) {v : ServiceV}

/-- The response's `deadline` code applied to the records term `records` and the trigger term `tr`: whether it gives a
deadline, the deadline, and its condition. -/
def deadlineT (fd : Code (Ty.fn [v.records, v.event] (Ty.option (.point .ms)))) (records tr : Term) :
    Except Refusal (Term × Term × Term) := do
  let rc ← Code.ofDataE v.records records
  let ec ← Code.ofDataE v.event tr
  let (o, c) ← fd (rc, ec, ())
  let ot ← Code.dataTermE _ o
  let (d, _) ← L.findE (Ty.option (.point .ms))
  pure (.is d 0 ot, .sel d 0 0 ot, c)

/-- Where a step of the kind ends accepted: it reaches its end, its cascade does not fault, and the invariants hold
after it. A kind with no end is never accepted with events. -/
def acceptedT (out : StepOut v) : Term :=
  match out.finish? with
  | some fo => andT out.reached (andT (.not fo.settle.faultT)
      (andT (allT (fo.invariants.map (·.2))) (allT (fo.checks.toList.map instHoldT))))
  | none => ff

/-- The time after an accepted step of the kind: a clock line's, else the state's. -/
def SymInput.nowAfter {shs : List (PendingShape v.event)} {n : Nat} (S : SymState v) : SymInput v shs n → Term
  | .clock time => time
  | _ => S.now

section
variable (fa : Code (Ty.fn [v.event] Ty.bool)) (fq : Code (Ty.fn [v.event, v.event] Ty.bool))
  (fd : Code (Ty.fn [v.records, v.event] (Ty.option (.point .ms)))) (within : Int)

/-- The event term `ev` of the step is a trigger that no event of the step answers and whose deadline after the step
is missing or past `now + within`, with its condition. -/
def lateOpenAt (out : StepOut v) (records now ev : Term) : Except Refusal (Term × Term) := do
  let (o, co) ← predT fa ev
  let (an, can) ← kindHitsT (pred2T fq ev) out
  let (has, dl, cd) ← deadlineT L fd records ev
  pure (andT o (andT (.not an) (.not (andT has (.le dl (.add now (.int within)))))), andT co (andT can cd))

/-- The response's goal for one input kind's step from `S` on `inp`, with the trigger variable `tr`, in two parts:
the step opens a trigger late; the step closes or delays the item of `tr`, or is a timely clock line past its
deadline. Both read only accepted steps. The last term is the condition that the response's functions are exact
there. -/
def respGoalT {shs : List (PendingShape v.event)} {n : Nat} (S : SymState v) (inp : SymInput v shs n) (out : StepOut v)
    (tr : Term) : Except Refusal (Term × Term × Term) := do
  match out.finish? with
  | none => pure (ff, ff, tt)
  | some fo =>
    let records' := fo.settle.terms.done.records
    let now' := inp.nowAfter S
    let acc := acceptedT out
    let (opens, co) ← kindHitsT (lateOpenAt L fa fq fd within out records' now') out
    let (has, d, c1) ← deadlineT L fd S.records tr
    let (an, can) ← kindHitsT (pred2T fq tr) out
    let (has', d', c2) ← deadlineT L fd records' tr
    let moved := andT has (andT (.not an) (.not (andT has' (.le d' d))))
    let past := match inp with
      | .clock time => andT has (.lt d time)
      | _ => ff
    pure (andT acc opens, andT acc (.or moved past), andT co (andT c1 (andT can c2)))

end

/-- The trigger variable of an input kind's response question: the first after the state's and the input's. -/
def trigVar {shs : List (PendingShape v.event)} {n : Nat} (inp : SymInput v shs n) : Nat :=
  stateWidth v + inp.tys.length

/-- The response question of an input kind: from a state of the right shape whose invariants hold, within the side
conditions and the step's condition, the response's functions miss their slots, or the step breaks the response as
`respGoalT` reads it, a clock line being timely. The second part is asked only where every machine's `instances`
fits at the records, so the instance shape holds there in full: a state after a step within the slots has it, and
the part is needed only after the step that applies the trigger. -/
def respStep {n : Nat} (resp : ResponseV v.records v.event) (inp : SymInput v (shapes v) n) (a : StepAsk v) :
    Except Refusal TypedScript := do
  let (fa, ca) ← resp.after.code L
  let (fq, cq) ← resp.then_.code L
  let (fd, cd) ← resp.deadline.code L
  let tr : Term := .var (trigVar inp)
  let twf ← need (lacksData v.event) (wfT L v.event tr)
  let srt ← need (lacks v.event) (L.srt? v.event)
  let S : SymState v := SymState.vars 0
  let tm ← kindTimelyT L S inp
  let (gOpen, gKeep, c) ← respGoalT L fa fq fd (resp.withinNat : Int) S inp a.t.out tr
  let fits ← instFitsT L v.machines S.records
  let q := a.ask (andT tm (.or (.not (andT (andT ca (andT cq cd)) c)) (.or gOpen (andT fits gKeep))))
  pure { q with tys := q.tys ++ [v.event], vars := q.vars ++ [srt], context := q.context ++ [twf] }

end

/-! The semantic side. -/

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

/-- A term of an `Option(Int)` value: its variant test and its field. -/
theorem optionInt_view {dopt n1 : Nat} (h1 : L.find? (Ty.option (.point .ms)) = some (dopt, n1))
    (hd : (Ty.option (.point .ms)).isData = true) (o : (Ty.option (.point .ms)).den0) {ot : Term}
    (ho : RelV L _ (Ty.up _ hd o) (ot.denote M)) :
    (Term.is dopt 0 ot).denote M = .bool (Step.optionInt o).isSome ∧
      ∀ dl, Step.optionInt o = some dl → (Term.sel dopt 0 0 ot).denote M = .int dl := by
  have h1t : (Ty.tuple [.point .ms]).isData = true := by simp [Ty.isData, Ty.isDatas]
  have hnone : (Ty.adt 3 [.point .ms] [[]]).isData = true := by simp [Ty.isData, Ty.isDatass, Ty.isDatas]
  obtain ⟨d', n', hf', hra⟩ := ho
  obtain rfl := find_det hf' h1
  match o with
  | .inl (dl, ()) =>
    erw [Ty.up_inl 3 _ [.point .ms] [[]] hd h1t] at hra
    obtain ⟨vals, hv, hvals⟩ := hra
    erw [Ty.up_tuple _ _ _ rfl rfl] at hvals
    obtain ⟨v0, _, rfl, hv0, rfl⟩ := hvals
    change v0 = .int dl at hv0
    subst hv0
    refine ⟨by simp [Term.denote, hv, Step.optionInt]; rfl, fun dl' h => ?_⟩
    simp only [Step.optionInt] at h
    cases h
    simp [Term.denote, hv]
  | .inr (.inl ()) =>
    erw [Ty.up_inr 3 _ [.point .ms] [[]] hd hnone, Ty.up_inl 3 _ [] [] hnone rfl] at hra
    obtain ⟨vals, hv, -⟩ := hra
    exact ⟨by simp [Term.denote, hv, Step.optionInt], fun _ h => nomatch h⟩
  | .inr (.inr x) => nomatch x

/-- The deadline terms of the records term and the trigger term: the condition holds exactly when `deadline` fits
there, and then the terms say whether it gives a deadline and which. -/
theorem deadlineT_encode (resp : ResponseV v.records v.event) {fd : Code (Ty.fn [v.records, v.event] (Ty.option (.point .ms)))}
    {cd : Term} (hfd : resp.deadline.code L = .ok (fd, cd)) (hcd : Holds M cd) (recs : v.records.den0)
    (tr : v.event.den0) {rt et : Term} (hr : RelV L v.records (Ty.up _ v.records_data recs) (rt.denote M))
    (he : RelV L v.event (Ty.up _ v.event_data tr) (et.denote M)) {has d c : Term}
    (h : deadlineT L fd rt et = .ok (has, d, c)) :
    (Holds M c ↔ resp.deadline.appFits L.count (recs, tr, ())) ∧
      (Holds M c → (Holds M has ↔ (resp.deadlineAt recs tr).isSome) ∧
        ∀ dl, resp.deadlineAt recs tr = some dl → d.denote M = .int dl) := by
  obtain ⟨rc, h1, h⟩ := bind_ok.1 h
  obtain ⟨ec, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨o, c'⟩, h3, h⟩ := bind_ok.1 h
  obtain ⟨ot, h4, h⟩ := bind_ok.1 h
  obtain ⟨⟨dopt, n1⟩, h5, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hrc : Smt.Rel M L _ (Ty.up _ v.records_data recs) rc := (rel_ofTerm (need_ok.1 h1) _).2 hr
  have hec : Smt.Rel M L _ (Ty.up _ v.event_data tr) ec := (rel_ofTerm (need_ok.1 h2) _).2 he
  have hargs : (Ty.tuple [v.records, v.event]).isData = true := by
    simp [Ty.isData, Ty.isDatas, v.records_data, v.event_data]
  have hnf : ∀ t ∈ [v.records, v.event], t.isFn = false := by
    simp [ofTerm_notFn (need_ok.1 h1), ofTerm_notFn (need_ok.1 h2)]
  refine ⟨resp.deadline.app_exact hfd hcd hnf _ _ (rels2 v.records_data v.event_data hargs hrc hec) h3, fun hc => ?_⟩
  have hod : (Ty.option (.point .ms)).isData = true := by simp [Ty.option, Ty.isData, Ty.isDatass, Ty.isDatas]
  have hb := resp.deadline.code_fn resp.deadline.ht hfd hcd _ _ (rels2 v.records_data v.event_data hargs hrc hec) o c h3 hc
  erw [Ty.up_fn _ (Ty.option (.point .ms)) _ hargs hod] at hb
  have hot := (rel_term (need_ok.1 h4) _).1 hb
  obtain ⟨his, hsel⟩ := optionInt_view (need_ok.1 h5) hod _ hot
  refine ⟨?_, fun dl hdl => hsel dl hdl⟩
  simp only [Holds, his, Val.toBool, ResponseV.deadlineAt]

/-- An accepted step reaches its end, from a step in progress at the time after the step. -/
theorem rel_reached {n : Nat} {hc : v.caller.isData = true} {inp : SymInput v (shapes v) n} {out : StepOut v}
    {s : State v} {x : Input v} (hR : StateRel M L T (shapes v) (SymState.vars 0) s) (hx : inp.decode M L hc = some x)
    (hrel : out.Rel M L T (shapes v) s x (step T v s x)) (hacc : (step T v s x).outcome = .accepted) :
    ∃ fo, out.finish? = some fo ∧ Holds M out.reached ∧ ∃ s0 a,
      (inp.nowAfter (SymState.vars 0)).denote M = .int a.state.now ∧
      Finished M L T (shapes v) fo s0 a .accepted (step T v s x) := by
  generalize step T v s x = r at hrel hacc
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases out with
    | command o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · rename_i hcall
        split at hrel
        · subst hrel; cases hacc
        · rename_i hr
          split at hrel
          · rename_i hok
            split at hrel
            · subst hrel; cases hacc
            · rename_i he
              refine ⟨_, rfl, ?_, _, _, by exact hR.now, hrel⟩
              simp only [StepOut.reached, holds_andT]
              exact ⟨hcall, (holds_allT_rules _).2 hr, hok, (holds_allT_rules _).2 he⟩
          · obtain ⟨-, j, hj, -⟩ := hrel; rw [hj] at hacc; cases hacc
      · subst hrel; cases hacc
    | _ => simp only [StepOut.Rel] at hrel
  | query i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
    cases out with
    | query o => obtain ⟨-, hq⟩ := hrel; rw [hacc] at hq; exact hq.elim
    | _ => simp only [StepOut.Rel] at hrel
  | answer k j to w =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases out with
    | answer o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · subst hrel; cases hacc
      · rename_i hr; exact ⟨_, rfl, (holds_allT_rules _).2 hr, _, _, by exact hR.now, hrel⟩
    | unmatched _ => simp only [StepOut.Rel] at hrel; subst hrel; cases hacc
    | _ => simp only [StepOut.Rel] at hrel
  | unmatched t to w =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases out with
    | answer o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · subst hrel; cases hacc
      · rename_i hr; exact ⟨_, rfl, (holds_allT_rules _).2 hr, _, _, by exact hR.now, hrel⟩
    | unmatched _ => simp only [StepOut.Rel] at hrel; subst hrel; cases hacc
    | _ => simp only [StepOut.Rel] at hrel
  | event i w =>
    obtain ⟨value, rfl, -⟩ := decode_event hx
    cases out with
    | event o => exact ⟨_, rfl, holds_tt, _, _, by exact hR.now, hrel⟩
    | _ => simp only [StepOut.Rel] at hrel
  | clock w =>
    obtain ⟨time, rfl, htm⟩ := decode_clock hx
    cases out with
    | clock o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · rename_i hfw
        split at hrel
        · subst hrel; cases hacc
        · rename_i hov
          refine ⟨_, rfl, ?_, _, _, by exact htm, hrel⟩
          simp only [StepOut.reached, holds_andT, holds_not]
          exact ⟨hfw, by simpa [Holds] using hov⟩
      · subst hrel; cases hacc
    | _ => simp only [StepOut.Rel] at hrel

/-- An accepted step's end, as the terms say: the step is accepted by them (`acceptedT`), the records term after it
denotes its records, the time after it is `nowAfter`'s, and every machine's `instances` fits at its records. -/
theorem accepted_end {n : Nat} {hc : v.caller.isData = true} {inp : SymInput v (shapes v) n} {out : StepOut v}
    {s : State v} {x : Input v} (hR : StateRel M L T (shapes v) (SymState.vars 0) s) (hx : inp.decode M L hc = some x)
    (hrel : out.Rel M L T (shapes v) s x (step T v s x)) (hacc : (step T v s x).outcome = .accepted) :
    ∃ fo, out.finish? = some fo ∧ Holds M (acceptedT out) ∧
      RelV L v.records (Ty.up _ v.records_data (step T v s x).state.records) (fo.settle.terms.done.records.denote M) ∧
      (inp.nowAfter (SymState.vars 0)).denote M = .int (step T v s x).state.now ∧
      instFitsAt L.count v.machines (step T v s x).state.records := by
  obtain ⟨fo, hfo, hre, s0, a, hnow, hF, hm⟩ := rel_reached hR hx hrel hacc
  generalize step T v s x = r at hacc hm
  revert hm
  cases hfa : fo.settle.fault? M with
  | some f => intro hm; simp only at hm; rw [hm] at hacc; cases hacc
  | none =>
    intro hm
    simp only at hm
    revert hm
    cases hb : brokenIn M fo.invariants ++ checksBroken L T M v.machines fo.checks with
    | cons _ _ => intro hm; simp only at hm; rw [hm] at hacc; cases hacc
    | nil =>
      intro hm
      obtain ⟨e, he⟩ := hm
      obtain ⟨hb1, hb2⟩ := List.append_eq_nil_iff.1 hb
      have hft : fo.settle.faultT.denote M = .bool false := by rw [hF, hfa]; rfl
      refine ⟨fo, hfo, ?_, by rw [he.result]; exact he.records, by rw [he.result]; exact hnow,
        by rw [he.result]; exact he.fits⟩
      simp only [acceptedT, hfo, holds_andT, holds_not]
      exact ⟨hre, by simp [Holds, hft, Val.toBool], (holds_allT_rules _).2 hb1, instHold_of_nil _ _ hb2⟩

/-- A step that is not accepted leaves the records and the time as they were. -/
theorem rel_quiet {n : Nat} {hc : v.caller.isData = true} {inp : SymInput v (shapes v) n} {out : StepOut v}
    {s : State v} {x : Input v} (hx : inp.decode M L hc = some x)
    (hrel : out.Rel M L T (shapes v) s x (step T v s x)) (hna : (step T v s x).outcome ≠ .accepted) :
    (step T v s x).state.records = s.records ∧ (step T v s x).state.now = s.now := by
  have fin : ∀ {fo : FinishOut v} {s0 : State v} {a : Step.Acc v} {r : Result v}, s0 = s →
      Finished M L T (shapes v) fo s0 a .accepted r → r.outcome ≠ .accepted →
      r.state.records = s.records ∧ r.state.now = s.now := by
    intro fo s0 a r h0 hF hn
    obtain ⟨-, hm⟩ := hF
    split at hm
    · subst hm h0; exact ⟨rfl, rfl⟩
    · split at hm
      · subst hm h0; exact ⟨rfl, rfl⟩
      · obtain ⟨e, he⟩ := hm; rw [he.result] at hn; exact absurd rfl hn
  generalize step T v s x = r at hrel hna
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases out with
    | command o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · split at hrel
        · subst hrel; exact ⟨rfl, rfl⟩
        · split at hrel
          · split at hrel
            · subst hrel; exact ⟨rfl, rfl⟩
            · obtain ⟨-, hm⟩ := hrel
              split at hm
              · subst hm; exact ⟨rfl, rfl⟩
              · split at hm
                · subst hm; exact ⟨rfl, rfl⟩
                · obtain ⟨e, he⟩ := hm; rw [he.result] at hna; exact absurd rfl hna
          · obtain ⟨h, -⟩ := hrel; rw [h]; exact ⟨rfl, rfl⟩
      · subst hrel; exact ⟨rfl, rfl⟩
    | _ => simp only [StepOut.Rel] at hrel
  | query i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
    cases out with
    | query o => obtain ⟨h, -⟩ := hrel; rw [h]; exact ⟨rfl, rfl⟩
    | _ => simp only [StepOut.Rel] at hrel
  | answer k j to w =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases out with
    | answer o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · subst hrel; exact ⟨rfl, rfl⟩
      · exact fin rfl hrel hna
    | unmatched _ => simp only [StepOut.Rel] at hrel; subst hrel; exact ⟨rfl, rfl⟩
    | _ => simp only [StepOut.Rel] at hrel
  | unmatched t to w =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases out with
    | answer o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · subst hrel; exact ⟨rfl, rfl⟩
      · exact fin rfl hrel hna
    | unmatched _ => simp only [StepOut.Rel] at hrel; subst hrel; exact ⟨rfl, rfl⟩
    | _ => simp only [StepOut.Rel] at hrel
  | event i w =>
    obtain ⟨value, rfl, -⟩ := decode_event hx
    cases out with
    | event o => exact fin rfl hrel hna
    | _ => simp only [StepOut.Rel] at hrel
  | clock w =>
    obtain ⟨time, rfl, -⟩ := decode_clock hx
    cases out with
    | clock o =>
      simp only [StepOut.Rel] at hrel
      split at hrel
      · split at hrel
        · subst hrel; exact ⟨rfl, rfl⟩
        · exact fin rfl hrel hna
      · subst hrel; exact ⟨rfl, rfl⟩
    | _ => simp only [StepOut.Rel] at hrel

/-- The side conditions of an input kind's questions hold the step's codes and sites. -/
theorem stepAsk_side {senv : StepEnv L (shapes v)} {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v} (ha : stepAsk L T P v senv inp = .ok a)
    (h : Holds M a.side) : Holds M a.t.codes ∧ Holds M a.t.sites := by
  simp only [stepAsk] at ha
  repeat (obtain ⟨_, -, ha⟩ := bind_ok.1 ha)
  cases pure_ok.1 ha
  simp only [holds_andT] at h
  exact ⟨h.1, h.2.1⟩

theorem holds_le_of {a b : Term} {x y : Int} (ha : a.denote M = .int x) (hb : b.denote M = .int y) :
    Holds M (.le a b) ↔ x ≤ y := by
  simp [Holds, Term.denote, ha, hb, Val.toInt, Val.toBool]

theorem holds_lt_of {a b : Term} {x y : Int} (ha : a.denote M = .int x) (hb : b.denote M = .int y) :
    Holds M (.lt a b) ↔ x < y := by
  simp [Holds, Term.denote, ha, hb, Val.toInt, Val.toBool]

/-- A clock line that a step accepts fits its timers, which its step condition asks of the first firing round. -/
theorem clockFits_of {s : State v} {x : Input v} (hst : stepFits L.count T (shapes v) s x)
    (hacc : (step T v s x).outcome = .accepted) : ClockFits L s x := by
  cases x with
  | clock time =>
    have hle : s.now ≤ time := by
      refine Classical.byContradiction fun hlt => ?_
      simp only [step, show time < s.now by omega, ite_true] at hacc
      cases hacc
    have hr := (hst hle).1
    simp only [roundsFit] at hr
    exact hr.1.1
  | _ => trivial

/-- The response question in one model: where the symbolic state, input and trigger decode to a state of the right
shape whose invariants hold, an input and a trigger, the model satisfies some assertion of the question nowhere, and the
step fits the slots and is timely, the step opens each trigger it does not answer with a deadline in time, and where
every machine's `instances` fits at the records before it, it keeps the trigger's deadline and passes none. -/
theorem step_keeps (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {resp : ResponseV v.records v.event}
    {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v} {q : TypedScript}
    (ha : stepAsk L T P v senv inp = .ok a) (hq : respStep L resp inp a = .ok q)
    (hun : ∃ c ∈ q.script.asserts, ¬ Holds M c)
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hkeys : Step.KeysOk T s) (hheld : Step.invariants s = [])
    {hc : v.caller.isData = true} {x : Input v} (hx : inp.decode M L hc = some x)
    (hcase : ∀ t, encodeStep L T P v senv (SymState.vars 0) inp = .ok t → Holds M t.out.case)
    (hb : (∃ c ∈ a.bound.script.asserts, ¬ Holds M c) ∨ StepFits L T P v s x) (htime : Step.timelyAt s x = true)
    {tr : v.event.den0} (htr : decodeV L v.event (M.vars (trigVar inp)) = some (Ty.up _ v.event_data tr)) :
    (∀ ev ∈ (step T v s x).events, resp.opens ev = true → resp.answers ev (step T v s x).moment = false →
      ∃ d, resp.deadlineAt (step T v s x).state.records ev = some d ∧
        d ≤ (step T v s x).state.now + (resp.withinNat : Int)) ∧
    (instFitsAt L.count v.machines s.records → ∀ d, resp.deadlineAt s.records tr = some d →
      (resp.answers tr (step T v s x).moment = false →
        ∃ d', resp.deadlineAt (step T v s x).state.records tr = some d' ∧ d' ≤ d) ∧
      ((step T v s x).state.now ≤ d ∨ (step T v s x).state.now = s.now)) := by
  have hR := decode_state hS
  obtain ⟨hside, hheldH, hcond, hrel⟩ := stepAsk_step chk senv ha hS hinv hsupp hkeys hheld hx hcase hb
  have hst : stepFits L.count T (shapes v) s x := by
    obtain ⟨hcodes, hsites⟩ := stepAsk_side ha hside
    exact ((step_encode chk senv hR hinv hx (stepAsk_t ha)).2 hcodes hsites (hcase _ (stepAsk_t ha))).1.1 hcond
  obtain ⟨⟨fa, ca⟩, hfa, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨fq, cq⟩, hfq, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨fd, cd⟩, hfd, hq⟩ := bind_ok.1 hq
  obtain ⟨twf, htwf, hq⟩ := bind_ok.1 hq
  obtain ⟨srt, -, hq⟩ := bind_ok.1 hq
  obtain ⟨tm, htm, hq⟩ := bind_ok.1 hq
  obtain ⟨⟨gOpen, gKeep, c⟩, hg, hq⟩ := bind_ok.1 hq
  obtain ⟨fits, hfits, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have htrRel : RelV L v.event (Ty.up _ v.event_data tr) ((Term.var (trigVar inp)).denote M) :=
    decode_rel _ _ _ (by simpa [Term.denote] using htr)
  have hgoal : ¬ Holds M (andT tm (.or (.not (andT (andT ca (andT cq cd)) c)) (.or gOpen (andT fits gKeep)))) := by
    intro hgH
    obtain ⟨c', hc', hna⟩ := hun
    have hctx := stepAsk_context chk senv ha hS hinv hsupp hkeys hx hcase
      [a.side, a.held, a.t.cond, andT tm (.or (.not (andT (andT ca (andT cq cd)) c)) (.or gOpen (andT fits gKeep)))]
    simp only [TypedScript.script, StepAsk.ask, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rw [stepAsk_asserts ha] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with (hc' | rfl) | rfl | rfl | rfl | rfl
    · exact hna (hctx c' hc')
    · exact hna (wfT_of_decodeV (need_ok.1 htwf) (by simpa [Term.denote] using htr))
    · exact hna hside
    · exact hna hheldH
    · exact hna hcond
    · exact hna hgH
  by_cases hacc : (step T v s x).outcome = .accepted
  · have hno : ∀ f, (step T v s x).outcome ≠ .fault f := fun f h => by rw [hacc] at h; cases h
    obtain ⟨fo, hfo, hacT, hrec', hnow', -⟩ := accepted_end hR hx hrel hacc
    have htmH : Holds M tm := (kindTimelyT_iff hR hx htm).2 ⟨clockFits_of hst hacc, htime⟩
    simp only [holds_andT, holds_or, holds_not] at hgoal
    have hg2 : ¬ (_ ∨ _) := fun h => hgoal ⟨htmH, h⟩
    rw [not_or, not_or, Classical.not_not] at hg2
    obtain ⟨⟨⟨hca, hcq, hcd⟩, hcc⟩, hnOpen, hnKeep⟩ := hg2
    simp only [respGoalT, hfo] at hg
    obtain ⟨⟨opens, co⟩, e1, hg⟩ := bind_ok.1 hg
    obtain ⟨⟨has, d, c1⟩, e2, hg⟩ := bind_ok.1 hg
    obtain ⟨⟨an, can⟩, e3, hg⟩ := bind_ok.1 hg
    obtain ⟨⟨has', d', c2⟩, e4, hg⟩ := bind_ok.1 hg
    cases pure_ok.1 hg
    simp only [holds_andT] at hcc hnOpen hnKeep
    obtain ⟨hco, hc1, hcan, hc2⟩ := hcc
    have hp : PredExact M L v (lateOpenAt L fa fq fd (resp.withinNat : Int) a.t.out fo.settle.terms.done.records
        (inp.nowAfter (SymState.vars 0)))
        (fun ev => resp.opens ev && !resp.answers ev (step T v s x).moment &&
          !(match resp.deadlineAt (step T v s x).state.records ev with
            | some dl => decide (dl ≤ (step T v s x).state.now + (resp.withinNat : Int))
            | none => false))
        (fun ev => resp.after.appFits L.count (ev, ()) ∧ (∀ ev' ∈ (step T v s x).events, resp.then_.appFits L.count (ev, ev', ())) ∧
          resp.deadline.appFits L.count ((step T v s x).state.records, ev, ())) := by
      intro ev' t c' henc ev hr
      obtain ⟨⟨o, co'⟩, f1, henc⟩ := bind_ok.1 henc
      obtain ⟨⟨an', can'⟩, f2, henc⟩ := bind_ok.1 henc
      obtain ⟨⟨hs, dl, cd'⟩, f3, henc⟩ := bind_ok.1 henc
      cases pure_ok.1 henc
      have x1 := predT_encode v.event_data resp.after hfa hca ev hr f1
      have x2 := kindHitsT_iff (ansT_exact hfq hcq hr) hx hrel hno f2
      have x3 := deadlineT_encode resp hfd hcd (step T v s x).state.records ev hrec' hr f3
      simp only [holds_andT]
      refine ⟨by rw [x1.1, x2.1, x3.1], fun ⟨k1, k2, k3⟩ => ?_⟩
      have hans : resp.answers ev (step T v s x).moment = true ↔
          ∃ ev'' ∈ (step T v s x).events, Step.toB (resp.then_.fn (ev, ev'', ())) = true := by
        simp [ResponseV.answers, Result.moment, List.any_eq_true]
      obtain ⟨x3a, x3b⟩ := x3.2 k3
      rw [x1.2 k1, holds_not, x2.2 k2, holds_not, holds_andT, x3a, ← hans]
      change (resp.opens ev = true ∧ ¬ resp.answers ev (step T v s x).moment = true ∧ ¬ (_ ∧ _)) ↔ _
      cases hdl : resp.deadlineAt (step T v s x).state.records ev with
      | none => cases resp.opens ev <;> cases resp.answers ev (step T v s x).moment <;> simp
      | some dv =>
        have hle := holds_le_of (M := M) (x3b dv hdl)
          (show (Term.add (inp.nowAfter (SymState.vars 0)) (.int (resp.withinNat : Int))).denote M =
            .int ((step T v s x).state.now + (resp.withinNat : Int)) by simp [Term.denote, hnow', Val.toInt])
        rw [hle]
        cases resp.opens ev <;> cases resp.answers ev (step T v s x).moment <;> simp
    have eO := kindHitsT_iff hp hx hrel hno e1
    refine ⟨fun ev hev hop han => ?_, fun hfitS dv hdv => ?_⟩
    · have hnp : ¬ ∃ ev ∈ (step T v s x).events, _ := fun h => hnOpen ⟨hacT, (eO.2 hco).2 h⟩
      cases hdl : resp.deadlineAt (step T v s x).state.records ev with
      | none => exact absurd ⟨ev, hev, by simp [hop, han, hdl]⟩ hnp
      | some dl =>
        refine ⟨dl, rfl, Classical.byContradiction fun hgt => hnp ⟨ev, hev, ?_⟩⟩
        simp [hop, han, hdl]; omega
    · have hfitsH : Holds M fits := (instFitsT_exact v.records_data s.records hR.records v.machines hfits).2 hfitS
      have hnK := fun h => hnKeep ⟨hfitsH, hacT, h⟩
      have y1 := deadlineT_encode resp hfd hcd s.records tr hR.records htrRel e2
      have y2 := kindHitsT_iff (ansT_exact hfq hcq htrRel) hx hrel hno e3
      have y3 := deadlineT_encode resp hfd hcd (step T v s x).state.records tr hrec' htrRel e4
      have hhas : Holds M has := (y1.2 hc1).1.2 (by simp [hdv])
      have hdD := (y1.2 hc1).2 dv hdv
      simp only [holds_or, holds_andT, holds_not] at hnK
      obtain ⟨hnMoved, hnPast⟩ := not_or.1 hnK
      refine ⟨fun han => ?_, ?_⟩
      · have hanF : ¬ Holds M an := fun h => by
          obtain ⟨ev, hev, hev'⟩ := (y2.2 hcan).1 h
          simp only [ResponseV.answers, Result.moment] at han
          exact List.any_eq_false.1 han ev hev hev'
        have hk := Classical.not_not.1 fun h => hnMoved ⟨hhas, hanF, h⟩
        obtain ⟨hhas', hle⟩ := hk
        obtain ⟨dv', hdv'⟩ := Option.isSome_iff_exists.1 ((y3.2 hc2).1.1 hhas')
        exact ⟨dv', hdv', (holds_le_of ((y3.2 hc2).2 dv' hdv') hdD).1 hle⟩
      · cases inp with
        | clock w =>
          obtain ⟨time, rfl, hw⟩ := decode_clock hx
          have hnow := hnow'
          simp only [SymInput.nowAfter] at hnow
          rw [hw] at hnow
          injection hnow with h
          refine .inl ?_
          rw [← h]
          exact Int.not_lt.1 fun hlt => hnPast ((holds_andT _ _).2 ⟨hhas, (holds_lt_of hdD hw).2 hlt⟩)
        | _ =>
          refine .inr ?_
          have := hnow'; simp only [SymInput.nowAfter] at this; rw [hR.now] at this; injection this with h; exact h.symm
  · obtain ⟨hrec, hnow⟩ := rel_quiet hx hrel hacc
    have hq := (step_quiet s x hacc).1
    refine ⟨fun ev hev => (by rw [hq] at hev; cases hev), fun _ dv hdv => ⟨fun _ => ⟨dv, by rw [hrec]; exact hdv, Int.le_refl _⟩,
      .inr hnow⟩⟩

/-- What an input kind's response line says, whichever verdict it reads: its question is built and unsat. -/
def RespLine (L : Layout) (T : List TypeDecl) (P : List AnySite) (senv : StepEnv L (shapes v))
    (resp : ResponseV v.records v.event) (inp : SymInput v (shapes v) senv.nT) : Prop :=
  ∃ a q, stepAsk L T P v senv inp = .ok a ∧ respStep L resp inp a = .ok q ∧ Unsat L q

theorem stepAsk_context_same {senv : StepEnv L (shapes v)} {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v}
    (ha : stepAsk L T P v senv inp = .ok a) (X Y : List Term) : (a.script X).context = (a.script Y).context := by
  simp only [stepAsk] at ha
  repeat (obtain ⟨_, -, ha⟩ := bind_ok.1 ha)
  cases pure_ok.1 ha
  rfl

theorem respStep_facts {senv : StepEnv L (shapes v)} {resp : ResponseV v.records v.event}
    {inp : SymInput v (shapes v) senv.nT} {a : StepAsk v} {q : TypedScript}
    (ha : stepAsk L T P v senv inp = .ok a) (hq : respStep L resp inp a = .ok q) :
    q.tys = stateTys v (shapes v) ++ inp.tys ++ [v.event] ∧ L.datatypes? = some q.datatypes ∧
      q.tys.mapM L.srt? = some q.vars := by
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨srt, hsrt, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  refine ⟨by simp [StepAsk.ask, stepAsk_tys L T P v senv ha], stepAsk_dts L T P v senv ha _, ?_⟩
  simp only [List.mapM_append, StepAsk.ask, stepAsk_vars L T P v senv ha, List.mapM_cons, List.mapM_nil,
    need_ok.1 hsrt]
  rfl

theorem layoutSorted_prefix {tys more : List Ty} {vs : List Srt} (hv : (tys ++ more).mapM L.srt? = some vs)
    (h : LayoutSorted L (tys ++ more) M) : LayoutSorted L tys M :=
  layoutSorted_of (fun dts hd => (h dts vs hd hv).2) fun n t ht dts σ hd hs =>
    (h dts vs hd hv).1 n σ (by
      rw [mapM_getElem? hv n, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ht).1, ht]; exact hs)

/-- What a step from a state within the slots keeps of the response, where every input kind's response question is
unsat, the step fits the slots (or every bound question is unsat) and is timely: the waiting parts are known where
every machine's `instances` fits at the records, for every trigger that fits the slots. -/
theorem state_keeps (chk : Checked P E T v) (senv : StepEnv L (shapes v)) {resp : ResponseV v.records v.event}
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), RespLine L T P senv resp inp)
    {s : State v} (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hheld : Step.invariants s = [])
    (hkeys : Step.KeysOk T s) (hW : Within L (shapes v) s) {x : Input v}
    (hx : (inputVals L chk.callerData x).isSome ∨
      ((step T v s x).outcome = .fault .answerUnmatched ∧ (step T v s x).state = s))
    (hfit : StepFits L T P v s x ∨ ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp)
    (htime : Step.timelyAt s x = true) :
    resp.Keeps T (instFitsAt L.count v.machines) (fun tr => (embedV L v.event (Ty.up _ v.event_data tr)).isSome)
      s x := by
  have hevE : v.event.embeddable = true := (stateTys_iff.1 chk.stateTys).2.2.2.2.1.1
  have quiet : (step T v s x).outcome ≠ .accepted → (step T v s x).state.records = s.records →
      (step T v s x).state.now = s.now →
      resp.Keeps T (instFitsAt L.count v.machines) (fun tr => (embedV L v.event (Ty.up _ v.event_data tr)).isSome)
        s x := fun hna hrec hnow => by
    have hq := (step_quiet s x hna).1
    refine ⟨fun ev hev => (by rw [hq] at hev; cases hev), fun _ tr dv _ hdv _ => ⟨dv, by rw [hrec]; exact hdv,
      Int.le_refl _⟩, fun _ _ _ _ _ => .inr hnow, fun h => ?_⟩
    rw [hrec]
    rcases h with h | h
    · exact h
    · exact absurd hq h
  by_cases hxs : (inputVals L chk.callerData x).isSome
  case neg =>
    obtain ⟨hf, hst⟩ := hx.resolve_left hxs
    exact quiet (by rw [hf]; simp) (by rw [hst]) (by rw [hst])
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hxs
  -- The bound question of a kind, in a model that holds the state and the input, fails some assertion or the step fits.
  have bnd : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), ∀ (a : StepAsk v) (M : Model) (more : List Ty)
      (vs : List Srt), stepAsk L T P v senv inp = .ok a →
      (stateTys v (shapes v) ++ inp.tys ++ more).mapM L.srt? = some vs →
      (∀ j (h : j < (stateTys v (shapes v) ++ inp.tys ++ more).length),
        Sorted L (stateTys v (shapes v) ++ inp.tys ++ more)[j] (M.vars j)) →
      LayoutSorted L (stateTys v (shapes v) ++ inp.tys ++ more) M →
      (∃ c ∈ a.bound.script.asserts, ¬ Holds M c) ∨ StepFits L T P v s x := by
    intro inp hmem a M more vs ha hvs hM hsel
    rcases hfit with hfit | hbu
    · exact .inr hfit
    · obtain ⟨gs, qs, hqs, hun⟩ := hbu inp hmem
      have hqs' := hqs
      simp only [questions, ha, bind, Except.bind] at hqs'
      cases pure_ok.1 hqs'
      have hu := hun _ (List.mem_cons_self ..) rfl
      refine .inl (hu.noModel_at (stepAsk_tys L T P v senv ha _) (stepAsk_dts L T P v senv ha _) (stepAsk_vars L T P v senv ha _) M
        (fun n h => varSorted_of_sorted (by
          have := hM n (by simp at h ⊢; omega)
          rwa [List.getElem_append_left (by simpa [stepAsk_tys L T P v senv ha] using h)] at this))
        (layoutSorted_prefix hvs hsel))
  -- A trigger that fits the slots: the step's facts about it, or the step is quiet.
  have trig : ∀ (tr : v.event.den0) (tw : Val), embedV L v.event (Ty.up _ v.event_data tr) = some tw →
      (∀ ev ∈ (step T v s x).events, resp.opens ev = true → resp.answers ev (step T v s x).moment = false →
        ∃ d, resp.deadlineAt (step T v s x).state.records ev = some d ∧
          d ≤ (step T v s x).state.now + (resp.withinNat : Int)) ∧
      (instFitsAt L.count v.machines s.records → ∀ d, resp.deadlineAt s.records tr = some d →
        (resp.answers tr (step T v s x).moment = false →
          ∃ d', resp.deadlineAt (step T v s x).state.records tr = some d' ∧ d' ≤ d) ∧
        ((step T v s x).state.now ≤ d ∨ (step T v s x).state.now = s.now)) := by
    intro tr tw htw
    rcases covered_with chk senv hkeys hW x hivs [v.event] [tw] ⟨sorted_of_embed htw, trivial⟩
        ⟨embedV_srtVal htw, trivial⟩ (by simp [v.event_data]) with
      ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase, hext⟩ | ⟨-, -, hst, halt⟩
    · obtain ⟨a, q, ha, hq, hu⟩ := hl inp hmem
      obtain ⟨ht, hd, hv⟩ := respStep_facts ha hq
      have hun := hu.noModel_at ht hd hv M (fun n h => varSorted_of_sorted (hM n h)) hsel
      have hvar : M.vars (trigVar inp) = tw := by simpa [trigVar] using hext 0 (by simp)
      exact step_keeps chk senv ha hq hun hS hinv hsupp hkeys hheld hxd hcase
        (bnd inp hmem a M [v.event] q.vars ha (by rw [← ht]; exact hv) hM hsel) htime
        (by rw [hvar]; exact decode_embed _ _ _ htw)
    · have hna : (step T v s x).outcome ≠ .accepted := by
        rcases halt with ⟨i, c, y, rfl⟩ | h
        · simp only [step]; split <;> simp
        · rw [h]; simp
      have hq := (step_quiet s x hna).1
      exact ⟨fun ev hev => (by rw [hq] at hev; cases hev), fun _ dv hdv => ⟨fun _ => ⟨dv, by rw [hst]; exact hdv,
        Int.le_refl _⟩, .inr (by rw [hst])⟩⟩
  -- The plain covering model: the step's events fit the slots, and the instance fit after an accepted step.
  rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, hc, M, hM, hsel, hS, hxd, hcase⟩ | ⟨-, -, hst, halt⟩
  · obtain ⟨a, q, ha, -, -⟩ := hl inp hmem
    have hb : (∃ c ∈ a.bound.script.asserts, ¬ Holds M c) ∨ StepFits L T P v s x := by
      obtain ⟨vs, hvs⟩ : ∃ vs, (stateTys v (shapes v) ++ inp.tys ++ []).mapM L.srt? = some vs :=
        ⟨_, by simpa [stepAsk_tys L T P v senv ha] using stepAsk_vars L T P v senv ha []⟩
      exact bnd inp hmem a M [] vs ha hvs (by simpa using hM) (by simpa using hsel)
    obtain ⟨-, -, -, hrel⟩ := stepAsk_step chk senv ha hS hinv hsupp hkeys hheld hxd hcase hb
    have hR := decode_state hS
    by_cases hacc : (step T v s x).outcome = .accepted
    · have hno : ∀ f, (step T v s x).outcome ≠ .fault f := fun f h => by rw [hacc] at h; cases h
      obtain ⟨fo, hfo, -, -, -, hfitpost⟩ := accepted_end hR hxd hrel hacc
      obtain ⟨_, _, hre, -, hF⟩ := (rel_end hxd hrel hno).1 fo hfo (by
        have := (accepted_end hR hxd hrel hacc); obtain ⟨fo', hfo', hacT, -⟩ := this
        rw [hfo] at hfo'; cases hfo'; simp only [acceptedT, hfo, holds_andT] at hacT; exact hacT.1)
      have hevs : ∀ ev ∈ (step T v s x).events, (embedV L v.event (Ty.up _ v.event_data ev)).isSome := by
        obtain ⟨evs, hevs, sv, hSd, h2⟩ := finished_events hF hno
        rw [hevs, hre, List.nil_append]
        intro ev hev
        obtain ⟨_, -, z, rfl, hz⟩ := forall2_mem_left h2 _ (List.mem_map_of_mem hev)
        exact embed_of_relV _ hevE _ _ hz
      refine ⟨fun ev hev => ⟨hevs ev hev, fun hop han => ?_⟩, fun hF tr d hG hd han => ?_,
        fun hF tr d hG hd => ?_, fun _ => hfitpost⟩
      · obtain ⟨tw, htw⟩ := Option.isSome_iff_exists.1 (hevs ev hev)
        exact (trig ev tw htw).1 ev hev hop han
      · obtain ⟨tw, htw⟩ := Option.isSome_iff_exists.1 hG
        exact ((trig tr tw htw).2 hF d hd).1 han
      · obtain ⟨tw, htw⟩ := Option.isSome_iff_exists.1 hG
        exact ((trig tr tw htw).2 hF d hd).2
    · obtain ⟨hrec, hnow⟩ := rel_quiet hxd hrel hacc
      exact quiet hacc hrec hnow
  · have hna : (step T v s x).outcome ≠ .accepted := by
      rcases halt with ⟨i, c, y, rfl⟩ | h
      · simp only [step]; split <;> simp
      · rw [h]; simp
    exact quiet hna (by rw [hst]) (by rw [hst])

/-- What a run's scope asks of each step: the state is within the slots, the input fits them (or is an answer that
names no request and leaves the state), and the step fits them (or every bound question is unsat). -/
def RespScope (L : Layout) (T : List TypeDecl) (P : List AnySite) (senv : StepEnv L (shapes v)) (hc : v.caller.isData = true)
    (s : State v) (x : Input v) : Prop :=
  Within L (shapes v) s ∧
    ((inputVals L hc x).isSome ∨ ((step T v s x).outcome = .fault .answerUnmatched ∧ (step T v s x).state = s)) ∧
    (StepFits L T P v s x ∨ ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp)

theorem eachStep_keeps (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    {resp : ResponseV v.records v.event}
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), RespLine L T P senv resp inp) :
    (xs : List (Input v)) → (s : State v) → Step.Inv P s → Step.StateSupp s → Step.invariants s = [] →
    Step.KeysOk T s → Step.ValidRun T s xs → Step.TimelyRun T s xs →
    Step.EachStep T (RespScope L T P senv chk.callerData) s xs →
    Step.EachStep T (resp.Keeps T (instFitsAt L.count v.machines)
      (fun tr => (embedV L v.event (Ty.up _ v.event_data tr)).isSome)) s xs
  | [], _, _, _, _, _, _, _, _ => trivial
  | x :: xs, s, hinv, hsupp, hheld, hkeys, ⟨hx, hxs⟩, ⟨ht, hts⟩, ⟨⟨hW, hin, hfit⟩, hsc⟩ =>
    ⟨state_keeps chk senv hl hinv hsupp hheld hkeys hW hin hfit ht,
      eachStep_keeps chk he senv hl xs _ (step_inv T chk.reach s hinv x) (Step.step_supp T he hsupp hinv.below x hx)
        (step_invariants T s x hheld) (step_keys T s hkeys x) hxs hts hsc⟩

/-- A response within the bounds: where every input kind's response question is unsat, no run on valid inputs with
timely clock lines from an initial state whose invariants hold violates the response, as long as every step of the
run stays within the slots (`RespScope`). -/
theorem response_scoped (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    {resp : ResponseV v.records v.event}
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), RespLine L T P senv resp inp)
    (hinit : Step.invariants (Step.State.init v) = []) (xs : List (Input v))
    (hvalid : Step.ValidRun T (Step.State.init v) xs) (htimely : Step.TimelyRun T (Step.State.init v) xs)
    (hscope : Step.EachStep T (RespScope L T P senv chk.callerData) (Step.State.init v) xs) :
    ¬ resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  exact not_violated T resp _ _ xs _ (eachStep_keeps chk he senv hl xs _ Step.init_inv (Step.init_supp he) hinit
    (Step.init_keys T hord chk.idle) hvalid htimely hscope)

/-- Every step of a run stays within the slots where every input kind's bound question is unsat, every input fits
and the state the run starts from is within them. -/
theorem scope_of_bounds (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    (hin : inputsFit L v = true)
    (hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp) :
    (xs : List (Input v)) → (s : State v) → Step.Inv P s → Step.StateSupp s → Step.invariants s = [] →
    Step.KeysOk T s → Within L (shapes v) s → Step.ValidRun T s xs →
    Step.EachStep T (RespScope L T P senv chk.callerData) s xs
  | [], _, _, _, _, _, _, _ => trivial
  | x :: xs, s, hinv, hsupp, hheld, hkeys, hW, ⟨hx, hxs⟩ =>
    ⟨⟨hW, inputs_fit chk hin hW x, .inr hb⟩,
      scope_of_bounds chk he senv hin hb xs _ (step_inv T chk.reach s hinv x) (Step.step_supp T he hsupp hinv.below x hx)
        (step_invariants T s x hheld) (step_keys T s hkeys x) (within_step chk senv hin hb hinv hsupp hheld hkeys hW x)
        hxs⟩

/-- A response proved by induction over steps (Prove.proved): where every input kind's response question and bound
question are unsat and the initial state and every value an input can carry fit the slots, no run on valid inputs with
timely clock lines from an initial state whose invariants hold violates the response, at any length. -/
theorem response_holds (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    {resp : ResponseV v.records v.event}
    (hl : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), RespLine L T P senv resp inp)
    (hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp)
    (hinit : Step.invariants (Step.State.init v) = []) (h0 : initFits L v = true) (hin : inputsFit L v = true)
    (xs : List (Input v)) (hvalid : Step.ValidRun T (Step.State.init v) xs)
    (htimely : Step.TimelyRun T (Step.State.init v) xs) :
    ¬ resp.Violated ((run T v (Step.State.init v) xs).2.map Result.moment) := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  exact not_violated T resp _ _ xs _ (eachStep_keeps chk he senv hl xs _ Step.init_inv (Step.init_supp he) hinit
    (Step.init_keys T hord chk.idle) hvalid htimely (scope_of_bounds chk he senv hin hb xs _ Step.init_inv
      (Step.init_supp he) hinit (Step.init_keys T hord chk.idle) (within_init h0) hvalid))

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {v : ServiceV}

theorem deadlineT_sound (hL : SortedLayout L) {fd : Code (Ty.fn [v.records, v.event] (Ty.option (.point .ms)))}
    (hfd : CodeOk L P ds H _ fd) (hr : Avail L v.records) (he : Avail L v.event) (ho : Avail L (Ty.option (.point .ms)))
    (records tr : Term) : Sound (fun _ => True) (deadlineT L fd records tr) :=
  sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) records hr) fun _ hrc =>
    sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) tr he) fun _ hec =>
    sound_bind (apply_sound hfd ⟨hrc, hec, trivial⟩ ho) fun _ _ =>
    sound_bind (dataTermE_sound _) fun _ _ =>
    sound_bind (findE_sound hL ho has_find) fun _ _ => trivial

end

/-- In each service's layout, a response's question never refuses with a layout gap. -/
theorem respStep_ofService (c : CheckedSpec) {v : ServiceV} {bnd : BoundsV v.records} (hv : v ∈ c.spec.services)
    {resp : ResponseV v.records v.event} (hr : resp ∈ v.responses) {n : Nat} (inp : SymInput v (shapes v) n)
    (a : StepAsk v) : Sound (fun _ => True) (respStep (Layout.ofService c.program.defs v bnd) resp inp a) := by
  have h := serviceGot_ofService (bnd := bnd) hv
  have chk := c.checked v hv
  have hev := avail_of_got h.event
  have hrec := avail_of_got h.records
  have hopt : Avail (Layout.ofService c.program.defs v bnd) (Ty.option (.point .ms)) := avail_use c v (by simp [useTys])
  obtain ⟨-, -, -, -, ⟨hee, hep⟩, -⟩ := stateTys_iff.1 chk.stateTys
  have hreach := chk.reach.responses resp hr
  have hroot := root_response hr
  unfold respStep
  refine sound_bind (Fun.code_ofService c hv _ hreach.1 hroot.1) fun ⟨fa, _⟩ ha => ?_
  refine sound_bind (Fun.code_ofService c hv _ hreach.2.1 hroot.2.1) fun ⟨fq, _⟩ hq => ?_
  refine sound_bind (Fun.code_ofService c hv _ hreach.2.2 hroot.2.2) fun ⟨fd, _⟩ hd => ?_
  refine sound_bind (sound_lacksData hev fun hh _ _ => wfT_isSome _ hh hee hep _) fun _ _ => ?_
  refine sound_bind (sound_srt hev) fun _ _ => ?_
  refine sound_bind (kindTimelyT_sound h.sorted (fun m hm => (h.machines m hm).1) _ inp) fun _ _ => ?_
  refine sound_bind (p := fun _ => True) ?_ fun _ _ => ?_
  · unfold respGoalT
    split
    · trivial
    · refine sound_bind (kindHitsT_sound (pred := lateOpenAt _ fa fq fd _ _ _ _) (fun ev =>
        sound_bind (predT_sound ha hev ev) fun _ _ =>
          sound_bind (kindHitsT_sound (pred2T_sound hq hev ev) _) fun _ _ =>
          sound_bind (deadlineT_sound h.sorted hd hrec hev hopt _ _) fun _ _ => trivial) _) fun _ _ => ?_
      refine sound_bind (deadlineT_sound h.sorted hd hrec hev hopt _ _) fun _ _ => ?_
      refine sound_bind (kindHitsT_sound (pred2T_sound hq hev _) _) fun _ _ => ?_
      exact sound_bind (deadlineT_sound h.sorted hd hrec hev hopt _ _) fun _ _ => trivial
  · exact sound_bind (instFitsT_sound _ (fun m hm => (h.machines m hm).1) _) fun _ _ => trivial

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV} {P : List AnySite}

/-- A response's question never yields a model that does not decode: a model of its context whose variables hold
values of their sorts gives the state, the input and the trigger its report shows. -/
theorem resp_decode (senv : StepEnv L (shapes v)) {inp : SymInput v (shapes v) senv.nT}
    (hmem : inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v)) (hc : v.caller.isData = true)
    {resp : ResponseV v.records v.event} {a : StepAsk v} {q : TypedScript} (ha : stepAsk L T P v senv inp = .ok a)
    (hq : respStep L resp inp a = .ok q) (hM : ∀ n (h : n < q.tys.length), VarSorted L q.tys[n] (M.vars n))
    (hctx : ∀ c ∈ q.context, Holds M c) :
    ∃ s x tr, (SymState.vars (v := v) 0).decode M L T (shapes v) = some s ∧ inp.decode M L hc = some x ∧
      decodeV L v.event (M.vars (trigVar inp)) = some tr := by
  obtain ⟨ht, -, -⟩ := respStep_facts ha hq
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
  obtain ⟨twf, htwf, hq'⟩ := bind_ok.1 hq'
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
  obtain ⟨_, -, hq'⟩ := bind_ok.1 hq'
  cases pure_ok.1 hq'
  rw [ht] at hM
  have hin := stepInputs_data hc hmem
  have hst := sorted_append_left (B := inp.tys ++ [v.event]) (by simpa using hM) (stateTys_data v)
  have hip := sorted_append_right (A := stateTys v (shapes v)) (B := inp.tys)
    (fun n h => by
      have h' : n < (stateTys v (shapes v) ++ inp.tys ++ [v.event]).length := by simp at h ⊢; omega
      have := hM n h'
      rwa [List.getElem_append_left h] at this) hin
  have hctx' : ∀ c ∈ (a.script []).context, Holds M c := fun c hc' => hctx c (by
    simp only [StepAsk.ask, List.mem_append, List.mem_singleton]
    exact .inl (by rw [stepAsk_context_same ha _ []]; exact hc'))
  have ha' := ha
  simp only [stepAsk] at ha'
  obtain ⟨t, -, ha'⟩ := bind_ok.1 ha'
  obtain ⟨wf, hwf, ha'⟩ := bind_ok.1 ha'
  obtain ⟨iwf, hiwf, ha'⟩ := bind_ok.1 ha'
  repeat (obtain ⟨_, -, ha'⟩ := bind_ok.1 ha')
  cases pure_ok.1 ha'
  obtain ⟨s, hs⟩ := vars_decode 0 T (shapes v) (need_ok.1 hwf) (hctx' wf (by simp)) hst
  obtain ⟨x, hx⟩ := SymInput.decode_total hc hin (need_ok.1 hiwf) (hctx' iwf (by simp))
    (stepInputs_terms hmem ▸ forall2_vars inp.tys (stateTys v (shapes v)).length hip)
  have hev : v.event.isData = true := v.event_data
  have hsrt : Sorted L v.event (M.vars (trigVar inp)) := by
    have hlt : trigVar inp < (stateTys v (shapes v) ++ inp.tys ++ [v.event]).length := by simp [trigVar, stateWidth]
    have heq : (stateTys v (shapes v) ++ inp.tys ++ [v.event])[trigVar inp] = v.event := by
      simp [trigVar, stateWidth, List.getElem_append_right]
    have := hM (trigVar inp) hlt
    rw [heq] at this
    exact sorted_of_varSorted hev this
  obtain ⟨tr, htr⟩ := decode_of_wf (M := M) (need_ok.1 htwf) (by simpa [Term.denote] using hsrt)
    (hctx twf (by simp))
  exact ⟨s, x, tr, hs, hx, by simpa [Term.denote] using htr⟩

end

end Tazuna.Smt
