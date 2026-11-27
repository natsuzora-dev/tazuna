import Tazuna.Smt.Query
import Tazuna.Smt.CommandStep
import Tazuna.Smt.Answer
import Tazuna.Smt.Event
import Tazuna.Smt.Clock

/-! The step encoding over every input kind. `encodeStep` hands a symbolic input to its kind's encoder, and
`step_encode` states for every kind at once, from each kind's theorem, what the terms mean: the codes' condition holds
exactly when the codes fit (`codesFit`); where it holds, the step's condition holds exactly when what the step applies
fits (`stepFits`), and then the step from the state and input a model's values decode to is the one the terms say
(`StepOut.Rel`). The internal steps of the cascade are inside each kind's end (`encodeFinish`).

The transition is a function of the state and input, so one statement gives both directions: a model's decoded state
and input step as its terms say (a decoded counterexample is a real step), and every reachable state is some model's
(`decode_run`), so a script with no model has no step that breaks it. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of a step, per input kind. -/
inductive StepOut (v : ServiceV) where
  | command (o : CommandOut v)
  | query (o : QueryOut)
  | answer (o : AnswerOut v)
  | unmatched (u : Term)
  | event (o : EventOut v)
  | clock (o : ClockOut v)

/-- The case a script asks about, which its theorems assume: for an answer, that the slot holds the request it names
(`hit`) or that no slot holds one of its type; other kinds have one case. -/
def StepOut.case {v : ServiceV} : StepOut v → Term
  | .answer o => o.hit
  | .unmatched u => u
  | _ => tt

/-- A step's terms and conditions: the step's own (exact, `stepFits`), the codes of the functions it applies (exact,
`codesFit`), and the codes the cascade's internal steps build at captured values. -/
structure EncodedStep (v : ServiceV) where
  out : StepOut v
  cond : Term
  codes : Term
  sites : Term

section
variable (L : Layout) (T : List TypeDecl)

/-- A step's terms from the symbolic state and input, by the input's kind. -/
def encodeStep (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))
    (S : SymState v) : SymInput v (shapes v) senv.nT → Except Refusal (EncodedStep v)
  | .command i caller input => do
    let x := v.commands.get i
    let (cc, cx) ← CommandCode.of L x
    let (apply, ca) ← v.apply.code L
    let (inv, ci) ← v.invariants.code L
    let ks ← need (.limit (.slots v.caller)) (callerTerms L x.data.origin x.callers)
    let live := (SymInput.command (shs := shapes v) (slots := senv.nT) i caller input).live P
    let ⟨o, c, cs⟩ ← encodeCommand L T P live v (shapes v) senv x cc apply inv ks S caller input
    pure ⟨.command o, c, andT cx (andT ca ci), cs⟩
  | .query i caller input => do
    let q := v.queries.get i
    let (qc, cq) ← QueryCode.of L q
    let ks ← need (.limit (.slots v.caller)) (callerTerms L q.data.origin q.callers)
    let (o, c) ← encodeQuery L q qc ks S caller input
    pure ⟨.query o, c, cq, tt⟩
  | .answer k j to value => do
    let (apply, ca) ← v.apply.code L
    let (inv, ci) ← v.invariants.code L
    let live := (SymInput.answer (v := v) (shs := shapes v) k j to value).live P
    let ⟨o, c, cs⟩ ← encodeAnswer L T P live (shapes v) k (shapes v)[k] senv j apply inv S to value
    pure ⟨.answer o, c, andT ca ci, cs⟩
  | .unmatched t to _ => pure ⟨.unmatched (answerUnmatchedT L senv t S.pending to), tt, tt, tt⟩
  | .event i value => do
    let (ec, ce) ← EventCode.of L v i
    let live := (SymInput.event (shs := shapes v) (slots := senv.nT) i value).live P
    let ⟨o, c, cs⟩ ← encodeEvent L T P live v (shapes v) senv ec S value
    pure ⟨.event o, c, ce, cs⟩
  | .clock time => do
    let (apply, ca) ← v.apply.code L
    let (inv, ci) ← v.invariants.code L
    let live := (SymInput.clock (v := v) (shs := shapes v) (slots := senv.nT) time).live P
    let ⟨o, c, cs⟩ ← encodeClock L T P live v (shapes v) senv apply inv S time
    pure ⟨.clock o, c, andT ca ci, cs⟩

end

section
variable (S : Ty → Nat) (T : List TypeDecl) {v : ServiceV}

/-- Whether the codes of the functions a step of the input's kind applies fit their slots. -/
def codesFit {shs : List (PendingShape v.event)} {n : Nat} : SymInput v shs n → Prop
  | .command i _ _ =>
    let x := v.commands.get i
    ((x.accepts.fits S).1 ∧ (x.decide.fits S).1 ∧ (x.ensures.fits S).1) ∧ (v.apply.fits S).1 ∧ (v.invariants.fits S).1
  | .query i _ _ => ((v.queries.get i).accepts.fits S).1 ∧ ((v.queries.get i).resolve.fits S).1
  | .answer .. => (v.apply.fits S).1 ∧ (v.invariants.fits S).1
  | .unmatched .. => True
  | .event i _ => (v.apply.fits S).1 ∧ ((v.subscribes.get i).wrap.fits S).1 ∧ (v.invariants.fits S).1
  | .clock _ => (v.apply.fits S).1 ∧ (v.invariants.fits S).1

/-- Whether what the step applies fits the slots, clause by clause as `step` runs: a command's admission, `decide`
and what follows it; a query's admission and `resolve`; an answer's request functions and what follows; an event's
wrap, its applications and the step's end; a clock line's rounds and the step's end. -/
def stepFits (shs : List (PendingShape v.event)) (s : State v) : Input v → Prop
  | .command i caller input =>
    let x := v.commands.get i
    let ctx := Step.ctx s s.records (Step.outside caller) input
    x.callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 (Step.outside caller)) = true →
      x.accepts.appFits S (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits S (ctx, ()) ∧ decidedFits S T shs { s with fresh := s.fresh + 1 } x ctx (x.decide.fn (ctx, ())))
  | .query i caller input => queryFits S s (v.queries.get i) caller input
  | .answer to a => ∀ p, s.pending.find? (·.id == to) = some p → answerFits S T shs s p to a
  | .event i value =>
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    (v.subscribes.get i).wrap.appFits S (value, ()) ∧ eventsFit S T s [ev] ∧
      finishFits S T shs (Step.applyEvents T { state := s } [ev])
  | .clock time =>
    s.now ≤ time →
      roundsFit S T { s with now := time } true (v.bounds.cascadeNat + 1) ∧
      ∀ s' effs, Step.fire { s with now := time } (v.bounds.cascadeNat + 1) = some (s', effs) →
        finishFits S T shs (Step.start { state := s' } effs)

end

section
variable (M : Model) (L : Layout) (T : List TypeDecl) {v : ServiceV}

/-- What a step's terms say of its result `r` from the state `s` and the input. -/
def StepOut.Rel (shs : List (PendingShape v.event)) (s : State v) :
    StepOut v → Input v → Result v → Prop
  | .command o, .command i _ _, r =>
    let s' := { s with fresh := s.fresh + 1 }
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = ⟨s', .invalid (n :: ns), [], []⟩
      | [] =>
        if (o.decided.ok.denote M).toBool then
          match brokenIn M o.decided.ensures with
          | n :: _ => r = ⟨s', .fault (.ensures n), [], []⟩
          | [] => Finished M L T shs o.finish s' { state := s' } .accepted r
        else r.state = s' ∧ ∃ j, r.outcome = .rejected ⟨(v.commands.get i).rejection, j⟩ ∧
          RelV L _ (Ty.up _ ((v.commands.get i).data).rejection j) (o.decided.rejection.denote M)
    else r = ⟨s', .invalid ["callers"], [], []⟩
  | .query o, .query i _ _, r => r.state = s ∧ o.Rel M L ((v.queries.get i).data).output r.outcome
  | .answer o, .answer to _, r =>
    match brokenIn M o.rules with
    | n :: ns => r = ⟨s, .invalid (n :: ns), [], []⟩
    | [] => Finished M L T shs o.finish s { state := { s with pending := s.pending.filter (·.id != to) } } .accepted r
  | .unmatched _, .answer .., r => r = ⟨s, .fault .answerUnmatched, [], []⟩
  | .event o, .event .., r => Finished M L T shs o.finish s { state := s } .accepted r
  | .clock o, .clock time, r =>
    if (o.forward.denote M).toBool then
      if (o.over.denote M).toBool then r = ⟨s, .fault .cascadeLimit, [], []⟩
      else Finished M L T shs o.finish s { state := { s with now := time } } .accepted r
    else r = ⟨s, .invalid ["time moves forward"], [], []⟩
  | _, _, _ => False

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

theorem apply_inv_exact {v : ServiceV} {apply : Code (Ty.fn [Ty.applyCtx v.records, v.event] v.records)}
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ca ci : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hinv : v.invariants.code L = .ok (inv, ci)) :
    Holds M (andT ca ci) ↔ (v.apply.fits L.count).1 ∧ (v.invariants.fits L.count).1 := by
  rw [holds_andT, (v.apply.code_exact (M := M) happ).1, (v.invariants.code_exact (M := M) hinv).1]

/-- T2 and exactness for every step kind. Wherever a model's values of the symbolic state denote a state `s` that
keeps the step invariant (a decoded state, or the state a step's end terms denote, `StateRel`) and the input's decode
to an input: the codes' condition holds exactly when the codes fit; where it,
the cascade's codes' condition and the case the script asks about hold, the step's condition holds exactly when what
the step applies fits, and wherever it holds the step from `s` is the one the terms say and the cascade it starts
waits only on own effects a value codes (`QueueCoded`). -/
theorem step_encode {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v))
    {S : SymState v} {s : State v} (hR : StateRel M L T (shapes v) S s) (hinv : Step.Inv P s)
    {inp : SymInput v (shapes v) senv.nT} {hc} {x : Input v} (hx : inp.decode M L hc = some x)
    {t : EncodedStep v} (henc : encodeStep L T P v senv S inp = .ok t) :
    (Holds M t.codes ↔ codesFit L.count inp) ∧
    (Holds M t.codes → Holds M t.sites → Holds M t.out.case →
      (Holds M t.cond ↔ stepFits L.count T (shapes v) s x) ∧
      (Holds M t.cond → t.out.Rel M L T (shapes v) s x (step T v s x)) ∧
      (Holds M t.cond → ∀ a, Step.Begins T s x a → QueueCoded L a)) := by
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, hsc, hsi⟩ := decode_command hx
    obtain ⟨⟨cc, cx⟩, hcc, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨inv, ci⟩, hinvc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hcmd, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨by rw [holds_andT, commandCode_exact hcc, apply_inv_exact happ hinvc]; rfl, fun hcodes hcs _ => ?_⟩
    obtain ⟨hcx, hca, hci⟩ : Holds M cx ∧ Holds M ca ∧ Holds M ci := by
      rw [holds_andT, holds_andT] at hcodes; exact hcodes
    have hks' := need_ok.1 hks
    have ex := command_encode chk (fun _ => shapes_inSites chk.reach) (shapesHold_shapes v) s hinv i caller input hcc hcx
      happ hca hinvc hci hks' senv hR hsc hsi _ (fun _ hb => liveJ_site hb) (fun _ o _ hb ho h => liveJ_run T chk.reach hb o ho h)
      (fun _ _ hdec h => liveJ_command T chk.reach i s _ input hdec h) hcmd hcs
    refine ⟨ex.1, ex.2.1, fun hcond a hb => ?_⟩
    cases hb with
    | command _ _ _ _ h => exact ex.2.2 hcond a h
  | query i sc si =>
    obtain ⟨caller, input, rfl, hsc, hsi⟩ := decode_query hx
    obtain ⟨⟨qc, cq⟩, hqc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c⟩, hqe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    exact ⟨queryCode_exact hqc, fun hcq _ _ =>
      ⟨(query_encode s i caller input hqc hcq (need_ok.1 hks) hR hsc hsi hqe).1,
        (query_encode s i caller input hqc hcq (need_ok.1 hks) hR hsc hsi hqe).2, fun _ _ hb => nomatch hb⟩⟩
  | answer k j toT valT =>
    have hk : (shapes v)[(k : Nat)]? = some (shapes v)[k] := List.getElem?_eq_getElem k.2
    obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨inv, ci⟩, hinvc, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hans, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨apply_inv_exact happ hinvc, fun hcodes hcs hhit => ?_⟩
    obtain ⟨hca, hci⟩ := (holds_andT _ _).1 hcodes
    have hx' : decodeAnswer M L (answerTy (shapes v)[k].output (shapes v)[k].rejection) toT valT = some x := hx
    obtain ⟨hty, to, value, rfl, hto, hval⟩ := decode_answer hx'
    have ex := answer_encode chk (fun _ => shapes_inSites chk.reach) (shapesHold_shapes v) s hinv hk to value happ hca hinvc hci senv j hR hto hty hval
      _ (fun _ hb => liveJ_site hb) (fun _ o _ hb ho h => liveJ_run T chk.reach hb o ho h)
      (fun env _ h => liveJ_answer T chk.reach (shapes_inSites chk.reach (List.getElem_mem _)).1 _ value env h) hans hcs
    refine ⟨by rw [ex.1]; exact ⟨fun h => h hhit, fun h _ => h⟩, fun hcond => (ex.2 hcond hhit).1, fun hcond a hb => ?_⟩
    cases hb with
    | answer _ _ p h _ hp hhold happ => exact (ex.2 hcond hhit).2 p hp h hhold a happ
  | unmatched ty toT valT =>
    cases pure_ok.1 henc
    obtain ⟨-, to, value, rfl, hto, -⟩ := decode_answer hx
    refine ⟨by simp [holds_tt, codesFit], fun _ _ hcase => ⟨?_, fun _ => answer_unmatched s to ty value hR.pending hto senv hcase,
      fun _ a hb => ?begins⟩⟩
    case begins =>
      cases hb with
      | answer _ _ p h _ hp _ _ =>
        have hn := unmatched_types s to _ hR.pending hto senv hcase p hp
        subst h
        rw [Ty_same_rfl] at hn
        cases hn
    refine ⟨fun _ p hf => ?_, fun _ => holds_tt⟩
    simp [answerFits, unmatched_types s to ty hR.pending hto senv hcase p hf]
  | event i sv =>
    obtain ⟨value, rfl, hsv⟩ := decode_event hx
    obtain ⟨⟨ec, ce⟩, hec, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hev, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have ex := fun hce => event_encode chk (fun _ => shapes_inSites chk.reach) (shapesHold_shapes v) s hinv i value hec
      hce hR hsv senv _ (fun _ hb => liveJ_site hb) (fun _ o _ hb ho h => liveJ_run T chk.reach hb o ho h)
      (fun _ h => liveJ_event T chk.reach i s value h) hev
    refine ⟨eventCode_exact hec, fun hce hcs _ => ⟨(ex hce hcs).1, (ex hce hcs).2.1, fun hcond a hb => ?_⟩⟩
    cases hb with
    | event _ _ _ h => exact (ex hce hcs).2.2 hcond a h
  | clock st =>
    obtain ⟨time, rfl, hst⟩ := decode_clock hx
    obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨inv, ci⟩, hinvc, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hcl, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨apply_inv_exact happ hinvc, fun hcodes hcs _ => ?_⟩
    obtain ⟨hca, hci⟩ := (holds_andT _ _).1 hcodes
    have ex := clock_encode chk (fun _ => shapes_inSites chk.reach) (shapesHold_shapes v) s hinv time happ hca hinvc hci
      hR hst senv _ (fun _ hb => liveJ_site hb) (fun _ o _ hb ho h => liveJ_run T chk.reach hb o ho h)
      (fun _ _ _ hf h => liveJ_clock chk.reach _ _ hf h) hcl hcs
    refine ⟨ex.1, ex.2.1, fun hcond a hb => ?_⟩
    cases hb with
    | clock _ s' effs _ hlt hf h => exact ex.2.2 hcond hlt s' effs hf a h


/-- The cascade a step of a kind starts keeps what the kind's encoding reads of it (`SymInput.LiveJ`): its own effects
are among those the kind can queue. -/
theorem begins_liveJ {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV} (hv : v.Reach P E)
    {shs : List (PendingShape v.event)} {n : Nat} {s : State v} (hinv : Step.Inv P s) {inp : SymInput v shs n} {hc}
    {x : Input v} (hx : inp.decode M L hc = some x) {a : Step.Acc v} (hb : Step.Begins T s x a) : inp.LiveJ P a := by
  cases inp with
  | command k sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases hb with
    | command _ _ _ _ h =>
      simp only [Step.execCommand] at h
      split at h
      · cases h
      · split at h
        · rename_i evs hdec
          obtain ⟨a1, h1, h⟩ := bind_ok.1 h
          split at h
          · cases h
          · cases h
            exact liveJ_command T hv k s _ input hdec h1
        · cases h
  | query => obtain ⟨_, _, rfl, -, -⟩ := decode_query hx; cases hb
  | answer k j toT valT =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases hb with
    | answer _ _ p h _ hp _ happ =>
      exact liveJ_onAnswer T hv (fun _ _ h' => by rw [← h]; simpa [SymInput.evs] using h') _
        (hinv.reach p (List.mem_of_find?_eq_some hp)).1 _ _ happ
  | unmatched t toT valT =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases hb with
    | answer _ _ p h _ hp _ happ =>
      subst h
      exact liveJ_onAnswer T hv (fun _ _ h => by simpa [SymInput.evs] using h) _
        (hinv.reach p (List.mem_of_find?_eq_some hp)).1 _ _ happ
  | event k sv =>
    obtain ⟨value, rfl, -⟩ := decode_event hx
    cases hb with
    | event _ _ _ h => exact liveJ_event T hv k _ value h
  | clock st =>
    obtain ⟨time, rfl, -⟩ := decode_clock hx
    cases hb with
    | clock _ s' effs _ _ hf h => exact liveJ_clock hv _ _ hf h

end

end Tazuna.Smt
