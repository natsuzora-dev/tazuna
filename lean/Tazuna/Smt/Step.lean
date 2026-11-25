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
inductive StepOut where
  | command (o : CommandOut)
  | query (o : QueryOut)
  | answer (o : AnswerOut)
  | unmatched (u : Term)
  | event (o : EventOut)
  | clock (o : ClockOut)

/-- The case a script asks about, which its theorems assume: for an answer, that the slot holds the request it names
(`hit`) or that no slot holds one of its type; other kinds have one case. -/
def StepOut.case : StepOut → Term
  | .answer o => o.hit
  | .unmatched u => u
  | _ => tt

/-- A step's terms and conditions: the step's own (exact, `stepFits`), the codes of the functions it applies (exact,
`codesFit`), and the codes the cascade's internal steps build at captured values. -/
structure EncodedStep where
  out : StepOut
  cond : Term
  codes : Term
  sites : Term

section
variable (L : Layout) (T : List TypeDecl)

/-- The constants of the callers a definition lists. -/
def callersOf {c : Ty} (callers : List c.den0) : Except Refusal (List Term) :=
  if hc : c.isData = true then need "a caller that has no constant" (callerTerms L hc callers)
  else .error (.outside "a caller type that is not data")

/-- A step's terms from the symbolic state and input, by the input's kind. -/
def encodeStep (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v P))
    (S : SymState) : SymInput v → Except Refusal EncodedStep
  | .command i caller input => do
    let x := v.commands.get i
    let (cc, cx) ← CommandCode.of L x
    let (apply, ca) ← v.apply.code L
    let (inv, ci) ← v.invariants.code L
    let ks ← callersOf L x.callers
    let ⟨o, c, cs⟩ ← encodeCommand L T P v (shapes v P) senv x cc apply inv ks S caller input
    pure ⟨.command o, c, andT cx (andT ca ci), cs⟩
  | .query i caller input => do
    let q := v.queries.get i
    let (qc, cq) ← QueryCode.of L q
    let ks ← callersOf L q.callers
    let (o, c) ← encodeQuery L q qc ks S caller input
    pure ⟨.query o, c, cq, tt⟩
  | .answer k j to value => do
    let sh ← need "an answer shape past the pending shapes" (shapes v P)[k]?
    let (apply, ca) ← v.apply.code L
    let (inv, ci) ← v.invariants.code L
    let ⟨o, c, cs⟩ ← encodeAnswer L T P (shapes v P) k sh j senv apply inv S to value
    pure ⟨.answer o, c, andT ca ci, cs⟩
  | .unmatched t to _ => do
    let u ← answerUnmatchedT L (shapes v P) t S.pending to
    pure ⟨.unmatched u, tt, tt, tt⟩
  | .event i value => do
    let (ec, ce) ← EventCode.of L v i
    let ⟨o, c, cs⟩ ← encodeEvent L T P v (shapes v P) senv ec S value
    pure ⟨.event o, c, ce, cs⟩
  | .clock time => do
    let (apply, ca) ← v.apply.code L
    let (inv, ci) ← v.invariants.code L
    let ⟨o, c, cs⟩ ← encodeClock L T P v (shapes v P) senv apply inv S time
    pure ⟨.clock o, c, andT ca ci, cs⟩

end

section
variable (S : Ty → Nat) (T : List TypeDecl) {v : ServiceV}

/-- Whether the codes of the functions a step of the input's kind applies fit their slots. -/
def codesFit : SymInput v → Prop
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
    let ctx := Step.ctx s s.records caller input
    x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
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
      roundsFit S T { s with now := time } true (v.bounds.cascade.toNat + 1) ∧
      ∀ s' effs, Step.fire { s with now := time } (v.bounds.cascade.toNat + 1) = some (s', effs) →
        finishFits S T shs (Step.start { state := s' } effs)

end

section
variable (M : Model) (L : Layout) (T : List TypeDecl) {v : ServiceV}

/-- What a step's terms say of its result `r` from the state `s` and the input. -/
def StepOut.Rel (shs : List (PendingShape v.event)) (s : State v) :
    StepOut → Input v → Result v → Prop
  | .command o, .command i _ _, r =>
    let s' := { s with fresh := s.fresh + 1 }
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = ⟨s', .invalid (n :: ns), [], []⟩
      | [] =>
        if (o.ok.denote M).toBool then
          match brokenIn M o.ensures with
          | n :: _ => r = ⟨s', .fault (.ensures n), [], []⟩
          | [] => Finished M L T shs o.finish s' { state := s' } .accepted r
        else r.state = s' ∧ ∃ j, r.outcome = .rejected ⟨(v.commands.get i).rejection, j⟩ ∧
          RelV L _ (Ty.up _ ((v.commands.get i).data).rejection j) (o.rejection.denote M)
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

theorem callersOf_ok {c : Ty} (hc : c.isData = true) {callers : List c.den0} {ks : List Term}
    (h : callersOf L callers = .ok ks) : callerTerms L hc callers = some ks := by
  simp only [callersOf, hc, dite_true] at h; exact need_ok.1 h

theorem apply_inv_exact {v : ServiceV} {apply : Code (Ty.fn [v.records, v.event] v.records)}
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ca ci : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hinv : v.invariants.code L = .ok (inv, ci)) :
    Holds M (andT ca ci) ↔ (v.apply.fits L.count).1 ∧ (v.invariants.fits L.count).1 := by
  rw [holds_andT, (v.apply.code_exact (M := M) happ).1, (v.invariants.code_exact (M := M) hinv).1]

/-- T2 and exactness for every step kind. Wherever a model's values of the symbolic state and input decode to a state
`s` that keeps the step invariant and to an input: the codes' condition holds exactly when the codes fit; where it,
the cascade's codes' condition and the case the script asks about hold, the step's condition holds exactly when what
the step applies fits, and wherever it holds the step from `s` is the one the terms say. -/
theorem step_encode {P : List AnySite} {v : ServiceV} (chk : Checked P T v)
    (senv : StepEnv L (shapes v P))
    {S : SymState} {s : State v} (hS : S.decode M L T (shapes v P) = some s) (hinv : Step.Inv P s)
    {inp : SymInput v} {hc} {x : Input v} (hx : inp.decode M L (shapes v P) hc = some x)
    {t : EncodedStep} (henc : encodeStep L T P v senv S inp = .ok t) :
    (Holds M t.codes ↔ codesFit L.count inp) ∧
    (Holds M t.codes → Holds M t.sites → Holds M t.out.case →
      (Holds M t.cond ↔ stepFits L.count T (shapes v P) s x) ∧
      (Holds M t.cond → t.out.Rel M L T (shapes v P) s x (step T v s x))) := by
  have hR := decode_state hS
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
    have hks' := callersOf_ok (v.commands.get i).data.caller hks
    exact command_encode chk (fun _ => shapes_inSites) s hinv i caller input hcc hcx happ hca hinvc hci hks' senv hR hsc hsi hcmd hcs
  | query i sc si =>
    obtain ⟨caller, input, rfl, hsc, hsi⟩ := decode_query hx
    obtain ⟨⟨qc, cq⟩, hqc, henc⟩ := bind_ok.1 henc
    obtain ⟨ks, hks, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c⟩, hqe, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    exact ⟨queryCode_exact hqc, fun hcq _ _ =>
      query_encode s i caller input hqc hcq (callersOf_ok (v.queries.get i).data.caller hks) hR hsc hsi hqe⟩
  | answer k j toT valT =>
    obtain ⟨sh, hk, henc⟩ := bind_ok.1 henc
    have hk := need_ok.1 hk
    obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨inv, ci⟩, hinvc, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hans, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨apply_inv_exact happ hinvc, fun hcodes hcs hhit => ?_⟩
    obtain ⟨hca, hci⟩ := (holds_andT _ _).1 hcodes
    have hx' : decodeAnswer M L (answerTy sh.output sh.rejection) toT valT = some x := by
      simpa [SymInput.decode, hk] using hx
    obtain ⟨hty, to, value, rfl, hto, hval⟩ := decode_answer hx'
    have ex := answer_encode chk (fun _ => shapes_inSites) s hinv hk j to value happ hca hinvc hci senv hR hto hty hval hans hcs
    exact ⟨by rw [ex.1]; exact ⟨fun h => h hhit, fun h _ => h⟩, fun hcond => ex.2 hcond hhit⟩
  | unmatched ty toT valT =>
    obtain ⟨u, hu, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨-, to, value, rfl, hto, -⟩ := decode_answer hx
    refine ⟨by simp [holds_tt, codesFit], fun _ _ hcase => ⟨?_, fun _ => answer_unmatched s to ty value hR.pending hto hu hcase⟩⟩
    refine ⟨fun _ p hf => ?_, fun _ => holds_tt⟩
    simp [answerFits, unmatched_types s to ty hR.pending hto hu hcase p hf]
  | event i sv =>
    obtain ⟨value, rfl, hsv⟩ := decode_event hx
    obtain ⟨⟨ec, ce⟩, hec, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hev, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    exact ⟨eventCode_exact hec, fun hce hcs _ =>
      event_encode chk (fun _ => shapes_inSites) s hinv i value hec hce hR hsv senv hev hcs⟩
  | clock st =>
    obtain ⟨time, rfl, hst⟩ := decode_clock hx
    obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨inv, ci⟩, hinvc, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hcl, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨apply_inv_exact happ hinvc, fun hcodes hcs _ => ?_⟩
    obtain ⟨hca, hci⟩ := (holds_andT _ _).1 hcodes
    exact clock_encode chk (fun _ => shapes_inSites) s hinv time happ hca hinvc hci hR hst senv hcl hcs

end

end Tazuna.Smt
