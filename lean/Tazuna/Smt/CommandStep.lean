import Tazuna.Smt.Finish

/-! The command kind: the caller and the `accepts` rules admit the input, `decide` accepts with events or rejects,
the events run through the events loop (each applied, every machine and reaction reacting), then the command's
`ensures` is checked on the records they leave, and the step ends (`encodeFinish`). Every outcome advances the fresh
counter. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of a command step's outcome: whether the caller is listed and the `accepts` rules, `decide` and what
follows it, and the step's end. -/
structure CommandOut (v : ServiceV) where
  callerOk : Term
  rules : List (Term × Term)
  decided : DecideOut v
  finish : FinishOut v

section
variable (L : Layout) (T : List TypeDecl)

/-- A command step's outcome terms, its condition and the codes' condition, from the codes of the command's and the
service's functions, the terms of the state, the caller and the input, and the listed callers' constants. The
condition asks only for what the step computes: the step's end only where `decide` accepted and `ensures` held. -/
def encodeCommand (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (x : CommandV v.records v.event v.caller) (cc : CommandCode x) (apply : Code (Ty.fn [v.records, v.event] v.records))
    (invariants : Code (Ty.fn [v.records] Ty.rules)) (callers : List Term)
    (S : SymState v) (caller input : Term) :
    Except Refusal (Encoded (CommandOut v)) := do
  let (a, c1) ← encodeAdmit (c := v.caller) L cc.accepts callers caller input
  let cx ← encodeCtx L S.records S.now S.fresh caller input
  let (dc, cd) ← encodeDecide L T v shs senv x cc apply cx S.now S.records S.machines S.nextId (.int 0)
  let ⟨fo, cf, cfx⟩ ← encodeFinish L T P v shs senv apply invariants S.now (.add S.fresh (.int 1)) S.pending dc.after
  pure ⟨⟨a.callerOk, a.rules, dc, fo⟩,
    .ite a.callerOk (andT c1 (.ite (allT (a.rules.map (·.2)))
      (andT cd (.ite (.and dc.ok (allT (dc.ensures.map (·.2)))) cf tt)) tt)) tt, cfx⟩

end

section
variable {v : ServiceV}

/-- Whether what a command step does after `decide` fits, for what `decide` returned: what follows it
(`decideFits`) and, on acceptance where `ensures`' rules hold, the step's end (`finishFits`). -/
def decidedFits (S : Ty → Nat) (T : List TypeDecl) (shs : List (PendingShape v.event)) (s : State v)
    (x : CommandV v.records v.event v.caller) (ctx : (Ty.ctx v.records x.input v.caller).den0) :
    (Ty.result (.list v.event) x.rejection).den0 → Prop
  | .inl (events, ()) =>
    decideFits S T s x ctx (.inl (events, ())) ∧
      (Step.broken (x.ensures.fn (ctx, (Step.reactAll T s events).1.records, ())) = [] →
        finishFits S T shs (Step.applyEvents T { state := s } events))
  | .inr r => decideFits S T s x ctx (.inr r)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- A command step: where the codes' conditions hold, the condition holds exactly when, for a listed caller, `accepts`
fits at the input and, where its rules hold, `decide` fits at the context and what follows it fits (`decidedFits`).
Wherever it holds, the outcome terms decide the step's outcome: an unlisted caller or a broken `accepts` rule is
Invalid; a rejection is the rejection the terms denote; a broken `ensures` rule is the step's fault; otherwise the
step ends as its end terms say (`Finished`), and the cascade an acceptance starts waits only on own effects the own
slots code. The fresh counter advances in every case. -/
theorem command_encode {P : List AnySite} {E : List AnyEffectSite} {v : ServiceV} (chk : Checked P E T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P) (hshp : ShapesHold shs v.declared)
    (s : State v) (hsinv : Step.Inv P s)
    (i : Fin v.commands.length) (caller : v.caller.den0) (input : (v.commands.get i).input.den0) {cc : CommandCode (v.commands.get i)} {cx : Term}
    (hcc : CommandCode.of L _ = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hinv : v.invariants.code L = .ok (inv, ci)) (hci : Holds M ci)
    {ks : List Term} (hks : callerTerms L ((v.commands.get i).data).caller (v.commands.get i).callers = some ks)
    (senv : StepEnv L shs)
    {S : SymState v} (hR : StateRel M L T shs S s) {sc si : Term}
    (hsc : RelV L v.caller (Ty.up _ ((v.commands.get i).data).caller caller) (sc.denote M))
    (hsi : RelV L (v.commands.get i).input (Ty.up _ ((v.commands.get i).data).input input) (si.denote M))
    {o : CommandOut v} {cond cfx : Term}
    (henc : encodeCommand L T P v shs senv (v.commands.get i) cc apply inv ks S sc si = .ok ⟨o, cond, cfx⟩) (hcfx : Holds M cfx) :
    let x := v.commands.get i
    let ctx := Step.ctx s s.records caller input
    let r := step T v s (.command i caller input)
    let s' := { s with fresh := s.fresh + 1 }
    (Holds M cond ↔ (x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
      x.accepts.appFits L.count (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits L.count (ctx, ()) ∧
          decidedFits L.count T shs { s with fresh := s.fresh + 1 } x ctx (x.decide.fn (ctx, ()))))) ∧
    (Holds M cond →
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
      else r = ⟨s', .invalid ["callers"], [], []⟩) ∧
    (Holds M cond → ∀ a, Step.execCommand T { state := s } x caller input = .ok (.accepted a) → QueueCoded L a) := by
  intro x ctx r s'
  have hcR := CommandCode.rel_of hcc hccx
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨cx, h1', henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dc, cd⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cfx'⟩, h3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hok, hbr⟩ := admit_rel ((v.commands.get i).data).input ((v.commands.get i).data).caller _
    ((v.commands.get i).data).accepts hcR.accepts _ hks caller input hsc hsi h1
  have hcx := commandCtx_rel v.records_data ((v.commands.get i).data).input ((v.commands.get i).data).caller
    ((v.commands.get i).data).ctx s caller input hR.records hR.now hR.fresh hsc hsi h1'
  let s1 : State v := { s with fresh := s.fresh + 1 }
  have hinv1 : Step.Inv P s1 := hsinv.congr rfl rfl
  have D := decide_encode chk hshs hshp x hcc hccx happ hca senv { state := s1 } ctx hcx hR.now hR.records hR.machines
    hR.nextId (q := .int 0) (q0 := 0) rfl (fresh := .add S.fresh (.int 1)) (by simp [Term.denote, hR.fresh, s1, Val.toInt])
    h2
  have hfin := fun events (hacc : AccRel M L T shs { state := s1 } dc.after (.add S.fresh (.int 1)) 0
      (Step.applyEvents T { state := s1 } events)) =>
    finish_encode chk hshs hshp happ hca hinv hci senv s1 .accepted { state := s1 } rfl hinv1 hR.now hR.pending hacc
      (applyEvents_ok chk.reach _ rfl hinv1 events) h3 hcfx
  refine ⟨?_, fun hc => ?_, fun hc a hex => ?_⟩
  · obtain ⟨⟨_, c1'⟩, g1, hcc0⟩ := bind_ok.1 hcc
    obtain ⟨_, -, hcc0⟩ := bind_ok.1 hcc0
    obtain ⟨_, -, hcc0⟩ := bind_ok.1 hcc0
    cases pure_ok.1 hcc0
    obtain ⟨hca1, -⟩ := (holds_andT _ _).1 hccx
    rw [holds_ite_tt (by rw [hok])]
    refine imp_congr_right fun _ => ?_
    rw [holds_andT]
    have e1 := admit_exact ((v.commands.get i).data).input x.accepts g1 hca1 input hsi h1
    have hrest : Holds M c1 → (Holds M (.ite (allT (adm.rules.map (·.2)))
        (andT cd (.ite (.and dc.ok (allT (dc.ensures.map (·.2)))) cf tt)) tt) ↔
        (Step.broken (x.accepts.fn (input, ())) = [] →
          x.decide.appFits L.count (ctx, ()) ∧ decidedFits L.count T shs s1 x ctx (x.decide.fn (ctx, ())))) := fun hc1 => by
      have hall : ((allT (adm.rules.map (·.2))).denote M).toBool = decide (Step.broken (x.accepts.fn (input, ())) = []) := by
        rw [toBool_allT_rules, hbr hc1]
      rw [holds_ite_tt hall, decide_eq_true_iff]
      refine imp_congr_right fun _ => ?_
      rw [holds_andT, D.1]
      have R := D.2
      have E := D.1
      revert R E
      cases hdv : x.decide.fn (ctx, ()) with
      | inr q =>
        match q, hdv with
        | .inl (j, ()), _ =>
          intro R E
          simp only [decidedFits]
          refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
          obtain ⟨hokf, -, -⟩ := R (E.2 h)
          rw [holds_ite_tt (b := false) (by simp only [Term.denote, toBool_bool, hokf, Bool.false_and])]
          simp
        | .inr e, _ => exact e.elim
      | inl p =>
        obtain ⟨events, ⟨⟩⟩ := p
        intro R E
        simp only [decidedFits]
        have tail : x.decide.appFits L.count (ctx, ()) ∧ decideFits L.count T s1 x ctx (.inl (events, ())) →
            (Holds M (.ite (.and dc.ok (allT (dc.ensures.map (·.2)))) cf tt) ↔
              (Step.broken (x.ensures.fn (ctx, (Step.reactAll T s1 events).1.records, ())) = [] →
                finishFits L.count T shs (Step.applyEvents T { state := s1 } events))) := fun h => by
          obtain ⟨hokt, hbe, hacc, -⟩ := R (E.2 h)
          rw [holds_ite_tt (b := decide (Step.broken (x.ensures.fn (ctx, (Step.reactAll T s1 events).1.records, ())) = []))
            (by simp only [Term.denote, toBool_bool, hokt, toBool_allT_rules, hbe, Bool.true_and]), decide_eq_true_iff]
          exact imp_congr_right fun _ => (hfin events hacc).1
        exact ⟨fun ⟨⟨p2, pd⟩, ht⟩ => ⟨p2, pd, (tail ⟨p2, pd⟩).1 ht⟩,
          fun ⟨p2, pd, pt⟩ => ⟨⟨p2, pd⟩, (tail ⟨p2, pd⟩).2 pt⟩⟩
    constructor
    · rintro ⟨hc1, hx⟩
      exact ⟨e1.1 hc1, (hrest hc1).1 hx⟩
    · rintro ⟨p1, px⟩
      have hc1 := e1.2 p1
      exact ⟨hc1, (hrest hc1).2 px⟩
  · simp only [r, s', step, Step.execCommand, Step.admit, bind, Except.bind]
    cases hin : (v.commands.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
    case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
    simp only [hok, hin, Val.toBool, ite_true]
    have hc' : Holds M (andT c1 (.ite (allT (adm.rules.map (·.2)))
        (andT cd (.ite (.and dc.ok (allT (dc.ensures.map (·.2)))) cf tt)) tt)) := by
      simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
    rw [holds_andT] at hc'
    have hbroken := hbr hc'.1
    rw [hbroken]
    cases hb : Step.broken ((v.commands.get i).accepts.fn (input, ())) with
    | cons n ns => rfl
    | nil =>
      simp only
      have hallT : ((allT (adm.rules.map (·.2))).denote M).toBool = true := by
        rw [toBool_allT_rules, hbroken, hb]; rfl
      have hcd' := (holds_ite_tt hallT).1 hc'.2 rfl
      obtain ⟨hcd, hct⟩ := (holds_andT _ _).1 hcd'
      have R := D.2 hcd
      revert R
      cases hdec : (v.commands.get i).decide.fn (Step.ctx s s.records caller input, ()) with
      | inr q =>
        match q, hdec with
        | .inl (j, ()), _ =>
          rintro ⟨hokf, hrj, -⟩
          simp only [hokf, Bool.false_eq_true, ite_false]
          exact ⟨by trivial, j, by trivial, hrj⟩
        | .inr e, _ => exact e.elim
      | inl p =>
        obtain ⟨events, ⟨⟩⟩ := p
        rintro ⟨hokt, hbe, hacc, hrecs, -⟩
        simp only [hokt, ite_true]
        obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, -, -, -, -, e5, -, -⟩ := id hacc
        obtain ⟨ps1, hps1⟩ := newsRel_writes e5
        have happly := hr1 ps1 hps1
        have hr := hrecs _ happly
        rw [happly]
        dsimp only at hr ⊢
        rw [hbe, ← hr]
        cases hbe' : Step.broken ((v.commands.get i).ensures.fn (Step.ctx s s.records caller input, recs1, ())) with
        | cons n ns => rfl
        | nil =>
          simp only
          have hcf : Holds M cf := (holds_ite_tt (b := true)
            (by
              simp only [Term.denote, toBool_bool, hokt, toBool_allT_rules, hbe, Bool.true_and]
              exact decide_eq_true (by rw [← hr]; exact hbe'))).1 hct rfl
          rw [happly] at hacc
          exact (finish_encode chk hshs hshp happ hca hinv hci senv s1 .accepted { state := s1 } rfl hinv1 hR.now hR.pending hacc
            (fun a1 h => applyEvents_ok chk.reach _ rfl hinv1 events a1 (happly.trans h)) h3 hcfx).2 hcf
  · simp only [Step.execCommand, x] at hex
    split at hex
    · cases hex
    rename_i hadm
    have hin : (v.commands.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true := by
      cases h : (v.commands.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
      · rw [Step.admit, h] at hadm; cases hadm
      · rfl
    have hb : Step.broken ((v.commands.get i).accepts.fn (input, ())) = [] := by
      rw [Step.admit, hin] at hadm; exact hadm
    have hc' : Holds M (andT c1 (.ite (allT (adm.rules.map (·.2)))
        (andT cd (.ite (.and dc.ok (allT (dc.ensures.map (·.2)))) cf tt)) tt)) := by
      simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
    rw [holds_andT] at hc'
    have hallT : ((allT (adm.rules.map (·.2))).denote M).toBool = true := by
      rw [toBool_allT_rules, hbr hc'.1, hb]; rfl
    obtain ⟨hcd, -⟩ := (holds_andT _ _).1 ((holds_ite_tt hallT).1 hc'.2 rfl)
    have R := D.2 hcd
    revert R hex
    cases hdec : (v.commands.get i).decide.fn (Step.ctx s s.records caller input, ()) with
    | inr q =>
      match q, hdec with
      | .inl (j, ()), _ => intro hex; cases hex
      | .inr e, _ => exact e.elim
    | inl p =>
      obtain ⟨events, ⟨⟩⟩ := p
      rintro hex ⟨-, -, hacc, -⟩
      simp only [bind, Except.bind] at hex
      cases happly : Step.applyEvents T { state := s1 } events with
      | error f => rw [happly] at hex; cases hex
      | ok a1 =>
        rw [happly] at hex
        simp only at hex
        split at hex
        · cases hex
        · cases hex
          exact hacc.queueCoded rfl _ happly

end

end Tazuna.Smt
