import Tazuna.Smt.StepEnd

/-! The command kind: the caller and the `accepts` rules admit the input, `decide` accepts with events or rejects,
the events run through the events loop (each applied, every machine and reaction reacting), then the command's
`ensures` is checked on the records they leave, and the step ends (`encodeFinish`). Every outcome advances the fresh
counter. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of a command step's outcome: whether the caller is listed and the `accepts` rules, whether `decide`
accepted, its rejection and its events, what the events loop leaves, the `ensures` rules on the records after, and the
step's end. -/
structure CommandOut where
  callerOk : Term
  rules : List (Term × Term)
  ok : Term
  rejection : Term
  events : Term
  after : EventsOut
  ensures : List (Term × Term)
  finish : FinishOut

section
variable (L : Layout) (T : List TypeDecl)

/-- A command step's outcome terms, its condition and the codes' condition, from the codes of the command's and the
service's functions, the terms of the state, the caller and the input, and the listed callers' constants. The
condition asks only for what the step computes. -/
def encodeCommand (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (x : CommandV v.records v.event v.caller) (cc : CommandCode x) (apply : Code (Ty.fn [v.records, v.event] v.records))
    (invariants : Code (Ty.fn [v.records] Ty.rules)) (callers : List Term)
    (records now fresh nextId pending caller input : Term) (xs : List Term) :
    Except Refusal (CommandOut × Term × Term) := do
  let cc0 ← need "a caller that has no term" (Code.ofTerm? v.caller caller)
  let eqs ← callers.mapM fun k => do eqCode L v.caller cc0 (← need "a caller that has no term" (Code.ofTerm? v.caller k))
  let ic ← need "an input that has no term" (Code.ofTerm? x.input input)
  let (rs, c1) ← cc.accepts (ic, ())
  let rules ← ruleTerms L rs
  let ctx ← adtCtor L 5 [v.records, x.input, v.caller] [[v.records, x.input, v.caller, .int, .dsl .fresh []]] 0
    [records, input, caller, now, fresh]
  let cx ← need "a context that has no term" (Code.ofTerm? (Ty.ctx v.records x.input v.caller) (Term.share ctx))
  let (res, c2) ← cc.decide (cx, ())
  let rest ← need "a result that has no term" (Code.term? _ res)
  let (d, _) ← need "a layout without the result type" (L.find? (Ty.result (.list v.event) x.rejection))
  let res := Term.share rest
  let evs := Term.sel d 0 0 res
  let (dl, n, dt) ← collD L (.list v.event) [v.event]
  let (o, c3) ← encodeEvents L T v shs dE dP dopt apply now (slotsOf dl dt n 1 evs) records xs nextId (.int 0)
  let rfc ← need "records that have no term" (Code.ofTerm? v.records o.records)
  let (ens, c4) ← cc.ensures (cx, rfc, ())
  let ensures ← ruleTerms L ens
  let (fo, cf, cfx) ← encodeFinish L T P v shs dE dP dopt apply invariants now (.add fresh (.int 1)) pending o
  let callerOk := anyT eqs
  let ok := Term.is d 0 res
  pure (⟨callerOk, rules, ok, .sel d 1 0 res, evs, o, ensures, fo⟩,
    .ite callerOk (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (.ite ok (andT c3 (andT c4
      (.ite (allT (ensures.map (·.2))) cf tt))) tt)) tt)) tt, cfx)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- T2 for a command: wherever the condition holds, the outcome terms decide the step's outcome. An unlisted caller or
a broken `accepts` rule is Invalid; a rejection is the rejection the terms denote; a broken `ensures` rule is the
step's fault; otherwise the step ends as its end terms say (`Finished`). The fresh counter advances in every case. -/
theorem command_step {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (s : State v) (hinv : Step.Inv P s)
    (i : Fin v.commands.length) (caller : v.caller.den0) (input : (v.commands.get i).input.den0)
    (hd : CommandData (v.commands.get i)) {cc : CommandCode (v.commands.get i)} {cx : Term}
    (hcc : CommandCode.of L _ = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hinv' : v.invariants.code L = .ok (inv, ci)) (hci : Holds M ci)
    {ks : List Term} (hks : callerTerms L hd.caller (v.commands.get i).callers = some ks)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh nextIdT pending sc si : Term} {xs : List Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hpend : PendingRel L shs (pending.denote M) s.pending)
    (hms : MachinesRel M L T v.machines xs s.machines)
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L (v.commands.get i).input (Ty.up _ hd.input input) (si.denote M))
    {o : CommandOut} {cond cfx : Term}
    (henc : encodeCommand L T P v shs dE dP dopt (v.commands.get i) cc apply inv ks records now fresh nextIdT pending sc
      si xs = .ok (o, cond, cfx))
    (hc : Holds M cond) (hcfx : Holds M cfx) :
    let r := step T v s (.command i caller input)
    let s' := { s with fresh := s.fresh + 1 }
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = ⟨s', .invalid (n :: ns), [], []⟩
      | [] =>
        if (o.ok.denote M).toBool then
          match brokenIn M o.ensures with
          | n :: _ => r = ⟨s', .fault (.ensures n), [], []⟩
          | [] => Finished M L T hd.records shs o.finish s' { state := s' } .accepted r
        else r.state = s' ∧ ∃ j, r.outcome = .rejected ⟨(v.commands.get i).rejection, j⟩ ∧
          RelV L _ (Ty.up _ hd.rejection j) (o.rejection.denote M)
    else r = ⟨s', .invalid ["callers"], [], []⟩ := by
  have hcc := CommandCode.rel_of hd hcc hccx
  have happ0 := happ
  have hinv0 := hinv'
  have happ := v.apply.code_fn hd.apply happ hca
  intro r s'
  obtain ⟨cc0, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cx, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨res, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨rest, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨d, dn⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, n, dt⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oe, c3⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cfx'⟩, h16, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 (v.commands.get i).callers ks hks eqs h2
  simp only [r, s', step, Step.execCommand, Step.admit, bind, Except.bind]
  cases hin : (v.commands.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
  case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
  simp only [hok, hin, Val.toBool, ite_true]
  have hc' : Holds M (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (.ite (Term.is d 0 (Term.share rest))
      (andT c3 (andT c4 (.ite (allT (ensures.map (·.2))) cf tt))) tt)) tt)) := by
    simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
  rw [holds_andT] at hc'
  have hic : Smt.Rel M L _ (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  have hacc := hcc.accepts _ (ic, ()) (rels1 hd.input hd.args hic) rs c1 h4 hc'.1
  erw [Ty.up_fn _ Ty.rules _ hd.args rfl] at hacc
  have hbroken := rules_broken h5 _ hacc
  rw [hbroken]
  cases hb : Step.broken ((v.commands.get i).accepts.fn (input, ())) with
  | cons n ns => rfl
  | nil =>
    simp only
    have hallT : (allT (rules.map (·.2))).denote M = .bool true := by
      rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil rules).1 (hbroken.trans hb))
    have hc2' : Holds M (andT c2 (.ite (Term.is d 0 (Term.share rest))
        (andT c3 (andT c4 (.ite (allT (ensures.map (·.2))) cf tt))) tt)) := by
      have := hc'.2; simp only [Holds, Term.denote, hallT, Val.toBool, ite_true] at this; exact this
    rw [holds_andT] at hc2'
    have hctx := adtCtor_rel (L := L) (M := M)
      (vs := [[v.records, (v.commands.get i).input, v.caller, .int, .dsl .fresh []]])
      ⟨0, by simp⟩ _ _ h6
      (Ty.up _ hd.records s.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, s.now, s.fresh, ())
      ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
    rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
    have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx (Step.ctx s s.records caller input)) cx :=
      (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctx)
    have hres := hcc.decide _ (cx, ()) (rels1 hd.ctx hd.ctxArgs hcx) res c2 h8 hc2'.1
    erw [Ty.up_fn _ _ _ hd.ctxArgs hd.result] at hres
    have hres' := (rel_term (need_ok.1 h9) _).1 hres
    have hfd := need_ok.1 h10
    have hc2'' := hc2'.2
    have hsh : (Term.share rest).denote M = rest.denote M := Term.denote_share M rest
    have hdata2 : (Ty.adt 2 [.list v.event, (v.commands.get i).rejection] [[(v.commands.get i).rejection]]).isData = true := by
      simp only [Ty.isData, Ty.isDatas, Ty.isDatass, hd.rejection, Bool.and_true]
    cases hdec : (v.commands.get i).decide.fn (Step.ctx s s.records caller input, ()) with
    | inr q =>
      match q, hdec with
      | .inl (j, ()), hdec =>
        rw [hdec] at hres'
        erw [Ty.up_inr 2 _ _ _ hd.result hdata2, Ty.up_inl 2 _ _ _ hdata2 (by simp only [Ty.isData, Ty.isDatas, hd.rejection, Bool.and_true]),
          Ty.up_tuple _ _ _ hd.rejection rfl] at hres'
        obtain ⟨d', n', hf', vals, hw, rv, rest', rfl, hrv, rfl⟩ := hres'
        obtain rfl := find_det hfd hf'
        have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool false := by
          simp [Term.denote, hsh, hw]
        simp only [hok', Bool.false_eq_true, ite_false]
        refine ⟨by trivial, j, by trivial, ?_⟩
        simp only [Term.denote, hsh, hw, and_self, ite_true, List.getElem?_cons_zero, Option.getD_some]
        exact hrv
      | .inr e, _ => exact e.elim
    | inl p =>
      obtain ⟨events, ⟨⟩⟩ := p
      rw [hdec] at hres'
      erw [Ty.up_inl 2 _ _ _ hd.result (by simp only [Ty.isData, Ty.isDatas, hd.event, Bool.and_true]),
        Ty.up_tuple _ _ _ hd.events rfl] at hres'
      obtain ⟨d', n', hf', vals, hw, ev, rest', rfl, hev, rfl⟩ := hres'
      obtain rfl := find_det hfd hf'
      have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool true := by
        simp [Term.denote, hsh, hw]
      simp only [hok', ite_true]
      replace hc2'' : Holds M (andT c3 (andT c4 (.ite (allT (ensures.map (·.2))) cf tt))) := by
        have := hc2''
        simp only [Holds, Term.denote, Term.denote_share, hw, beq_self_eq_true, Bool.and_self, Val.toBool,
          ite_true] at this
        exact this
      obtain ⟨hc3, hc4, hc5⟩ : Holds M c3 ∧ Holds M c4 ∧ Holds M (.ite (allT (ensures.map (·.2))) cf tt) := by
        rw [holds_andT, holds_andT] at hc2''; exact hc2''
      have hevs : Smt.Rel M L (.list v.event) (Ty.up _ hd.events events) (Term.sel d 0 0 (Term.share rest)) := by
        show RelV _ _ _ _
        rw [sel_ctor 0 (hsh.trans hw)]; exact hev
      obtain ⟨sv, hS, -, hsw, hh⟩ := list_view hevs h11
      erw [Ty.up_list _ _ hd.event] at hh
      let s1 : State v := { s with fresh := s.fresh + 1 }
      have hinv1 : Step.Inv P s1 := hinv.congr rfl rfl rfl
      have hdone := events_done (T := T) hP hvx hinv1.machinesReach hshs hor hd.records hd.event hd.apply happ hE hPE
        hopt { state := s1 } rfl hnow hS hsw hh hrec hms hnid (fresh := .add fresh (.int 1))
        (by simp [Term.denote, hfresh, s1, Val.toInt]) h12 hc3
      have hd2 := hdone
      obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, e1, -, -, -, e5, -, -⟩ := hd2
      obtain ⟨ps1, hps1⟩ := newsRel_writes e5
      have happly := hr1 ps1 hps1
      rw [happly]
      dsimp only
      have hrfc : Smt.Rel M L v.records (Ty.up _ hd.records recs1) rfc := (rel_ofTerm (need_ok.1 h13) _).2 e1
      have hens := hcc.ensures _ _ (rels2 hd.ctx hd.records hd.ensArgs hcx hrfc) ens c4 h14 hc4
      erw [Ty.up_fn _ Ty.rules _ hd.ensArgs rfl] at hens
      have hbe := rules_broken h15 _ hens
      rw [hbe]
      cases hbe' : Step.broken ((v.commands.get i).ensures.fn (Step.ctx s s.records caller input, recs1, ())) with
      | cons n ns => rfl
      | nil =>
        simp only
        have hallE : (allT (ensures.map (·.2))).denote M = .bool true := by
          rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil ensures).1 (hbe.trans hbe'))
        have hcf : Holds M cf := by
          have := hc5; simp only [Holds, Term.denote, hallE, Val.toBool, ite_true] at this
          exact this
        rw [happly] at hdone
        exact finish_rel hP hvx hinv1.machinesReach hshs hor hcd hqd hd.records hd.event happ0 hca hinv0 hci hE hPE hopt
          s1 .accepted { state := s1 } rfl hinv1 hnow hpend hdone
          (fun a1 h => applyEvents_ok hvx _ rfl hinv1 events a1 (happly.trans h)) h16 hcf hcfx

end

section
variable {v : ServiceV}

/-- Whether what a command step does after `decide` fits, for what `decide` returned: on acceptance, the events'
applications in turn from `s` (`eventsFit`), `ensures` at the records they leave and, where its rules hold, the step's
end (`finishFits`). -/
def decidedFits (S : Ty → Nat) (T : List TypeDecl) (shs : List (PendingShape v.event)) (s : State v)
    (x : CommandV v.records v.event v.caller) (ctx : (Ty.ctx v.records x.input v.caller).den0) :
    (Ty.result (.list v.event) x.rejection).den0 → Prop
  | .inl (events, ()) =>
    let sA := Step.reactAll T s events
    eventsFit S T s events ∧ x.ensures.appFits S (ctx, sA.1.records, ()) ∧
      (Step.broken (x.ensures.fn (ctx, sA.1.records, ())) = [] →
        finishFits S T shs (Step.applyEvents T { state := s } events))
  | .inr _ => True

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- The condition of a command's step is exact: for a listed caller, it holds exactly when `accepts` fits at the
input and, where its rules hold, `decide` fits at the context and what follows it fits (`decidedFits`). -/
theorem command_exact {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (s : State v) (hsinv : Step.Inv P s)
    (i : Fin v.commands.length) (caller : v.caller.den0) (input : (v.commands.get i).input.den0)
    (hd : CommandData (v.commands.get i)) {cc : CommandCode (v.commands.get i)} {cx : Term}
    (hcc : CommandCode.of L _ = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hinv : v.invariants.code L = .ok (inv, ci)) (hci : Holds M ci)
    {ks : List Term} (hks : callerTerms L hd.caller (v.commands.get i).callers = some ks)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh nextIdT pending sc si : Term} {xs : List Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hpend : PendingRel L shs (pending.denote M) s.pending)
    (hms : MachinesRel M L T v.machines xs s.machines)
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L (v.commands.get i).input (Ty.up _ hd.input input) (si.denote M))
    {o : CommandOut} {cond cfx : Term}
    (henc : encodeCommand L T P v shs dE dP dopt (v.commands.get i) cc apply inv ks records now fresh nextIdT pending sc
      si xs = .ok (o, cond, cfx)) (hcfx : Holds M cfx) :
    let x := v.commands.get i
    let ctx := Step.ctx s s.records caller input
    Holds M cond ↔ (x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
      x.accepts.appFits L.count (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits L.count (ctx, ()) ∧
          decidedFits L.count T shs { s with fresh := s.fresh + 1 } x ctx (x.decide.fn (ctx, ())))) := by
  intro x ctx
  have hcc' := CommandCode.rel_of hd hcc hccx
  obtain ⟨⟨a, c1'⟩, g1, hcc0⟩ := bind_ok.1 hcc
  obtain ⟨⟨d', c2'⟩, g2, hcc0⟩ := bind_ok.1 hcc0
  obtain ⟨⟨n', c3'⟩, g3, hcc0⟩ := bind_ok.1 hcc0
  cases pure_ok.1 hcc0
  obtain ⟨hca1, hca23⟩ := (holds_andT _ _).1 hccx
  obtain ⟨hca2, hca3⟩ := (holds_andT _ _).1 hca23
  have happ' := v.apply.code_fn hd.apply happ hca
  obtain ⟨cc0, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctxT, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cx, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨res, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨rest, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨d, dn⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, n, dt⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oe, c3⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cfx'⟩, h16, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 (v.commands.get i).callers ks hks eqs h2
  rw [holds_ite_tt (by rw [hok])]
  refine imp_congr_right fun _ => ?_
  rw [holds_andT]
  have hic : Smt.Rel M L _ (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  have hargs := rels1 hd.input hd.args hic
  have e1 : Holds M c1 ↔ x.accepts.appFits L.count (input, ()) :=
    x.accepts.app_exact g1 hca1 (by simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h3)) _ _ hargs h4
  have hctx := adtCtor_rel (L := L) (M := M)
    (vs := [[v.records, (v.commands.get i).input, v.caller, .int, .dsl .fresh []]])
    ⟨0, by simp⟩ _ _ h6
    (Ty.up _ hd.records s.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, s.now, s.fresh, ())
    ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
  rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx ctx) cx :=
    (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctx)
  have hargs' := rels1 hd.ctx hd.ctxArgs hcx
  have e2 : Holds M c2 ↔ x.decide.appFits L.count (ctx, ()) :=
    x.decide.app_exact g2 hca2 (by simp [Ty.ctx, Ty.isFn]) _ _ hargs' h8
  have hrest : Holds M c1 → (Holds M (.ite (allT (rules.map (·.2))) (andT c2 (.ite (Term.is d 0 (Term.share rest))
      (andT c3 (andT c4 (.ite (allT (ensures.map (·.2))) cf tt))) tt)) tt) ↔
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits L.count (ctx, ()) ∧
          decidedFits L.count T shs { s with fresh := s.fresh + 1 } x ctx (x.decide.fn (ctx, ())))) := fun hc1 => by
    have hacc := hcc'.accepts _ (ic, ()) hargs rs c1 h4 hc1
    erw [Ty.up_fn _ Ty.rules _ hd.args rfl] at hacc
    have hbroken := rules_broken h5 _ hacc
    have hall : ((allT (rules.map (·.2))).denote M).toBool = decide (Step.broken (x.accepts.fn (input, ())) = []) := by
      rw [allT_denote, Val.toBool, ← hbroken]
      by_cases hb : brokenIn M rules = []
      · simp [(brokenIn_nil rules).1 hb, hb]
      · have : (rules.map (·.2)).all (fun t => (t.denote M).toBool) ≠ true := fun h =>
          hb ((brokenIn_nil (M := M) rules).2 h)
        simp [hb]; simpa using this
    rw [holds_ite_tt hall, decide_eq_true_iff]
    refine imp_congr_right fun _ => ?_
    rw [holds_andT]
    have hdec : Holds M c2 → (Holds M (.ite (Term.is d 0 (Term.share rest))
        (andT c3 (andT c4 (.ite (allT (ensures.map (·.2))) cf tt))) tt) ↔
        decidedFits L.count T shs { s with fresh := s.fresh + 1 } x ctx (x.decide.fn (ctx, ()))) := fun hc2 => by
      have hres := hcc'.decide _ (cx, ()) hargs' res c2 h8 hc2
      erw [Ty.up_fn _ _ _ hd.ctxArgs hd.result] at hres
      have hres' := (rel_term (need_ok.1 h9) _).1 hres
      have hfd := need_ok.1 h10
      have hsh : (Term.share rest).denote M = rest.denote M := Term.denote_share M rest
      have hdata2 : (Ty.adt 2 [.list v.event, (v.commands.get i).rejection]
          [[(v.commands.get i).rejection]]).isData = true := by
        simp only [Ty.isData, Ty.isDatas, Ty.isDatass, hd.rejection, Bool.and_true]
      cases hdv : (v.commands.get i).decide.fn (Step.ctx s s.records caller input, ()) with
      | inr q =>
        match q, hdv with
        | .inl (j, ()), hdv =>
          rw [hdv] at hres'
          erw [Ty.up_inr 2 _ _ _ hd.result hdata2, Ty.up_inl 2 _ _ _ hdata2
            (by simp only [Ty.isData, Ty.isDatas, hd.rejection, Bool.and_true]),
            Ty.up_tuple _ _ _ hd.rejection rfl] at hres'
          obtain ⟨d', n', hf', vals, hw, rv, rest', rfl, hrv, rfl⟩ := hres'
          obtain rfl := find_det hfd hf'
          have hok' : ((Term.is d 0 (Term.share rest)).denote M).toBool = false := by
            simp [Term.denote, hsh, hw, Val.toBool]
          rw [holds_ite_tt hok']
          simp [decidedFits]
        | .inr e, _ => exact e.elim
      | inl p =>
        obtain ⟨events, ⟨⟩⟩ := p
        rw [hdv] at hres'
        erw [Ty.up_inl 2 _ _ _ hd.result (by simp only [Ty.isData, Ty.isDatas, hd.event, Bool.and_true]),
          Ty.up_tuple _ _ _ hd.events rfl] at hres'
        obtain ⟨d', n', hf', vals, hw, ev, rest', rfl, hev, rfl⟩ := hres'
        obtain rfl := find_det hfd hf'
        have hok' : ((Term.is d 0 (Term.share rest)).denote M).toBool = true := by
          simp [Term.denote, hsh, hw, Val.toBool]
        rw [holds_ite_tt hok']
        simp only [true_implies, decidedFits]
        have hevs : Smt.Rel M L (.list v.event) (Ty.up _ hd.events events) (Term.sel d 0 0 (Term.share rest)) := by
          show RelV _ _ _ _
          rw [sel_ctor 0 (hsh.trans hw)]; exact hev
        obtain ⟨sv, hS, -, hsw, hh⟩ := list_view hevs h11
        erw [Ty.up_list _ _ hd.event] at hh
        let s1 : State v := { s with fresh := s.fresh + 1 }
        let sA := (Step.reactAll T s1 events).1
        have hinv1 : Step.Inv P s1 := hsinv.congr rfl rfl rfl
        have e3 : Holds M c3 ↔ eventsFit L.count T s1 events :=
          events_exact (fun m hm => (hor m hm).1) hd.records hd.event happ hca _ sv hS hsw events hh s1 hnow hrec hms h12
        have hdone : Holds M c3 → SettleDone M L T hd.records shs { state := s1 } ⟨.bool false, oe, .add fresh (.int 1)⟩
            (Step.applyEvents T { state := s1 } events) := fun hc3 =>
          events_done (T := T) hP hvx hinv1.machinesReach hshs hor hd.records hd.event hd.apply happ' hE hPE hopt
            { state := s1 } rfl hnow hS hsw hh hrec hms hnid (by simp [Term.denote, hfresh, s1, Val.toInt]) h12 hc3
        have hrf : Holds M c3 → RelV L v.records (Ty.up _ hd.records sA.records) (oe.records.denote M) := fun hc3 =>
          (events_rel hP hvx hinv1.machinesReach hshs hor hd.records hd.event hd.apply happ' hE hPE hopt _ sv hS hsw
            events hh s1 hnow hrec hms hnid rfl h12 hc3).1
        have e45 : Holds M c3 → (Holds M c4 ↔ x.ensures.appFits L.count (ctx, sA.records, ())) ∧
            (Holds M c4 → (Holds M (.ite (allT (ensures.map (·.2))) cf tt) ↔
              (Step.broken (x.ensures.fn (ctx, sA.records, ())) = [] →
                finishFits L.count T shs (Step.applyEvents T { state := s1 } events)))) := by
          intro hc3
          have hrfc : Smt.Rel M L v.records (Ty.up _ hd.records sA.records) rfc :=
            (rel_ofTerm (need_ok.1 h13) _).2 (hrf hc3)
          have hargs3 := rels2 hd.ctx hd.records hd.ensArgs hcx hrfc
          refine ⟨x.ensures.app_exact g3 hca3 (by
            intro t ht
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · simp [Ty.ctx, Ty.isFn]
            · exact ofTerm_notFn (need_ok.1 h13)) _ _ hargs3 h14, fun hc4 => ?_⟩
          have hens := hcc'.ensures _ _ hargs3 ens c4 h14 hc4
          erw [Ty.up_fn _ Ty.rules _ hd.ensArgs rfl] at hens
          have hbe := rules_broken h15 _ hens
          have hallE : ((allT (ensures.map (·.2))).denote M).toBool =
              decide (Step.broken (x.ensures.fn (ctx, sA.records, ())) = []) := by
            rw [allT_denote, Val.toBool, ← hbe]
            by_cases hb : brokenIn M ensures = []
            · simp [(brokenIn_nil ensures).1 hb, hb]
            · have : (ensures.map (·.2)).all (fun t => (t.denote M).toBool) ≠ true := fun h =>
                hb ((brokenIn_nil (M := M) ensures).2 h)
              simp [hb]; simpa using this
          rw [holds_ite_tt hallE, decide_eq_true_iff]
          refine imp_congr_right fun _ => ?_
          exact finish_exact hP hvx hinv1.machinesReach hshs hor hcd hqd hqout hd.records hd.event happ hca hinv hci hE hPE
            hopt { state := s1 } rfl hnow hpend (hdone hc3) (applyEvents_ok hvx _ rfl hinv1 events) h16 hcfx
        rw [holds_andT, holds_andT]
        constructor
        · rintro ⟨hc3, hc4, hc5⟩
          exact ⟨e3.1 hc3, ((e45 hc3).1).1 hc4, ((e45 hc3).2 hc4).1 hc5⟩
        · rintro ⟨p3, p4, p5⟩
          have hc3 := e3.2 p3
          have hc4 := ((e45 hc3).1).2 p4
          exact ⟨hc3, hc4, ((e45 hc3).2 hc4).2 p5⟩
    constructor
    · rintro ⟨hc2, hx⟩
      exact ⟨e2.1 hc2, (hdec hc2).1 hx⟩
    · rintro ⟨p2, px⟩
      have hc2 := e2.2 p2
      exact ⟨hc2, (hdec hc2).2 px⟩
  constructor
  · rintro ⟨hc1, hx⟩
    exact ⟨e1.1 hc1, (hrest hc1).1 hx⟩
  · rintro ⟨p1, px⟩
    have hc1 := e1.2 p1
    exact ⟨hc1, (hrest hc1).2 px⟩

end


end Tazuna.Smt
