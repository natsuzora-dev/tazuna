import Tazuna.Smt.Finish

/-! The command kind: the caller and the `accepts` rules admit the input, `decide` accepts with events or rejects,
the events run through the events loop (each applied, every machine and reaction reacting, their requests written),
then the command's `ensures` is checked on the records they leave, and the service's and machines' invariants on the
state after. Every outcome advances the fresh counter. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of a command step's outcome: whether the caller is listed and the `accepts` rules, whether `decide`
accepted, its rejection and its events, what the events loop leaves, the `ensures` rules and the invariants on the
records after, the instance checks on the tables after, and the new pending table. -/
structure CommandOut where
  callerOk : Term
  rules : List (Term × Term)
  ok : Term
  rejection : Term
  events : Term
  after : EventsOut
  ensures : List (Term × Term)
  invariants : List (Term × Term)
  checks : List (List InstCheck)
  pending : Term

section
variable (L : Layout) (T : List TypeDecl)

/-- A command step's outcome terms and its condition, from the codes of the command's and the service's functions,
the terms of the state, the caller and the input, and the listed callers' constants. The condition asks only for
what the step computes. -/
def encodeCommand (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (x : CommandV v.records v.event v.caller) (cc : CommandCode x) (apply : Code (Ty.fn [v.records, v.event] v.records))
    (invariants : Code (Ty.fn [v.records] Ty.rules)) (callers : List Term)
    (records now fresh nextId pending caller input : Term) (xs : List Term) : Except Refusal (CommandOut × Term) := do
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
  let (pT, cp) ← encodePending L shs pending o.news
  let rfc ← need "records that have no term" (Code.ofTerm? v.records o.records)
  let (ens, c4) ← cc.ensures (cx, rfc, ())
  let ensures ← ruleTerms L ens
  let (invs, c5) ← invariants (rfc, ())
  let invariants ← ruleTerms L invs
  let (checks, ck) ← encodeInstChecks L T v.machines o.tables o.records now
  let callerOk := anyT eqs
  let ok := Term.is d 0 res
  pure (⟨callerOk, rules, ok, .sel d 1 0 res, evs, o, ensures, invariants, checks, pT⟩,
    .ite callerOk (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (.ite ok (andT c3 (andT cp (andT c4
      (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt)))) tt)) tt)) tt)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- T2 for a command: wherever the condition holds, the outcome terms decide the step's outcome. An unlisted caller or
a broken `accepts` rule is Invalid; a rejection is the rejection the terms denote; a broken `ensures` rule or
invariant (the service's, then each machine's instances in key order) is the step's fault; otherwise the step is
accepted with the events, records and instance tables the terms denote, writes the requests `ps` its events start at
the next wire ids and sends them, and the pending table and next id terms denote what follows. The fresh counter
advances in every case. -/
theorem command_step {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
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
    {o : CommandOut} {cond : Term}
    (henc : encodeCommand L T v shs dE dP dopt (v.commands.get i) cc apply inv ks records now fresh nextIdT pending sc si
      xs = .ok (o, cond))
    (hc : Holds M cond) :
    let r := step T v s (.command i caller input)
    let s' := { s with fresh := s.fresh + 1 }
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = ⟨s', .invalid (n :: ns), [], []⟩
      | [] =>
        if (o.ok.denote M).toBool then
          match brokenIn M o.ensures with
          | n :: _ => r = ⟨s', .fault (.ensures n), [], []⟩
          | [] => match brokenIn M o.invariants ++ checksBroken L T M v.machines o.checks with
            | n :: _ => r = ⟨s', .fault (.invariant n), [], []⟩
            | [] => r.outcome = .accepted ∧
                (∃ ps, r.out = ps.map Step.Pending.line ∧ r.state.pending = s.pending ++ ps ∧
                  r.state.nextId = s.nextId + ps.length ∧
                  ∃ ps', ps'.Perm r.state.pending ∧ PendingRel L shs (o.pending.denote M) ps') ∧
                o.after.nextId.denote M = .int (Int.ofNat r.state.nextId) ∧
                r.state = { s' with records := r.state.records, machines := r.state.machines,
                                    pending := r.state.pending, nextId := r.state.nextId } ∧
                RelV L v.records (Ty.up _ hd.records r.state.records) (o.after.records.denote M) ∧
                MachinesRel M L T v.machines o.after.tables r.state.machines ∧
                RelV L (.list v.event) (Ty.up _ hd.events r.events) (o.events.denote M)
        else r.state = s' ∧ ∃ j, r.outcome = .rejected ⟨(v.commands.get i).rejection, j⟩ ∧
          RelV L _ (Ty.up _ hd.rejection j) (o.rejection.denote M)
    else r = ⟨s', .invalid ["callers"], [], []⟩ := by
  have hcc := CommandCode.rel_of hd hcc hccx
  have happ := v.apply.code_fn hd.apply happ hca
  have hinv' := v.invariants.code_fn hd.invariants hinv' hci
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
  obtain ⟨⟨pT, cp⟩, h12', henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c5⟩, h16, henc⟩ := bind_ok.1 henc
  obtain ⟨invariants, h17, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, ck⟩, h18, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 (v.commands.get i).callers ks hks eqs h2
  simp only [r, s', step, Step.admit]
  cases hin : (v.commands.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
  case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
  simp only [hok, hin, Val.toBool, ite_true]
  have hc' : Holds M (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (.ite (Term.is d 0 (Term.share rest))
      (andT c3 (andT cp (andT c4 (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt)))) tt)) tt)) := by
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
        (andT c3 (andT cp (andT c4 (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt)))) tt)) := by
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
      replace hc2'' : Holds M (andT c3 (andT cp (andT c4 (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt)))) := by
        have := hc2''
        simp only [Holds, Term.denote, Term.denote_share, hw, beq_self_eq_true, Bool.and_self, Val.toBool,
          ite_true] at this
        exact this
      obtain ⟨hc3, hcp, hc4, hc5k⟩ : Holds M c3 ∧ Holds M cp ∧ Holds M c4 ∧
          Holds M (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt) := by
        rw [holds_andT, holds_andT, holds_andT] at hc2''; exact hc2''
      have hevs : Smt.Rel M L (.list v.event) (Ty.up _ hd.events events) (Term.sel d 0 0 (Term.share rest)) := by
        show RelV _ _ _ _
        rw [sel_ctor 0 (hsh.trans hw)]; exact hev
      obtain ⟨sv, hS, -, hsw, hh⟩ := list_view hevs h11
      erw [Ty.up_list _ _ hd.event] at hh
      let s1 : State v := { s with fresh := s.fresh + 1 }
      obtain ⟨ps, happly, hperm, r1, r2, r3⟩ := events_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply happ
        hE hPE hopt { state := s1 } (hinv.congr rfl rfl rfl) hnow hS hsw hh hrec hms hnid h12 hc3 hpend h12' hcp
      rw [happly]
      let sA := (Step.reactAll T s1 events).1
      have hrfc : Smt.Rel M L v.records (Ty.up _ hd.records sA.records) rfc := (rel_ofTerm (need_ok.1 h13) _).2 r1
      have hens := hcc.ensures _ _ (rels2 hd.ctx hd.records hd.ensArgs hcx hrfc) ens c4 h14 hc4
      erw [Ty.up_fn _ Ty.rules _ hd.ensArgs rfl] at hens
      have hbe := rules_broken h15 _ hens
      simp only [Step.Acc.wrote]
      rw [hbe]
      cases hbe' : Step.broken ((v.commands.get i).ensures.fn (Step.ctx s s.records caller input, sA.records, ())) with
      | cons n ns => rfl
      | nil =>
        simp only
        have hallE : (allT (ensures.map (·.2))).denote M = .bool true := by
          rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil ensures).1 (hbe.trans hbe'))
        obtain ⟨hc5, hck⟩ : Holds M c5 ∧ Holds M ck := by
          have := hc5k; simp only [Holds, Term.denote, hallE, Val.toBool, ite_true] at this
          exact (holds_andT _ _).1 this
        have hiv := hinv' _ _ (rels1 hd.records (by simp [Ty.isData, Ty.isDatas, hd.records]) hrfc) invs c5 h16 hc5
        erw [Ty.up_fn _ Ty.rules _ (by simp [Ty.isData, Ty.isDatas, hd.records]) rfl] at hiv
        have hbi := rules_broken h17 _ hiv
        have hbs := instChecks_rel sA.records s.now hd.records r1 hnow v.machines _ _ r2
          (fun m hm => (hor m hm).2) h18 hck
        rw [finish_ok T s1 _ rfl]
        have hinvs : Step.invariants { sA with pending := sA.pending ++ ps, nextId := s1.nextId + ps.length } =
            brokenIn M invariants ++ checksBroken L T M v.machines checks := by
          simp only [Step.invariants]
          rw [hbi, hbs, show sA.now = s.now from Step.reactAll_now T s1 events]
          rfl
        rw [hinvs]
        cases brokenIn M invariants ++ checksBroken L T M v.machines checks with
        | cons n ns => rfl
        | nil =>
          dsimp only
          obtain ⟨ps', hp', hrelP⟩ := hperm
          have hpA : (Step.reactAll T s1 events).1.pending = s.pending := Step.reactAll_pending T s1 events
          refine ⟨rfl, ⟨ps, by simp, by rw [hpA], rfl, ps', by rw [hpA]; exact hp', hrelP⟩, r3, ?_, r1, r2, ?_⟩
          · rw [Step.reactAll_keeps T s1 events]
          · rw [sel_ctor 0 (hsh.trans hw)]; exact hev

end

section
variable {v : ServiceV}

/-- Whether what a command step does after `decide` fits, for what `decide` returned: on acceptance, the events'
applications in turn from `s` (`eventsFit`), the requests they start beside the pending ones in the pending table,
`ensures` at the records they leave and, where its rules hold, the service's and machines' invariants on the state
after. -/
def decidedFits (S : Ty → Nat) (T : List TypeDecl) (shs : List (PendingShape v.event)) (s : State v)
    (x : CommandV v.records v.event v.caller) (ctx : (Ty.ctx v.records x.input v.caller).den0) :
    (Ty.result (.list v.event) x.rejection).den0 → Prop
  | .inl (events, ()) =>
    let sA := Step.reactAll T s events
    eventsFit S T s events ∧ s.pending.length + (Step.reqsOf sA.2).length ≤ S (pendingTable shs) ∧
      x.ensures.appFits S (ctx, sA.1.records, ()) ∧
      (Step.broken (x.ensures.fn (ctx, sA.1.records, ())) = [] →
        v.invariants.appFits S (sA.1.records, ()) ∧ instChecksFit S sA.1.records s.now sA.1.machines)
  | .inr _ => True

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- The condition of a command's step is exact: for a listed caller, it holds exactly when `accepts` fits at the
input and, where its rules hold, `decide` fits at the context and what follows it fits (`decidedFits`). -/
theorem command_exact {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
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
    {o : CommandOut} {cond : Term}
    (henc : encodeCommand L T v shs dE dP dopt (v.commands.get i) cc apply inv ks records now fresh nextIdT pending sc si
      xs = .ok (o, cond)) :
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
  obtain ⟨⟨pT, cp⟩, h12', henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c5⟩, h16, henc⟩ := bind_ok.1 henc
  obtain ⟨invariants, h17, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, ck⟩, h18, henc⟩ := bind_ok.1 henc
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
      (andT c3 (andT cp (andT c4 (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt)))) tt)) tt) ↔
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
        (andT c3 (andT cp (andT c4 (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt)))) tt) ↔
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
        have hvm : ∀ m ∈ v.machines, m.Reach P := by
          intro m hm
          rw [← hsinv.machinesOf] at hm
          obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 hm
          exact hsinv.machines sm hsm
        have e3 : Holds M c3 ↔ eventsFit L.count T s1 events :=
          events_exact (fun m hm => (hor m hm).1) hd.records hd.event happ hca _ sv hS hsw events hh s1 hnow hrec hms h12
        have hrel : Holds M c3 → RelV L v.records (Ty.up _ hd.records sA.records) (oe.records.denote M) ∧
            MachinesRel M L T v.machines oe.tables sA.machines ∧
            NewsRel M L shs v.declared oe.news (Step.reqsOf (Step.reactAll T s1 events).2) s1.nextId := fun hc3 => by
          obtain ⟨r1, r2, -, r4, -, -⟩ := events_rel hP hvx hvm hshs hor hd.records hd.event hd.apply happ' hE hPE hopt _ sv
            hS hsw events hh s1 hnow hrec hms hnid rfl h12 hc3
          exact ⟨r1, r2, r4⟩
        have ecp : Holds M c3 → (Holds M cp ↔
            s1.pending.length + (Step.reqsOf (Step.reactAll T s1 events).2).length ≤ L.count (pendingTable shs)) := fun hc3 => by
          obtain ⟨-, -, sv', zs, hS', hw', hh', xs', hxp, hq⟩ := hrel hc3
          exact pending_exact hpend hS' hw' hh' hxp hq h12'
        have e45 : Holds M c3 → (Holds M c4 ↔ x.ensures.appFits L.count (ctx, sA.records, ())) ∧
            (Holds M c4 → (Holds M (.ite (allT (ensures.map (·.2))) (andT c5 ck) tt) ↔
              (Step.broken (x.ensures.fn (ctx, sA.records, ())) = [] →
                v.invariants.appFits L.count (sA.records, ()) ∧ instChecksFit L.count sA.records s1.now sA.machines))) := by
          intro hc3
          obtain ⟨hrf, hms', -⟩ := hrel hc3
          have hrfc : Smt.Rel M L v.records (Ty.up _ hd.records sA.records) rfc := (rel_ofTerm (need_ok.1 h13) _).2 hrf
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
          rw [holds_andT]
          refine and_congr (v.invariants.app_exact hinv hci (by simpa using ofTerm_notFn (need_ok.1 h13)) _ _
            (rels1 hd.records (by simp [Ty.isData, Ty.isDatas, hd.records]) hrfc) h16) ?_
          rw [show s1.now = sA.now from (Step.reactAll_now T s1 events).symm]
          exact instChecks_exact sA.records sA.now hd.records hrf (by rw [show sA.now = s.now from Step.reactAll_now T s1 events]; exact hnow) v.machines
            oe.tables sA.machines hms' h18
        rw [holds_andT, holds_andT, holds_andT]
        constructor
        · rintro ⟨hc3, hcp, hc4, hc5⟩
          exact ⟨e3.1 hc3, (ecp hc3).1 hcp, ((e45 hc3).1).1 hc4, ((e45 hc3).2 hc4).1 hc5⟩
        · rintro ⟨p3, pp, p4, p5⟩
          have hc3 := e3.2 p3
          have hc4 := ((e45 hc3).1).2 p4
          exact ⟨hc3, (ecp hc3).2 pp, hc4, ((e45 hc3).2 hc4).2 p5⟩
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
