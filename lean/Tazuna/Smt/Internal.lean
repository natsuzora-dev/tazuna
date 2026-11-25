import Tazuna.Smt.Finish
import Tazuna.Smt.CommandExact
import Tazuna.Semantics.Settle

/-! One internal step: an own command or query the step queued runs as `Step.runCommand` or `Step.runQuery` does. A
command's caller and `accepts` rules admit the input, `decide` accepts with events or rejects, the events run through
the events loop from the running records, tables, next id and queue place, `ensures` is checked on the records they
leave, and `on_answer` (the program's site at the values the effect captured) turns the answer into events that run
through the loop again. Requests the loops start are not written into the pending table here: the step writes every
internal step's requests once, at its end. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of an own command's internal step: whether the caller is listed and the `accepts` rules, whether
`decide` accepted, the `ensures` rules on the records its events leave, and what the events loop leaves after
`decide`'s events (nothing on a rejection) and after `on_answer`'s. -/
structure OwnCommandOut where
  callerOk : Term
  rules : List (Term × Term)
  ok : Term
  ensures : List (Term × Term)
  decided : EventsOut
  answered : EventsOut

/-- The terms of an own query's internal step: whether the caller is listed, the `accepts` rules, and what the
events loop leaves after `on_answer`'s events. -/
structure OwnQueryOut where
  callerOk : Term
  rules : List (Term × Term)
  answered : EventsOut

section
variable (L : Layout) (T : List TypeDecl)

/-- An own command's internal step terms and condition, from the codes of the command and of its `on_answer` site
over the captured values `σ`, the terms of the running state, the caller and the input, and the listed callers'
constants. The condition asks only for what the internal step computes. -/
def encodeOwnCommand (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (x : CommandV v.records v.event v.caller) (cc : CommandCode x) {Γ : List Ty}
    (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) (σ : Codes Γ)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (callers : List Term)
    (records now fresh n q caller input : Term) (xs : List Term) : Except Refusal (OwnCommandOut × Term) := do
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
  let ok := Term.is d 0 res
  let (dl, nl, dt) ← collD L (.list v.event) [v.event]
  let (o1, c3) ← encodeEvents L T v shs dE dP dopt apply now (gateSlots ok (slotsOf dl dt nl 1 (.sel d 0 0 res)))
    records xs n q
  let rfc ← need "records that have no term" (Code.ofTerm? v.records o1.records)
  let (ens, c4) ← cc.ensures (cx, rfc, ())
  let ensures ← ruleTerms L ens
  let nil ← adtCtor L 1 [] [[]] 0 []
  let okNil ← adtCtor L 2 [Ty.nil, x.rejection] [[Ty.nil], [x.rejection]] 0 [nil]
  let err ← adtCtor L 2 [Ty.nil, x.rejection] [[Ty.nil], [x.rejection]] 1 [.sel d 1 0 res]
  let ac ← need "an answer that has no term" (Code.ofTerm? (Ty.result Ty.nil x.rejection) (Term.share (.ite ok okNil err)))
  let (oa, c5) ← site.code L σ
  let (evs, c6) ← oa (ac, ())
  let evt ← need "events that have no term" (Code.term? _ evs)
  let (o2, c7) ← encodeEvents L T v shs dE dP dopt apply now (slotsOf dl dt nl 1 evt) o1.records o1.tables o1.nextId
    o1.queued
  let callerOk := anyT eqs
  pure (⟨callerOk, rules, ok, ensures, o1, o2⟩,
    .ite callerOk (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (andT c3 (andT (.ite ok c4 tt)
      (.ite (.and ok (.not (allT (ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))))) tt)) tt)


/-- An own query's internal step terms and condition, from the codes of the query and of its `on_answer` site over
the captured values `σ`, the terms of the running state, the caller and the input, and the listed callers'
constants: the caller and the `accepts` rules admit the input, `resolve` answers, and `on_answer`'s events run
through the events loop. -/
def encodeOwnQuery (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (x : QueryV v.records v.caller) (qc : QueryCode x) {Γ : List Ty} (site : Site Γ (Ty.fn [x.output] (.list v.event)))
    (σ : Codes Γ) (apply : Code (Ty.fn [v.records, v.event] v.records)) (callers : List Term)
    (records now fresh n q caller input : Term) (xs : List Term) : Except Refusal (OwnQueryOut × Term) := do
  let cc0 ← need "a caller that has no term" (Code.ofTerm? v.caller caller)
  let eqs ← callers.mapM fun k => do eqCode L v.caller cc0 (← need "a caller that has no term" (Code.ofTerm? v.caller k))
  let ic ← need "an input that has no term" (Code.ofTerm? x.input input)
  let (rs, c1) ← qc.accepts (ic, ())
  let rules ← ruleTerms L rs
  let ctx ← adtCtor L 5 [v.records, x.input, v.caller] [[v.records, x.input, v.caller, .int, .dsl .fresh []]] 0
    [records, input, caller, now, fresh]
  let cx ← need "a context that has no term" (Code.ofTerm? (Ty.ctx v.records x.input v.caller) (Term.share ctx))
  let (out, c2) ← qc.resolve (cx, ())
  let (oa, c3) ← site.code L σ
  let (evs, c4) ← oa (out, ())
  let evt ← need "events that have no term" (Code.term? _ evs)
  let (dl, nl, dt) ← collD L (.list v.event) [v.event]
  let (o, c5) ← encodeEvents L T v shs dE dP dopt apply now (slotsOf dl dt nl 1 evt) records xs n q
  let callerOk := anyT eqs
  pure (⟨callerOk, rules, o⟩,
    .ite callerOk (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (andT c3 (andT c4 c5))) tt)) tt)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- Slots gated by a false flag hold no event. -/
theorem gate_false_events {f : Term} (hf : f.denote M = .bool false) :
    (S : List Slot) → (∀ sl ∈ S, sl.2.length = 1) →
    ∃ sv, SlotsDen M (gateSlots f S) sv ∧ (∀ p ∈ sv, p.2.length = 1) ∧ Holds2 (EBag L v.event) [] sv
  | [], _ => ⟨[], trivial, by simp, by simp [Holds2, occupied, Forall2]⟩
  | (g, xs) :: S, hw => by
    obtain ⟨sv, hS, hsw, hh⟩ := gate_false_events hf S fun sl h => hw sl (by simp [h])
    refine ⟨(false, Term.denotes M xs) :: sv, ⟨by simp [Term.denote, hf, Val.toBool], rfl, hS⟩, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · simpa [denotes_length] using hw (g, xs) (by simp)
      · exact hsw p hp
    · simpa [Holds2, occupied] using hh

theorem slotsOf_width (d dt n w : Nat) (b : Term) : ∀ sl ∈ slotsOf d dt n w b, sl.2.length = w := by
  intro sl hsl
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hsl
  simp

/-- The news slots name pending requests for the requests they hold: externals list each. -/
theorem newsRel_writes {shs : List (PendingShape v.event)} {ds : List (String × DeclaredV)} {news : List Slot}
    {effs : List (Sender × EffectV v.event)} {n0 : Nat} (h : NewsRel M L shs ds news effs n0) :
    ∃ ps, Forall2 (Step.Writes ds) (effs.zipIdx n0) ps := by
  obtain ⟨sv, zs, -, -, -, xs, hp, hq⟩ := h
  have h1 : Forall2 (Step.Writes ds) xs (zs.map fun z => pendingOf shs z.1 z.2) :=
    forall2_map_right _ (fun _ _ hw => hw.2) hq
  obtain ⟨ps, -, h2⟩ := forall2_perm hp (forall2_flip h1)
  exact ⟨ps, forall2_flip h2⟩

/-- The events loop over a list's slots from a step in progress: what `events_rel` says of the terms, and, for
whichever pending requests the step writes for the requests the events start, `applyEvents`' result. -/
theorem loop_apply {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hap : (Ty.fn [v.records, v.event] v.records).isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} (happ : Smt.Rel M L _ (Ty.up _ hap v.apply.fn) apply)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    (hvm : ∀ m ∈ v.machines, m.Reach P) (a : Step.Acc v) {now : Term} (hnow : now.denote M = .int a.state.now)
    {S : List Slot} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = 1)
    {evs : List v.event.den0} (hev : Holds2 (EBag L v.event) (evs.map (Ty.up _ hed)) sv)
    {records : Term} (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    {xs : List Term} (hms : MachinesRel M L T v.machines xs a.state.machines)
    {n q : Term} {q0 : Nat} (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    {o : EventsOut} {c : Term} (henc : encodeEvents L T v shs dE dP dopt apply now S records xs n q = .ok (o, c))
    (hc : Holds M c) :
    let effs := (Step.reactAll T a.state evs).2
    RelV L v.records (Ty.up _ hrd (Step.reactAll T a.state evs).1.records) (o.records.denote M) ∧
      MachinesRel M L T v.machines o.tables (Step.reactAll T a.state evs).1.machines ∧
      o.nextId.denote M = .int ((a.state.nextId + (Step.reqsOf effs).length : Nat) : Int) ∧
      NewsRel M L shs v.declared o.news (Step.reqsOf effs) a.state.nextId ∧
      o.queued.denote M = .int ((q0 + (Step.queuedOf effs).length : Nat) : Int) ∧
      OwnRel M L o.owns (Step.queuedOf effs) q0 ∧
      ∀ ps, Forall2 (Step.Writes v.declared) ((Step.reqsOf effs).zipIdx a.state.nextId) ps →
        Step.applyEvents T a evs = .ok (({ a with state := (Step.reactAll T a.state evs).1, events := a.events ++ evs }.wrote
          ps (a.state.nextId + (Step.reqsOf effs).length)).queued (Step.queuedOf effs)) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := events_rel hP hvx hvm hshs hor hrd hed hap happ hE hPE hopt S sv hS hw evs hev
    a.state hnow hrec hms hn hq henc hc
  exact ⟨r1, r2, r3, r4, r5, r6, fun ps hps => Step.applyEvents_requests T evs a ps hps⟩


theorem up_nil (h : Ty.nil.isData = true) :
    Ty.up Ty.nil h (.inl () : Ty.nil.den0) = Alts.inj (vs := [[]]) ⟨0, by simp⟩ () :=
  (Ty.up_inl 1 [] [] [] h rfl _).trans rfl

theorem up_okNil {j : Ty} (h : (Ty.result Ty.nil j).isData = true) :
    Ty.up _ h (Step.okNil : (Ty.result Ty.nil j).den0) =
      Alts.inj (vs := [[Ty.nil], [j]]) ⟨0, by simp⟩ (Ty.up Ty.nil rfl (.inl ()), ()) := by
  refine (Ty.up_inl 2 [Ty.nil, j] [Ty.nil] [[j]] h rfl _).trans ?_
  show Sum.inl _ = Sum.inl _
  exact congrArg _ (Ty.up_tuple _ _ _ rfl rfl _)

theorem up_err {j : Ty} (h : (Ty.result Ty.nil j).isData = true) (hj : j.isData = true) (y : j.den0) :
    Ty.up _ h (.inr (.inl (y, ())) : (Ty.result Ty.nil j).den0) =
      Alts.inj (vs := [[Ty.nil], [j]]) ⟨1, by simp⟩ (Ty.up j hj y, ()) := by
  have hj' : (Ty.adt 2 [Ty.nil, j] [[j]]).isData = true := by simp [Ty.isData, Ty.isDatas, Ty.isDatass, hj]
  refine (Ty.up_inr 2 [Ty.nil, j] [Ty.nil] [[j]] h hj' _).trans ?_
  show Sum.inr _ = Sum.inr _
  refine congrArg Sum.inr ((Ty.up_inl 2 [Ty.nil, j] [j] [] hj' (by simp [Ty.isData, Ty.isDatas, hj]) _).trans ?_)
  show Sum.inl _ = Sum.inl _
  exact congrArg _ (Ty.up_tuple _ _ _ hj rfl _)

/-- An internal step that ran to its end from `a`: the records and machines that `o` denotes, the fresh counter
`fresh`, the events `evs` applied, the requests `effs` started at wire ids from `a`'s next id (for whichever pending
requests `ps` the step writes for them, as the news slots hold), and the own commands and queries `os` queued at
places from `q0`, as the own slots hold. -/
def InternalDone (M : Model) (L : Layout) (T : List TypeDecl) (hrd : v.records.isData = true)
    (shs : List (PendingShape v.event)) (a : Step.Acc v) (fresh : Nat) (o : EventsOut) (news owns : List Slot)
    (q0 : Nat) (r : Except Fault (Step.Acc v)) : Prop :=
  ∃ (recs : v.records.den0) (ms : List (Step.MachineState v.records v.event)) (evs : List v.event.den0)
    (effs : List (Sender × EffectV v.event)) (os : List (EffectV v.event)),
    (∀ ps, Forall2 (Step.Writes v.declared) (effs.zipIdx a.state.nextId) ps →
      r = .ok { state := { a.state with records := recs, machines := ms, fresh := fresh,
                                         pending := a.state.pending ++ ps, nextId := a.state.nextId + ps.length },
                events := a.events ++ evs, out := a.out ++ ps.map Step.Pending.line, own := a.own ++ os }) ∧
    RelV L v.records (Ty.up _ hrd recs) (o.records.denote M) ∧ MachinesRel M L T v.machines o.tables ms ∧
    o.nextId.denote M = .int ((a.state.nextId + effs.length : Nat) : Int) ∧
    NewsRel M L shs v.declared news effs a.state.nextId ∧
    o.queued.denote M = .int ((q0 + os.length : Nat) : Int) ∧ OwnRel M L owns os q0

/-- T2 for an own command's internal step: wherever the condition holds, an unlisted caller or a broken `accepts`
rule is `Fault.invalidEffect`, a broken `ensures` rule after an acceptance is `Fault.ensures`, and otherwise the
internal step runs to its end with what the terms denote (`InternalDone`), the fresh counter advanced. -/
theorem ownCommand_rel {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (a : Step.Acc v) (hinv : Step.Inv P a.state)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (hd : CommandData x) {cc : CommandCode x} {cx : Term} (hcc : CommandCode.of L x = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ)
    {ks : List Term} (hks : callerTerms L hd.caller x.callers = some ks)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q sc si : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hd.records a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ hd.input input) (si.denote M))
    {o : OwnCommandOut} {cond : Term}
    (henc : encodeOwnCommand L T v shs dE dP dopt x cc site σ apply ks records now fresh n q sc si xs = .ok (o, cond))
    (hc : Holds M cond) :
    let r := Step.runCommand T a x caller input (site.fn env)
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = .error (.invalidEffect x.name (n :: ns))
      | [] =>
        match (o.ok.denote M).toBool, brokenIn M o.ensures with
        | true, n :: _ => r = .error (.ensures n)
        | _, _ => InternalDone M L T hd.records shs a (a.state.fresh + 1) o.answered
            (o.decided.news ++ o.answered.news) (o.decided.owns ++ o.answered.owns) q0 r
    else r = .error (.invalidEffect x.name ["callers"]) := by
  have hcc := CommandCode.rel_of hd hcc hccx
  have happ := v.apply.code_fn hd.apply happ hca
  intro r
  obtain ⟨cc0, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cxt, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨res, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨rest, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨d, dn⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c3⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  obtain ⟨nil, h16, henc⟩ := bind_ok.1 henc
  obtain ⟨okNil, h17, henc⟩ := bind_ok.1 henc
  obtain ⟨err, h18, henc⟩ := bind_ok.1 henc
  obtain ⟨ac, h19, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c5⟩, h20, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c6⟩, h21, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h22, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o2, c7⟩, h23, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvm : ∀ m ∈ v.machines, m.Reach P := by
    intro m hm
    rw [← hinv.machinesOf] at hm
    obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 hm
    exact hinv.machines sm hsm
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 x.callers ks hks eqs h2
  simp only [r, Step.runCommand, Step.admit]
  cases hin : x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
  case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
  simp only [hok, hin, Val.toBool, ite_true]
  have hc' : Holds M (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (andT c3 (andT (.ite (Term.is d 0 (Term.share rest)) c4 tt)
      (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))))) tt)) := by
    simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
  rw [holds_andT] at hc'
  have hic : Smt.Rel M L _ (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  have hacc := hcc.accepts _ (ic, ()) (rels1 hd.input hd.args hic) rs c1 h4 hc'.1
  erw [Ty.up_fn _ Ty.rules _ hd.args rfl] at hacc
  have hbroken := rules_broken h5 _ hacc
  rw [hbroken]
  cases hb : Step.broken (x.accepts.fn (input, ())) with
  | cons n ns => rfl
  | nil =>
  simp only
  have hallT : (allT (rules.map (·.2))).denote M = .bool true := by
    rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil rules).1 (hbroken.trans hb))
  have hc2' : Holds M (andT c2 (andT c3 (andT (.ite (Term.is d 0 (Term.share rest)) c4 tt)
      (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))))) := by
    have := hc'.2; simp only [Holds, Term.denote, hallT, Val.toBool, ite_true] at this; exact this
  obtain ⟨hc2, hc3, hc4, hctail⟩ : Holds M c2 ∧ Holds M c3 ∧ Holds M (.ite (Term.is d 0 (Term.share rest)) c4 tt) ∧
      Holds M (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt
        (andT c5 (andT c6 c7))) := by
    rw [holds_andT, holds_andT, holds_andT] at hc2'; exact hc2'
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[v.records, x.input, v.caller, .int, .dsl .fresh []]])
    ⟨0, by simp⟩ _ _ h6
    (Ty.up _ hd.records a.state.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, a.state.now, a.state.fresh, ())
    ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
  rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx (Step.ctx a.state a.state.records caller input)) cxt :=
    (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctx)
  have hres := hcc.decide _ (cxt, ()) (rels1 hd.ctx hd.ctxArgs hcx) res c2 h8 hc2
  erw [Ty.up_fn _ _ _ hd.ctxArgs hd.result] at hres
  have hres' := (rel_term (need_ok.1 h9) _).1 hres
  have hfd := need_ok.1 h10
  have hsh : (Term.share rest).denote M = rest.denote M := Term.denote_share M rest
  have hdata2 : (Ty.adt 2 [.list v.event, x.rejection] [[x.rejection]]).isData = true := by
    simp only [Ty.isData, Ty.isDatas, Ty.isDatass, hd.rejection, Bool.and_true]
  have hle : (Ty.list v.event).isData = true := hd.events
  have hrn : (Ty.result Ty.nil x.rejection).isData = true := by
    simp [Ty.result, Ty.nil, Ty.isData, Ty.isDatas, Ty.isDatass, hd.rejection]
  have hta : (Ty.tuple [Ty.result Ty.nil x.rejection]).isData = true := by simp [Ty.isData, Ty.isDatas, hrn]
  have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs) site.body
    σ _ hσ oa c5
  have hoa' : ∀ hc5 : Holds M c5, Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := fun hc5 => by
    rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa h20 hc5
  let a1 : Step.Acc v := { a with state := { a.state with fresh := a.state.fresh + 1 } }
  cases hdec : x.decide.fn (Step.ctx a.state a.state.records caller input, ()) with
  | inr qq =>
    match qq, hdec with
    | .inr e, _ => exact e.elim
    | .inl (j, ()), hdec =>
    rw [hdec] at hres'
    erw [Ty.up_inr 2 _ _ _ hd.result hdata2, Ty.up_inl 2 _ _ _ hdata2 (by simp only [Ty.isData, Ty.isDatas, hd.rejection, Bool.and_true]),
      Ty.up_tuple _ _ _ hd.rejection rfl] at hres'
    obtain ⟨d', n', hf', vals, hw, rv, rest', rfl, hrv, rfl⟩ := hres'
    obtain rfl := find_det hfd hf'
    have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool false := by simp [Term.denote, hsh, hw]
    have hite : ∀ t u : Term, (Term.ite (Term.is d 0 (Term.share rest)) t u).denote M = u.denote M := fun t u => by
      show (if (Term.denote M (Term.is d 0 (Term.share rest))).toBool then _ else _) = _
      rw [hok']; rfl
    have hand : ∀ t : Term, (Term.and (Term.is d 0 (Term.share rest)) t).denote M = .bool false := fun t => by
      show Val.bool ((Term.denote M (Term.is d 0 (Term.share rest))).toBool && _) = _
      rw [hok']; rfl
    rw [hok']
    dsimp only [Val.toBool]
    have hct : Holds M (andT c5 (andT c6 c7)) := by
      have := hctail; unfold Holds at this ⊢
      rw [show Term.denote M (Term.ite (Term.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt
        (andT c5 (andT c6 c7))) = Term.denote M (andT c5 (andT c6 c7)) from by
          show (if (Term.denote M (Term.and _ _)).toBool then _ else _) = _
          rw [hand]; rfl] at this
      exact this
    obtain ⟨hc5, hc6, hc7⟩ : Holds M c5 ∧ Holds M c6 ∧ Holds M c7 := by
      rw [holds_andT, holds_andT] at hct; exact hct
    obtain ⟨sv1, hS1, hw1, hh1⟩ := gate_false_events (L := L) (v := v) hok' _
      (slotsOf_width dl dt nl 1 (.sel d 0 0 (Term.share rest)))
    obtain ⟨p1, p2, p3, p4, p5, p6, -⟩ := loop_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply happ hE hPE
      hopt hvm a1 hnow hS1 hw1 (evs := []) (by simpa using hh1) hrec hms hn hq h12 hc3
    simp only [Step.reactAll, Step.reqsOf, Step.queuedOf, List.filter_nil, List.map_nil, List.length_nil,
      Nat.add_zero] at p1 p2 p3 p4 p5 p6
    have hrj : RelV L x.rejection (Ty.up _ hd.rejection j) ((Term.sel d 1 0 (Term.share rest)).denote M) := by
      rw [sel_ctor 0 (hsh.trans hw)]; exact hrv
    have herr := adtCtor_rel (L := L) (M := M) (vs := [[Ty.nil], [x.rejection]]) ⟨1, by simp⟩ _ _ h18
      (Ty.up _ hd.rejection j, ()) ⟨_, _, rfl, hrj, rfl⟩
    rw [← up_err hrn hd.rejection j] at herr
    have hac : Smt.Rel M L _ (Ty.up _ hrn (.inr (.inl (j, ())))) ac :=
      (rel_ofTerm (need_ok.1 h19) _).2 (by rw [Term.denote_share, hite]; exact herr)
    have hevs2 := hoa' hc5 _ (ac, ()) (rels1 hrn hta hac) evs c6 h21 hc6
    erw [Ty.up_fn _ _ _ hta hle] at hevs2
    have hevt := (rel_term (need_ok.1 h22) _).1 hevs2
    obtain ⟨sv2, hS2, -, hsw2, hh2⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h11
    erw [Ty.up_list _ _ hd.event] at hh2
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := loop_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply happ hE hPE
      hopt hvm a1 hnow hS2 hsw2 hh2 p1 p2 p3 p5 h23 hc7
    have hkeep := Step.reactAll_keeps T a1.state
      ((site.fn env).fn ((.inr (.inl (j, ())) : (Ty.result Ty.nil x.rejection).den0), ()))
    refine ⟨_, _, (site.fn env).fn ((.inr (.inl (j, ())) : (Ty.result Ty.nil x.rejection).den0), ()), _, _, ?_, q1, q2,
      q3, ?_, q5, ?_⟩
    · intro ps hps
      rw [q7 ps hps, forall2_zipIdx_length _ _ hps, hkeep]
      simp [a1, Step.Acc.wrote, Step.Acc.queued]
    · simpa using newsRel_append p4 q4
    · simpa using ownRel_append p6 q6
  | inl pr =>
    obtain ⟨events, ⟨⟩⟩ := pr
    rw [hdec] at hres'
    erw [Ty.up_inl 2 _ _ _ hd.result (by simp only [Ty.isData, Ty.isDatas, hd.event, Bool.and_true]),
      Ty.up_tuple _ _ _ hd.events rfl] at hres'
    obtain ⟨d', n', hf', vals, hw, ev, rest', rfl, hev, rfl⟩ := hres'
    obtain rfl := find_det hfd hf'
    have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool true := by simp [Term.denote, hsh, hw]
    have hite : ∀ t u : Term, (Term.ite (Term.is d 0 (Term.share rest)) t u).denote M = t.denote M := fun t u => by
      show (if (Term.denote M (Term.is d 0 (Term.share rest))).toBool then _ else _) = _
      rw [hok']; rfl
    rw [hok']
    dsimp only [Val.toBool]
    have hc4' : Holds M c4 := by have := hc4; unfold Holds at this ⊢; rw [hite] at this; exact this
    have hevs : Smt.Rel M L (.list v.event) (Ty.up _ hd.events events) (Term.sel d 0 0 (Term.share rest)) := by
      show RelV _ _ _ _
      rw [sel_ctor 0 (hsh.trans hw)]; exact hev
    obtain ⟨sv, hS, -, hsw, hh⟩ := list_view hevs h11
    erw [Ty.up_list _ _ hd.event] at hh
    obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := loop_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply happ hE hPE
      hopt hvm a1 hnow (gate_true hok' hS) hsw hh hrec hms hn hq h12 hc3
    let sA := (Step.reactAll T a1.state events).1
    have hpA : sA.pending = a.state.pending := Step.reactAll_pending T a1.state events
    have hnA : sA.now = a.state.now := Step.reactAll_now T a1.state events
    have hrfc : Smt.Rel M L v.records (Ty.up _ hd.records sA.records) rfc := (rel_ofTerm (need_ok.1 h13) _).2 p1
    have hens := hcc.ensures _ _ (rels2 hd.ctx hd.records hd.ensArgs hcx hrfc) ens c4 h14 hc4'
    erw [Ty.up_fn _ Ty.rules _ hd.ensArgs rfl] at hens
    have hbe := rules_broken h15 _ hens
    rw [hbe]
    cases hbe' : Step.broken (x.ensures.fn (Step.ctx a.state a.state.records caller input, sA.records, ())) with
    | cons n ns =>
      obtain ⟨ps1, hps1⟩ := newsRel_writes p4
      erw [p7 ps1 hps1]
      simp only [Step.Acc.wrote, Step.Acc.queued, bind, Except.bind]
      erw [hbe']
    | nil =>
    have hallE : (allT (ensures.map (·.2))).denote M = .bool true := by
      rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil ensures).1 (hbe.trans hbe'))
    have hct : Holds M (andT c5 (andT c6 c7)) := by
      have := hctail; unfold Holds at this ⊢
      rw [show Term.denote M (Term.ite (Term.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt
        (andT c5 (andT c6 c7))) = Term.denote M (andT c5 (andT c6 c7)) from by
          show (if (Val.bool ((Term.denote M (Term.is d 0 (Term.share rest))).toBool &&
            (Term.denote M (Term.not (allT (ensures.map (·.2))))).toBool)).toBool then _ else _) = _
          rw [hok']
          show (if (Val.bool (true && (Val.bool (!(Term.denote M (allT (ensures.map (·.2)))).toBool)).toBool)).toBool
            then _ else _) = _
          rw [hallE]; rfl] at this
      exact this
    obtain ⟨hc5, hc6, hc7⟩ : Holds M c5 ∧ Holds M c6 ∧ Holds M c7 := by
      rw [holds_andT, holds_andT] at hct; exact hct
    have hnil := adtCtor_rel (L := L) (M := M) (vs := [[]]) ⟨0, by simp⟩ _ _ h16 () (by show RelVs L [] () []; trivial)
    rw [← up_nil rfl] at hnil
    have hokn := adtCtor_rel (L := L) (M := M) (vs := [[Ty.nil], [x.rejection]]) ⟨0, by simp⟩ _ _ h17
      (Ty.up Ty.nil rfl (.inl ()), ()) ⟨_, _, rfl, hnil, rfl⟩
    rw [← up_okNil hrn] at hokn
    have hac : Smt.Rel M L _ (Ty.up _ hrn Step.okNil) ac :=
      (rel_ofTerm (need_ok.1 h19) _).2 (by rw [Term.denote_share, hite]; exact hokn)
    have hevs2 := hoa' hc5 _ (ac, ()) (rels1 hrn hta hac) evs c6 h21 hc6
    erw [Ty.up_fn _ _ _ hta hle] at hevs2
    have hevt := (rel_term (need_ok.1 h22) _).1 hevs2
    obtain ⟨sv2, hS2, -, hsw2, hh2⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h11
    erw [Ty.up_list _ _ hd.event] at hh2
    let evs2 : List v.event.den0 := (site.fn env).fn ⟨Step.okNil, ()⟩
    change Holds2 (EBag L v.event) (evs2.map (Ty.up _ hd.event)) sv2 at hh2
    let reqs1 := Step.reqsOf (Step.reactAll T a1.state events).2
    let N1 := a.state.nextId + reqs1.length
    let a2 : Step.Acc v := { state := { sA with pending := sA.pending, nextId := N1 } }
    obtain ⟨q1, q2, q3, q4, q5, q6, -⟩ := loop_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply happ hE hPE
      hopt hvm a2 (by rw [← hnA] at hnow; exact hnow) hS2 hsw2 hh2 p1 p2 p3 p5 h23 hc7
    dsimp only [a2] at q1 q2 q3 q4 q5 q6
    erw [Step.reactAll_with T sA sA.pending N1] at q1 q2 q3 q4 q5 q6
    refine ⟨(Step.reactAll T sA evs2).1.records, (Step.reactAll T sA evs2).1.machines,
      List.append events evs2,
      reqs1 ++ Step.reqsOf (Step.reactAll T sA evs2).2,
      Step.queuedOf (Step.reactAll T a1.state events).2 ++ Step.queuedOf (Step.reactAll T sA evs2).2,
      fun ps hps => ?_, q1, q2, ?_, newsRel_append p4 q4, ?_, ownRel_append p6 q6⟩
    · rw [List.zipIdx_append] at hps
      obtain ⟨ps1, ps2, rfl, hps1, hps2⟩ := forall2_split _ _ hps
      have hl1 := forall2_zipIdx_length _ _ hps1
      let a2' : Step.Acc v := ((({ a1 with state := sA, events := @HAppend.hAppend (List v.event.den0) (List v.event.den0) _ _ a1.events events } : Step.Acc v).wrote ps1
        (a1.state.nextId + reqs1.length)).queued (Step.queuedOf (Step.reactAll T a1.state events).2))
      obtain ⟨-, -, -, -, -, -, q7⟩ := loop_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply happ hE hPE
        hopt hvm a2' (by rw [← hnA] at hnow; exact hnow) hS2 hsw2 hh2 p1 p2 p3 p5 h23 hc7
      have hs2 : a2'.state = { sA with pending := a.state.pending ++ ps1, nextId := N1 } := by
        simp [a2', Step.Acc.wrote, Step.Acc.queued, hpA, N1, a1]
      erw [hs2, Step.reactAll_with T sA _ N1] at q7
      erw [p7 ps1 hps1]
      simp only [bind, Except.bind]
      erw [hbe']
      dsimp only
      rw [show (({ a1 with state := sA, events := @HAppend.hAppend (List v.event.den0) (List v.event.den0) _ _ a1.events events } : Step.Acc v).wrote ps1
        (a1.state.nextId + reqs1.length)).queued (Step.queuedOf (Step.reactAll T a1.state events).2) = a2' from rfl]
      erw [q7 ps2 (by simpa [hl1, N1] using hps2)]
      have hk2 := Step.reactAll_keeps T sA evs2
      have hl2 := forall2_zipIdx_length _ _ hps2
      simp only [a2', a1, Step.Acc.wrote, Step.Acc.queued, List.append_assoc, List.length_append, List.map_append,
        Except.ok.injEq]
      have hfA : sA.fresh = a.state.fresh + 1 := Step.reactAll_fresh T a1.state events
      simp only [Step.reactAll_now, Step.reactAll_fresh, hnA, hfA, hl1, hl2, N1, reqs1,
        Nat.add_assoc]
      congr 1
      exact List.append_assoc _ _ _
    · rw [q3]; simp only [N1, List.length_append, Nat.add_assoc]
    · rw [q5]; simp only [List.length_append, Nat.add_assoc]


/-- Whether what an own command's internal step does after `decide` fits, for what `decide` returned: on acceptance,
the events' applications in turn from `s` and `ensures` at the records they leave, then, unless `ensures` broke a rule,
the `on_answer` source, its application to `Ok(Nil)` and the answer's events in turn; on a rejection, the `on_answer`
source, its application to the rejection and the answer's events in turn. -/
def ownDecidedFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : CommandV v.records v.event v.caller)
    (ctx : (Ty.ctx v.records x.input v.caller).den0) (oa : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) :
    (Ty.result (.list v.event) x.rejection).den0 → Prop
  | .inl (events, ()) =>
    let sA := (Step.reactAll T s events).1
    eventsFit S T s events ∧ x.ensures.appFits S (ctx, sA.records, ()) ∧
      (Step.broken (x.ensures.fn (ctx, sA.records, ())) = [] →
        (oa.fits S).1 ∧ oa.appFits S ⟨Step.okNil, ()⟩ ∧ eventsFit S T sA (oa.fn ⟨Step.okNil, ()⟩))
  | .inr (.inl (j, ())) =>
    (oa.fits S).1 ∧ oa.appFits S ⟨.inr (.inl (j, ())), ()⟩ ∧ eventsFit S T s (oa.fn ⟨.inr (.inl (j, ())), ()⟩)
  | .inr (.inr e) => e.elim

/-- The condition of an own command's internal step is exact: for a listed caller, it holds exactly when `accepts`
fits at the input and, where its rules hold, `decide` fits at the context and what follows it fits
(`ownDecidedFits`). -/
theorem ownCommand_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true) (a : Step.Acc v)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (hd : CommandData x) {cc : CommandCode x} {cx : Term} (hcc : CommandCode.of L x = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ) (hΓf : ∀ t ∈ Γ, t.isFn = false)
    {ks : List Term} (hks : callerTerms L hd.caller x.callers = some ks)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q sc si : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hd.records a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ hd.input input) (si.denote M))
    {o : OwnCommandOut} {cond : Term}
    (henc : encodeOwnCommand L T v shs dE dP dopt x cc site σ apply ks records now fresh n q sc si xs = .ok (o, cond)) :
    let ctx := Step.ctx a.state a.state.records caller input
    Holds M cond ↔ (x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
      x.accepts.appFits L.count (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits L.count (ctx, ()) ∧
          ownDecidedFits L.count T { a.state with fresh := a.state.fresh + 1 } x ctx (site.fn env)
            (x.decide.fn (ctx, ())))) := by
  intro ctx
  have hcc' := CommandCode.rel_of hd hcc hccx
  obtain ⟨⟨_, c1'⟩, g1, hcc0⟩ := bind_ok.1 hcc
  obtain ⟨⟨_, c2'⟩, g2, hcc0⟩ := bind_ok.1 hcc0
  obtain ⟨⟨_, c3'⟩, g3, hcc0⟩ := bind_ok.1 hcc0
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
  obtain ⟨cxt, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨res, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨rest, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨d, dn⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c3⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  obtain ⟨nil, h16, henc⟩ := bind_ok.1 henc
  obtain ⟨okNil, h17, henc⟩ := bind_ok.1 henc
  obtain ⟨err, h18, henc⟩ := bind_ok.1 henc
  obtain ⟨ac, h19, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c5⟩, h20, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c6⟩, h21, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h22, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o2, c7⟩, h23, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 x.callers ks hks eqs h2
  rw [holds_ite_tt (by rw [hok])]
  refine imp_congr_right fun _ => ?_
  rw [holds_andT]
  have hic : Smt.Rel M L _ (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  have hargs := rels1 hd.input hd.args hic
  have e1 : Holds M c1 ↔ x.accepts.appFits L.count (input, ()) :=
    x.accepts.app_exact g1 hca1 (by simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h3)) _ _ hargs h4
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[v.records, x.input, v.caller, .int, .dsl .fresh []]])
    ⟨0, by simp⟩ _ _ h6
    (Ty.up _ hd.records a.state.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, a.state.now, a.state.fresh, ())
    ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
  rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx ctx) cxt :=
    (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctx)
  have hargs' := rels1 hd.ctx hd.ctxArgs hcx
  have e2 : Holds M c2 ↔ x.decide.appFits L.count (ctx, ()) :=
    x.decide.app_exact g2 hca2 (by simp [Ty.ctx, Ty.isFn]) _ _ hargs' h8
  have hrn : (Ty.result Ty.nil x.rejection).isData = true := by
    simp [Ty.result, Ty.nil, Ty.isData, Ty.isDatas, Ty.isDatass, hd.rejection]
  have hta : (Ty.tuple [Ty.result Ty.nil x.rejection]).isData = true := by simp [Ty.isData, Ty.isDatas, hrn]
  have x1 := encode_exact site.defs site.defs.eval (site.defs.encode L) (site.defs.fits L.count)
    (Defs.encode_agrees M L site.defs) (Defs.encode_exact M L site.defs) site.body σ _ (FTs.dflt _) hσ
    (frels_of_notFn hΓf _ _ _) oa c5 h20
  have hfit : (site.fn env).fits L.count = Expr.fits L.count site.defs site.defs.eval (site.defs.fits L.count) site.body
      (Ty.up _ site.hΓ env) (FTs.dflt _) := by
    simp only [Fun.fits, Site.fn]
  have e5 : Holds M c5 ↔ ((site.fn env).fits L.count).1 := by rw [hfit]; exact x1.1
  have e6 : ∀ (ans : (Ty.result Ty.nil x.rejection).den0), Smt.Rel M L _ (Ty.up _ hrn ans) ac → Holds M c5 →
      (Holds M c6 ↔ (site.fn env).appFits L.count ⟨ans, ()⟩) := fun ans hac hc5 => by
    have := (x1.2 hc5 _ (FTs.dflt _) (ac, ()) (rels1 hrn hta hac)
      (frels_of_notFn (by simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h19)) _ _ _)
      evs c6 h21).1
    rw [this]; unfold Fun.appFits; rw [hfit]
  have hle : (Ty.list v.event).isData = true := hd.events
  let s1 : State v := { a.state with fresh := a.state.fresh + 1 }
  -- The answer's part: `on_answer`'s source, its application to `ans`, and the events loop from `s`.
  have etail : ∀ (s : State v) (ans : (Ty.result Ty.nil x.rejection).den0), Smt.Rel M L _ (Ty.up _ hrn ans) ac →
      now.denote M = .int s.now → RelV L v.records (Ty.up _ hd.records s.records) (o1.records.denote M) →
      MachinesRel M L T v.machines o1.tables s.machines →
      (Holds M (andT c5 (andT c6 c7)) ↔ ((site.fn env).fits L.count).1 ∧ (site.fn env).appFits L.count ⟨ans, ()⟩ ∧
        eventsFit L.count T s ((site.fn env).fn ⟨ans, ()⟩)) := fun s ans hac hnw hr hm => by
    rw [holds_andT, holds_andT]
    have e7 : Holds M c5 → Holds M c6 → (Holds M c7 ↔ eventsFit L.count T s ((site.fn env).fn ⟨ans, ()⟩)) :=
      fun hc5 hc6 => by
        have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs)
          site.body σ _ hσ oa c5 h20 hc5
        have hoa' : Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := by
          rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa
        have hevs2 := hoa' _ (ac, ()) (rels1 hrn hta hac) evs c6 h21 hc6
        erw [Ty.up_fn _ _ _ hta hle] at hevs2
        have hevt := (rel_term (need_ok.1 h22) _).1 hevs2
        obtain ⟨sv2, hS2, -, hsw2, hh2⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h11
        erw [Ty.up_list _ _ hd.event] at hh2
        exact events_exact (fun m hm => (hor m hm).1) hd.records hd.event happ hca _ sv2 hS2 hsw2 _ hh2 s hnw hr hm h23
    constructor
    · rintro ⟨hc5, hc6, hc7⟩
      exact ⟨e5.1 hc5, (e6 ans hac hc5).1 hc6, (e7 hc5 hc6).1 hc7⟩
    · rintro ⟨p5, p6, p7⟩
      have hc5 := e5.2 p5
      have hc6 := (e6 ans hac hc5).2 p6
      exact ⟨hc5, hc6, (e7 hc5 hc6).2 p7⟩
  have hrest : Holds M c1 → (Holds M (.ite (allT (rules.map (·.2))) (andT c2 (andT c3 (andT
      (.ite (Term.is d 0 (Term.share rest)) c4 tt)
      (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))))) tt) ↔
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits L.count (ctx, ()) ∧ ownDecidedFits L.count T s1 x ctx (site.fn env) (x.decide.fn (ctx, ())))) :=
      fun hc1 => by
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
    have hdec : Holds M c2 → (Holds M (andT c3 (andT (.ite (Term.is d 0 (Term.share rest)) c4 tt)
        (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt (andT c5 (andT c6 c7))))) ↔
        ownDecidedFits L.count T s1 x ctx (site.fn env) (x.decide.fn (ctx, ()))) := fun hc2 => by
      have hres := hcc'.decide _ (cxt, ()) hargs' res c2 h8 hc2
      erw [Ty.up_fn _ _ _ hd.ctxArgs hd.result] at hres
      have hres' := (rel_term (need_ok.1 h9) _).1 hres
      have hfd := need_ok.1 h10
      have hsh : (Term.share rest).denote M = rest.denote M := Term.denote_share M rest
      have hdata2 : (Ty.adt 2 [.list v.event, x.rejection] [[x.rejection]]).isData = true := by
        simp only [Ty.isData, Ty.isDatas, Ty.isDatass, hd.rejection, Bool.and_true]
      rw [holds_andT, holds_andT]
      cases hdv : x.decide.fn (Step.ctx a.state a.state.records caller input, ()) with
      | inr qq =>
        match qq, hdv with
        | .inr e, _ => exact e.elim
        | .inl (j, ()), hdv =>
        rw [hdv] at hres'
        erw [Ty.up_inr 2 _ _ _ hd.result hdata2, Ty.up_inl 2 _ _ _ hdata2
          (by simp only [Ty.isData, Ty.isDatas, hd.rejection, Bool.and_true]),
          Ty.up_tuple _ _ _ hd.rejection rfl] at hres'
        obtain ⟨d', n', hf', vals, hw, rv, rest', rfl, hrv, rfl⟩ := hres'
        obtain rfl := find_det hfd hf'
        have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool false := by simp [Term.denote, hsh, hw]
        obtain ⟨sv1, hS1, hw1, hh1⟩ := gate_false_events (L := L) (v := v) hok' _
          (slotsOf_width dl dt nl 1 (.sel d 0 0 (Term.share rest)))
        have hc3 : Holds M c3 :=
          (events_exact (fun m hm => (hor m hm).1) hd.records hd.event happ hca _ sv1 hS1 hw1 [] (by simpa using hh1) s1
            hnow hrec hms h12).2 trivial
        obtain ⟨r1, r2, -⟩ := events_rel hP hvx hvm hshs hor hd.records hd.event hd.apply happ' hE hPE hopt _ sv1 hS1
          hw1 [] (by simpa using hh1) s1 hnow hrec hms hn hq h12 hc3
        simp only [Step.reactAll] at r1 r2
        have hite : ∀ t u : Term, (Term.ite (Term.is d 0 (Term.share rest)) t u).denote M = u.denote M := fun t u => by
          show (if (Term.denote M (Term.is d 0 (Term.share rest))).toBool then _ else _) = _
          rw [hok']; rfl
        have hand : ∀ t : Term, (Term.and (Term.is d 0 (Term.share rest)) t).denote M = .bool false := fun t => by
          show Val.bool ((Term.denote M (Term.is d 0 (Term.share rest))).toBool && _) = _
          rw [hok']; rfl
        have hrj : RelV L x.rejection (Ty.up _ hd.rejection j) ((Term.sel d 1 0 (Term.share rest)).denote M) := by
          rw [sel_ctor 0 (hsh.trans hw)]; exact hrv
        have herr := adtCtor_rel (L := L) (M := M) (vs := [[Ty.nil], [x.rejection]]) ⟨1, by simp⟩ _ _ h18
          (Ty.up _ hd.rejection j, ()) ⟨_, _, rfl, hrj, rfl⟩
        rw [← up_err hrn hd.rejection j] at herr
        have hac : Smt.Rel M L _ (Ty.up _ hrn (.inr (.inl (j, ())))) ac :=
          (rel_ofTerm (need_ok.1 h19) _).2 (by rw [Term.denote_share, hite]; exact herr)
        have et := etail s1 _ hac hnow r1 r2
        simp only [ownDecidedFits]
        have h4' : Holds M (.ite (Term.is d 0 (Term.share rest)) c4 tt) := by unfold Holds; rw [hite]; exact holds_tt
        have ht' : Holds M (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt
            (andT c5 (andT c6 c7))) ↔ Holds M (andT c5 (andT c6 c7)) := by
          unfold Holds
          rw [show Term.denote M (Term.ite (Term.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2)))))
            tt (andT c5 (andT c6 c7))) = Term.denote M (andT c5 (andT c6 c7)) from by
              show (if (Term.denote M (Term.and _ _)).toBool then _ else _) = _
              rw [hand]; rfl]
        rw [ht', et]
        exact ⟨fun h => h.2.2, fun h => ⟨hc3, h4', h⟩⟩
      | inl pr =>
        obtain ⟨events, ⟨⟩⟩ := pr
        rw [hdv] at hres'
        erw [Ty.up_inl 2 _ _ _ hd.result (by simp only [Ty.isData, Ty.isDatas, hd.event, Bool.and_true]),
          Ty.up_tuple _ _ _ hd.events rfl] at hres'
        obtain ⟨d', n', hf', vals, hw, ev, rest', rfl, hev, rfl⟩ := hres'
        obtain rfl := find_det hfd hf'
        have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool true := by simp [Term.denote, hsh, hw]
        have hite : ∀ t u : Term, (Term.ite (Term.is d 0 (Term.share rest)) t u).denote M = t.denote M := fun t u => by
          show (if (Term.denote M (Term.is d 0 (Term.share rest))).toBool then _ else _) = _
          rw [hok']; rfl
        have hevs : Smt.Rel M L (.list v.event) (Ty.up _ hd.events events) (Term.sel d 0 0 (Term.share rest)) := by
          show RelV _ _ _ _
          rw [sel_ctor 0 (hsh.trans hw)]; exact hev
        obtain ⟨sv, hS, -, hsw, hh⟩ := list_view hevs h11
        erw [Ty.up_list _ _ hd.event] at hh
        let sA := (Step.reactAll T s1 events).1
        have e3 : Holds M c3 ↔ eventsFit L.count T s1 events :=
          events_exact (fun m hm => (hor m hm).1) hd.records hd.event happ hca _ sv (gate_true hok' hS) hsw events hh s1
            hnow hrec hms h12
        have hrel : Holds M c3 → RelV L v.records (Ty.up _ hd.records sA.records) (o1.records.denote M) ∧
            MachinesRel M L T v.machines o1.tables sA.machines := fun hc3 => by
          obtain ⟨r1, r2, -⟩ := events_rel hP hvx hvm hshs hor hd.records hd.event hd.apply happ' hE hPE hopt _ sv
            (gate_true hok' hS) hsw events hh s1 hnow hrec hms hn hq h12 hc3
          exact ⟨r1, r2⟩
        have e4 : Holds M c3 → (Holds M c4 ↔ x.ensures.appFits L.count (ctx, sA.records, ())) ∧
            (Holds M c4 → (Holds M (.ite (.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))) tt
              (andT c5 (andT c6 c7))) ↔ (Step.broken (x.ensures.fn (ctx, sA.records, ())) = [] →
                ((site.fn env).fits L.count).1 ∧ (site.fn env).appFits L.count ⟨Step.okNil, ()⟩ ∧
                  eventsFit L.count T sA ((site.fn env).fn ⟨Step.okNil, ()⟩)))) := fun hc3 => by
          obtain ⟨hrf, hms'⟩ := hrel hc3
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
          have hcnd : ((Term.and (Term.is d 0 (Term.share rest)) (.not (allT (ensures.map (·.2))))).denote M).toBool =
              !decide (Step.broken (x.ensures.fn (ctx, sA.records, ())) = []) := by
            show (Val.bool ((Term.denote M (Term.is d 0 (Term.share rest))).toBool &&
              (Val.bool (!(Term.denote M (allT (ensures.map (·.2)))).toBool)).toBool)).toBool = _
            rw [hok', ← hallE]; rfl
          have hnil := adtCtor_rel (L := L) (M := M) (vs := [[]]) ⟨0, by simp⟩ _ _ h16 ()
            (by show RelVs L [] () []; trivial)
          rw [← up_nil rfl] at hnil
          have hokn := adtCtor_rel (L := L) (M := M) (vs := [[Ty.nil], [x.rejection]]) ⟨0, by simp⟩ _ _ h17
            (Ty.up Ty.nil rfl (.inl ()), ()) ⟨_, _, rfl, hnil, rfl⟩
          rw [← up_okNil hrn] at hokn
          have hac : Smt.Rel M L _ (Ty.up _ hrn Step.okNil) ac :=
            (rel_ofTerm (need_ok.1 h19) _).2 (by rw [Term.denote_share, hite]; exact hokn)
          have hnA : now.denote M = .int sA.now := by rw [show sA.now = a.state.now from Step.reactAll_now T s1 events]; exact hnow
          rw [holds_ite, hcnd, ← etail sA _ hac hnA hrf hms']
          by_cases hb : Step.broken (x.ensures.fn (ctx, sA.records, ())) = []
          · simp [hb]
          · simp [hb, holds_tt]
        simp only [ownDecidedFits]
        have h4' : Holds M (.ite (Term.is d 0 (Term.share rest)) c4 tt) ↔ Holds M c4 := by unfold Holds; rw [hite]
        rw [h4']
        constructor
        · rintro ⟨hc3, hc4, hc5⟩
          exact ⟨e3.1 hc3, ((e4 hc3).1).1 hc4, ((e4 hc3).2 hc4).1 hc5⟩
        · rintro ⟨p3, p4, p5⟩
          have hc3 := e3.2 p3
          have hc4 := ((e4 hc3).1).2 p4
          exact ⟨hc3, hc4, ((e4 hc3).2 hc4).2 p5⟩
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


/-- T2 for an own query's internal step: wherever the condition holds, an unlisted caller or a broken `accepts` rule
is `Fault.invalidEffect`, and otherwise the internal step runs to its end with what the terms denote
(`InternalDone`); a query leaves the fresh counter as it was. -/
theorem ownQuery_rel {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true) (hed : v.event.isData = true)
    (a : Step.Acc v) (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (hd : QueryData x) {qc : QueryCode x} {cq : Term} (hqc : QueryCode.of L x = .ok (qc, cq)) (hcq : Holds M cq)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [x.output] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ)
    {ks : List Term} (hks : callerTerms L hd.caller x.callers = some ks)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {records now fresh n q sc si : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ hd.records a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ hd.input input) (si.denote M))
    {o : OwnQueryOut} {cond : Term}
    (henc : encodeOwnQuery L T v shs dE dP dopt x qc site σ apply ks records now fresh n q sc si xs = .ok (o, cond))
    (hc : Holds M cond) :
    let r := Step.runQuery T a x caller input (site.fn env)
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = .error (.invalidEffect x.name (n :: ns))
      | [] => InternalDone M L T hd.records shs a a.state.fresh o.answered o.answered.news o.answered.owns q0 r
    else r = .error (.invalidEffect x.name ["callers"]) := by
  have hqc := QueryCode.rel_of hd hqc hcq
  have hap : (Ty.fn [v.records, v.event] v.records).isData = true := by simp [Ty.isData, Ty.isDatas, hd.records, hed]
  have happ := v.apply.code_fn hap happ hca
  intro r
  obtain ⟨cc0, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cxt, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c3⟩, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c4⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c5⟩, h13, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 x.callers ks hks eqs h2
  simp only [r, Step.runQuery, Step.admit]
  cases hin : x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
  case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
  simp only [hok, hin, Val.toBool, ite_true]
  have hc' : Holds M (andT c1 (.ite (allT (rules.map (·.2))) (andT c2 (andT c3 (andT c4 c5))) tt)) := by
    simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
  rw [holds_andT] at hc'
  have hic : Smt.Rel M L _ (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  have hacc := hqc.accepts _ (ic, ()) (rels1 hd.input hd.args hic) rs c1 h4 hc'.1
  erw [Ty.up_fn _ Ty.rules _ hd.args rfl] at hacc
  have hbroken := rules_broken h5 _ hacc
  rw [hbroken]
  cases hb : Step.broken (x.accepts.fn (input, ())) with
  | cons n ns => rfl
  | nil =>
  simp only
  have hallT : (allT (rules.map (·.2))).denote M = .bool true := by
    rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil rules).1 (hbroken.trans hb))
  obtain ⟨hc2, hc3, hc4, hc5⟩ : Holds M c2 ∧ Holds M c3 ∧ Holds M c4 ∧ Holds M c5 := by
    have := hc'.2; simp only [Holds, Term.denote, hallT, Val.toBool, ite_true] at this
    have h : Holds M (andT c2 (andT c3 (andT c4 c5))) := this
    rw [holds_andT, holds_andT, holds_andT] at h; exact h
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[v.records, x.input, v.caller, .int, .dsl .fresh []]])
    ⟨0, by simp⟩ _ _ h6
    (Ty.up _ hd.records a.state.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, a.state.now, a.state.fresh, ())
    ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
  rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx (Step.ctx a.state a.state.records caller input)) cxt :=
    (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctx)
  have hres := hqc.resolve _ (cxt, ()) (rels1 hd.ctx hd.ctxArgs hcx) out c2 h8 hc2
  erw [Ty.up_fn _ _ _ hd.ctxArgs hd.output] at hres
  have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, hed]
  have hta : (Ty.tuple [x.output]).isData = true := by simp [Ty.isData, Ty.isDatas, hd.output]
  have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs) site.body
    σ _ hσ oa c3 h9 hc3
  have hoa' : Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := by
    rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa
  have hevs := hoa' _ (out, ()) (rels1 hd.output hta hres) evs c4 h10 hc4
  erw [Ty.up_fn _ _ _ hta hle] at hevs
  have hevt := (rel_term (need_ok.1 h11) _).1 hevs
  obtain ⟨sv, hS, -, hsw, hh⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h12
  erw [Ty.up_list _ _ hed] at hh
  let evs1 : List v.event.den0 := (site.fn env).fn ⟨x.resolve.fn ⟨Step.ctx a.state a.state.records caller input, ()⟩, ()⟩
  change Holds2 (EBag L v.event) (evs1.map (Ty.up _ hed)) sv at hh
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := loop_apply (T := T) hP hvx hshs hor hd.records hed hap happ hE hPE
    hopt hvm a hnow hS hsw hh hrec hms hn hq h13 hc5
  have hkeep := Step.reactAll_keeps T a.state evs1
  refine ⟨_, _, evs1, _, _, fun ps hps => ?_, q1, q2, q3, q4, q5, q6⟩
  erw [q7 ps hps]
  rw [forall2_zipIdx_length _ _ hps, hkeep]
  simp [Step.Acc.wrote, Step.Acc.queued]

/-- The condition of an own query's internal step is exact: for a listed caller, it holds exactly when `accepts`
fits at the input and, where its rules hold, `resolve` fits at the context, and the `on_answer` source, its
application to the output and the answer's events in turn fit. -/
theorem ownQuery_exact (a : Step.Acc v) (hor : ∀ m ∈ v.machines, m.key.orderable = true) (hed : v.event.isData = true)
    (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (hd : QueryData x) {qc : QueryCode x} {cq : Term} (hqc : QueryCode.of L x = .ok (qc, cq)) (hcq : Holds M cq)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [x.output] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ) (hΓf : ∀ t ∈ Γ, t.isFn = false)
    (hout : x.output.isFn = false) {ks : List Term} (hks : callerTerms L hd.caller x.callers = some ks)
    {shs : List (PendingShape v.event)} {dE dP dopt : Nat}
    {records now fresh n q sc si : Term} {xs : List Term}
    (hrec : RelV L v.records (Ty.up _ hd.records a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ hd.input input) (si.denote M))
    {o : OwnQueryOut} {cond : Term}
    (henc : encodeOwnQuery L T v shs dE dP dopt x qc site σ apply ks records now fresh n q sc si xs = .ok (o, cond)) :
    let ctx := Step.ctx a.state a.state.records caller input
    Holds M cond ↔ (x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
      x.accepts.appFits L.count (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.resolve.appFits L.count (ctx, ()) ∧ ((site.fn env).fits L.count).1 ∧
          (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩ ∧
          eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩))) := by
  intro ctx
  have hqc' := QueryCode.rel_of hd hqc hcq
  obtain ⟨⟨_, c1'⟩, g1, hqc0⟩ := bind_ok.1 hqc
  obtain ⟨⟨_, c2'⟩, g2, hqc0⟩ := bind_ok.1 hqc0
  cases pure_ok.1 hqc0
  obtain ⟨hca1, hca2⟩ := (holds_andT _ _).1 hcq
  obtain ⟨cc0, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctxT, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cxt, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c3⟩, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c4⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c5⟩, h13, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc0 x.callers ks hks eqs h2
  rw [holds_ite_tt (by rw [hok])]
  refine imp_congr_right fun _ => ?_
  rw [holds_andT]
  have hic : Smt.Rel M L _ (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  have hargs := rels1 hd.input hd.args hic
  have e1 : Holds M c1 ↔ x.accepts.appFits L.count (input, ()) :=
    x.accepts.app_exact g1 hca1 (by simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h3)) _ _ hargs h4
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[v.records, x.input, v.caller, .int, .dsl .fresh []]])
    ⟨0, by simp⟩ _ _ h6
    (Ty.up _ hd.records a.state.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, a.state.now, a.state.fresh, ())
    ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
  rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx ctx) cxt :=
    (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctx)
  have hargs' := rels1 hd.ctx hd.ctxArgs hcx
  have e2 : Holds M c2 ↔ x.resolve.appFits L.count (ctx, ()) :=
    x.resolve.app_exact g2 hca2 (by simp [Ty.ctx, Ty.isFn]) _ _ hargs' h8
  have hta : (Ty.tuple [x.output]).isData = true := by simp [Ty.isData, Ty.isDatas, hd.output]
  have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, hed]
  have hap : (Ty.fn [v.records, v.event] v.records).isData = true := by simp [Ty.isData, Ty.isDatas, hd.records, hed]
  have x1 := encode_exact site.defs site.defs.eval (site.defs.encode L) (site.defs.fits L.count)
    (Defs.encode_agrees M L site.defs) (Defs.encode_exact M L site.defs) site.body σ _ (FTs.dflt _) hσ
    (frels_of_notFn hΓf _ _ _) oa c3 h9
  have hfit : (site.fn env).fits L.count = Expr.fits L.count site.defs site.defs.eval (site.defs.fits L.count) site.body
      (Ty.up _ site.hΓ env) (FTs.dflt _) := by
    simp only [Fun.fits, Site.fn]
  have e3 : Holds M c3 ↔ ((site.fn env).fits L.count).1 := by rw [hfit]; exact x1.1
  have hrest : Holds M c2 → (Holds M (andT c3 (andT c4 c5)) ↔ ((site.fn env).fits L.count).1 ∧
      (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩ ∧
      eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩)) := fun hc2 => by
    have hres := hqc'.resolve _ (cxt, ()) hargs' out c2 h8 hc2
    erw [Ty.up_fn _ _ _ hd.ctxArgs hd.output] at hres
    have e4 : Holds M c3 → (Holds M c4 ↔ (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩) := fun hc3 => by
      have := (x1.2 hc3 _ (FTs.dflt _) (out, ()) (rels1 hd.output hta hres)
        (frels_of_notFn (by simp only [List.mem_singleton, forall_eq]; exact hout) _ _ _) evs c4 h10).1
      rw [this]; unfold Fun.appFits; rw [hfit]
    have e5 : Holds M c3 → Holds M c4 →
        (Holds M c5 ↔ eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩)) := fun hc3 hc4 => by
      have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs)
        site.body σ _ hσ oa c3 h9 hc3
      have hoa' : Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := by
        rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa
      have hevs := hoa' _ (out, ()) (rels1 hd.output hta hres) evs c4 h10 hc4
      erw [Ty.up_fn _ _ _ hta hle] at hevs
      have hevt := (rel_term (need_ok.1 h11) _).1 hevs
      obtain ⟨sv, hS, -, hsw, hh⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h12
      erw [Ty.up_list _ _ hed] at hh
      exact events_exact hor hd.records hed happ hca _ sv hS hsw _ hh a.state hnow hrec hms h13
    rw [holds_andT, holds_andT]
    constructor
    · rintro ⟨hc3, hc4, hc5⟩
      exact ⟨e3.1 hc3, (e4 hc3).1 hc4, (e5 hc3 hc4).1 hc5⟩
    · rintro ⟨p3, p4, p5⟩
      have hc3 := e3.2 p3
      have hc4 := (e4 hc3).2 p4
      exact ⟨hc3, hc4, (e5 hc3 hc4).2 p5⟩
  have hrules : Holds M c1 → (Holds M (.ite (allT (rules.map (·.2))) (andT c2 (andT c3 (andT c4 c5))) tt) ↔
      (Step.broken (x.accepts.fn (input, ())) = [] → x.resolve.appFits L.count (ctx, ()) ∧
        ((site.fn env).fits L.count).1 ∧ (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩ ∧
        eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩))) := fun hc1 => by
    have hacc := hqc'.accepts _ (ic, ()) hargs rs c1 h4 hc1
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
    constructor
    · rintro ⟨hc2, hx⟩
      exact ⟨e2.1 hc2, (hrest hc2).1 hx⟩
    · rintro ⟨p2, px⟩
      have hc2 := e2.2 p2
      exact ⟨hc2, (hrest hc2).2 px⟩
  constructor
  · rintro ⟨hc1, hx⟩
    exact ⟨e1.1 hc1, (hrules hc1).1 hx⟩
  · rintro ⟨p1, px⟩
    have hc1 := e1.2 p1
    exact ⟨hc1, (hrules hc1).2 px⟩

end

end Tazuna.Smt
