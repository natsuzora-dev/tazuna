import Tazuna.Smt.Decide
import Tazuna.Smt.Query
import Tazuna.Semantics.Settle

/-! One internal step: an own command or query the step queued runs as `Step.runCommand` or `Step.runQuery` does. A
command's caller and `accepts` rules admit the input, `decide` accepts with events or rejects, the events run through
the events loop from the running records, tables, next id and queue place, `ensures` is checked on the records they
leave, and `on_answer` (the program's site at the values the effect captured) turns the answer into events that run
through the loop again. Requests the loops start are not written into the pending table here: the step writes every
internal step's requests once, at its end. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of an own command's internal step: whether the caller is listed and the `accepts` rules, `decide` and
what follows it, and what the events loop leaves after `on_answer`'s events. -/
structure OwnCommandOut where
  callerOk : Term
  rules : List (Term × Term)
  decided : DecideOut
  answered : EventsOut

/-- What an own command's internal step leaves: the loop after `on_answer`, with the news and own slots of both
loops. -/
def OwnCommandOut.done (o : OwnCommandOut) : EventsOut :=
  { o.answered with news := o.decided.after.news ++ o.answered.news, owns := o.decided.after.owns ++ o.answered.owns }

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
def encodeOwnCommand (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (x : CommandV v.records v.event v.caller) (cc : CommandCode x) {Γ : List Ty}
    (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) (σ : Codes Γ)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (callers : List Term)
    (records now fresh n q caller input : Term) (xs : List Term) : Except Refusal (OwnCommandOut × Term) := do
  let (a, c1) ← encodeAdmit L cc.accepts callers records now fresh caller input
  let (dc, cd) ← encodeDecide L T v shs senv x cc apply a.ctx now records xs n q
  let nil ← adtCtor L 1 [] [[]] 0 []
  let okNil ← adtCtor L 2 [Ty.nil, x.rejection] [[Ty.nil], [x.rejection]] 0 [nil]
  let err ← adtCtor L 2 [Ty.nil, x.rejection] [[Ty.nil], [x.rejection]] 1 [dc.rejection]
  let ac ← need "an answer that has no term" (Code.ofTerm? (Ty.result Ty.nil x.rejection) (Term.share (.ite dc.ok okNil err)))
  let (oa, c5) ← site.code L σ
  let (evs, c6) ← oa (ac, ())
  let evt ← need "events that have no term" (Code.term? _ evs)
  let (dl, nl, dt) ← collD L (.list v.event) [v.event]
  let (o2, c7) ← encodeEvents L T v shs senv apply now (slotsOf dl dt nl 1 evt) dc.after.records dc.after.tables
    dc.after.nextId dc.after.queued
  pure (⟨a.callerOk, a.rules, dc, o2⟩,
    .ite a.callerOk (andT c1 (.ite (allT (a.rules.map (·.2))) (andT cd
      (.ite (.and dc.ok (.not (allT (dc.ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))) tt)) tt)


/-- An own query's internal step terms and condition, from the codes of the query and of its `on_answer` site over
the captured values `σ`, the terms of the running state, the caller and the input, and the listed callers'
constants: the caller and the `accepts` rules admit the input, `resolve` answers, and `on_answer`'s events run
through the events loop. -/
def encodeOwnQuery (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (x : QueryV v.records v.caller) (qc : QueryCode x) {Γ : List Ty} (site : Site Γ (Ty.fn [x.output] (.list v.event)))
    (σ : Codes Γ) (apply : Code (Ty.fn [v.records, v.event] v.records)) (callers : List Term)
    (records now fresh n q caller input : Term) (xs : List Term) : Except Refusal (OwnQueryOut × Term) := do
  let (a, c1) ← encodeAdmit L qc.accepts callers records now fresh caller input
  let (out, c2) ← qc.resolve (a.ctx, ())
  let (oa, c3) ← site.code L σ
  let (evs, c4) ← oa (out, ())
  let evt ← need "events that have no term" (Code.term? _ evs)
  let (dl, nl, dt) ← collD L (.list v.event) [v.event]
  let (o, c5) ← encodeEvents L T v shs senv apply now (slotsOf dl dt nl 1 evt) records xs n q
  pure (⟨a.callerOk, a.rules, o⟩,
    .ite a.callerOk (andT c1 (.ite (allT (a.rules.map (·.2))) (andT c2 (andT c3 (andT c4 c5))) tt)) tt)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

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

/-- Whether `on_answer`'s part of an internal step fits from `s`: its source, its application to the answer `ans`
and the answer's events in turn. -/
def onAnswerFits {t : Ty} (S : Ty → Nat) (T : List TypeDecl) (s : State v) (oa : Fun (Ty.fn [t] (.list v.event)))
    (ans : t.den0) : Prop :=
  (oa.fits S).1 ∧ oa.appFits S ⟨ans, ()⟩ ∧ eventsFit S T s (oa.fn ⟨ans, ()⟩)

/-- Whether what an own command's internal step does after `decide` fits, for what `decide` returned: what follows it
(`decideFits`) and, on acceptance unless `ensures` broke a rule, `on_answer`'s part for `Ok(Nil)` from the state the
events leave; on a rejection, `on_answer`'s part for the rejection. -/
def ownDecidedFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : CommandV v.records v.event v.caller)
    (ctx : (Ty.ctx v.records x.input v.caller).den0) (oa : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) :
    (Ty.result (.list v.event) x.rejection).den0 → Prop
  | .inl (events, ()) =>
    decideFits S T s x ctx (.inl (events, ())) ∧
      (Step.broken (x.ensures.fn (ctx, (Step.reactAll T s events).1.records, ())) = [] →
        onAnswerFits S T (Step.reactAll T s events).1 oa Step.okNil)
  | .inr (.inl (j, ())) => onAnswerFits S T s oa (.inr (.inl (j, ())))
  | .inr (.inr e) => e.elim

/-- An own command's internal step: the condition holds exactly when, for a listed caller, `accepts` fits at the input
and, where its rules hold, `decide` fits at the context and what follows it fits (`ownDecidedFits`). Wherever it
holds, an unlisted caller or a broken `accepts` rule is `Fault.invalidEffect`, a broken `ensures` rule after an
acceptance is `Fault.ensures`, and otherwise the internal step runs to its end with what the terms denote (`AccRel`),
the fresh counter advanced. -/
theorem ownCommand_encode {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P) (a : Step.Acc v)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0) {cc : CommandCode x}
    {cx : Term} (hcc : CommandCode.of L x = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ) (hΓf : ∀ t ∈ Γ, t.isFn = false)
    {ks : List Term} (hks : callerTerms L x.data.caller x.callers = some ks)
    (senv : StepEnv L shs)
    {records now fresh n q sc si : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ x.data.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ x.data.input input) (si.denote M))
    {o : OwnCommandOut} {cond : Term}
    (henc : encodeOwnCommand L T v shs senv x cc site σ apply ks records now fresh n q sc si xs = .ok (o, cond)) :
    let ctx := Step.ctx a.state a.state.records caller input
    let r := Step.runCommand T a x caller input (site.fn env)
    (Holds M cond ↔ (x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
      x.accepts.appFits L.count (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.decide.appFits L.count (ctx, ()) ∧
          ownDecidedFits L.count T { a.state with fresh := a.state.fresh + 1 } x ctx (site.fn env)
            (x.decide.fn (ctx, ()))))) ∧
    (Holds M cond →
      if (o.callerOk.denote M).toBool then
        match brokenIn M o.rules with
        | n :: ns => r = .error (.invalidEffect x.name (n :: ns))
        | [] =>
          match (o.decided.ok.denote M).toBool, brokenIn M o.decided.ensures with
          | true, n :: _ => r = .error (.ensures n)
          | _, _ => AccRel M L T shs a o.done (.add fresh (.int 1)) q0 r
      else r = .error (.invalidEffect x.name ["callers"])) := by
  intro ctx r
  have hcc' := CommandCode.rel_of hcc hccx
  have happ' := v.apply.code_fn v.apply.ht happ hca
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dc, cd⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨nil, h16, henc⟩ := bind_ok.1 henc
  obtain ⟨okNil, h17, henc⟩ := bind_ok.1 henc
  obtain ⟨err, h18, henc⟩ := bind_ok.1 henc
  obtain ⟨ac, h19, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c5⟩, h20, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c6⟩, h21, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h22, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o2, c7⟩, h23, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hok, hbr, hcx⟩ := admit_rel v.records_data x.data.input x.data.caller x.data.ctx _ x.data.accepts
    hcc'.accepts _ hks a.state caller input hrec hnow hfresh hsc hsi h1
  let a1 : Step.Acc v := { a with state := { a.state with fresh := a.state.fresh + 1 } }
  have hfr1 : (Term.add fresh (.int 1)).denote M = .int (Int.ofNat a1.state.fresh) := by
    simp only [Term.denote, hfresh]; rfl
  have D := decide_encode chk hshs x hcc hccx happ hca senv a1 ctx hcx hnow hrec hms hn hq hfr1 h2
  have hle : (Ty.list v.event).isData = true := x.data.events
  have hrn : (Ty.result Ty.nil x.rejection).isData = true := by
    simp [Ty.result, Ty.nil, Ty.isData, Ty.isDatas, Ty.isDatass, x.data.rejection]
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
  have hview : ∀ (ans : (Ty.result Ty.nil x.rejection).den0), Smt.Rel M L _ (Ty.up _ hrn ans) ac → Holds M c5 →
      Holds M c6 → ∃ sv, SlotsDen M (slotsOf dl dt nl 1 evt) sv ∧ (∀ p ∈ sv, p.2.length = 1) ∧
        Holds2 (EBag L v.event) (((site.fn env).fn ⟨ans, ()⟩).map (Ty.up _ v.event_data)) sv := fun ans hac hc5 hc6 => by
    have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs)
      site.body σ _ hσ oa c5 h20 hc5
    have hoa' : Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := by
      rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa
    have hevs2 := hoa' _ (ac, ()) (rels1 hrn hta hac) evs c6 h21 hc6
    erw [Ty.up_fn _ _ _ hta hle] at hevs2
    have hevt := (rel_term (need_ok.1 h22) _).1 hevs2
    obtain ⟨sv2, hS2, -, hsw2, hh2⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h11
    erw [Ty.up_list _ _ v.event_data] at hh2
    exact ⟨sv2, hS2, hsw2, hh2⟩
  have etail : ∀ (s : State v) (ans : (Ty.result Ty.nil x.rejection).den0), Smt.Rel M L _ (Ty.up _ hrn ans) ac →
      now.denote M = .int s.now → RelV L v.records (Ty.up _ v.records_data s.records) (dc.after.records.denote M) →
      MachinesRel M L T v.machines dc.after.tables s.machines →
      (Holds M (andT c5 (andT c6 c7)) ↔ onAnswerFits L.count T s (site.fn env) ans) := fun s ans hac hnw hr hm => by
    rw [holds_andT, holds_andT]
    have e7 : Holds M c5 → Holds M c6 → (Holds M c7 ↔ eventsFit L.count T s ((site.fn env).fn ⟨ans, ()⟩)) :=
      fun hc5 hc6 => by
        obtain ⟨sv2, hS2, hsw2, hh2⟩ := hview ans hac hc5 hc6
        exact events_exact (fun m hm => (chk.keys m hm).1) happ hca _ sv2 hS2 hsw2 _ hh2 s hnw hr hm h23
    constructor
    · rintro ⟨hc5, hc6, hc7⟩
      exact ⟨e5.1 hc5, (e6 ans hac hc5).1 hc6, (e7 hc5 hc6).1 hc7⟩
    · rintro ⟨p5, p6, p7⟩
      have hc5 := e5.2 p5
      have hc6 := (e6 ans hac hc5).2 p6
      exact ⟨hc5, hc6, (e7 hc5 hc6).2 p7⟩
  have erel : ∀ (a2 : Step.Acc v) (q1 : Nat) (ans : (Ty.result Ty.nil x.rejection).den0),
      Smt.Rel M L _ (Ty.up _ hrn ans) ac → now.denote M = .int a2.state.now →
      RelV L v.records (Ty.up _ v.records_data a2.state.records) (dc.after.records.denote M) →
      MachinesRel M L T v.machines dc.after.tables a2.state.machines →
      (Term.add fresh (.int 1)).denote M = .int (Int.ofNat a2.state.fresh) →
      dc.after.nextId.denote M = .int (Int.ofNat a2.state.nextId) → dc.after.queued.denote M = .int q1 →
      Holds M (andT c5 (andT c6 c7)) →
      AccRel M L T shs a2 o2 (.add fresh (.int 1)) q1 (Step.applyEvents T a2 ((site.fn env).fn ⟨ans, ()⟩)) :=
    fun a2 q1 ans hac hnw hr hm hf hn2 hq2 h567 => by
      obtain ⟨hc5, hc6, hc7⟩ : Holds M c5 ∧ Holds M c6 ∧ Holds M c7 := by
        rw [holds_andT, holds_andT] at h567; exact h567
      obtain ⟨sv2, hS2, hsw2, hh2⟩ := hview ans hac hc5 hc6
      exact loop_acc (T := T) chk hshs happ' senv a2 hnw hS2 hsw2 hh2 hr hm hn2 hq2 hf h23 hc7
  have hacR : ∀ j, RelV L x.rejection (Ty.up _ x.data.rejection j) (dc.rejection.denote M) →
      dc.ok.denote M = .bool false → Smt.Rel M L _ (Ty.up _ hrn (.inr (.inl (j, ())))) ac := fun j hrj hokf => by
    have herr := adtCtor_rel (L := L) (M := M) (vs := [[Ty.nil], [x.rejection]]) ⟨1, by simp⟩ _ _ h18
      (Ty.up _ x.data.rejection j, ()) ⟨_, _, rfl, hrj, rfl⟩
    rw [← up_err hrn x.data.rejection j] at herr
    exact (rel_ofTerm (need_ok.1 h19) _).2 (by simp only [Term.denote_share, Term.denote, hokf, toBool_bool]; exact herr)
  have hacA : dc.ok.denote M = .bool true → Smt.Rel M L _ (Ty.up _ hrn Step.okNil) ac := fun hokt => by
    have hnil := adtCtor_rel (L := L) (M := M) (vs := [[]]) ⟨0, by simp⟩ _ _ h16 () (by show RelVs L [] () []; trivial)
    rw [← up_nil rfl] at hnil
    have hokn := adtCtor_rel (L := L) (M := M) (vs := [[Ty.nil], [x.rejection]]) ⟨0, by simp⟩ _ _ h17
      (Ty.up Ty.nil rfl (.inl ()), ()) ⟨_, _, rfl, hnil, rfl⟩
    rw [← up_okNil hrn] at hokn
    exact (rel_ofTerm (need_ok.1 h19) _).2 (by simp only [Term.denote_share, Term.denote, hokt, toBool_bool]; exact hokn)
  refine ⟨?_, fun hc => ?_⟩
  · obtain ⟨⟨_, c1'⟩, g1, hcc0⟩ := bind_ok.1 hcc
    obtain ⟨_, -, hcc0⟩ := bind_ok.1 hcc0
    obtain ⟨_, -, hcc0⟩ := bind_ok.1 hcc0
    cases pure_ok.1 hcc0
    obtain ⟨hca1, -⟩ := (holds_andT _ _).1 hccx
    rw [holds_ite_tt (by rw [hok])]
    refine imp_congr_right fun _ => ?_
    rw [holds_andT]
    have e1 := admit_exact x.data.input x.accepts g1 hca1 input hsi h1
    have hrest : Holds M c1 → (Holds M (.ite (allT (adm.rules.map (·.2))) (andT cd
        (.ite (.and dc.ok (.not (allT (dc.ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))) tt) ↔
        (Step.broken (x.accepts.fn (input, ())) = [] →
          x.decide.appFits L.count (ctx, ()) ∧ ownDecidedFits L.count T a1.state x ctx (site.fn env)
            (x.decide.fn (ctx, ())))) := fun hc1 => by
      have hall : ((allT (adm.rules.map (·.2))).denote M).toBool = decide (Step.broken (x.accepts.fn (input, ())) = []) := by
        rw [toBool_allT_rules, hbr hc1]
      rw [holds_ite_tt hall, decide_eq_true_iff]
      refine imp_congr_right fun _ => ?_
      rw [holds_andT, D.1]
      have R := D.2
      have E := D.1
      revert R E
      cases hdv : x.decide.fn (ctx, ()) with
      | inr qq =>
        match qq, hdv with
        | .inr e, _ => exact e.elim
        | .inl (j, ()), _ =>
          intro R E
          simp only [ownDecidedFits]
          have tail : x.decide.appFits L.count (ctx, ()) →
              (Holds M (.ite (.and dc.ok (.not (allT (dc.ensures.map (·.2))))) tt (andT c5 (andT c6 c7))) ↔
                onAnswerFits L.count T a1.state (site.fn env) (.inr (.inl (j, ())))) := fun p2 => by
            obtain ⟨hokf, hrj, hacc⟩ := R (E.2 ⟨p2, trivial⟩)
            obtain ⟨r1, r2, -⟩ := hacc.ends
            rw [holds_ite, show ((Term.and dc.ok (.not (allT (dc.ensures.map (·.2))))).denote M).toBool = false by
              simp only [Term.denote, hokf, toBool_bool, Bool.false_and]]
            exact etail a1.state _ (hacR j hrj hokf) hnow r1 r2
          exact ⟨fun ⟨⟨p2, _⟩, ht⟩ => ⟨p2, (tail p2).1 ht⟩, fun ⟨p2, pt⟩ => ⟨⟨p2, trivial⟩, (tail p2).2 pt⟩⟩
      | inl pr =>
        obtain ⟨events, ⟨⟩⟩ := pr
        intro R E
        simp only [ownDecidedFits]
        let sA := (Step.reactAll T a1.state events).1
        have tail : x.decide.appFits L.count (ctx, ()) ∧ decideFits L.count T a1.state x ctx (.inl (events, ())) →
            (Holds M (.ite (.and dc.ok (.not (allT (dc.ensures.map (·.2))))) tt (andT c5 (andT c6 c7))) ↔
              (Step.broken (x.ensures.fn (ctx, sA.records, ())) = [] →
                onAnswerFits L.count T sA (site.fn env) Step.okNil)) := fun h => by
          obtain ⟨hokt, hbe, -, -, hrA, hmA⟩ := R (E.2 h)
          have hnA : now.denote M = .int sA.now := by
            rw [show sA.now = a.state.now from Step.reactAll_now T a1.state events]; exact hnow
          rw [holds_ite, show ((Term.and dc.ok (.not (allT (dc.ensures.map (·.2))))).denote M).toBool =
              !decide (Step.broken (x.ensures.fn (ctx, sA.records, ())) = []) by
            simp only [Term.denote, hokt, toBool_bool, toBool_allT_rules, hbe, Bool.true_and]; rfl,
            ← etail sA _ (hacA hokt) hnA hrA hmA]
          by_cases hb : Step.broken (x.ensures.fn (ctx, sA.records, ())) = []
          · simp [hb]
          · simp [hb, holds_tt]
        exact ⟨fun ⟨⟨p2, pd⟩, ht⟩ => ⟨p2, pd, (tail ⟨p2, pd⟩).1 ht⟩,
          fun ⟨p2, pd, pt⟩ => ⟨⟨p2, pd⟩, (tail ⟨p2, pd⟩).2 pt⟩⟩
    constructor
    · rintro ⟨hc1, hx⟩
      exact ⟨e1.1 hc1, (hrest hc1).1 hx⟩
    · rintro ⟨p1, px⟩
      have hc1 := e1.2 p1
      exact ⟨hc1, (hrest hc1).2 px⟩
  · simp only [r, Step.runCommand, Step.execCommand, Step.admit, bind, Except.bind]
    cases hin : x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
    case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
    simp only [hok, hin, Val.toBool, ite_true]
    have hc' : Holds M (andT c1 (.ite (allT (adm.rules.map (·.2))) (andT cd
        (.ite (.and dc.ok (.not (allT (dc.ensures.map (·.2))))) tt (andT c5 (andT c6 c7)))) tt)) := by
      simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
    rw [holds_andT] at hc'
    have hbroken := hbr hc'.1
    rw [hbroken]
    cases hb : Step.broken (x.accepts.fn (input, ())) with
    | cons n ns => rfl
    | nil =>
    simp only
    have hallT : ((allT (adm.rules.map (·.2))).denote M).toBool = true := by
      rw [toBool_allT_rules, hbroken, hb]; rfl
    obtain ⟨hcd, hct⟩ := (holds_andT _ _).1 ((holds_ite_tt hallT).1 hc'.2 rfl)
    have R := D.2 hcd
    revert R
    cases hdec : x.decide.fn (Step.ctx a.state a.state.records caller input, ()) with
    | inr qq =>
      match qq, hdec with
      | .inr e, _ => exact e.elim
      | .inl (j, ()), _ =>
      rintro ⟨hokf, hrj, hacc⟩
      simp only [hokf]
      have h567 : Holds M (andT c5 (andT c6 c7)) := by
        rw [holds_ite, show ((Term.and dc.ok (.not (allT (dc.ensures.map (·.2))))).denote M).toBool = false by
          simp only [Term.denote, hokf, toBool_bool, Bool.false_and]] at hct
        exact hct
      exact AccRel.of_fresh (AccRel.bind (o2 := o2) (f2 := .add fresh (.int 1))
        (g := fun a2 => Step.applyEvents T a2 ((site.fn env).fn ⟨.inr (.inl (j, ())), ()⟩)) hacc
        fun a2 os hra _ r1 r2 r3 r4 r6 => by
        cases hra
        exact erel a1 _ _ (hacR j hrj hokf) hnow r1 r2 r3 r4 r6 h567)
    | inl pr =>
      obtain ⟨events, ⟨⟩⟩ := pr
      rintro ⟨hokt, hbe, hacc, hrecs, -⟩
      simp only [hokt, hbe]
      obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, -, -, -, -, e5, -, -⟩ := id hacc
      obtain ⟨ps1, hps1⟩ := newsRel_writes e5
      have happly := hr1 ps1 hps1
      have hrs := hrecs _ happly
      dsimp only at hrs
      cases hbe' : Step.broken (x.ensures.fn (Step.ctx a.state a.state.records caller input,
          (Step.reactAll T a1.state events).1.records, ())) with
      | cons n ns =>
        simp only
        rw [happly]
        dsimp only
        rw [hrs, hbe']
      | nil =>
        simp only
        have h567 : Holds M (andT c5 (andT c6 c7)) := by
          rw [holds_ite, show ((Term.and dc.ok (.not (allT (dc.ensures.map (·.2))))).denote M).toBool = false by
            simp only [Term.denote, hokt, toBool_bool, toBool_allT_rules, hbe]; simp [ctx, hbe']] at hct
          exact hct
        have H := AccRel.of_fresh (AccRel.bind (g := fun a2 => Step.applyEvents T a2 ((site.fn env).fn ⟨Step.okNil, ()⟩))
          hacc fun a2 os hra _ r1 r2 r3 r4 r6 => by
            have hnw : now.denote M = .int a2.state.now := by
              rw [hra] at happly; obtain rfl := Except.ok.inj happly; exact hnow
            exact erel a2 _ _ (hacA hokt) hnw r1 r2 r3 r4 r6 h567)
        have hbe'' : Step.broken (x.ensures.fn (Step.ctx a.state a.state.records caller input, recs1, ())) = [] := by
          rw [hrs]; exact hbe'
        rw [happly] at H ⊢
        dsimp only at H ⊢
        rw [hbe'']
        exact H

/-- T2 for an own query's internal step: wherever the condition holds, an unlisted caller or a broken `accepts` rule
is `Fault.invalidEffect`, and otherwise the internal step runs to its end with what the terms denote
(`AccRel`); a query leaves the fresh counter as it was. -/
theorem ownQuery_rel {P : List AnySite} (chk : Checked P T v) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (a : Step.Acc v) (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0) {qc : QueryCode x} {cq : Term} (hqc : QueryCode.of L x = .ok (qc, cq)) (hcq : Holds M cq)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [x.output] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ)
    {ks : List Term} (hks : callerTerms L x.data.caller x.callers = some ks)
    (senv : StepEnv L shs)
    {records now fresh n q sc si : Term} {xs : List Term} {q0 : Nat}
    (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ x.data.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ x.data.input input) (si.denote M))
    {o : OwnQueryOut} {cond : Term}
    (henc : encodeOwnQuery L T v shs senv x qc site σ apply ks records now fresh n q sc si xs = .ok (o, cond))
    (hc : Holds M cond) :
    let r := Step.runQuery T a x caller input (site.fn env)
    if (o.callerOk.denote M).toBool then
      match brokenIn M o.rules with
      | n :: ns => r = .error (.invalidEffect x.name (n :: ns))
      | [] => AccRel M L T shs a o.answered fresh q0 r
    else r = .error (.invalidEffect x.name ["callers"]) := by
  have hqc := QueryCode.rel_of hqc hcq
  have v.apply.ht : (Ty.fn [v.records, v.event] v.records).isData = true := by simp [Ty.isData, Ty.isDatas, v.records_data, v.event_data]
  have happ := v.apply.code_fn v.apply.ht happ hca
  intro r
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c3⟩, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c4⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c5⟩, h13, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hok, hbr, hcx⟩ := admit_rel v.records_data x.data.input x.data.caller x.data.ctx _ x.data.accepts hqc.accepts _ hks a.state caller
    input hrec hnow hfresh hsc hsi h1
  simp only [r, Step.runQuery, Step.execQuery, Step.admit]
  cases hin : x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller)
  case false => simp only [hok, hin, Val.toBool, Bool.false_eq_true, ite_false]
  simp only [hok, hin, Val.toBool, ite_true]
  have hc' : Holds M (andT c1 (.ite (allT (adm.rules.map (·.2))) (andT c2 (andT c3 (andT c4 c5))) tt)) := by
    simpa only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] using hc
  rw [holds_andT] at hc'
  have hbroken := hbr hc'.1
  rw [hbroken]
  cases hb : Step.broken (x.accepts.fn (input, ())) with
  | cons n ns => rfl
  | nil =>
  simp only
  have hallT : (allT (adm.rules.map (·.2))).denote M = .bool true := by
    rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil adm.rules).1 (hbroken.trans hb))
  obtain ⟨hc2, hc3, hc4, hc5⟩ : Holds M c2 ∧ Holds M c3 ∧ Holds M c4 ∧ Holds M c5 := by
    have := hc'.2; simp only [Holds, Term.denote, hallT, Val.toBool, ite_true] at this
    have h : Holds M (andT c2 (andT c3 (andT c4 c5))) := this
    rw [holds_andT, holds_andT, holds_andT] at h; exact h
  have hres := hqc.resolve _ (adm.ctx, ()) (rels1 x.data.ctx x.data.ctxArgs hcx) out c2 h8 hc2
  erw [Ty.up_fn _ _ _ x.data.ctxArgs x.data.output] at hres
  have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, v.event_data]
  have hta : (Ty.tuple [x.output]).isData = true := by simp [Ty.isData, Ty.isDatas, x.data.output]
  have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs) site.body
    σ _ hσ oa c3 h9 hc3
  have hoa' : Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := by
    rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa
  have hevs := hoa' _ (out, ()) (rels1 x.data.output hta hres) evs c4 h10 hc4
  erw [Ty.up_fn _ _ _ hta hle] at hevs
  have hevt := (rel_term (need_ok.1 h11) _).1 hevs
  obtain ⟨sv, hS, -, hsw, hh⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h12
  erw [Ty.up_list _ _ v.event_data] at hh
  let evs1 : List v.event.den0 := (site.fn env).fn ⟨x.resolve.fn ⟨Step.ctx a.state a.state.records caller input, ()⟩, ()⟩
  change Holds2 (EBag L v.event) (evs1.map (Ty.up _ v.event_data)) sv at hh
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := loop_apply (T := T) chk hshs happ senv a hnow hS hsw hh hrec hms hn hq h13 hc5
  have hkeep := Step.reactAll_keeps T a.state evs1
  refine ⟨_, _, a.state.fresh, evs1, _, _, fun ps hps => ?_, q1, q2, hfresh, q3, q4, q5, q6⟩
  erw [q7 ps hps]
  rw [forall2_zipIdx_length _ _ hps, hkeep]
  simp [Step.Acc.wrote, Step.Acc.queued]

/-- The condition of an own query's internal step is exact: for a listed caller, it holds exactly when `accepts`
fits at the input and, where its rules hold, `resolve` fits at the context, and the `on_answer` source, its
application to the output and the answer's events in turn fit. -/
theorem ownQuery_exact (a : Step.Acc v) (hor : ∀ m ∈ v.machines, m.key.orderable = true)
    (x : QueryV v.records v.caller) (caller : v.caller.den0) (input : x.input.den0) {qc : QueryCode x} {cq : Term} (hqc : QueryCode.of L x = .ok (qc, cq)) (hcq : Holds M cq)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {Γ : List Ty} (site : Site Γ (Ty.fn [x.output] (.list v.event))) (env : (Ty.tuple Γ).den0)
    {σ : Codes Γ} (hσ : Rels M L Γ (Ty.up _ site.hΓ env) σ) (hΓf : ∀ t ∈ Γ, t.isFn = false)
    (hout : x.output.isFn = false) {ks : List Term} (hks : callerTerms L x.data.caller x.callers = some ks)
    {shs : List (PendingShape v.event)} {senv : StepEnv L shs}
    {records now fresh n q sc si : Term} {xs : List Term}
    (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    (hnow : now.denote M = .int a.state.now) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    (hms : MachinesRel M L T v.machines xs a.state.machines)
    (hsc : RelV L v.caller (Ty.up _ x.data.caller caller) (sc.denote M))
    (hsi : RelV L x.input (Ty.up _ x.data.input input) (si.denote M))
    {o : OwnQueryOut} {cond : Term}
    (henc : encodeOwnQuery L T v shs senv x qc site σ apply ks records now fresh n q sc si xs = .ok (o, cond)) :
    let ctx := Step.ctx a.state a.state.records caller input
    Holds M cond ↔ (x.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
      x.accepts.appFits L.count (input, ()) ∧
      (Step.broken (x.accepts.fn (input, ())) = [] →
        x.resolve.appFits L.count (ctx, ()) ∧ ((site.fn env).fits L.count).1 ∧
          (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩ ∧
          eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩))) := by
  intro ctx
  have hqc' := QueryCode.rel_of hqc hcq
  obtain ⟨⟨_, c1'⟩, g1, hqc0⟩ := bind_ok.1 hqc
  obtain ⟨⟨_, c2'⟩, g2, hqc0⟩ := bind_ok.1 hqc0
  cases pure_ok.1 hqc0
  obtain ⟨hca1, hca2⟩ := (holds_andT _ _).1 hcq
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c3⟩, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c4⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c5⟩, h13, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hok, hbr, hcx⟩ := admit_rel v.records_data x.data.input x.data.caller x.data.ctx _ x.data.accepts hqc'.accepts _ hks a.state caller
    input hrec hnow hfresh hsc hsi h1
  rw [holds_ite_tt (by rw [hok])]
  refine imp_congr_right fun _ => ?_
  rw [holds_andT]
  have e1 := admit_exact x.data.input x.accepts g1 hca1 input hsi h1
  have hargs' := rels1 x.data.ctx x.data.ctxArgs hcx
  have e2 : Holds M c2 ↔ x.resolve.appFits L.count (ctx, ()) :=
    x.resolve.app_exact g2 hca2 (by simp [Ty.ctx, Ty.isFn]) _ _ hargs' h8
  have hta : (Ty.tuple [x.output]).isData = true := by simp [Ty.isData, Ty.isDatas, x.data.output]
  have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, v.event_data]
  have v.apply.ht : (Ty.fn [v.records, v.event] v.records).isData = true := by simp [Ty.isData, Ty.isDatas, v.records_data, v.event_data]
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
    have hres := hqc'.resolve _ (adm.ctx, ()) hargs' out c2 h8 hc2
    erw [Ty.up_fn _ _ _ x.data.ctxArgs x.data.output] at hres
    have e4 : Holds M c3 → (Holds M c4 ↔ (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩) := fun hc3 => by
      have := (x1.2 hc3 _ (FTs.dflt _) (out, ()) (rels1 x.data.output hta hres)
        (frels_of_notFn (by simp only [List.mem_singleton, forall_eq]; exact hout) _ _ _) evs c4 h10).1
      rw [this]; unfold Fun.appFits; rw [hfit]
    have e5 : Holds M c3 → Holds M c4 →
        (Holds M c5 ↔ eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩)) := fun hc3 hc4 => by
      have hoa := encode_agrees site.defs site.defs.eval (site.defs.encode L) (Defs.encode_agrees M L site.defs)
        site.body σ _ hσ oa c3 h9 hc3
      have hoa' : Rel M L _ (Ty.up _ site.ht (site.fn env).fn) oa := by
        rw [Fun.fn, Ty.up_down]; simp only [Fun.eval, Site.fn]; exact hoa
      have hevs := hoa' _ (out, ()) (rels1 x.data.output hta hres) evs c4 h10 hc4
      erw [Ty.up_fn _ _ _ hta hle] at hevs
      have hevt := (rel_term (need_ok.1 h11) _).1 hevs
      obtain ⟨sv, hS, -, hsw, hh⟩ := list_view (show Smt.Rel M L (.list v.event) (Ty.up _ hle _) evt from hevt) h12
      erw [Ty.up_list _ _ v.event_data] at hh
      exact events_exact hor happ hca _ sv hS hsw _ hh a.state hnow hrec hms h13
    rw [holds_andT, holds_andT]
    constructor
    · rintro ⟨hc3, hc4, hc5⟩
      exact ⟨e3.1 hc3, (e4 hc3).1 hc4, (e5 hc3 hc4).1 hc5⟩
    · rintro ⟨p3, p4, p5⟩
      have hc3 := e3.2 p3
      have hc4 := (e4 hc3).2 p4
      exact ⟨hc3, hc4, (e5 hc3 hc4).2 p5⟩
  have hrules : Holds M c1 → (Holds M (.ite (allT (adm.rules.map (·.2))) (andT c2 (andT c3 (andT c4 c5))) tt) ↔
      (Step.broken (x.accepts.fn (input, ())) = [] → x.resolve.appFits L.count (ctx, ()) ∧
        ((site.fn env).fits L.count).1 ∧ (site.fn env).appFits L.count ⟨x.resolve.fn (ctx, ()), ()⟩ ∧
        eventsFit L.count T a.state ((site.fn env).fn ⟨x.resolve.fn (ctx, ()), ()⟩))) := fun hc1 => by
    have hbroken := hbr hc1
    have hall : ((allT (adm.rules.map (·.2))).denote M).toBool = decide (Step.broken (x.accepts.fn (input, ())) = []) := by
      rw [toBool_allT_rules, hbroken]
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
