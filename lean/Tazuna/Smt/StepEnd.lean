import Tazuna.Smt.Cascade

/-! How a step that applies events ends, as `Step.finish` says: the cascade runs the own commands and queries the
events queued (`encodeSettle`), every request the events and the internal steps start is written into the pending table
in one pass, and the service's and every machine's invariants are checked on the state the cascade leaves. The step
kinds differ only in what comes before (`events_done` for a list of events). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of a step's end: the cascade, the new pending table, and the invariants and instance checks on the state
the cascade leaves. -/
structure FinishOut where
  settle : SettleOut
  pending : Term
  invariants : List (Term × Term)
  checks : List (List InstCheck)

section
variable (L : Layout) (T : List TypeDecl)

/-- A step's end after the events loop `o`, from the pending table term the step began with: its terms, its condition
and the codes' condition. The pending write and the invariants are asked only where the cascade does not fault, since
the step then leaves the state it began with. -/
def encodeFinish (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (inv : Code (Ty.fn [v.records] Ty.rules))
    (now fresh pending : Term) (o : EventsOut) : Except Refusal (FinishOut × Term × Term) := do
  -- Without an effect datatype nothing is ever queued, so no internal step reads the default.
  let dflt := (effectDefault L v.event).getD tt
  let (so, cs, cx) ← encodeSettle L T P v shs dE dP dopt apply dflt now v.bounds.cascade.toNat 0 o.owns
    ⟨.bool false, o, fresh⟩
  let (pT, cp) ← encodePending L shs pending (o.news ++ so.terms.done.news)
  let (rules, ci) ← encodeInvariants L inv so.terms.done.records
  let (checks, ck) ← encodeInstChecks L T v.machines so.terms.done.tables so.terms.done.records now
  pure (⟨so, pT, rules, checks⟩, andT cs (.ite so.faultT tt (andT cp (andT ci ck))), cx)

/-- The terms of an event step: the event the subscription wraps the value into, what the events loop over it leaves,
and the step's end. -/
structure EventOut where
  event : Term
  after : EventsOut
  finish : FinishOut

/-- An event step's terms, its condition and the codes' condition, from the subscription's and the service's codes
and the terms of the state and the received value. -/
def encodeEvent (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    {i : Fin v.subscribes.length} (ec : EventCode v i) (records now fresh nextId pending : Term) (xs : List Term)
    (value : Term) : Except Refusal (EventOut × Term × Term) := do
  let (et, cw) ← encodeWrap ec value
  let (o, c) ← encodeEvents L T v shs dE dP dopt ec.apply now [(tt, [et])] records xs nextId (.int 0)
  let (fo, cf, cx) ← encodeFinish L T P v shs dE dP dopt ec.apply ec.invariants now fresh pending o
  pure (⟨et, o, fo⟩, andT cw (andT c cf), cx)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- What a step's end terms say of its result `r`, from the step in progress `a` before its events: the cascade's
fault, else the first broken invariant (the service's, then each machine's instances in key order), else the outcome
with the records, machines and fresh counter the terms denote, the requests `ps` written at the next wire ids and
sent, and the pending table and next id terms denoting what follows (pending as a multiset). A fault leaves `s0`. -/
def Finished (M : Model) (L : Layout) (T : List TypeDecl) (hrd : v.records.isData = true)
    (shs : List (PendingShape v.event)) (fo : FinishOut) (s0 : State v) (a : Step.Acc v) (outcome : Outcome)
    (r : Result v) : Prop :=
  match fo.settle.fault? M with
  | some f => r = ⟨s0, .fault f, [], []⟩
  | none => match brokenIn M fo.invariants ++ checksBroken L T M v.machines fo.checks with
    | n :: _ => r = ⟨s0, .fault (.invariant n), [], []⟩
    | [] => ∃ (recs : v.records.den0) (ms : List (Step.MachineState v.records v.event)) (fr : Nat)
        (evs : List v.event.den0) (ps : List (Step.Pending v.event)),
        r = ⟨{ a.state with records := recs, machines := ms, fresh := fr, pending := a.state.pending ++ ps,
                            nextId := a.state.nextId + ps.length },
              outcome, a.events ++ evs, a.out ++ ps.map Step.Pending.line⟩ ∧
        RelV L v.records (Ty.up _ hrd recs) (fo.settle.terms.done.records.denote M) ∧
        MachinesRel M L T v.machines fo.settle.terms.done.tables ms ∧
        fo.settle.terms.fresh.denote M = .int (fr : Int) ∧
        fo.settle.terms.done.nextId.denote M = .int ((a.state.nextId + ps.length : Nat) : Int) ∧
        ∃ ps', ps'.Perm (a.state.pending ++ ps) ∧ PendingRel L shs (fo.pending.denote M) ps'

/-- The events loop from a step in progress with an empty queue: what it leaves, in the form the cascade continues. -/
theorem events_done {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hap : (Ty.fn [v.records, v.event] v.records).isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} (happ : Smt.Rel M L _ (Ty.up _ hap v.apply.fn) apply)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    (a : Step.Acc v) (hown : a.own = []) {now : Term} (hnow : now.denote M = .int a.state.now)
    {S : List Slot} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = 1)
    {evs : List v.event.den0} (hev : Holds2 (EBag L v.event) (evs.map (Ty.up _ hed)) sv)
    {records : Term} (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    {xs : List Term} (hms : MachinesRel M L T v.machines xs a.state.machines)
    {n fresh : Term} (hn : n.denote M = .int (Int.ofNat a.state.nextId))
    (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    {o : EventsOut} {c : Term} (henc : encodeEvents L T v shs dE dP dopt apply now S records xs n (.int 0) = .ok (o, c))
    (hc : Holds M c) :
    SettleDone M L T hrd shs a ⟨.bool false, o, fresh⟩ (Step.applyEvents T a evs) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, hr⟩ := loop_apply (q := .int 0) (q0 := 0) hP hvx hshs hor hrd hed hap happ hE hPE hopt
    hvm a hnow hS hw hev hrec hms hn rfl henc hc
  refine ⟨_, _, a.state.fresh, evs, Step.reqsOf (Step.reactAll T a.state evs).2,
    Step.queuedOf (Step.reactAll T a.state evs).2, fun ps hps => ?_, r1, r2, hfresh, r3, r4, by simpa [hown] using r5,
    by simpa [hown] using r6⟩
  rw [hr ps hps]
  have hl := forall2_zipIdx_length _ _ hps
  have hk := Step.reactAll_keeps T a.state evs
  simp only [Step.Acc.wrote, Step.Acc.queued, hl, Step.reactAll_pending, hown, List.nil_append]
  rw [hk]

/-- T2 for a step's end: wherever the conditions hold, the result `Step.finish` gives for the result `r` of the step's
events is what the terms say (`Finished`). -/
theorem finish_rel {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci0 : Term} (hinvc : v.invariants.code L = .ok (inv, ci0))
    (hci0 : Holds M ci0)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    (s0 : State v) (outcome : Outcome) (a : Step.Acc v) (hown : a.own = []) (hinv : Step.Inv P a.state)
    {now fresh pending : Term} (hnow : now.denote M = .int a.state.now)
    (hpend : PendingRel L shs (pending.denote M) a.state.pending)
    {o : EventsOut} {r : Except Fault (Step.Acc v)} (hdone : SettleDone M L T hrd shs a ⟨.bool false, o, fresh⟩ r)
    (hr : ∀ a1, r = .ok a1 → Step.Inv P a1.state ∧ Step.QueueOk P a1)
    {fo : FinishOut} {c cx : Term}
    (henc : encodeFinish L T P v shs dE dP dopt apply inv now fresh pending o = .ok (fo, c, cx))
    (hc : Holds M c) (hcx : Holds M cx) :
    Finished M L T hrd shs fo s0 a outcome (Step.finish T s0 r outcome) := by
  obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, e1, e2, e3, e4, e5, e6, e7⟩ := hdone
  obtain ⟨ps1, hps1⟩ := newsRel_writes e5
  have hl1 := forall2_zipIdx_length _ _ hps1
  have hra := hr1 ps1 hps1
  obtain ⟨hinv1, hq1⟩ := hr _ hra
  obtain ⟨⟨so, cs, cx'⟩, hset, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨pT, cp⟩, hpe, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rules, ci⟩, hi, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, ck⟩, hck, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hcs, hrest⟩ := (holds_andT _ _).1 hc
  have hfd : (Ty.fn [v.records] Ty.rules).isData = true := by
    simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hrd]
  have hinvR := v.invariants.code_fn hfd hinvc hci0
  obtain ⟨hF, hm⟩ := settle_rel hP hvx hvm hshs hor hcd hqd hrd hed happ hca hE hPE hopt
    v.bounds.cascade.toNat 0 o.owns ⟨.bool false, o, fresh⟩ _ hinv1 hq1 (by simpa [hown] using e7) hnow rfl e1 e2 e3
    (by rw [e4, ← hl1]; rfl) (by simpa [hown] using e6) hset hcs hcx
  unfold Finished Step.finish
  rw [hra]
  simp only [bind, Except.bind]
  rw [Step.settle_eq_from]
  revert hm
  cases hfo : so.fault? M with
  | some f =>
    intro hm
    simp only at hm
    rw [hm]
    rfl
  | none =>
    intro hm
    obtain ⟨recs2, ms2, fr2, evs2, effs2, os2, hr2, f1, f2, f3, f4, f5, -, -⟩ := hm
    obtain ⟨ps2, hps2⟩ := newsRel_writes f5
    have hl2 := forall2_zipIdx_length _ _ hps2
    rw [hr2 ps2 hps2]
    simp only [Except.map]
    have hFf : so.faultT.denote M = .bool false := by rw [hF, hfo]; rfl
    obtain ⟨hcp, hci, hck'⟩ : Holds M cp ∧ Holds M ci ∧ Holds M ck := by
      have := (holds_ite _ _ _).1 hrest
      rw [hFf] at this
      simp only [toBool_bool, Bool.false_eq_true, ite_false] at this
      rw [holds_andT, holds_andT] at this
      exact this
    have hnews : NewsRel M L shs v.declared (o.news ++ so.terms.done.news) (effs1 ++ effs2) a.state.nextId :=
      newsRel_append e5 (by simpa [hl1] using f5)
    obtain ⟨sv, zs, hS, hw, hh, xs, hp, hq⟩ := hnews
    obtain ⟨ps, hps, ps', hperm, hrelP⟩ := pending_rel hpend hinv.below hinv.nodup hS hw hh hp hq hpe hcp
    rw [List.zipIdx_append] at hps
    obtain ⟨ps1', ps2', rfl, hps1', hps2'⟩ := forall2_split _ _ hps
    obtain rfl := writes_unique hps1 hps1'
    obtain rfl := writes_unique hps2 (by simpa [hl1] using hps2')
    have hb := invariants_rel v.invariants hrd hfd hinvR recs2 f1 hi hci
    have hbs := instChecks_rel recs2 a.state.now hrd f1 hnow v.machines _ _ f2 (fun m hm => (hor m hm).2) hck hck'
    have hinvs : Step.invariants ({ a.state with records := recs2, machines := ms2, fresh := fr2,
                                                 pending := a.state.pending ++ ps1 ++ ps2,
                                                 nextId := a.state.nextId + ps1.length + ps2.length } : State v) =
        brokenIn M rules ++ checksBroken L T M v.machines checks := by
      simp only [Step.invariants]
      rw [hb, hbs]
      rfl
    simp only [List.append_assoc, Nat.add_assoc] at hinvs ⊢
    rw [hl1, hl2] at hinvs ⊢
    rw [hinvs]
    cases brokenIn M rules ++ checksBroken L T M v.machines checks with
    | cons n ns => rfl
    | nil =>
      refine ⟨recs2, ms2, fr2, evs1 ++ evs2, ps1 ++ ps2, ?_, f1, f2, f3, ?_, ps', by simpa using hperm, hrelP⟩
      · simp [hl1, hl2]
      · rw [f4]; simp [hl1, hl2, Nat.add_assoc]

/-- Whether a step's end fits, for the result `r` of its events: the internal steps the cascade runs
(`settleFits`) and, where it does not fault, every pending request in the pending table and the service's and every
machine's invariants on the state it leaves. -/
def finishFits (S : Ty → Nat) (T : List TypeDecl) (shs : List (PendingShape v.event)) (r : Except Fault (Step.Acc v)) :
    Prop :=
  ∀ a1, r = .ok a1 → settleFits S T v.bounds.cascade.toNat 0 a1 ∧
    ∀ a2, Step.settleFrom T v.bounds.cascade.toNat 0 a1 = .ok a2 →
      a2.state.pending.length ≤ S (pendingTable shs) ∧ v.invariants.appFits S (a2.state.records, ()) ∧
      instChecksFit S a2.state.records a2.state.now a2.state.machines

/-- A step's end condition is exact: it holds exactly when the step's end fits (`finishFits`). -/
theorem finish_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci0 : Term} (hinvc : v.invariants.code L = .ok (inv, ci0))
    (hci0 : Holds M ci0)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    (a : Step.Acc v) (hown : a.own = [])
    {now fresh pending : Term} (hnow : now.denote M = .int a.state.now)
    (hpend : PendingRel L shs (pending.denote M) a.state.pending)
    {o : EventsOut} {r : Except Fault (Step.Acc v)} (hdone : SettleDone M L T hrd shs a ⟨.bool false, o, fresh⟩ r)
    (hr : ∀ a1, r = .ok a1 → Step.Inv P a1.state ∧ Step.QueueOk P a1)
    {fo : FinishOut} {c cx : Term}
    (henc : encodeFinish L T P v shs dE dP dopt apply inv now fresh pending o = .ok (fo, c, cx))
    (hcx : Holds M cx) :
    Holds M c ↔ finishFits L.count T shs r := by
  obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, e1, e2, e3, e4, e5, e6, e7⟩ := hdone
  obtain ⟨ps1, hps1⟩ := newsRel_writes e5
  have hl1 := forall2_zipIdx_length _ _ hps1
  have hra := hr1 ps1 hps1
  revert hra
  generalize hA : ({ state := { a.state with records := recs1, machines := ms1, fresh := fr1,
                                             pending := a.state.pending ++ ps1, nextId := a.state.nextId + ps1.length },
                     events := a.events ++ evs1, out := a.out ++ ps1.map Step.Pending.line,
                     own := a.own ++ os1 } : Step.Acc v) = a1
  intro hra
  obtain ⟨hinv1, hq1⟩ := hr _ hra
  obtain ⟨⟨so, cs, cx'⟩, hset, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨pT, cp⟩, hpe, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rules, ci⟩, hi, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, ck⟩, hck, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hS1 : OwnRel M L o.owns a1.own 0 := by rw [← hA]; simpa [hown] using e7
  have hn1 : o.nextId.denote M = .int (Int.ofNat a1.state.nextId) := by rw [← hA, e4, ← hl1]; rfl
  have hq1' : o.queued.denote M = .int ((a1.own.length : Nat) : Int) := by rw [← hA]; simpa [hown] using e6
  have e1' : RelV L v.records (Ty.up _ hrd a1.state.records) (o.records.denote M) := by rw [← hA]; exact e1
  have e2' : MachinesRel M L T v.machines o.tables a1.state.machines := by rw [← hA]; exact e2
  have e3' : fresh.denote M = .int (Int.ofNat a1.state.fresh) := by rw [← hA]; exact e3
  have hnow1 : now.denote M = .int a1.state.now := by rw [← hA]; exact hnow
  have es := settle_exact hP hvx hvm hshs hor hcd hqd hqout hrd hed happ hca hE hPE hopt
    v.bounds.cascade.toNat 0 o.owns ⟨.bool false, o, fresh⟩ _ hinv1 hq1 hS1 hnow1 rfl e1' e2' e3' hn1 hq1' hset hcx
  have hrel := fun hcs : Holds M cs => settle_rel hP hvx hvm hshs hor hcd hqd hrd hed happ hca hE hPE hopt
    v.bounds.cascade.toNat 0 o.owns ⟨.bool false, o, fresh⟩ _ hinv1 hq1 hS1 hnow1 rfl e1' e2' e3' hn1 hq1' hset hcs hcx
  have hfits : finishFits L.count T shs r ↔ settleFits L.count T v.bounds.cascade.toNat 0 a1 ∧
      ∀ a2, Step.settleFrom T v.bounds.cascade.toNat 0 a1 = .ok a2 →
        a2.state.pending.length ≤ L.count (pendingTable shs) ∧ v.invariants.appFits L.count (a2.state.records, ()) ∧
        instChecksFit L.count a2.state.records a2.state.now a2.state.machines := by
    rw [hra]
    exact ⟨fun h => h _ rfl, fun h a1 e => by cases e; exact h⟩
  rw [hfits, holds_andT]
  have key : ∀ hcs : Holds M cs, (Holds M (.ite so.faultT tt (andT cp (andT ci ck))) ↔
      ∀ a2, Step.settleFrom T v.bounds.cascade.toNat 0 a1 = .ok a2 →
        a2.state.pending.length ≤ L.count (pendingTable shs) ∧ v.invariants.appFits L.count (a2.state.records, ()) ∧
        instChecksFit L.count a2.state.records a2.state.now a2.state.machines) := by
    intro hcs
    obtain ⟨hF, hm⟩ := hrel hcs
    revert hm
    cases hfo : so.fault? M with
    | some f =>
      intro hm
      have hFt : so.faultT.denote M = .bool true := by rw [hF, hfo]; rfl
      rw [holds_ite, hFt]
      simp only [toBool_bool, ite_true]
      refine iff_of_true holds_tt fun a2 h => ?_
      simp only at hm
      rw [hm] at h
      cases h
    | none =>
      intro hm
      subst hA
      have hFf : so.faultT.denote M = .bool false := by rw [hF, hfo]; rfl
      rw [holds_ite, hFf]
      simp only [toBool_bool, Bool.false_eq_true, ite_false]
      obtain ⟨recs2, ms2, fr2, evs2, effs2, os2, hr2, f1, f2, f3, f4, f5, -, -⟩ := hm
      obtain ⟨ps2, hps2⟩ := newsRel_writes f5
      have hl2 := forall2_zipIdx_length _ _ hps2
      have hnews : NewsRel M L shs v.declared (o.news ++ so.terms.done.news) (effs1 ++ effs2) a.state.nextId :=
        newsRel_append e5 (by simpa [hl1] using f5)
      obtain ⟨sv, zs, hS, hw, hh, xs, hp, hq⟩ := hnews
      have ep := pending_exact hpend hS hw hh hp hq hpe
      have ei := invariants_exact v.invariants hrd hinvc hci0 recs2 f1 hi
      have ek := instChecks_exact recs2 _ hrd f1 hnow v.machines _ _ f2 hck
      have hall : ∀ a2, Step.settleFrom T v.bounds.cascade.toNat 0 _ = .ok a2 ↔ a2 = _ := fun a2 => by
        rw [hr2 ps2 hps2]; exact ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩
      simp only [hall, forall_eq]
      rw [holds_andT, holds_andT, ep, ei, ek]
      simp [hl1, hl2]
  constructor
  · rintro ⟨hcs, hrest⟩
    exact ⟨es.1 hcs, (key hcs).1 hrest⟩
  · rintro ⟨hsf, hrest⟩
    have hcs := es.2 hsf
    exact ⟨hcs, (key hcs).2 hrest⟩

/-- The machines of a state that keeps the step invariant reach the program's sites. -/
theorem _root_.Tazuna.Ir.Step.Inv.machinesReach {P : List AnySite} {s : State v} (hinv : Step.Inv P s) : ∀ m ∈ v.machines, m.Reach P := by
  intro m hm
  rw [← hinv.machinesOf] at hm
  obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 hm
  exact hinv.machines sm hsm

/-- What `events_done` asks of a list of events' result besides the terms: the step invariant and a queue of own
effects that reach the program, which `applyEvents` keeps. -/
theorem applyEvents_ok {P : List AnySite} (hvx : ∀ x ∈ v.reactions, x.Reach P) (a : Step.Acc v) (hown : a.own = [])
    (hinv : Step.Inv P a.state) (evs : List v.event.den0) :
    ∀ a1, Step.applyEvents T a evs = .ok a1 → Step.Inv P a1.state ∧ Step.QueueOk P a1 := fun _ h =>
  ⟨Step.applyEvents_inv T ⟨hinv.machinesReach, hvx⟩ evs a hinv h,
    Step.applyEvents_queue T ⟨hinv.machinesReach, hvx⟩ evs a h hinv (by simp [Step.QueueOk, hown])⟩

/-- T2 for an event: the events loop over the one slot holding the wrapped value, then the step's end. -/
theorem event_step {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce) {records sv now nextIdT fresh pending : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    {et cw : Term} (hwr : encodeWrap ec sv = .ok (et, cw)) (hcw : Holds M cw)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : EventsOut} {c : Term}
    (henc : encodeEvents L T v shs dE dP dopt ec.apply now [(tt, [et])] records xs nextIdT (.int 0) = .ok (o, c))
    (hc : Holds M c) {fo : FinishOut} {cf cx : Term}
    (hf : encodeFinish L T P v shs dE dP dopt ec.apply ec.invariants now fresh pending o = .ok (fo, cf, cx))
    (hcf : Holds M cf) (hcx : Holds M cx) :
    Finished M L T hd.records shs fo s { state := s } .accepted (step T v s (.event i value)) := by
  have he := EventCode.rel_of hd hec hce
  have hevT := wrap_rel i value hd he hsv hwr hcw
  obtain ⟨⟨a, c1⟩, g1, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2⟩, -, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3⟩, g3, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  obtain ⟨hc1, -, hc3⟩ : Holds M c1 ∧ Holds M c2 ∧ Holds M c3 := by
    rw [holds_andT, holds_andT] at hce; exact hce
  have hdone := events_done (T := T) hP hvx hinv.machinesReach hshs hor hd.records hd.event hd.apply he.apply hE hPE
    hopt { state := s } rfl hnow (S := [(tt, [et])]) (sv := [(true, [et.denote M])]) ⟨rfl, rfl, trivial⟩ (by simp)
    (evs := [(v.subscribes.get i).wrap.fn (value, ())]) ⟨⟨_, rfl, hevT⟩, trivial⟩ hrec hms hnid hfresh henc hc
  exact finish_rel hP hvx hinv.machinesReach hshs hor hcd hqd hd.records hd.event g1 hc1 g3 hc3 hE hPE hopt s
    .accepted { state := s } rfl hinv hnow hpend hdone (applyEvents_ok hvx _ rfl hinv _) hf hcf hcx

/-- `event_step`'s conditions are exact together: they hold exactly when the kept sources fit, the wrap fits at the
value, the event's applications fit (`eventsFit`), and the step's end fits (`finishFits`). -/
theorem event_step_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) {records sv now nextIdT fresh pending : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    {et cw : Term} (hwr : encodeWrap ec sv = .ok (et, cw))
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : EventsOut} {c : Term}
    (henc : encodeEvents L T v shs dE dP dopt ec.apply now [(tt, [et])] records xs nextIdT (.int 0) = .ok (o, c))
    {fo : FinishOut} {cf cx : Term}
    (hf : encodeFinish L T P v shs dE dP dopt ec.apply ec.invariants now fresh pending o = .ok (fo, cf, cx))
    (hcx : Holds M cx) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    Holds M (andT ce (andT cw (andT c cf))) ↔
      ((v.apply.fits L.count).1 ∧ ((v.subscribes.get i).wrap.fits L.count).1 ∧ (v.invariants.fits L.count).1) ∧
      (v.subscribes.get i).wrap.appFits L.count (value, ()) ∧ eventsFit L.count T s [ev] ∧
      finishFits L.count T shs (Step.applyEvents T { state := s } [ev]) := by
  intro ev
  have e0 := eventCode_exact (M := M) hec
  have e1 : ∀ hce : Holds M ce, (Holds M cw ↔ (v.subscribes.get i).wrap.appFits L.count (value, ())) :=
    fun hce => wrap_exact i value hd hec hce hsv hwr
  obtain ⟨⟨a, c1'⟩, g1, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2'⟩, g2, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3'⟩, g3, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  have hevT : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw),
      RelV L v.event (Ty.up _ hd.event ev) (et.denote M) := fun hce hcw =>
    wrap_rel i value hd (EventCode.rel_of hd hec hce) hsv hwr hcw
  have e2 : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw), (Holds M c ↔ eventsFit L.count T s [ev]) :=
    fun hce hcw => events_exact (fun m hm => (hor m hm).1) hd.records hd.event g1 ((holds_andT _ _).1 hce).1
      [(tt, [et])] [(true, [et.denote M])] ⟨rfl, rfl, trivial⟩ (by simp) [ev] ⟨⟨_, rfl, hevT hce hcw⟩, trivial⟩ s hnow
      hrec hms henc
  have e3 : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw) (hc : Holds M c),
      (Holds M cf ↔ finishFits L.count T shs (Step.applyEvents T { state := s } [ev])) := fun hce hcw hc => by
    have he := EventCode.rel_of hd hec hce
    obtain ⟨hc1, -, hc3⟩ : Holds M c1' ∧ Holds M c2' ∧ Holds M c3' := by
      rw [holds_andT, holds_andT] at hce; exact hce
    have hdone := events_done (T := T) hP hvx hinv.machinesReach hshs hor hd.records hd.event hd.apply he.apply hE
      hPE hopt { state := s } rfl hnow (S := [(tt, [et])]) (sv := [(true, [et.denote M])]) ⟨rfl, rfl, trivial⟩ (by simp)
      (evs := [ev]) ⟨⟨_, rfl, hevT hce hcw⟩, trivial⟩ hrec hms hnid hfresh henc hc
    exact finish_exact hP hvx hinv.machinesReach hshs hor hcd hqd hqout hd.records hd.event g1 hc1 g3 hc3 hE hPE hopt
      { state := s } rfl hnow hpend hdone (applyEvents_ok hvx _ rfl hinv _) hf hcx
  rw [holds_andT (andT c1' (andT c2' c3')), holds_andT cw, holds_andT c]
  constructor
  · rintro ⟨hce, hcw, hc, hcf⟩
    exact ⟨e0.1 hce, (e1 hce).1 hcw, (e2 hce hcw).1 hc, (e3 hce hcw hc).1 hcf⟩
  · rintro ⟨p0, p1, p2, p3⟩
    have hce := e0.2 p0
    have hcw := (e1 hce).2 p1
    have hc := (e2 hce hcw).2 p2
    exact ⟨hce, hcw, hc, (e3 hce hcw hc).2 p3⟩

/-- An event step's condition is exact and gives T2: where the codes' conditions hold, it holds exactly when the wrap
fits at the value, the event's applications fit and the step's end fits, and then the step ends as the end terms
say. -/
theorem event_encode {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce) {records sv now nextIdT fresh pending : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : EventOut} {c cx : Term}
    (henc : encodeEvent L T P v shs dE dP dopt ec records now fresh nextIdT pending xs sv = .ok (o, c, cx))
    (hcx : Holds M cx) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    (Holds M c ↔ (v.subscribes.get i).wrap.appFits L.count (value, ()) ∧ eventsFit L.count T s [ev] ∧
      finishFits L.count T shs (Step.applyEvents T { state := s } [ev])) ∧
    (Holds M c → Finished M L T hd.records shs o.finish s { state := s } .accepted (step T v s (.event i value))) := by
  obtain ⟨⟨et, cw⟩, hwr, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨eo, ce'⟩, hev, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cx'⟩, hf, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hx := event_step_exact hP hvx hshs hor hcd hqd hqout s hinv i value hd hec hrec hsv hnow hnid hfresh hpend hms hwr
    hE hPE hopt hev hf hcx
  simp only [holds_andT ce, hce, true_and, (eventCode_exact (M := M) hec).1 hce] at hx
  refine ⟨hx, fun hc => ?_⟩
  obtain ⟨hcw, hc', hcf⟩ : Holds M cw ∧ Holds M ce' ∧ Holds M cf := by rw [holds_andT, holds_andT] at hc; exact hc
  exact event_step hP hvx hshs hor hcd hqd s hinv i value hd hec hce hrec hsv hnow hnid hfresh hpend hms hwr hcw hE hPE
    hopt hev hc' hf hcf hcx

end

end Tazuna.Smt
