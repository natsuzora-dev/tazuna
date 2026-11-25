import Tazuna.Smt.InternalDispatch

/-! The cascade: the internal steps one input takes, unrolled up to `bounds.cascade`. Internal step `i` runs the own
effect at queue place `k + i` (`queueAt` over every own slot so far) when the place is occupied and no earlier internal
step faulted; each internal step's own slots join the queue, as `Step.settleFrom` walks a queue that is never popped.
A place past the bound that is occupied is `Fault.cascadeLimit`, exactly as the semantics says. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of the cascade: each internal step's flag (it runs) and terms, whether a place past the bound is
occupied, and the step terms after the last internal step, whose slots are every internal step's news and own slots. -/
structure SettleOut where
  steps : List (Term × OwnStepOut)
  over : Term
  terms : StepTerms

/-- The fault the model names: the first running internal step that faults, else the bound when a place past it is
occupied. -/
def SettleOut.fault? (M : Model) (o : SettleOut) : Option Fault :=
  match o.steps.find? fun s => (s.1.denote M).toBool && (s.2.terms.fault.denote M).toBool with
  | some s => s.2.fault? M
  | none => if (o.over.denote M).toBool then some .cascadeLimit else none

/-- Whether the cascade faults: an internal step it runs faults, or a place past the bound is occupied. -/
def SettleOut.faultT (o : SettleOut) : Term := .or o.terms.fault o.over

section
variable (L : Layout) (T : List TypeDecl)

/-- The cascade from queue place `k` with `fuel` internal steps left, over the own slots `S` and the step terms `t`
(its slots are not read): its terms, its condition (each internal step's, where it runs) and the codes' condition. -/
def encodeSettle (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (dE dP dopt : Nat)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (dflt now : Term) :
    (fuel k : Nat) → (S : List Slot) → (t : StepTerms) → Except Refusal (SettleOut × Term × Term)
  | 0, k, S, t =>
    pure (⟨[], .and (.not t.fault) (queueAt dflt S (.int k)).1, ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩⟩,
      tt, tt)
  | f + 1, k, S, t => do
    let qa := queueAt dflt S (.int k)
    let act := Term.share (.and (.not t.fault) qa.1)
    let (o, c, cx) ← encodeOwnStep L T P v shs dE dP dopt apply t.done.records now t.fresh t.done.nextId t.done.queued qa.2
      t.done.tables
    let t1 := pickTerms act o.terms ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩
    let (rest, c', cx') ← encodeSettle P v shs dE dP dopt apply dflt now f (k + 1) (S ++ t1.done.owns) t1
    pure (⟨(act, o) :: rest.steps, rest.over,
        { rest.terms with done := { rest.terms.done with news := t1.done.news ++ rest.terms.done.news,
                                                         owns := t1.done.owns ++ rest.terms.done.owns } }⟩,
      andT (.ite act c tt) c', andT cx cx')

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- What the cascade from `a` leaves when no internal step faults and the bound holds: the records, machines and fresh
counter the terms denote, the events applied, the requests `effs` started at wire ids from `a`'s next id (for
whichever pending requests the step writes for them, as the news slots hold), and the own effects `os` queued at
places from `a`'s queue length, as the own slots hold. -/
def SettleDone (M : Model) (L : Layout) (T : List TypeDecl) (hrd : v.records.isData = true)
    (shs : List (PendingShape v.event)) (a : Step.Acc v) (o : StepTerms) (r : Except Fault (Step.Acc v)) : Prop :=
  ∃ (recs : v.records.den0) (ms : List (Step.MachineState v.records v.event)) (fr : Nat) (evs : List v.event.den0)
    (effs : List (Sender × EffectV v.event)) (os : List (EffectV v.event)),
    (∀ ps, Forall2 (Step.Writes v.declared) (effs.zipIdx a.state.nextId) ps →
      r = .ok { state := { a.state with records := recs, machines := ms, fresh := fr,
                                         pending := a.state.pending ++ ps, nextId := a.state.nextId + ps.length },
                events := a.events ++ evs, out := a.out ++ ps.map Step.Pending.line, own := a.own ++ os }) ∧
    RelV L v.records (Ty.up _ hrd recs) (o.done.records.denote M) ∧ MachinesRel M L T v.machines o.done.tables ms ∧
    o.fresh.denote M = .int (fr : Int) ∧
    o.done.nextId.denote M = .int ((a.state.nextId + effs.length : Nat) : Int) ∧
    NewsRel M L shs v.declared o.done.news effs a.state.nextId ∧
    o.done.queued.denote M = .int ((a.own.length + os.length : Nat) : Int) ∧ OwnRel M L o.done.owns os a.own.length

theorem newsRel_nil {e : Ty} {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {n0 : Nat} :
    NewsRel M L shs ds [] [] n0 :=
  ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩

theorem settleFrom_none (fuel k : Nat) (a : Step.Acc v) (h : a.own[k]? = none) : Step.settleFrom T fuel k a = .ok a := by
  unfold Step.settleFrom; rw [h]

theorem writes_unique {ds : List (String × DeclaredV)} {e : Ty} :
    {xs : List ((Sender × EffectV e) × Nat)} → {ps qs : List (Step.Pending e)} →
    Forall2 (Step.Writes ds) xs ps → Forall2 (Step.Writes ds) xs qs → ps = qs
  | [], [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, ⟨⟨r, o, hr, ho, rfl⟩, h⟩, ⟨⟨r', o', hr', ho', rfl⟩, h'⟩ => by
    rw [hr] at hr'
    cases hr'
    rw [ho] at ho'
    cases ho'
    rw [writes_unique h h']
  | [], [], _ :: _, _, h | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], _, h => h.elim

theorem settle_fault_skip {act : Term} {o : OwnStepOut} {steps : List (Term × OwnStepOut)} {over : Term}
    {t t' : StepTerms} (h : ((act.denote M).toBool && (o.terms.fault.denote M).toBool) = false) :
    SettleOut.fault? M ⟨(act, o) :: steps, over, t⟩ = SettleOut.fault? M ⟨steps, over, t'⟩ := by
  simp only [SettleOut.fault?, List.find?_cons, h]

theorem fold_width (base : StepTerms) (hb : base.done.news = [] ∧ base.done.owns = []) :
    (ks : List (Term × StepTerms)) →
    (∀ kk ∈ ks, (∀ sl ∈ kk.2.done.news, sl.2.length = 2) ∧ ∀ sl ∈ kk.2.done.owns, sl.2.length = 2) →
    (∀ sl ∈ (ks.foldr (fun k t => pickTerms k.1 k.2 t) base).done.news, sl.2.length = 2) ∧
      ∀ sl ∈ (ks.foldr (fun k t => pickTerms k.1 k.2 t) base).done.owns, sl.2.length = 2
  | [], _ => by simp [hb]
  | (c, a) :: ks, hw => by
    have ih := fold_width base hb ks fun kk h => hw kk (List.mem_cons_of_mem _ h)
    have ha := hw (c, a) (by simp)
    exact ⟨width_append (width_gate c ha.1) ih.1, width_append (width_gate c ha.2) ih.2⟩

/-- The merged step terms of an own effect write slots of two items. -/
theorem encodeOwnStep_width {P : List AnySite} {shs : List (PendingShape v.event)} {dE dP dopt : Nat}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {records now fresh n q eff : Term} {xs : List Term}
    {o : OwnStepOut} {c cx : Term}
    (h : encodeOwnStep L T P v shs dE dP dopt apply records now fresh n q eff xs = .ok (o, c, cx)) :
    (∀ sl ∈ o.terms.done.news, sl.2.length = 2) ∧ ∀ sl ∈ o.terms.done.owns, sl.2.length = 2 := by
  obtain ⟨ks, hks, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hF := mapM_ok _ _ _ hks
  have := fold_width ⟨tt, ⟨records, xs, n, [], [], q⟩, fresh⟩ ⟨rfl, rfl⟩ (ks.map fun k => (k.1, k.2.2.1)) (by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    obtain ⟨⟨key', i'⟩, -, hR'⟩ := forall2_mem_right hF z hz
    obtain ⟨⟨ko', st', c', cx'⟩, hkind', hR'⟩ := bind_ok.1 hR'
    cases pure_ok.1 hR'
    exact encodeOwnKind_width hkind')
  rw [List.foldr_map] at this
  exact this

/-- Once an internal step faulted, the cascade's fault term stays true. -/
theorem settle_fault_stays {P : List AnySite} {shs : List (PendingShape v.event)} {dE dP dopt : Nat}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {dflt now : Term} :
    (fuel k : Nat) → (S : List Slot) → (t : StepTerms) → t.fault.denote M = .bool true →
    {o : SettleOut} → {c cx : Term} → encodeSettle L T P v shs dE dP dopt apply dflt now fuel k S t = .ok (o, c, cx) →
    o.terms.fault.denote M = .bool true
  | 0, _, _, _, htf, _, _, _, henc => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, -, -⟩ := henc
    exact htf
  | f + 1, k, S, t, htf, _, _, _, henc => by
    obtain ⟨⟨o1, c1, cx1⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2, cx2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hact : (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)).denote M = .bool false := by
      simp [Term.denote, htf, toBool_bool]
    have h1 : (pickTerms (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) o1.terms
        ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩).fault.denote M = .bool true := by
      simp only [pickTerms, Term.denote_share, Term.denote, hact, toBool_bool, Bool.false_eq_true, ite_false]; exact htf
    have h3 := settle_fault_stays f (k + 1) _ _ h1 h2
    exact h3

/-- T2 for the cascade: wherever the condition holds, the fault the model names is `Step.settleFrom`'s, and otherwise
the cascade runs to its end with what the terms denote (`SettleDone`). -/
theorem settle_rel {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt)) {dflt now : Term} :
    (fuel k : Nat) → (S : List Slot) → (t : StepTerms) → (a : Step.Acc v) → Step.Inv P a.state →
    Step.QueueOk P a → OwnRel M L S a.own 0 → now.denote M = .int a.state.now → t.fault.denote M = .bool false →
    RelV L v.records (Ty.up _ hrd a.state.records) (t.done.records.denote M) →
    MachinesRel M L T v.machines t.done.tables a.state.machines →
    t.fresh.denote M = .int (Int.ofNat a.state.fresh) → t.done.nextId.denote M = .int (Int.ofNat a.state.nextId) →
    t.done.queued.denote M = .int ((a.own.length : Nat) : Int) →
    {o : SettleOut} → {c cx : Term} → encodeSettle L T P v shs dE dP dopt apply dflt now fuel k S t = .ok (o, c, cx) →
    Holds M c → Holds M cx →
    o.faultT.denote M = .bool (o.fault? M).isSome ∧
    match o.fault? M with
    | some f => Step.settleFrom T fuel k a = .error f
    | none => SettleDone M L T hrd shs a o.terms (Step.settleFrom T fuel k a)
  | 0, k, S, t, a, _, _, hS, _, htf, hrec, hms, hfr, hn, hq, o, c, cx, henc, _, _ => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨rfl, rfl, rfl⟩ := henc
    have hk := queueAt_rel dflt hS (k := .int k) k (by simp [Term.denote])
    refine ⟨?_, ?_⟩
    · by_cases hlt : k < a.own.length <;>
        simp [SettleOut.faultT, SettleOut.fault?, Term.denote, htf, hk.1, toBool_bool, hlt]
    simp only [SettleOut.fault?, List.find?_nil, Term.denote, htf, hk.1, toBool_bool, Bool.not_false, Bool.true_and]
    by_cases hlt : k < a.own.length
    · simp only [hlt, decide_true, ite_true]
      unfold Step.settleFrom
      rw [List.getElem?_eq_getElem hlt]
    · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
      rw [settleFrom_none 0 k a (List.getElem?_eq_none (by omega))]
      refine ⟨a.state.records, a.state.machines, a.state.fresh, [], [], [], fun ps hps => ?_, hrec, hms, hfr,
        by simpa using hn, ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩,
        by simpa using hq, ownRel_nil _⟩
      cases ps with
      | nil => simp
      | cons => exact hps.elim
  | f + 1, k, S, t, a, hinv, hqok, hS, hnow, htf, hrec, hms, hfr, hn, hq, o, c, cx, henc, hc, hcx => by
    obtain ⟨⟨o1, c1, cx1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2, cx2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hc1', hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨hcx1, hcx2⟩ := (holds_andT _ _).1 hcx
    have hk := queueAt_rel dflt hS (k := .int k) k (by simp [Term.denote])
    have hact : (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)).denote M =
        .bool (decide (k < a.own.length)) := by
      simp [Term.denote, htf, hk.1, toBool_bool]
    have hw1 := encodeOwnStep_width h1
    by_cases hlt : k < a.own.length
    · have hact' := hact
      simp only [hlt, decide_true] at hact'
      have hc1 : Holds M c1 := by
        have := (holds_ite _ _ _).1 hc1'
        rw [hact'] at this
        simpa only [toBool_bool, ite_true] using this
      obtain ⟨hown, hreach⟩ := hqok _ (List.getElem_mem hlt)
      obtain ⟨hfault, hrun⟩ := ownStep_rel hP hvx hshs hor a hinv hcd hqd hrd hed happ hca hE hPE hopt hrec hnow hfr hn hq
        hms a.own[k] (hk.2 hlt) hown hreach h1 hc1 hcx1
      have hsem : Step.settleFrom T (f + 1) k a = (Step.runOwn T a a.own[k]) >>= Step.settleFrom T f (k + 1) := by
        exact Step.settleFrom.eq_3 T k a a.own[k] f (List.getElem?_eq_getElem hlt)
      rw [hsem]
      have hpick : ∀ x y : Term, (Term.share (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) x y)).denote M =
          x.denote M := fun x y => by simp [Term.denote, hact', toBool_bool]
      revert hrun
      cases hof : o1.fault? M with
      | some f' =>
        intro hrun
        have hft : (o1.terms.fault.denote M).toBool = true := by rw [hfault, hof]; rfl
        have hst := settle_fault_stays (L := L) (T := T) (M := M) f (k + 1) _ _
          (by simp only [pickTerms]; rw [hpick, hfault, hof]; rfl) h2
        refine ⟨?_, ?_⟩
        · simp [SettleOut.faultT, SettleOut.fault?, hact', toBool_bool, hft, hof, Term.denote, hst]
        simp only [SettleOut.fault?, List.find?_cons, hact', toBool_bool, hft, Bool.and_self, hof, hrun, bind,
          Except.bind]
      | none =>
        rintro ⟨fr, hfr1, hdone⟩
        have hff : (o1.terms.fault.denote M).toBool = false := by rw [hfault, hof]; rfl
        rw [settle_fault_skip (t' := rest.terms) (by simp [hact', hff, toBool_bool])]
        obtain ⟨recs0, ms0, evs0, effs0, os0, hr0, r1, r2, r3, r4, r5, r6⟩ := hdone
        obtain ⟨ps0, hps0⟩ := newsRel_writes r4
        have hrun0 := hr0 ps0 hps0
        rw [hrun0]
        simp only [bind, Except.bind]
        have hl0 := forall2_zipIdx_length _ _ hps0
        have hinv1 := Step.runOwn_inv T ⟨hvm, hvx⟩ a hinv _ hrun0
        have hq1 := Step.runOwn_queue T ⟨hvm, hvx⟩ a hinv hqok _ hrun0
        have hlt0 : o1.terms.done.tables.length = t.done.tables.length := by
          rw [machinesRel_length r2, machinesRel_length hms]
        have hS1 : OwnRel M L (S ++ (gateSlots (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
            o1.terms.done.owns ++ [])) (a.own ++ os0) 0 := by
          refine ownRel_append hS ?_
          have := ownRel_append (ownRel_gate (L := L) hact' r6) (ownRel_nil (a.own.length + os0.length))
          rw [List.append_nil] at this
          simpa using this
        have IH := settle_rel hP hvx hvm hshs hor hcd hqd hrd hed happ hca hE hPE hopt f (k + 1) _ _ _ hinv1 hq1 hS1
          hnow (by simp only [pickTerms]; rw [hpick, hfault, hof]; rfl)
          (by simp only [pickTerms]; rw [hpick]; exact r1)
          (by
            simp only [pickTerms]
            exact machinesRel_congr _ _ _ _ (pick_tables hact' _ _ hlt0).symm r2)
          (by simp only [pickTerms]; rw [hpick]; exact hfr1)
          (by simp only [pickTerms]; rw [hpick, r3, hl0]; rfl)
          (by simp only [pickTerms]; rw [hpick, r5]; simp)
          h2 hc2 hcx2
        obtain ⟨IHF, IH⟩ := IH
        refine ⟨by simpa [SettleOut.faultT] using IHF, ?_⟩
        revert IH
        cases rest.fault? M with
        | some f'' => exact id
        | none =>
          rintro ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, s1, s2, s3, s4, s5, s6, s7⟩
          refine ⟨recs1, ms1, fr1, evs0 ++ evs1, effs0 ++ effs1, os0 ++ os1, fun ps hps => ?_, s1, s2, s3, ?_, ?_, ?_,
            ?_⟩
          · rw [List.zipIdx_append] at hps
            obtain ⟨ps0', ps1, rfl, hps0', hps1⟩ := forall2_split _ _ hps
            obtain rfl := writes_unique hps0' hps0
            rw [hr1 ps1 (by simpa [hl0] using hps1)]
            simp [List.append_assoc, Nat.add_assoc]
          · rw [s4]; simp [hl0, Nat.add_assoc]
          · have h0 : NewsRel M L shs v.declared (gateSlots (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
                o1.terms.done.news ++ []) effs0 a.state.nextId := by
              simpa using newsRel_append (newsRel_gate (L := L) hact' r4) (newsRel_nil (L := L) (M := M))
            exact newsRel_append h0 (by simpa [hl0] using s5)
          · rw [s6]; simp [Nat.add_assoc]
          · have h0 : OwnRel M L (gateSlots (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
                o1.terms.done.owns ++ []) os0 a.own.length := by
              simpa using ownRel_append (ownRel_gate (L := L) hact' r6) (ownRel_nil (a.own.length + os0.length))
            exact ownRel_append h0 (by simpa using s7)
    · have hact' := hact
      simp only [hlt, decide_false] at hact'
      have hnone : a.own[k]? = none := List.getElem?_eq_none (by omega)
      have hnone1 : a.own[k + 1]? = none := List.getElem?_eq_none (by omega)
      rw [settleFrom_none (f + 1) k a hnone]
      have hpick : ∀ x y : Term, (Term.share (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) x y)).denote M =
          y.denote M := fun x y => by simp [Term.denote, hact', toBool_bool]
      rw [settle_fault_skip (t' := rest.terms) (by simp [hact', toBool_bool])]
      have hS1 : OwnRel M L (S ++ (gateSlots (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
          o1.terms.done.owns ++ [])) a.own 0 := by
        have := ownRel_append hS (ownRel_append (ownRel_gate_false (L := L) (e := v.event) hact' hw1.2 (0 + a.own.length))
          (ownRel_nil _))
        simpa using this
      have IH := settle_rel hP hvx hvm hshs hor hcd hqd hrd hed happ hca hE hPE hopt f (k + 1) _ _ _ hinv hqok hS1
        hnow (by simp only [pickTerms]; rw [hpick]; exact htf)
        (by simp only [pickTerms]; rw [hpick]; exact hrec)
        (by simp only [pickTerms]; exact machinesRel_congr _ _ _ _ (pick_tables_false hact' _ _).symm hms)
        (by simp only [pickTerms]; rw [hpick]; exact hfr)
        (by simp only [pickTerms]; rw [hpick]; exact hn)
        (by simp only [pickTerms]; rw [hpick]; exact hq)
        h2 hc2 hcx2
      rw [settleFrom_none f (k + 1) a hnone1] at IH
      obtain ⟨IHF, IH⟩ := IH
      refine ⟨by simpa [SettleOut.faultT] using IHF, ?_⟩
      revert IH
      cases rest.fault? M with
      | some f'' => exact id
      | none =>
        rintro ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, s1, s2, s3, s4, s5, s6, s7⟩
        refine ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, s1, s2, s3, s4, ?_, s6, ?_⟩
        · have h0 := newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := v.declared) hact' hw1.1
            a.state.nextId) (newsRel_nil (L := L) (M := M))
          exact newsRel_append h0 s5
        · have h0 := ownRel_append (ownRel_gate_false (L := L) (e := v.event) hact' hw1.2 a.own.length)
            (ownRel_nil _)
          exact ownRel_append h0 s7

/-- Whether the cascade from queue place `k` with `fuel` internal steps left fits from `a`: each internal step it runs,
until one faults. -/
def settleFits (S : Ty → Nat) (T : List TypeDecl) : Nat → Nat → Step.Acc v → Prop
  | 0, _, _ => True
  | f + 1, k, a => match a.own[k]? with
    | none => True
    | some eff => ownFits S T a.state eff ∧ ∀ a', Step.runOwn T a eff = .ok a' → settleFits S T f (k + 1) a'

/-- After a fault no internal step runs, so the cascade's condition asks for nothing. -/
theorem settle_cond_fault {P : List AnySite} {shs : List (PendingShape v.event)} {dE dP dopt : Nat}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {dflt now : Term} :
    (fuel k : Nat) → (S : List Slot) → (t : StepTerms) → t.fault.denote M = .bool true →
    {o : SettleOut} → {c cx : Term} → encodeSettle L T P v shs dE dP dopt apply dflt now fuel k S t = .ok (o, c, cx) →
    Holds M c
  | 0, _, _, _, _, _, _, _, henc => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl, -⟩ := henc
    exact holds_tt
  | f + 1, k, S, t, htf, _, _, _, henc => by
    obtain ⟨⟨o1, c1, cx1⟩, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2, cx2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have hact : (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)).denote M = .bool false := by
      simp [Term.denote, htf, toBool_bool]
    rw [holds_andT]
    refine ⟨by rw [holds_ite, hact]; exact holds_tt, settle_cond_fault f (k + 1) _ _ ?_ h2⟩
    simp only [pickTerms, Term.denote_share, Term.denote, hact, toBool_bool, Bool.false_eq_true, ite_false]
    exact htf

/-- The cascade's condition is exact: it holds exactly when every internal step the cascade runs fits
(`settleFits`). -/
theorem settle_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    (hvm : ∀ m ∈ v.machines, m.Reach P) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hcd : ∀ x ∈ v.commands, CommandData x) (hqd : ∀ x ∈ v.queries, QueryData x)
    (hqout : ∀ x ∈ v.queries, x.output.isFn = false)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt)) {dflt now : Term} :
    (fuel k : Nat) → (S : List Slot) → (t : StepTerms) → (a : Step.Acc v) → Step.Inv P a.state →
    Step.QueueOk P a → OwnRel M L S a.own 0 → now.denote M = .int a.state.now → t.fault.denote M = .bool false →
    RelV L v.records (Ty.up _ hrd a.state.records) (t.done.records.denote M) →
    MachinesRel M L T v.machines t.done.tables a.state.machines →
    t.fresh.denote M = .int (Int.ofNat a.state.fresh) → t.done.nextId.denote M = .int (Int.ofNat a.state.nextId) →
    t.done.queued.denote M = .int ((a.own.length : Nat) : Int) →
    {o : SettleOut} → {c cx : Term} → encodeSettle L T P v shs dE dP dopt apply dflt now fuel k S t = .ok (o, c, cx) →
    Holds M cx → (Holds M c ↔ settleFits L.count T fuel k a)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, henc, _ => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl, -⟩ := henc
    exact iff_of_true holds_tt trivial
  | f + 1, k, S, t, a, hinv, hqok, hS, hnow, htf, hrec, hms, hfr, hn, hq, o, c, cx, henc, hcx => by
    obtain ⟨⟨o1, c1, cx1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2, cx2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hcx1, hcx2⟩ := (holds_andT _ _).1 hcx
    have hk := queueAt_rel dflt hS (k := .int k) k (by simp [Term.denote])
    have hact : (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)).denote M =
        .bool (decide (k < a.own.length)) := by
      simp [Term.denote, htf, hk.1, toBool_bool]
    have hw1 := encodeOwnStep_width h1
    rw [holds_andT]
    by_cases hlt : k < a.own.length
    · have hact' := hact
      simp only [hlt, decide_true] at hact'
      obtain ⟨hown, hreach⟩ := hqok _ (List.getElem_mem hlt)
      have e1 := ownStep_exact hP hvx hvm hshs hor a hcd hqd hqout hrd hed happ hca hE hPE hopt hrec hnow hfr hn hq hms
        a.own[k] (hk.2 hlt) hown hreach h1 hcx1
      have hite : Holds M (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) c1 tt) ↔ Holds M c1 := by
        rw [holds_ite, hact']; simp only [toBool_bool, ite_true]
      simp only [settleFits, List.getElem?_eq_getElem hlt]
      rw [hite, e1]
      have hpick : ∀ x y : Term, (Term.share (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) x y)).denote M =
          x.denote M := fun x y => by simp [Term.denote, hact', toBool_bool]
      have tail : Holds M c1 → (Holds M c2 ↔ ∀ a', Step.runOwn T a a.own[k] = .ok a' → settleFits L.count T f (k + 1) a') := by
        intro hc1
        obtain ⟨hfault, hrun⟩ := ownStep_rel hP hvx hshs hor a hinv hcd hqd hrd hed happ hca hE hPE hopt hrec hnow hfr hn hq
          hms a.own[k] (hk.2 hlt) hown hreach h1 hc1 hcx1
        revert hrun
        cases hof : o1.fault? M with
        | some f' =>
          intro hrun
          refine iff_of_true (settle_cond_fault f (k + 1) _ _ ?_ h2) (fun a' h => by rw [hrun] at h; cases h)
          simp only [pickTerms]; rw [hpick, hfault, hof]; rfl
        | none =>
          rintro ⟨fr, hfr1, hdone⟩
          obtain ⟨recs0, ms0, evs0, effs0, os0, hr0, r1, r2, r3, r4, r5, r6⟩ := hdone
          obtain ⟨ps0, hps0⟩ := newsRel_writes r4
          have hrun0 := hr0 ps0 hps0
          have hl0 := forall2_zipIdx_length _ _ hps0
          have hinv1 := Step.runOwn_inv T ⟨hvm, hvx⟩ a hinv _ hrun0
          have hq1 := Step.runOwn_queue T ⟨hvm, hvx⟩ a hinv hqok _ hrun0
          have hlt0 : o1.terms.done.tables.length = t.done.tables.length := by
            rw [machinesRel_length r2, machinesRel_length hms]
          have hS1 : OwnRel M L (S ++ (gateSlots (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
              o1.terms.done.owns ++ [])) (a.own ++ os0) 0 := by
            refine ownRel_append hS ?_
            have := ownRel_append (ownRel_gate (L := L) hact' r6) (ownRel_nil (a.own.length + os0.length))
            rw [List.append_nil] at this
            simpa using this
          rw [settle_exact hP hvx hvm hshs hor hcd hqd hqout hrd hed happ hca hE hPE hopt f (k + 1) _ _ _ hinv1 hq1 hS1
            hnow (by simp only [pickTerms]; rw [hpick, hfault, hof]; rfl)
            (by simp only [pickTerms]; rw [hpick]; exact r1)
            (by
              simp only [pickTerms]
              exact machinesRel_congr _ _ _ _ (pick_tables hact' _ _ hlt0).symm r2)
            (by simp only [pickTerms]; rw [hpick]; exact hfr1)
            (by simp only [pickTerms]; rw [hpick, r3, hl0]; rfl)
            (by simp only [pickTerms]; rw [hpick, r5]; simp)
            h2 hcx2]
          constructor
          · intro h a' ha'
            rw [hrun0] at ha'
            cases ha'
            exact h
          · intro h
            exact h _ hrun0
      constructor
      · rintro ⟨hc1, hc2⟩
        exact ⟨hc1, (tail (e1.2 hc1)).1 hc2⟩
      · rintro ⟨hc1, h⟩
        exact ⟨hc1, (tail (e1.2 hc1)).2 h⟩
    · have hact' := hact
      simp only [hlt, decide_false] at hact'
      have hnone : a.own[k]? = none := List.getElem?_eq_none (by omega)
      have hnone1 : a.own[k + 1]? = none := List.getElem?_eq_none (by omega)
      have hpick : ∀ x y : Term, (Term.share (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) x y)).denote M =
          y.denote M := fun x y => by simp [Term.denote, hact', toBool_bool]
      have hS1 : OwnRel M L (S ++ (gateSlots (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
          o1.terms.done.owns ++ [])) a.own 0 := by
        have := ownRel_append hS (ownRel_append (ownRel_gate_false (L := L) (e := v.event) hact' hw1.2 (0 + a.own.length))
          (ownRel_nil _))
        simpa using this
      have e2 := settle_exact hP hvx hvm hshs hor hcd hqd hqout hrd hed happ hca hE hPE hopt f (k + 1) _ _ _ hinv hqok hS1
        hnow (by simp only [pickTerms]; rw [hpick]; exact htf)
        (by simp only [pickTerms]; rw [hpick]; exact hrec)
        (by simp only [pickTerms]; exact machinesRel_congr _ _ _ _ (pick_tables_false hact' _ _).symm hms)
        (by simp only [pickTerms]; rw [hpick]; exact hfr)
        (by simp only [pickTerms]; rw [hpick]; exact hn)
        (by simp only [pickTerms]; rw [hpick]; exact hq)
        h2 hcx2
      have hf2 : settleFits L.count T f (k + 1) a := by
        cases f with
        | zero => trivial
        | succ f => simp only [settleFits, hnone1]
      simp only [settleFits, hnone]
      exact iff_of_true ⟨by rw [holds_ite, hact']; exact holds_tt, e2.2 hf2⟩ trivial

end

end Tazuna.Smt
