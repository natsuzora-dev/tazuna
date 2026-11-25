import Tazuna.Smt.InternalDispatch

/-! The cascade: the internal steps one input takes, unrolled up to `bounds.cascade`. Internal step `i` runs the own
effect at queue place `k + i` (`queueAt` over every own slot so far) when the place is occupied and no earlier internal
step faulted; each internal step's own slots join the queue, as `Step.settleFrom` walks a queue that is never popped.
A place past the bound that is occupied is `Fault.cascadeLimit`, exactly as the semantics says. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of the cascade: each internal step's flag (it runs) and terms, whether a place past the bound is
occupied, and the step terms after the last internal step, whose slots are every internal step's news and own slots. -/
structure SettleOut (v : ServiceV) where
  steps : List (Term × OwnStepOut v)
  over : Term
  terms : StepTerms v

/-- The fault the model names: the first running internal step that faults, else the bound when a place past it is
occupied. -/
def SettleOut.fault? {v : ServiceV} (M : Model) (o : SettleOut v) : Option Fault :=
  match o.steps.find? fun s => (s.1.denote M).toBool && (s.2.terms.fault.denote M).toBool with
  | some s => s.2.fault? M
  | none => if (o.over.denote M).toBool then some .cascadeLimit else none

/-- Whether the cascade faults: an internal step it runs faults, or a place past the bound is occupied. -/
def SettleOut.faultT {v : ServiceV} (o : SettleOut v) : Term := .or o.terms.fault o.over

section
variable (L : Layout) (T : List TypeDecl)

/-- The cascade from queue place `k` with `fuel` internal steps left, over the own slots `S` and the step terms `t`
(its slots are not read): its terms, its condition (each internal step's, where it runs) and the codes' condition. -/
def encodeSettle (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (dflt now : Term) :
    (fuel k : Nat) → (S : List OwnSlot) → (t : StepTerms v) → Except Refusal (Encoded (SettleOut v))
  | 0, k, S, t =>
    pure ⟨⟨[], .and (.not t.fault) (queueAt dflt S (.int k)).1, ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩⟩,
      tt, tt⟩
  | f + 1, k, S, t => do
    let qa := queueAt dflt S (.int k)
    let act := Term.share (.and (.not t.fault) qa.1)
    let ⟨o, c, cx⟩ ← encodeOwnStep L T P v shs senv apply t.done.records now t.fresh t.done.nextId t.done.queued qa.2
      t.done.tables
    let t1 := pickTerms act o.terms ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩
    let ⟨rest, c', cx'⟩ ← encodeSettle P v shs senv apply dflt now f (k + 1) (S ++ t1.done.owns) t1
    pure ⟨⟨(act, o) :: rest.steps, rest.over,
        { rest.terms with done := { rest.terms.done with news := t1.done.news ++ rest.terms.done.news,
                                                         owns := t1.done.owns ++ rest.terms.done.owns } }⟩,
      andT (.ite act c tt) c', andT cx cx'⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

theorem newsRel_nil {e : Ty} {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {n0 : Nat} :
    NewsRel M L shs ds [] [] n0 :=
  ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2], [], by simp, trivial⟩

theorem settleFrom_none (fuel k : Nat) (a : Step.Acc v) (h : a.own[k]? = none) : Step.settleFrom T fuel k a = .ok a := by
  unfold Step.settleFrom; rw [h]

theorem settle_fault_skip {act : Term} {o : OwnStepOut v} {steps : List (Term × OwnStepOut v)} {over : Term}
    {t t' : StepTerms v} (h : ((act.denote M).toBool && (o.terms.fault.denote M).toBool) = false) :
    SettleOut.fault? M ⟨(act, o) :: steps, over, t⟩ = SettleOut.fault? M ⟨steps, over, t'⟩ := by
  simp only [SettleOut.fault?, List.find?_cons, h]

/-- Once an internal step faulted, the cascade's fault term stays true. -/
theorem settle_fault_stays {P : List AnySite} {shs : List (PendingShape v.event)} {senv : StepEnv L shs}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {dflt now : Term} :
    (fuel k : Nat) → (S : List OwnSlot) → (t : StepTerms v) → t.fault.denote M = .bool true →
    {o : SettleOut v} → {c cx : Term} → encodeSettle L T P v shs senv apply dflt now fuel k S t = .ok ⟨o, c, cx⟩ →
    o.terms.fault.denote M = .bool true
  | 0, _, _, _, htf, _, _, _, henc => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq] at henc
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

/-- Whether the cascade from queue place `k` with `fuel` internal steps left fits from `a`: each internal step it runs,
until one faults. -/
def settleFits (S : Ty → Nat) (T : List TypeDecl) : Nat → Nat → Step.Acc v → Prop
  | 0, _, _ => True
  | f + 1, k, a => match a.own[k]? with
    | none => True
    | some eff => ownFits S T a.state eff ∧ ∀ a', Step.runOwn T a eff = .ok a' → settleFits S T f (k + 1) a'

/-- After a fault no internal step runs, so the cascade's condition asks for nothing. -/
theorem settle_cond_fault {P : List AnySite} {shs : List (PendingShape v.event)} {senv : StepEnv L shs}
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {dflt now : Term} :
    (fuel k : Nat) → (S : List OwnSlot) → (t : StepTerms v) → t.fault.denote M = .bool true →
    {o : SettleOut v} → {c cx : Term} → encodeSettle L T P v shs senv apply dflt now fuel k S t = .ok ⟨o, c, cx⟩ →
    Holds M c
  | 0, _, _, _, _, _, _, _, henc => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq] at henc
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

/-- The cascade: where the codes' condition holds, the condition holds exactly when every internal step the cascade
runs fits (`settleFits`), and wherever it holds the fault the model names is `Step.settleFrom`'s, and otherwise the
cascade runs to its end with what the terms denote (`AccRel`, own effects queued from `a`'s queue length). -/
theorem settle_encode {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    (senv : StepEnv L shs) {dflt now : Term} :
    (fuel k : Nat) → (S : List OwnSlot) → (t : StepTerms v) → (a : Step.Acc v) → Step.Inv P a.state →
    Step.QueueOk P a → OwnRel M L S a.own 0 → now.denote M = .int a.state.now → t.fault.denote M = .bool false →
    RelV L v.records (Ty.up _ v.records_data a.state.records) (t.done.records.denote M) →
    MachinesRel M L T v.machines t.done.tables a.state.machines →
    t.fresh.denote M = .int (Int.ofNat a.state.fresh) → t.done.nextId.denote M = .int (Int.ofNat a.state.nextId) →
    t.done.queued.denote M = .int ((a.own.length : Nat) : Int) →
    {o : SettleOut v} → {c cx : Term} → encodeSettle L T P v shs senv apply dflt now fuel k S t = .ok ⟨o, c, cx⟩ →
    Holds M cx →
    (Holds M c ↔ settleFits L.count T fuel k a) ∧
    (Holds M c → o.faultT.denote M = .bool (o.fault? M).isSome ∧
      match o.fault? M with
      | some f => Step.settleFrom T fuel k a = .error f
      | none => AccRel M L T shs a o.terms.done o.terms.fresh a.own.length (Step.settleFrom T fuel k a))
  | 0, k, S, t, a, _, _, hS, _, htf, hrec, hms, hfr, hn, hq, o, c, cx, henc, _ => by
    simp only [encodeSettle, pure, Except.pure, Except.ok.injEq] at henc
    obtain ⟨rfl, rfl, rfl⟩ := henc
    refine ⟨iff_of_true holds_tt trivial, fun _ => ?_⟩
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
  | f + 1, k, S, t, a, hinv, hqok, hS, hnow, htf, hrec, hms, hfr, hn, hq, o, c, cx, henc, hcx => by
    obtain ⟨⟨o1, c1, cx1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2, cx2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    obtain ⟨hcx1, hcx2⟩ := (holds_andT _ _).1 hcx
    have hk := queueAt_rel dflt hS (k := .int k) k (by simp [Term.denote])
    have hact : (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)).denote M =
        .bool (decide (k < a.own.length)) := by
      simp [Term.denote, htf, hk.1, toBool_bool]
    refine ⟨?_, fun hc => ?_⟩
    · rw [holds_andT]
      by_cases hlt : k < a.own.length
      · have hact' := hact
        simp only [hlt, decide_true] at hact'
        obtain ⟨hown, hreach⟩ := hqok _ (List.getElem_mem hlt)
        have e1 := (ownStep_encode chk hshs a happ hca senv hrec hnow hfr hn hq hms
          a.own[k] (hk.2 hlt) hown hreach h1 hcx1).1
        have hite : Holds M (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) c1 tt) ↔ Holds M c1 := by
          rw [holds_ite, hact']; simp only [toBool_bool, ite_true]
        simp only [settleFits, List.getElem?_eq_getElem hlt]
        rw [hite, e1]
        have hpick : ∀ x y : Term, (Term.share (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) x y)).denote M =
            x.denote M := fun x y => by simp [Term.denote, hact', toBool_bool]
        have tail : Holds M c1 → (Holds M c2 ↔ ∀ a', Step.runOwn T a a.own[k] = .ok a' → settleFits L.count T f (k + 1) a') := by
          intro hc1
          obtain ⟨hfault, hrun⟩ := (ownStep_encode chk hshs a happ hca senv hrec hnow hfr hn hq
            hms a.own[k] (hk.2 hlt) hown hreach h1 hcx1).2 hc1
          revert hrun
          cases hof : o1.fault? M with
          | some f' =>
            intro hrun
            refine iff_of_true (settle_cond_fault f (k + 1) _ _ ?_ h2) (fun a' h => by rw [hrun] at h; cases h)
            simp only [pickTerms]; rw [hpick, hfault, hof]; rfl
          | none =>
            intro hdone
            have hA1 := AccRel.pick (b := ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩) hact' ⟨rfl, rfl⟩ hdone
            obtain ⟨a1, hrun0⟩ := hA1.ok
            obtain ⟨r1, r2, r3, r4, rnow, os0, hown1, r5, r6⟩ := (hrun0 ▸ hA1).ends
            rw [(settle_encode chk hshs happ hca senv f (k + 1) _ _ _
              (Step.runOwn_inv T chk.reach a hinv _ hrun0)
              (Step.runOwn_queue T chk.reach a hinv hqok _ hrun0)
              (by rw [hown1]; exact ownRel_append hS (by simpa using r6)) (by rw [rnow]; exact hnow)
              (by simp only [pickTerms]; rw [hpick, hfault, hof]; rfl) r1 r2 r3 r4
              (by rw [r5, hown1, List.length_append]) h2 hcx2).1]
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
        have hS1 : OwnRel M L (S ++ (gateOwns (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
            o1.terms.done.owns ++ [])) a.own 0 := by
          have := ownRel_append hS (ownRel_append (ownRel_gate_false (L := L) (e := v.event) hact'
            (S := o1.terms.done.owns) (0 + a.own.length)) (ownRel_nil _))
          simpa using this
        have e2 := (settle_encode chk hshs happ hca senv f (k + 1) _ _ _ hinv hqok hS1
          hnow (by simp only [pickTerms]; rw [hpick]; exact htf)
          (by simp only [pickTerms]; rw [hpick]; exact hrec)
          (by simp only [pickTerms]; exact machinesRel_congr _ _ _ _ (pick_tables_false hact' _ _).symm hms)
          (by simp only [pickTerms]; rw [hpick]; exact hfr)
          (by simp only [pickTerms]; rw [hpick]; exact hn)
          (by simp only [pickTerms]; rw [hpick]; exact hq)
          h2 hcx2).1
        have hf2 : settleFits L.count T f (k + 1) a := by
          cases f with
          | zero => trivial
          | succ f => simp only [settleFits, hnone1]
        simp only [settleFits, hnone]
        exact iff_of_true ⟨by rw [holds_ite, hact']; exact holds_tt, e2.2 hf2⟩ trivial
    · obtain ⟨hc1', hc2⟩ := (holds_andT _ _).1 hc
      by_cases hlt : k < a.own.length
      · have hact' := hact
        simp only [hlt, decide_true] at hact'
        have hc1 : Holds M c1 := by
          have := (holds_ite _ _ _).1 hc1'
          rw [hact'] at this
          simpa only [toBool_bool, ite_true] using this
        obtain ⟨hown, hreach⟩ := hqok _ (List.getElem_mem hlt)
        obtain ⟨hfault, hrun⟩ := (ownStep_encode chk hshs a happ hca senv hrec hnow hfr hn hq
          hms a.own[k] (hk.2 hlt) hown hreach h1 hcx1).2 hc1
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
          intro hdone
          have hff : (o1.terms.fault.denote M).toBool = false := by rw [hfault, hof]; rfl
          rw [settle_fault_skip (t' := rest.terms) (by simp [hact', hff, toBool_bool])]
          have hA1 := AccRel.pick (b := ⟨t.fault, { t.done with news := [], owns := [] }, t.fresh⟩) hact' ⟨rfl, rfl⟩ hdone
          obtain ⟨a1, hrun0⟩ := hA1.ok
          obtain ⟨r1, r2, r3, r4, rnow, os0, hown1, r5, r6⟩ := (hrun0 ▸ hA1).ends
          obtain ⟨IHF, IH⟩ := (settle_encode chk hshs happ hca senv f (k + 1) _ _ _
            (Step.runOwn_inv T chk.reach a hinv _ hrun0)
            (Step.runOwn_queue T chk.reach a hinv hqok _ hrun0)
            (by rw [hown1]; exact ownRel_append hS (by simpa using r6)) (by rw [rnow]; exact hnow)
            (by simp only [pickTerms]; rw [hpick, hfault, hof]; rfl) r1 r2 r3 r4
            (by rw [r5, hown1, List.length_append]) h2 hcx2).2 hc2
          refine ⟨by simpa [SettleOut.faultT] using IHF, ?_⟩
          revert IH
          cases rest.fault? M with
          | some f'' => intro IH; rw [hrun0]; exact IH
          | none =>
            intro IH
            refine AccRel.bind hA1 fun a1' os hr hown _ _ _ _ _ _ => ?_
            obtain rfl := Except.ok.inj (hrun0.symm.trans hr)
            rw [hown, List.length_append] at IH
            exact IH
      · have hact' := hact
        simp only [hlt, decide_false] at hact'
        have hnone : a.own[k]? = none := List.getElem?_eq_none (by omega)
        have hnone1 : a.own[k + 1]? = none := List.getElem?_eq_none (by omega)
        rw [settleFrom_none (f + 1) k a hnone]
        have hpick : ∀ x y : Term, (Term.share (.ite (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1)) x y)).denote M =
            y.denote M := fun x y => by simp [Term.denote, hact', toBool_bool]
        rw [settle_fault_skip (t' := rest.terms) (by simp [hact', toBool_bool])]
        have hS1 : OwnRel M L (S ++ (gateOwns (Term.share (.and (.not t.fault) (queueAt dflt S (.int k)).1))
            o1.terms.done.owns ++ [])) a.own 0 := by
          have := ownRel_append hS (ownRel_append (ownRel_gate_false (L := L) (e := v.event) hact'
            (S := o1.terms.done.owns) (0 + a.own.length)) (ownRel_nil _))
          simpa using this
        have IH := (settle_encode chk hshs happ hca senv f (k + 1) _ _ _ hinv hqok hS1
          hnow (by simp only [pickTerms]; rw [hpick]; exact htf)
          (by simp only [pickTerms]; rw [hpick]; exact hrec)
          (by simp only [pickTerms]; exact machinesRel_congr _ _ _ _ (pick_tables_false hact' _ _).symm hms)
          (by simp only [pickTerms]; rw [hpick]; exact hfr)
          (by simp only [pickTerms]; rw [hpick]; exact hn)
          (by simp only [pickTerms]; rw [hpick]; exact hq)
          h2 hcx2).2 hc2
        rw [settleFrom_none f (k + 1) a hnone1] at IH
        obtain ⟨IHF, IH⟩ := IH
        refine ⟨by simpa [SettleOut.faultT] using IHF, ?_⟩
        revert IH
        cases rest.fault? M with
        | some f'' => exact id
        | none =>
          rintro ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, s1, s2, s3, s4, s5, s6, s7⟩
          refine ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, s1, s2, s3, s4, ?_, s6, ?_⟩
          · have h0 := newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := v.declared) hact'
              (S := o1.terms.done.news) a.state.nextId) (newsRel_nil (L := L) (M := M))
            exact newsRel_append h0 s5
          · have h0 := ownRel_append (ownRel_gate_false (L := L) (e := v.event) hact' (S := o1.terms.done.owns)
              a.own.length) (ownRel_nil _)
            exact ownRel_append h0 s7

end

end Tazuna.Smt
