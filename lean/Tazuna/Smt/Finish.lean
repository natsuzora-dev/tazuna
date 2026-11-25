import Tazuna.Smt.Cascade

/-! How a step that applies events ends, as `Step.finish` says: the cascade runs the own commands and queries the
events queued (`encodeSettle`), every request the events and the internal steps start is written into the pending table
in one pass, and the service's and every machine's invariants are checked on the state the cascade leaves. The step
kinds differ only in what comes before (`loop_acc` for a list of events). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout)

/-- The service's invariants on the records term: each rule's name and whether it holds, with the condition. -/
def encodeInvariants {r : Ty} (inv : Code (Ty.fn [r] Ty.rules)) (records : Term) :
    Except Refusal (List (Term × Term) × Term) := do
  let rc ← Code.ofTermE r records
  let (invs, c) ← inv (rc, ())
  let rules ← ruleTerms L invs
  pure (rules, c)

end

section
variable {L : Layout} {M : Model}

/-- The invariant terms name the rules the records break. -/
theorem invariants_rel {r : Ty} (f : Fun (Ty.fn [r] Ty.rules)) (hr : r.isData = true) (hf : (Ty.fn [r] Ty.rules).isData = true)
    {inv : Code (Ty.fn [r] Ty.rules)} (hinv : Smt.Rel M L _ (Ty.up _ hf f.fn) inv) (recs : r.den0) {records : Term}
    (hrec : RelV L r (Ty.up _ hr recs) (records.denote M)) {rules : List (Term × Term)} {c : Term}
    (henc : encodeInvariants L inv records = .ok (rules, c)) (hc : Holds M c) :
    brokenIn M rules = Step.broken (f.fn (recs, ())) := by
  obtain ⟨rc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rules', h3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hrc : Smt.Rel M L r (Ty.up _ hr recs) rc := (rel_ofTerm (need_ok.1 h1) _).2 hrec
  have hargs : (Ty.tuple [r]).isData = true := by simp [Ty.isData, Ty.isDatas, hr]
  have hiv := hinv _ _ (rels1 hr hargs hrc) invs c h2 hc
  erw [Ty.up_fn _ Ty.rules _ hargs rfl] at hiv
  exact rules_broken h3 _ hiv

/-- The invariants' condition is exact: it holds exactly when they fit at the records. -/
theorem invariants_exact {r : Ty} (f : Fun (Ty.fn [r] Ty.rules)) (hr : r.isData = true)
    {inv : Code (Ty.fn [r] Ty.rules)} {ci : Term} (hf : f.code L = .ok (inv, ci)) (hci : Holds M ci) (recs : r.den0)
    {records : Term} (hrec : RelV L r (Ty.up _ hr recs) (records.denote M)) {rules : List (Term × Term)} {c : Term}
    (henc : encodeInvariants L inv records = .ok (rules, c)) :
    Holds M c ↔ f.appFits L.count (recs, ()) := by
  obtain ⟨rc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rules', -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hrc : Smt.Rel M L r (Ty.up _ hr recs) rc := (rel_ofTerm (need_ok.1 h1) _).2 hrec
  exact f.app_exact hf hci (by simpa using ofTerm_notFn (need_ok.1 h1)) _ _ (rels1 hr f.args_data hrc) h2

end

/-- The terms of a step's end: the cascade, the new pending table, and the invariants and instance checks on the state
the cascade leaves. -/
structure FinishOut (v : ServiceV) where
  settle : SettleOut v
  pending : Term
  invariants : List (Term × Term)
  checks : PerMachine (fun _ => List InstCheck) v.machines

section
variable (L : Layout) (T : List TypeDecl)

-- `queueAt` reads the default effect only where no own slot holds the place, and no fit asks that value.
set_option linter.tazuna.silentDefault false in
/-- A step's end after the events loop `o`, from the pending table term the step began with: its terms, its condition
and the codes' condition. The pending write and the invariants are asked only where the cascade does not fault, since
the step then leaves the state it began with. -/
def encodeFinish (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (inv : Code (Ty.fn [v.records] Ty.rules))
    (now fresh pending : Term) (o : EventsOut v) : Except Refusal (Encoded (FinishOut v)) := do
  -- `queueAt` reads the default only where no own slot holds the place, so its value is never asked.
  let dflt := (effectDefault L v.event).getD tt
  let ⟨so, cs, cx⟩ ← encodeSettle L T P v shs senv apply dflt now v.bounds.cascadeNat 0 o.owns
    ⟨.bool false, o, fresh⟩
  let (pT, cp) ← encodePending L shs pending (o.news ++ so.terms.done.news)
  let (rules, ci) ← encodeInvariants L inv so.terms.done.records
  let (checks, ck) ← encodeInstChecks L T v.machines so.terms.done.tables so.terms.done.records now
  pure ⟨⟨so, pT, rules, checks⟩, andT cs (.ite so.faultT tt (andT cp (andT ci ck))), cx⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- What a step's end terms say of its result `r`, from the step in progress `a` before its events: the cascade's
fault, else the first broken invariant (the service's, then each machine's instances in key order), else the outcome
with the records, machines and fresh counter the terms denote, the requests `ps` written at the next wire ids and
sent, and the pending table and next id terms denoting what follows (pending as a multiset). A fault leaves `s0`. -/
def Finished (M : Model) (L : Layout) (T : List TypeDecl)
    (shs : List (PendingShape v.event)) (fo : FinishOut v) (s0 : State v) (a : Step.Acc v) (outcome : Outcome)
    (r : Result v) : Prop :=
  match fo.settle.fault? M with
  | some f => r = ⟨s0, .fault f, [], []⟩
  | none => match brokenIn M fo.invariants ++ checksBroken L T M v.machines fo.checks with
    | n :: _ => r = ⟨s0, .fault (.invariant n), [], []⟩
    | [] => ∃ (recs : v.records.den0) (ms : Step.Machines v.machines) (fr : Nat)
        (evs : List v.event.den0) (ps : List (Step.Pending v.event)),
        r = ⟨{ a.state with records := recs, machines := ms, fresh := fr, pending := a.state.pending ++ ps,
                            nextId := a.state.nextId + ps.length },
              outcome, a.events ++ evs, a.out ++ ps.map Step.Pending.line⟩ ∧
        RelV L v.records (Ty.up _ v.records_data recs) (fo.settle.terms.done.records.denote M) ∧
        MachinesRel M L T v.machines fo.settle.terms.done.tables ms ∧
        fo.settle.terms.fresh.denote M = .int (fr : Int) ∧
        fo.settle.terms.done.nextId.denote M = .int ((a.state.nextId + ps.length : Nat) : Int) ∧
        ∃ ps', ps'.Perm (a.state.pending ++ ps) ∧ PendingRel L shs (fo.pending.denote M) ps'

/-- Whether a step's end fits, for the result `r` of its events: the internal steps the cascade runs
(`settleFits`) and, where it does not fault, every pending request in the pending table and the service's and every
machine's invariants on the state it leaves. -/
def finishFits (S : Ty → Nat) (T : List TypeDecl) (shs : List (PendingShape v.event)) (r : Except Fault (Step.Acc v)) :
    Prop :=
  ∀ a1, r = .ok a1 → settleFits S T v.bounds.cascadeNat 0 a1 ∧
    ∀ a2, Step.settleFrom T v.bounds.cascadeNat 0 a1 = .ok a2 →
      a2.state.pending.length ≤ S (pendingTable shs) ∧ v.invariants.appFits S (a2.state.records, ()) ∧
      instChecksFit S a2.state.records a2.state.now a2.state.machines

/-- A step's end: its condition holds exactly when the step's end fits (`finishFits`), and wherever it holds the result
`Step.finish` gives for the result `r` of the step's events is what the terms say (`Finished`). -/
theorem finish_encode {P : List AnySite} (chk : Checked P T v) {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci0 : Term} (hinvc : v.invariants.code L = .ok (inv, ci0))
    (hci0 : Holds M ci0)
    (senv : StepEnv L shs)
    (s0 : State v) (outcome : Outcome) (a : Step.Acc v) (hown : a.own = []) (hinv : Step.Inv P a.state)
    {now fresh pending : Term} (hnow : now.denote M = .int a.state.now)
    (hpend : PendingRel L shs (pending.denote M) a.state.pending)
    {o : EventsOut v} {r : Except Fault (Step.Acc v)} (hdone : AccRel M L T shs a o fresh 0 r)
    (hr : ∀ a1, r = .ok a1 → Step.Inv P a1.state ∧ Step.QueueOk P a1)
    {fo : FinishOut v} {c cx : Term}
    (henc : encodeFinish L T P v shs senv apply inv now fresh pending o = .ok ⟨fo, c, cx⟩)
    (hcx : Holds M cx) :
    (Holds M c ↔ finishFits L.count T shs r) ∧
    (Holds M c → Finished M L T shs fo s0 a outcome (Step.finish T s0 r outcome)) := by
  obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, e1, e2, e3, e4, e5, e6, e7⟩ := hdone
  obtain ⟨ps1, hps1⟩ := newsRel_writes e5
  have hl1 := forall2_zipIdx_length _ _ hps1
  have hra := hr1 ps1 hps1
  obtain ⟨⟨so, cs, cx'⟩, hset, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨pT, cp⟩, hpe, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rules, ci⟩, hi, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, ck⟩, hck, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  refine ⟨?_, fun hc => ?_⟩
  · revert hra
    generalize hA : ({ state := { a.state with records := recs1, machines := ms1, fresh := fr1,
                                               pending := a.state.pending ++ ps1, nextId := a.state.nextId + ps1.length },
                       events := a.events ++ evs1, out := a.out ++ ps1.map Step.Pending.line,
                       own := a.own ++ os1 } : Step.Acc v) = a1
    intro hra
    obtain ⟨hinv1, hq1⟩ := hr _ hra
    have hS1 : OwnRel M L o.owns a1.own 0 := by rw [← hA]; simpa [hown] using e7
    have hn1 : o.nextId.denote M = .int (Int.ofNat a1.state.nextId) := by rw [← hA, e4, ← hl1]; rfl
    have hq1' : o.queued.denote M = .int ((a1.own.length : Nat) : Int) := by rw [← hA]; simpa [hown] using e6
    have e1' : RelV L v.records (Ty.up _ v.records_data a1.state.records) (o.records.denote M) := by rw [← hA]; exact e1
    have e2' : MachinesRel M L T v.machines o.tables a1.state.machines := by rw [← hA]; exact e2
    have e3' : fresh.denote M = .int (Int.ofNat a1.state.fresh) := by rw [← hA]; exact e3
    have hnow1 : now.denote M = .int a1.state.now := by rw [← hA]; exact hnow
    obtain ⟨es, hrel⟩ := settle_encode chk hshs happ hca senv
      v.bounds.cascadeNat 0 o.owns ⟨.bool false, o, fresh⟩ _ hinv1 hq1 hS1 hnow1 rfl e1' e2' e3' hn1 hq1' hset hcx
    have hfits : finishFits L.count T shs r ↔ settleFits L.count T v.bounds.cascadeNat 0 a1 ∧
        ∀ a2, Step.settleFrom T v.bounds.cascadeNat 0 a1 = .ok a2 →
          a2.state.pending.length ≤ L.count (pendingTable shs) ∧ v.invariants.appFits L.count (a2.state.records, ()) ∧
          instChecksFit L.count a2.state.records a2.state.now a2.state.machines := by
      rw [hra]
      exact ⟨fun h => h _ rfl, fun h a1 e => by cases e; exact h⟩
    rw [hfits, holds_andT]
    have key : ∀ hcs : Holds M cs, (Holds M (.ite so.faultT tt (andT cp (andT ci ck))) ↔
        ∀ a2, Step.settleFrom T v.bounds.cascadeNat 0 a1 = .ok a2 →
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
        have ei := invariants_exact v.invariants v.records_data hinvc hci0 recs2 f1 hi
        have ek := (instChecks_encode recs2 _ f1 hnow v.machines _ _ f2 (fun m hm => (chk.keys m hm).2) hck).1
        have hall : ∀ a2, Step.settleFrom T v.bounds.cascadeNat 0 _ = .ok a2 ↔ a2 = _ := fun a2 => by
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
  · obtain ⟨hinv1, hq1⟩ := hr _ hra
    obtain ⟨hcs, hrest⟩ := (holds_andT _ _).1 hc
    have hfd : (Ty.fn [v.records] Ty.rules).isData = true := by
      simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, v.records_data]
    have hinvR := v.invariants.code_fn hfd hinvc hci0
    obtain ⟨hF, hm⟩ := (settle_encode chk hshs happ hca senv
      v.bounds.cascadeNat 0 o.owns ⟨.bool false, o, fresh⟩ _ hinv1 hq1 (by simpa [hown] using e7) hnow rfl e1 e2 e3
      (by rw [e4, ← hl1]; rfl) (by simpa [hown] using e6) hset hcx).2 hcs
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
      have hb := invariants_rel v.invariants v.records_data hfd hinvR recs2 f1 hi hci
      have hbs := (instChecks_encode recs2 a.state.now f1 hnow v.machines _ _ f2 (fun m hm => (chk.keys m hm).2) hck).2 hck'
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

/-- What `finish_encode` asks of a list of events' result besides the terms: the step invariant and a queue of own
effects that reach the program, which `applyEvents` keeps. -/
theorem applyEvents_ok {P : List AnySite} (hv : v.Reach P) (a : Step.Acc v) (hown : a.own = [])
    (hinv : Step.Inv P a.state) (evs : List v.event.den0) :
    ∀ a1, Step.applyEvents T a evs = .ok a1 → Step.Inv P a1.state ∧ Step.QueueOk P a1 := fun _ h =>
  ⟨Step.applyEvents_inv T hv evs a hinv h,
    Step.applyEvents_queue T hv evs a h hinv (by simp [Step.QueueOk, hown])⟩

end

end Tazuna.Smt
