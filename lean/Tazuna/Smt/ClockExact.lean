import Tazuna.Smt.Clock
import Tazuna.Smt.CommandExact

/-! The condition of a clock line's step is exact (run-log entry 63): it fails only where a function the
step really applies outgrows a slot count. Every round asks for each machine's `after` and `effect` sources, and for
both applied where an instance fires; the pending write asks that the requests fit the pending table; the invariants
are asked at the line's time. Rounds past the first that fired nothing, and everything after a step that exceeds the
cascade bound, ask nothing. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (S : Ty → Nat) (T : List TypeDecl) {r e : Ty}

/-- Whether a firing round's functions fit, machines in order: each machine's `after` and `effect` sources, and both
applied at the state the firing instance enters (none where an earlier machine fired). -/
def firesFit (recs : r.den0) (now d : Int) : Bool → List (Step.MachineState r e) → Prop
  | _, [] => True
  | b, ⟨m, insts⟩ :: rest => (m.after.fits S).1 ∧ (m.effect.fits S).1 ∧
      (∀ i ∈ insts, (!b && Step.firesIn T m d insts i) = true → ∀ dl tg, i.timer = some (dl, tg) →
        m.after.appFits S (.inl (i.key, tg, recs, now, ()), ()) ∧ m.effect.appFits S (.inl (i.key, tg, recs, now, ()), ())) ∧
      firesFit recs now d (b || insts.any (Step.hitsAt d)) rest

/-- Whether a round's functions fit: at the earliest due deadline where it is active and a timer is due, else only the
sources. -/
def roundFit (recs : r.den0) (now : Int) (ab : Bool) (sms : List (Step.MachineState r e)) : Prop :=
  match (if ab then (Step.dues sms now).min? else none) with
  | some d => firesFit S T recs now d false sms
  | none => firesFit S T recs now 0 true sms

/-- Whether `k` rounds' functions fit, each round on the machines the one before left. -/
def roundsFit {v : ServiceV} (s : State v) : Bool → Nat → Prop
  | _, 0 => True
  | ab, k + 1 => roundFit S T s.records s.now ab s.machines ∧
      roundsFit { s with machines := (Step.roundOf s.records s.now ab s.machines).1 }
        (ab && (Step.dues s.machines s.now).min?.isSome) k

theorem firesFit_true (recs : r.den0) (now d d' : Int) : (sms : List (Step.MachineState r e)) →
    (firesFit S T recs now d true sms ↔ firesFit S T recs now d' true sms)
  | [] => Iff.rfl
  | ⟨m, insts⟩ :: rest => by
    simp only [firesFit, Bool.not_true, Bool.false_and, Bool.false_eq_true, false_implies, implies_true, Bool.true_or,
      true_and]
    rw [firesFit_true recs now d d' rest]

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- Every machine's part of a firing round asks exactly that its functions fit (`firesFit`). -/
theorem fires_exact (recs : v.records.den0) (tnow : Int) {records now : Term} (hrd : v.records.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {d : Term} {dv : Int} (hd : d.denote M = .int dv) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    MachinesRel M L T ms xs sms →
    {done : Term} → {b : Bool} → done.denote M = .bool b →
    {os : List FireOut} → {c : Term} → encodeFires L T ms xs done d records now = .ok (os, c) →
    (Holds M c ↔ firesFit L.count T recs tnow dv b sms)
  | [], [], [], _, done, b, hdone, os, c, henc => by
    simp only [encodeFires, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl⟩ := henc
    simp [firesFit, holds_tt]
  | m :: ms, x :: xs, sm :: sms, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, done, b, hdone, os, c, henc => by
    obtain ⟨⟨af, c0⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨fx, c1⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c2⟩, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨os', c3⟩, h4, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    have hrec' : RelV L v.records (Ty.up _ m.records_data recs) (records.denote M) := hrec
    have e0 := (m.after.code_exact (M := M) h1).1
    have e1 := (m.effect.code_exact (M := M) h2).1
    simp only [firesFit]
    rw [holds_andT, holds_andT, holds_andT, e0, e1]
    constructor
    · rintro ⟨p0, p1, p2, p3⟩
      have hc0 := e0.2 p0
      have hc1 := e1.2 p1
      have hfx := effect_codeRel (M := M) m h2 hc1
      have haf := m.after.code_fn m.after.ht h1 hc0
      obtain ⟨-, hhit, -⟩ := fire_table (T := T) m haf hfx recs tnow hrec' hnow tbl htbl hdone hd h3 p2
      have hdone' : (Term.share (.or done o.hit)).denote M = .bool (b || (instancesOf T m tbl).any (Step.hitsAt dv)) := by
        rw [Term.denote_share]; show Val.bool _ = _; rw [hdone, hhit]; rfl
      exact ⟨p0, p1, (fire_exact m h1 hc0 h2 hc1 recs tnow hrec' hnow tbl htbl hdone hd h3).1 p2,
        (fires_exact recs tnow hrd hrec hnow hd ms xs sms hrest hdone' h4).1 p3⟩
    · rintro ⟨p0, p1, p2, p3⟩
      have hc0 := e0.2 p0
      have hc1 := e1.2 p1
      have hc2 := (fire_exact m h1 hc0 h2 hc1 recs tnow hrec' hnow tbl htbl hdone hd h3).2 p2
      have hfx := effect_codeRel (M := M) m h2 hc1
      have haf := m.after.code_fn m.after.ht h1 hc0
      obtain ⟨-, hhit, -⟩ := fire_table (T := T) m haf hfx recs tnow hrec' hnow tbl htbl hdone hd h3 hc2
      have hdone' : (Term.share (.or done o.hit)).denote M = .bool (b || (instancesOf T m tbl).any (Step.hitsAt dv)) := by
        rw [Term.denote_share]; show Val.bool _ = _; rw [hdone, hhit]; rfl
      exact ⟨p0, p1, hc2, (fires_exact recs tnow hrd hrec hnow hd ms xs sms hrest hdone' h4).2 p3⟩
  | [], [], _ :: _, h, _, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _, _ | _ :: _, [], _, h, _, _, _, _, _, _
  | _ :: _, _ :: _, [], h, _, _, _, _, _, _ => h.elim

/-- A firing round asks exactly that its functions fit (`roundFit`). -/
theorem round_exact (recs : v.records.den0) (tnow : Int) {records now : Term} (hrd : v.records.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {ms : List (MachineV v.records v.event)} {xs : List Term} {sms : List (Step.MachineState v.records v.event)}
    (hms : MachinesRel M L T ms xs sms) {active : Term} {ab : Bool} (hact : active.denote M = .bool ab)
    {ro : RoundOut} {c : Term} (henc : encodeRound L T ms xs active records now = .ok (ro, c)) :
    Holds M c ↔ roundFit L.count T recs tnow ab sms := by
  obtain ⟨dues, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨os, c'⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨odues, hF, hP⟩ := dueAll_rel (T := T) hnow ms xs sms hms h1
  obtain ⟨hhas, hmin⟩ := minDue_den hF
  obtain ⟨dv, hdv⟩ := minDue_int hF
  rw [min?_perm hP] at hhas hmin
  have hngo : (Term.not (Term.share (.and active (minDueT dues).1))).denote M =
      .bool !(ab && (Step.dues sms tnow).min?.isSome) := by
    show Val.bool _ = _; rw [Term.denote_share]; show Val.bool (!(Val.bool _).toBool) = _; rw [hact, hhas]; rfl
  have hd : (Term.share (minDueT dues).2).denote M = .int dv := by rw [Term.denote_share, hdv]
  rw [fires_exact recs tnow hrd hrec hnow hd ms xs sms hms hngo h2]
  unfold roundFit
  cases ab with
  | false => simp only [Bool.false_and, Bool.not_false, Bool.false_eq_true, ite_false]; exact firesFit_true _ T recs tnow dv 0 sms
  | true =>
    simp only [Bool.true_and, ite_true]
    cases hm : (Step.dues sms tnow).min? with
    | none => simp only [Option.isSome_none, Bool.not_false]; exact firesFit_true _ T recs tnow dv 0 sms
    | some dmin =>
      have hdm : dv = dmin := by have := hmin dmin hm; rw [hdv] at this; cases this; rfl
      subst hdm
      simp only [Option.isSome_some, Bool.not_true]

/-- The firing rounds ask exactly that every round's functions fit (`roundsFit`). -/
theorem rounds_exact {shs : List (PendingShape v.event)} {ds : List (String × DeclaredV)} {dE dP dopt : Nat}
    {records now : Term} (hrd : v.records.isData = true) (hord : ∀ m ∈ v.machines, m.key.ordered T = true) :
    (k : Nat) → (s : State v) → RelV L v.records (Ty.up _ hrd s.records) (records.denote M) →
    now.denote M = .int s.now → {xs : List Term} → MachinesRel M L T v.machines xs s.machines →
    {active : Term} → {ab : Bool} → active.denote M = .bool ab → {nid : Term} →
    {o : RoundsOut} → {c : Term} → encodeRounds L T shs ds dE dP dopt v.machines records now k xs active nid = .ok (o, c) →
    (Holds M c ↔ roundsFit L.count T s ab k)
  | 0, s, _, _, xs, _, active, ab, _, nid, o, c, henc => by
    simp only [encodeRounds, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl⟩ := henc
    simp [roundsFit, holds_tt]
  | k + 1, s, hrec, hnow, xs, hms, active, ab, hact, nid, o, c, henc => by
    obtain ⟨⟨ro, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨news, nid'⟩, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rest, c2⟩, h3, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    have e1 := round_exact (T := T) s.records s.now hrd hrec hnow hms hact h1
    simp only [roundsFit]
    rw [holds_andT, e1]
    have ih : roundFit L.count T s.records s.now ab s.machines → (Holds M c2 ↔
        roundsFit L.count T { s with machines := (Step.roundOf s.records s.now ab s.machines).1 }
          (ab && (Step.dues s.machines s.now).min?.isSome) k) := fun hf => by
      obtain ⟨hgo, hrel, -⟩ := round_rel s.records s.now hrd hrec hnow hms hord hact h1 (e1.2 hf)
      exact rounds_exact hrd hord k ({ s with machines := (Step.roundOf s.records s.now ab s.machines).1 } : State v)
        hrec hnow hrel hgo h3
    exact ⟨fun ⟨p1, p2⟩ => ⟨p1, (ih p1).1 p2⟩, fun ⟨p1, p2⟩ => ⟨p1, (ih p1).2 p2⟩⟩

/-- The condition of a clock line's step is exact: it holds exactly when, if time moves forward, every
firing round's functions fit, and, unless every round fires, the requests fit the pending table, the service's
invariants fit at the records, and every machine's invariants fit at the instances the rounds leave, at the line's
time. -/
theorem clock_exact {P : List AnySite} (hP : SitesUnique P) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) (s : State v) (hinv : Step.Inv P s) (time : Int) (hrd : v.records.isData = true)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hci : v.invariants.code L = .ok (inv, ci)) (hcinv : Holds M ci)
    {records now st pending nextIdT : Term} (hrec : RelV L v.records (Ty.up _ hrd s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hst : st.denote M = .int time)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines) (hord : ∀ m ∈ v.machines, m.key.ordered T = true)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : ClockOut} {cond : Term} (henc : encodeClock L T v shs dE dP dopt inv records now st pending nextIdT xs = .ok (o, cond)) :
    Holds M cond ↔ (s.now ≤ time →
      roundsFit L.count T { s with now := time } true (v.bounds.cascade.toNat + 1) ∧
      ∀ s' effs, Step.fire { s with now := time } (v.bounds.cascade.toNat + 1) = some (s', effs) →
        s.pending.length + effs.length ≤ L.count (pendingTable shs) ∧ v.invariants.appFits L.count (s.records, ()) ∧
        instChecksFit L.count s.records time s'.machines) := by
  obtain ⟨⟨ro, cr⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨pT, cp⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rc, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, ci'⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, cm⟩, h6, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hfw : ((Term.le now st).denote M).toBool = decide (s.now ≤ time) := by
    simp only [Term.denote, hnow, hst, Val.toInt, Val.toBool]
  rw [holds_ite_tt hfw]
  by_cases ht : s.now ≤ time
  · simp only [ht, decide_true, true_implies]
    let s0 : State v := { s with now := time }
    have hrec0 : RelV L v.records (Ty.up _ hrd s0.records) (records.denote M) := hrec
    have er := rounds_exact (shs := shs) (ds := v.declared) (dE := dE) (dP := dP) (dopt := dopt) hrd hord
      (v.bounds.cascade.toNat + 1) s0 hrec0 hst hms (ab := true) rfl h1
    rw [holds_andT, er]
    -- The service's invariants.
    have hrc : Smt.Rel M L _ (Ty.up _ hrd s.records) rc := (rel_ofTerm (need_ok.1 h3) _).2 hrec
    have hargs : Smt.Rels M L [v.records] (Ty.up (.tuple [v.records]) (by simp [Ty.isData, Ty.isDatas, hrd])
        (s.records, ())) (rc, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [v.records]) (by simp [Ty.isData, Ty.isDatas, hrd]) (s.records, ())).1 rc ∧ True
      erw [Ty.up_tuple _ _ _ hrd rfl]; exact ⟨hrc, trivial⟩
    have hx := v.invariants.app_exact hci hcinv (by simpa using ofTerm_notFn (need_ok.1 h3)) _ _ hargs h4
    have rest : roundsFit L.count T s0 true (v.bounds.cascade.toNat + 1) →
        (Holds M (.ite ro.over tt (andT cp (andT ci' cm))) ↔ ∀ s' effs,
          Step.fire s0 (v.bounds.cascade.toNat + 1) = some (s', effs) →
          s.pending.length + effs.length ≤ L.count (pendingTable shs) ∧ v.invariants.appFits L.count (s.records, ()) ∧
          instChecksFit L.count s.records time s'.machines) := fun hf => by
      have hro := rounds_rel hP hshs hE hPE hopt hrd hord (v.bounds.cascade.toNat + 1) s0 hrec0 hst hinv.machines hms
        (ab := true) rfl hnid h1 (er.2 hf)
      simp only [Step.fireFrom, ite_true] at hro
      cases hfire : Step.fire s0 (v.bounds.cascade.toNat + 1) with
      | none =>
        rw [hfire] at hro
        rw [holds_ite]
        simp only [hro, Val.toBool, ite_true, holds_tt, true_iff]
        intro s' effs h; cases h
      | some p =>
        obtain ⟨s', effs⟩ := p
        rw [hfire] at hro
        obtain ⟨hover, hmach, hs', -, svN, zsN, hSN, hwN, hhN, xsN, hpN, hqN⟩ := hro
        rw [holds_ite, hover]
        simp only [Val.toBool, Bool.false_eq_true, ite_false]
        have ep := pending_exact hpend hSN hwN hhN hpN hqN h2
        have ec := instChecks_exact s.records time hrd hrec hst v.machines ro.tables s'.machines hmach h6
        rw [holds_andT, holds_andT, ep, hx, ec]
        constructor
        · intro h s'' effs' heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact h
        · intro h; exact h s' effs rfl
    exact ⟨fun ⟨p1, p2⟩ => ⟨p1, (rest p1).1 p2⟩, fun ⟨p1, p2⟩ => ⟨p1, (rest p1).2 p2⟩⟩
  · simp only [ht, decide_false, Bool.false_eq_true, false_implies]

end

end Tazuna.Smt
