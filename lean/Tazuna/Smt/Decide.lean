import Tazuna.Smt.Events
import Tazuna.Smt.Command

/-! What `decide` and the events it accepts with do, which the step's command and an own command's internal step share,
as `Step.execCommand` says: `decide` accepts with events or rejects, the events run through the events loop from the
running records, tables, next id and queue place (their slots count only on an acceptance), and `ensures` is checked
on the records they leave. `AccRel` is what such a run leaves, in the form every later part of a step continues from. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The terms of `decide` and what follows it: whether it accepted, its rejection and its events, what the events loop
leaves (nothing on a rejection), and the `ensures` rules on the records after. -/
structure DecideOut (v : ServiceV) where
  ok : Term
  rejection : Term
  events : Term
  after : EventsOut v
  ensures : List (Term × Term)

section
variable (L : Layout) (T : List TypeDecl)

/-- `decide`'s terms, the events loop's from the running records, tables, next id and queue place, and `ensures`' on
the records it leaves, at the context code `ctx`, with the condition: `decide`'s, the loop's, and `ensures`' where
`decide` accepted. -/
def encodeDecide (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (x : CommandV v.records v.event v.caller) (cc : CommandCode x) (apply : Code (Ty.fn [v.records, v.event] v.records))
    (ctx : Code (Ty.ctx v.records x.input v.caller)) (now records : Term) (xs : PerMachine (fun _ => Term) v.machines) (n q : Term) :
    Except Refusal (DecideOut v × Term) := do
  let (res, c2) ← cc.decide (ctx, ())
  let rest ← need "a result that has no term" (Code.term? _ res)
  let (d, _) ← need "a layout without the result type" (L.find? (Ty.result (.list v.event) x.rejection))
  let res := Term.share rest
  let ok := Term.is d 0 res
  let evs := Term.sel d 0 0 res
  let (dl, nl, dt) ← collD L (.list v.event) [v.event]
  let (o, c3) ← encodeEvents L T v shs senv apply now (gateSlots ok (slotsOf dl dt nl 1 evs)) records xs n q
  let rfc ← need "records that have no term" (Code.ofTerm? v.records o.records)
  let (ens, c4) ← cc.ensures (ctx, rfc, ())
  let ensures ← ruleTerms L ens
  pure (⟨ok, .sel d 1 0 res, evs, o, ensures⟩, andT c2 (andT c3 (.ite ok c4 tt)))

end

theorem toBool_bool (b : Bool) : (Val.bool b).toBool = b := rfl

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- Slots gated by a false flag hold no event. -/
theorem gate_false_events {f : Term} (hf : f.denote M = .bool false) :
    (S : List (Slot 1)) → ∃ sv, SlotsDen M (gateSlots f S) sv ∧ Holds2 (EBag L v.event) [] sv
  | [] => ⟨[], trivial, by simp [Holds2, occupied, Forall2]⟩
  | (_, xs) :: S => by
    obtain ⟨sv, hS, hh⟩ := gate_false_events hf S
    exact ⟨(false, Term.denotes M xs.1) :: sv, ⟨by simp [Term.denote, hf, Val.toBool], rfl, hS⟩,
      by simpa [Holds2, occupied] using hh⟩

/-- The news slots name pending requests for the requests they hold: externals list each. -/
theorem newsRel_writes {shs : List (PendingShape v.event)} {ds : List (String × DeclaredV)} {news : List PendingSlot}
    {effs : List (Sender × EffectV v.event)} {n0 : Nat} (h : NewsRel M L shs ds news effs n0) :
    ∃ ps, Forall2 (Step.Writes ds) (effs.zipIdx n0) ps := by
  obtain ⟨sv, zs, -, -, -, xs, hp, hq⟩ := h
  have h1 : Forall2 (Step.Writes ds) xs (zs.map fun z => pendingOf shs z.1 z.2) :=
    forall2_map_right _ (fun _ _ hw => hw.2) hq
  obtain ⟨ps, -, h2⟩ := forall2_perm hp (forall2_flip h1)
  exact ⟨ps, forall2_flip h2⟩

/-- The events loop over a list's slots from a step in progress: what `events_encode` says of the terms, and, for
whichever pending requests the step writes for the requests the events start, `applyEvents`' result. -/
theorem loop_apply {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca) (senv : StepEnv L shs) (a : Step.Acc v) {now : Term} (hnow : now.denote M = .int a.state.now)
    {S : List (Slot 1)} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv)
    {evs : List v.event.den0} (hev : Holds2 (EBag L v.event) (evs.map (Ty.up _ v.event_data)) sv)
    {records : Term} (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    {xs : PerMachine (fun _ => Term) v.machines} (hms : MachinesRel M L T v.machines xs a.state.machines)
    {n q : Term} {q0 : Nat} (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    {o : EventsOut v} {c : Term} (henc : encodeEvents L T v shs senv apply now S records xs n q = .ok (o, c))
    (hc : Holds M c) :
    let effs := (Step.reactAll T a.state evs).2
    RelV L v.records (Ty.up _ v.records_data (Step.reactAll T a.state evs).1.records) (o.records.denote M) ∧
      MachinesRel M L T v.machines o.tables (Step.reactAll T a.state evs).1.machines ∧
      o.nextId.denote M = .int ((a.state.nextId + (Step.reqsOf effs).length : Nat) : Int) ∧
      NewsRel M L shs v.declared o.news (Step.reqsOf effs) a.state.nextId ∧
      o.queued.denote M = .int ((q0 + (Step.queuedOf effs).length : Nat) : Int) ∧
      OwnRel M L o.owns (Step.queuedOf effs) q0 ∧
      ∀ ps, Forall2 (Step.Writes v.declared) ((Step.reqsOf effs).zipIdx a.state.nextId) ps →
        Step.applyEvents T a evs = .ok (({ a with state := (Step.reactAll T a.state evs).1, events := a.events ++ evs }.wrote
          ps (a.state.nextId + (Step.reqsOf effs).length)).queued (Step.queuedOf effs)) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := (events_encode chk hshs happ hca senv S sv hS evs hev
    a.state hnow hrec hms henc).2 hn hq hc
  exact ⟨r1, r2, r3, r4, r5, r6, fun ps hps => Step.applyEvents_requests T evs a ps hps⟩


/-- What a run from `a` leaves when it ends without a fault, as the terms say: the records and machines `o` denotes,
the fresh counter `fresh` denotes, the events `evs` applied, the requests `effs` started at wire ids from `a`'s next id
(for whichever pending requests `ps` the step writes for them, as the news slots hold), and the own commands and
queries `os` queued at places from `q0`, as the own slots hold. -/
def AccRel (M : Model) (L : Layout) (T : List TypeDecl) (shs : List (PendingShape v.event)) (a : Step.Acc v)
    (o : EventsOut v) (fresh : Term) (q0 : Nat) (r : Except Fault (Step.Acc v)) : Prop :=
  ∃ (recs : v.records.den0) (ms : Step.Machines v.machines) (fr : Nat) (evs : List v.event.den0)
    (effs : List (Sender × EffectV v.event)) (os : List (EffectV v.event)),
    (∀ ps, Forall2 (Step.Writes v.declared) (effs.zipIdx a.state.nextId) ps →
      r = .ok { state := { a.state with records := recs, machines := ms, fresh := fr,
                                         pending := a.state.pending ++ ps, nextId := a.state.nextId + ps.length },
                events := a.events ++ evs, out := a.out ++ ps.map Step.Pending.line, own := a.own ++ os }) ∧
    RelV L v.records (Ty.up _ v.records_data recs) (o.records.denote M) ∧ MachinesRel M L T v.machines o.tables ms ∧
    fresh.denote M = .int (fr : Int) ∧
    o.nextId.denote M = .int ((a.state.nextId + effs.length : Nat) : Int) ∧
    NewsRel M L shs v.declared o.news effs a.state.nextId ∧
    o.queued.denote M = .int ((q0 + os.length : Nat) : Int) ∧ OwnRel M L o.owns os q0

/-- The events loop over a list's slots from a step in progress, as `AccRel` says of `applyEvents`' result. -/
theorem loop_acc {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca) (senv : StepEnv L shs) (a : Step.Acc v) {now : Term} (hnow : now.denote M = .int a.state.now)
    {S : List (Slot 1)} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv)
    {evs : List v.event.den0} (hev : Holds2 (EBag L v.event) (evs.map (Ty.up _ v.event_data)) sv)
    {records : Term} (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    {xs : PerMachine (fun _ => Term) v.machines} (hms : MachinesRel M L T v.machines xs a.state.machines)
    {n q fresh : Term} {q0 : Nat} (hn : n.denote M = .int (Int.ofNat a.state.nextId)) (hq : q.denote M = .int q0)
    (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    {o : EventsOut v} {c : Term} (henc : encodeEvents L T v shs senv apply now S records xs n q = .ok (o, c))
    (hc : Holds M c) :
    AccRel M L T shs a o fresh q0 (Step.applyEvents T a evs) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, hr⟩ := loop_apply chk hshs happ hca senv a hnow hS hev hrec hms hn hq henc hc
  refine ⟨_, _, a.state.fresh, evs, Step.reqsOf (Step.reactAll T a.state evs).2,
    Step.queuedOf (Step.reactAll T a.state evs).2, fun ps hps => ?_, r1, r2, hfresh, r3, r4, r5, r6⟩
  rw [hr ps hps]
  have hl := forall2_zipIdx_length _ _ hps
  have hk := Step.reactAll_keeps T a.state evs
  simp only [Step.Acc.wrote, Step.Acc.queued, hl, Step.reactAll_pending]
  rw [hk]

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

/-- A run that sets only the fresh counter of `a` leaves, as `AccRel` says, what it leaves from `a`: the relation sets
the fresh counter itself. -/
theorem AccRel.of_fresh {shs : List (PendingShape v.event)} {a : Step.Acc v} {k : Nat} {o : EventsOut v} {f : Term}
    {q0 : Nat} {r : Except Fault (Step.Acc v)}
    (h : AccRel M L T shs { a with state := { a.state with fresh := k } } o f q0 r) : AccRel M L T shs a o f q0 r := h

/-- What a run that ends at `a'` leaves, as the terms say: the facts the next part of a step continues from. -/
theorem AccRel.ends {shs : List (PendingShape v.event)} {a a' : Step.Acc v} {o : EventsOut v} {f : Term} {q0 : Nat}
    (h : AccRel M L T shs a o f q0 (.ok a')) :
    RelV L v.records (Ty.up _ v.records_data a'.state.records) (o.records.denote M) ∧
      MachinesRel M L T v.machines o.tables a'.state.machines ∧ f.denote M = .int (Int.ofNat a'.state.fresh) ∧
      o.nextId.denote M = .int (Int.ofNat a'.state.nextId) ∧ a'.state.now = a.state.now ∧
      ∃ os, a'.own = a.own ++ os ∧ o.queued.denote M = .int ((q0 + os.length : Nat) : Int) ∧ OwnRel M L o.owns os q0 := by
  obtain ⟨recs, ms, fr, evs, effs, os, hr, r1, r2, r3, r4, r5, r6, r7⟩ := h
  obtain ⟨ps, hps⟩ := newsRel_writes r5
  obtain rfl := Except.ok.inj (hr ps hps)
  exact ⟨r1, r2, r3, by rw [r4, forall2_zipIdx_length _ _ hps]; rfl, rfl, os, rfl, r6, r7⟩

/-- A run that `AccRel` describes ends without a fault. -/
theorem AccRel.ok {shs : List (PendingShape v.event)} {a : Step.Acc v} {o : EventsOut v} {f : Term} {q0 : Nat}
    {r : Except Fault (Step.Acc v)} (h : AccRel M L T shs a o f q0 r) : ∃ a', r = .ok a' := by
  obtain ⟨_, _, _, _, _, _, hr, -, -, -, -, r5, -, -⟩ := h
  obtain ⟨ps, hps⟩ := newsRel_writes r5
  exact ⟨_, hr ps hps⟩

/-- Two runs in turn: what the first leaves, then the second from the state the first's terms denote, is what the
two leave together, the news and own slots of both. -/
theorem AccRel.bind {shs : List (PendingShape v.event)} {a : Step.Acc v} {o1 o2 : EventsOut v} {f1 f2 : Term}
    {q0 : Nat} {r : Except Fault (Step.Acc v)} {g : Step.Acc v → Except Fault (Step.Acc v)}
    (h1 : AccRel M L T shs a o1 f1 q0 r)
    (h2 : ∀ a1 (os : List (EffectV v.event)), r = .ok a1 → a1.own = a.own ++ os →
      RelV L v.records (Ty.up _ v.records_data a1.state.records) (o1.records.denote M) →
      MachinesRel M L T v.machines o1.tables a1.state.machines → f1.denote M = .int (Int.ofNat a1.state.fresh) →
      o1.nextId.denote M = .int (Int.ofNat a1.state.nextId) → o1.queued.denote M = .int ((q0 + os.length : Nat) : Int) →
      OwnRel M L o1.owns os q0 → AccRel M L T shs a1 o2 f2 (q0 + os.length) (g a1)) :
    AccRel M L T shs a { o2 with news := o1.news ++ o2.news, owns := o1.owns ++ o2.owns } f2 q0 (r >>= g) := by
  obtain ⟨recs0, ms0, fr0, evs0, effs0, os0, hr0, r1, r2, r3, r4, r5, r6, r7⟩ := h1
  obtain ⟨ps0, hps0⟩ := newsRel_writes r5
  have hl0 := forall2_zipIdx_length _ _ hps0
  have hrun0 := hr0 ps0 hps0
  obtain ⟨recs1, ms1, fr1, evs1, effs1, os1, hr1, s1, s2, s3, s4, s5, s6, s7⟩ :=
    h2 _ os0 hrun0 rfl r1 r2 r3 (by rw [r4, hl0]; rfl) r6 r7
  refine ⟨recs1, ms1, fr1, evs0 ++ evs1, effs0 ++ effs1, os0 ++ os1, fun ps hps => ?_, s1, s2, s3, ?_,
    newsRel_append r5 (by simpa [hl0] using s5), ?_, ownRel_append r7 (by simpa using s7)⟩
  · rw [List.zipIdx_append] at hps
    obtain ⟨ps0', ps1, rfl, hps0', hps1⟩ := forall2_split _ _ hps
    obtain rfl := writes_unique hps0' hps0
    rw [hrun0]
    show g _ = _
    rw [hr1 ps1 (by simpa [hl0] using hps1)]
    simp [List.append_assoc, Nat.add_assoc]
  · rw [s4]; simp [hl0, Nat.add_assoc]
  · rw [s6]; simp [Nat.add_assoc]

/-- Whether what follows `decide` fits, for what it returned: on acceptance, the events' applications in turn from `s`
and `ensures` at the records they leave. -/
def decideFits (S : Ty → Nat) (T : List TypeDecl) (s : State v) (x : CommandV v.records v.event v.caller)
    (ctx : (Ty.ctx v.records x.input v.caller).den0) : (Ty.result (.list v.event) x.rejection).den0 → Prop
  | .inl (events, ()) => eventsFit S T s events ∧ x.ensures.appFits S (ctx, (Step.reactAll T s events).1.records, ())
  | .inr _ => True

/-- `decide` and what follows it, from the step in progress `a` and the context `cv`: the condition holds exactly
when `decide` fits at the context and what follows fits (`decideFits`); wherever it holds, an acceptance runs the
events from `a` as the loop's terms say (`AccRel`) with the `ensures` rules the records after it break, and a
rejection is the one the terms denote and leaves `a` as it was. -/
theorem decide_encode {P : List AnySite} (chk : Checked P T v) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P) (x : CommandV v.records v.event v.caller) {cc : CommandCode x} {cx : Term}
    (hcc : CommandCode.of L x = .ok (cc, cx)) (hccx : Holds M cx)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca) (senv : StepEnv L shs) (a : Step.Acc v) (cv : (Ty.ctx v.records x.input v.caller).den0)
    {ctx : Code (Ty.ctx v.records x.input v.caller)} (hctx : Smt.Rel M L _ (Ty.up _ x.data.ctx cv) ctx)
    {now records n q fresh : Term} {xs : PerMachine (fun _ => Term) v.machines} {q0 : Nat} (hnow : now.denote M = .int a.state.now)
    (hrec : RelV L v.records (Ty.up _ v.records_data a.state.records) (records.denote M))
    (hms : MachinesRel M L T v.machines xs a.state.machines) (hn : n.denote M = .int (Int.ofNat a.state.nextId))
    (hq : q.denote M = .int q0) (hfresh : fresh.denote M = .int (Int.ofNat a.state.fresh))
    {o : DecideOut v} {c : Term} (henc : encodeDecide L T v shs senv x cc apply ctx now records xs n q = .ok (o, c)) :
    (Holds M c ↔ x.decide.appFits L.count (cv, ()) ∧ decideFits L.count T a.state x cv (x.decide.fn (cv, ()))) ∧
    (Holds M c → match x.decide.fn (cv, ()) with
      | .inl (events, ()) => o.ok.denote M = .bool true ∧
        brokenIn M o.ensures = Step.broken (x.ensures.fn (cv, (Step.reactAll T a.state events).1.records, ())) ∧
        AccRel M L T shs a o.after fresh q0 (Step.applyEvents T a events) ∧
        (∀ a', Step.applyEvents T a events = .ok a' → a'.state.records = (Step.reactAll T a.state events).1.records) ∧
        RelV L v.records (Ty.up _ v.records_data (Step.reactAll T a.state events).1.records) (o.after.records.denote M) ∧
        MachinesRel M L T v.machines o.after.tables (Step.reactAll T a.state events).1.machines
      | .inr (.inl (j, ())) => o.ok.denote M = .bool false ∧
        RelV L x.rejection (Ty.up _ x.data.rejection j) (o.rejection.denote M) ∧ AccRel M L T shs a o.after fresh q0 (.ok a)
      | .inr (.inr e) => e.elim) := by
  have hcR := CommandCode.rel_of hcc hccx
  obtain ⟨⟨_, c1'⟩, g1, hcc0⟩ := bind_ok.1 hcc
  obtain ⟨⟨_, c2'⟩, g2, hcc0⟩ := bind_ok.1 hcc0
  obtain ⟨⟨_, c3'⟩, g3, hcc0⟩ := bind_ok.1 hcc0
  cases pure_ok.1 hcc0
  obtain ⟨-, hca23⟩ := (holds_andT _ _).1 hccx
  obtain ⟨hca2, hca3⟩ := (holds_andT _ _).1 hca23
  obtain ⟨⟨res, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨rest, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨d, dn⟩, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dt⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o1, c3⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ens, c4⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨ensures, h15, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hargs := rels1 x.data.ctx x.data.ctxArgs hctx
  have e2 : Holds M c2 ↔ x.decide.appFits L.count (cv, ()) :=
    x.decide.app_exact g2 hca2 (by simp [Ty.ctx, Ty.isFn]) _ _ hargs h8
  have key : Holds M c2 →
      (Holds M (andT c3 (.ite (Term.is d 0 (Term.share rest)) c4 tt)) ↔
        decideFits L.count T a.state x cv (x.decide.fn (cv, ()))) ∧
      (Holds M (andT c3 (.ite (Term.is d 0 (Term.share rest)) c4 tt)) → match x.decide.fn (cv, ()) with
        | .inl (events, ()) => (Term.is d 0 (Term.share rest)).denote M = .bool true ∧
          brokenIn M ensures = Step.broken (x.ensures.fn (cv, (Step.reactAll T a.state events).1.records, ())) ∧
          AccRel M L T shs a o1 fresh q0 (Step.applyEvents T a events) ∧
          (∀ a', Step.applyEvents T a events = .ok a' → a'.state.records = (Step.reactAll T a.state events).1.records) ∧
          RelV L v.records (Ty.up _ v.records_data (Step.reactAll T a.state events).1.records) (o1.records.denote M) ∧
          MachinesRel M L T v.machines o1.tables (Step.reactAll T a.state events).1.machines
        | .inr (.inl (j, ())) => (Term.is d 0 (Term.share rest)).denote M = .bool false ∧
          RelV L x.rejection (Ty.up _ x.data.rejection j) ((Term.sel d 1 0 (Term.share rest)).denote M) ∧
          AccRel M L T shs a o1 fresh q0 (.ok a)
        | .inr (.inr e) => e.elim) := by
    intro hc2
    have hres := hcR.decide _ (ctx, ()) hargs res c2 h8 hc2
    erw [Ty.up_fn _ _ _ x.data.ctxArgs x.data.result] at hres
    have hres' := (rel_term (need_ok.1 h9) _).1 hres
    have hfd := need_ok.1 h10
    have hsh : (Term.share rest).denote M = rest.denote M := Term.denote_share M rest
    have hdata2 : (Ty.adt 2 [.list v.event, x.rejection] [[x.rejection]]).isData = true := by
      simp only [Ty.isData, Ty.isDatas, Ty.isDatass, x.data.rejection, Bool.and_true]
    cases hdv : x.decide.fn (cv, ()) with
    | inr q' =>
      match q', hdv with
      | .inl (j, ()), hdv =>
        rw [hdv] at hres'
        erw [Ty.up_inr 2 _ _ _ x.data.result hdata2, Ty.up_inl 2 _ _ _ hdata2
          (by simp only [Ty.isData, Ty.isDatas, x.data.rejection, Bool.and_true]),
          Ty.up_tuple _ _ _ x.data.rejection rfl] at hres'
        obtain ⟨d', n', hf', vals, hw, rv, rest', rfl, hrv, rfl⟩ := hres'
        obtain rfl := find_det hfd hf'
        have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool false := by simp [Term.denote, hsh, hw]
        obtain ⟨sv1, hS1, hh1⟩ := gate_false_events (L := L) (v := v) hok' _
        have e3 := (events_encode chk hshs happ hca senv _ sv1 hS1 []
          (by simpa using hh1) a.state hnow hrec hms h12).1
        have hite : Holds M (.ite (Term.is d 0 (Term.share rest)) c4 tt) := by
          rw [holds_ite, hok']; exact holds_tt
        refine ⟨by rw [holds_andT, e3]; exact iff_of_true ⟨trivial, hite⟩ trivial, fun hc => ?_⟩
        obtain ⟨p1, p2, p3, p4, p5, p6, -⟩ := loop_apply (T := T) chk hshs happ hca senv a hnow hS1 (evs := [])
          (by simpa using hh1) hrec hms hn hq h12 ((holds_andT _ _).1 hc).1
        simp only [Step.reactAll, Step.reqsOf, Step.queuedOf, List.filter_nil, List.map_nil, List.length_nil,
          Nat.add_zero] at p1 p2 p3 p4 p5 p6
        refine ⟨hok', by simpa [Term.denote, hsh, hw] using hrv,
          a.state.records, a.state.machines, a.state.fresh, [], [], [], fun ps hps => ?_, p1, p2, hfresh, p3, p4,
          by simpa using p5, p6⟩
        cases ps with
        | nil => simp
        | cons => exact hps.elim
      | .inr e, _ => exact e.elim
    | inl p =>
      obtain ⟨events, ⟨⟩⟩ := p
      rw [hdv] at hres'
      erw [Ty.up_inl 2 _ _ _ x.data.result (by simp only [Ty.isData, Ty.isDatas, v.event_data, Bool.and_true]),
        Ty.up_tuple _ _ _ x.data.events rfl] at hres'
      obtain ⟨d', n', hf', vals, hw, ev, rest', rfl, hev, rfl⟩ := hres'
      obtain rfl := find_det hfd hf'
      have hok' : (Term.is d 0 (Term.share rest)).denote M = .bool true := by simp [Term.denote, hsh, hw]
      have hevs : Smt.Rel M L (.list v.event) (Ty.up _ x.data.events events) (Term.sel d 0 0 (Term.share rest)) := by
        show RelV _ _ _ _
        rw [sel_ctor 0 (hsh.trans hw)]; exact hev
      obtain ⟨sv, hS, -, -, hh⟩ := list_view hevs h11
      erw [Ty.up_list _ _ v.event_data] at hh
      have hS' := gate_true hok' hS
      have e3 := (events_encode chk hshs happ hca senv _ sv hS' events hh a.state hnow hrec hms h12).1
      have hite : Holds M (.ite (Term.is d 0 (Term.share rest)) c4 tt) ↔ Holds M c4 := by
        rw [holds_ite, hok']; rfl
      have hloop := fun hc3 : Holds M c3 =>
        loop_apply (T := T) chk hshs happ hca senv a hnow hS' hh hrec hms hn hq h12 hc3
      have hens : Holds M c3 → (Holds M c4 ↔ x.ensures.appFits L.count (cv, (Step.reactAll T a.state events).1.records, ())) ∧
          (Holds M c4 → brokenIn M ensures = Step.broken (x.ensures.fn (cv, (Step.reactAll T a.state events).1.records, ()))) := by
        intro hc3
        have hrfc : Smt.Rel M L v.records (Ty.up _ v.records_data (Step.reactAll T a.state events).1.records) rfc :=
          (rel_ofTerm (need_ok.1 h13) _).2 (hloop hc3).1
        have hargs3 := rels2 x.data.ctx v.records_data x.data.ensArgs hctx hrfc
        refine ⟨x.ensures.app_exact g3 hca3 (by
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · simp [Ty.ctx, Ty.isFn]
          · exact ofTerm_notFn (need_ok.1 h13)) _ _ hargs3 h14, fun hc4 => ?_⟩
        have hens := hcR.ensures _ _ hargs3 ens c4 h14 hc4
        erw [Ty.up_fn _ Ty.rules _ x.data.ensArgs rfl] at hens
        exact rules_broken h15 _ hens
      rw [holds_andT, hite, e3]
      refine ⟨⟨fun ⟨p3, hc4⟩ => ⟨p3, ((hens (e3.2 p3)).1).1 hc4⟩, fun ⟨p3, p4⟩ => ⟨p3, ((hens (e3.2 p3)).1).2 p4⟩⟩,
        fun ⟨p3, hc4⟩ => ?_⟩
      have hc3 := e3.2 p3
      refine ⟨hok', (hens hc3).2 hc4,
        loop_acc (T := T) chk hshs happ hca senv a hnow hS' hh hrec hms hn hq hfresh h12 hc3, fun a' ha' => ?_,
        (hloop hc3).1, (hloop hc3).2.1⟩
      obtain ⟨-, -, -, p4, -, -, p7⟩ := hloop hc3
      obtain ⟨ps, hps⟩ := newsRel_writes p4
      rw [p7 ps hps] at ha'
      cases ha'
      rfl
  refine ⟨?_, fun hc => ?_⟩
  · rw [holds_andT]
    exact ⟨fun ⟨hc2, hx⟩ => ⟨e2.1 hc2, ((key hc2).1).1 hx⟩, fun ⟨p2, px⟩ => ⟨e2.2 p2, ((key (e2.2 p2)).1).2 px⟩⟩
  · obtain ⟨hc2, hx⟩ := (holds_andT _ _).1 hc
    exact (key hc2).2 hx

end

end Tazuna.Smt
