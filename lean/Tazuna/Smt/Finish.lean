import Tazuna.Smt.Events

/-! What every step with a list of events shares: the events loop (`encodeEvents`) and the pending write give the
state `applyEvents` leaves (`events_apply`), and the step ends by checking the service's invariants on the records
after and every machine's on the tables after (`finish_ok`, `encodeInvariants`). The event step is the loop over one
slot holding the wrapped value (`event_step`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout)

/-- The event a subscription wraps the received value into, with its condition. -/
def encodeWrap {v : ServiceV} {i : Fin v.subscribes.length} (ec : EventCode v i) (value : Term) :
    Except Refusal (Term × Term) := do
  let vc ← need "a value that has no term" (Code.ofTerm? _ value)
  let (ev, c) ← ec.wrap (vc, ())
  let et ← need "an event that has no term" (Code.term? _ ev)
  pure (et, c)

/-- The service's invariants on the records term: each rule's name and whether it holds, with the condition. -/
def encodeInvariants {r : Ty} (inv : Code (Ty.fn [r] Ty.rules)) (records : Term) :
    Except Refusal (List (Term × Term) × Term) := do
  let rc ← need "records that have no term" (Code.ofTerm? r records)
  let (invs, c) ← inv (rc, ())
  let rules ← ruleTerms L invs
  pure (rules, c)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model}

theorem wrap_rel {v : ServiceV} (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
    (hd : EventData v i) {ec : EventCode v i} (he : ec.Rel M L hd) {sv : Term}
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) {et c : Term} (henc : encodeWrap ec sv = .ok (et, c))
    (hc : Holds M c) : RelV L v.event (Ty.up _ hd.event ((v.subscribes.get i).wrap.fn (value, ()))) (et.denote M) := by
  obtain ⟨vc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ev, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨et', h3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvc : Smt.Rel M L _ (Ty.up _ hd.value value) vc := (rel_ofTerm (need_ok.1 h1) _).2 hsv
  have hev := he.wrap _ (vc, ()) (rels1 hd.value hd.wrapArgs hvc) ev c h2 hc
  erw [Ty.up_fn _ _ _ hd.wrapArgs hd.event] at hev
  exact (rel_term (need_ok.1 h3) _).1 hev

/-- The wrap's condition is exact: it holds exactly when the wrap fits at the value. -/
theorem wrap_exact {v : ServiceV} (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
    (hd : EventData v i) {ec : EventCode v i} {ce : Term} (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce)
    {sv : Term} (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) {et c : Term}
    (henc : encodeWrap ec sv = .ok (et, c)) :
    Holds M c ↔ (v.subscribes.get i).wrap.appFits L.count (value, ()) := by
  obtain ⟨⟨a, c1'⟩, -, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2'⟩, g2, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3'⟩, -, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  obtain ⟨-, hcwn⟩ := (holds_andT _ _).1 hce
  obtain ⟨hcw, -⟩ := (holds_andT _ _).1 hcwn
  obtain ⟨vc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ev, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨et', -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvc : Smt.Rel M L _ (Ty.up _ hd.value value) vc := (rel_ofTerm (need_ok.1 h1) _).2 hsv
  exact (v.subscribes.get i).wrap.app_exact g2 hcw (by simpa using ofTerm_notFn (need_ok.1 h1)) _ _
    (rels1 hd.value hd.wrapArgs hvc) h2

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

section
variable {v : ServiceV} (T : List TypeDecl)

/-- A step whose events started no own command or query ends by checking the invariants. -/
theorem finish_ok (s0 : State v) (a : Step.Acc v) (ha : a.own = []) (outcome : Outcome) :
    Step.finish T s0 (.ok a) outcome = match Step.invariants a.state with
      | n :: _ => ⟨s0, .fault (.invariant n), [], []⟩
      | [] => ⟨a.state, outcome, a.events, a.out⟩ := by
  have : Step.settle T v.bounds.cascade.toNat a = .ok a := by
    unfold Step.settle; rw [ha]
  simp only [Step.finish, bind, Except.bind, this]
  rfl

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model}

/-- T2 for applying a list of events and writing their requests: wherever the conditions hold, `applyEvents` succeeds
with the records and machines the terms denote, the requests `ps` written at the next ids and sent, the next id term
denoting the id after them, and the new pending table term denoting the pending requests as a multiset. -/
theorem events_apply {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hap : (Ty.fn [v.records, v.event] v.records).isData = true)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} (happ : Smt.Rel M L _ (Ty.up _ hap v.apply.fn) apply)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    (a : Step.Acc v) (hinv : Step.Inv P a.state) {now : Term} (hnow : now.denote M = .int a.state.now)
    {S : List Slot} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = 1)
    {evs : List v.event.den0} (hev : Holds2 (EBag L v.event) (evs.map (Ty.up _ hed)) sv)
    {records : Term} (hrec : RelV L v.records (Ty.up _ hrd a.state.records) (records.denote M))
    {xs : List Term} (hms : MachinesRel M L T v.machines xs a.state.machines)
    {nT : Term} (hn : nT.denote M = .int (Int.ofNat a.state.nextId))
    {o : EventsOut} {c : Term} (henc : encodeEvents L T v shs dE dP dopt apply now S records xs nT = .ok (o, c))
    (hc : Holds M c) {pending : Term} (hpend : PendingRel L shs (pending.denote M) a.state.pending)
    {pT cp : Term} (hpe : encodePending L shs pending o.news = .ok (pT, cp)) (hcp : Holds M cp) :
    ∃ ps, Step.applyEvents T a evs = .ok ({ a with state := (Step.reactAll T a.state evs).1, events := a.events ++ evs }.wrote
        ps (a.state.nextId + ps.length)) ∧
      (∃ ps', ps'.Perm (a.state.pending ++ ps) ∧ PendingRel L shs (pT.denote M) ps') ∧
      RelV L v.records (Ty.up _ hrd (Step.reactAll T a.state evs).1.records) (o.records.denote M) ∧
      MachinesRel M L T v.machines o.tables (Step.reactAll T a.state evs).1.machines ∧
      o.nextId.denote M = .int (Int.ofNat (a.state.nextId + ps.length)) := by
  have hvm : ∀ m ∈ v.machines, m.Reach P := by
    intro m hm
    rw [← hinv.machinesOf] at hm
    obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 hm
    exact hinv.machines sm hsm
  obtain ⟨r1, r2, r3, sv', zs, hS', hw', hh', xs', hxp, hq⟩ := events_rel hP hvx hvm hshs hor hrd hed hap happ hE hPE
    hopt S sv hS hw evs hev a.state hnow hrec hms hn henc hc
  obtain ⟨ps, hps, ps', hperm, hrelP⟩ := pending_rel hpend hinv.below hinv.nodup hS' hw' hh' hxp hq hpe hcp
  have hlen : ps.length = (Step.reactAll T a.state evs).2.length := by
    rw [← forall2_length hps, List.length_zipIdx]
  refine ⟨ps, ?_, ⟨ps', hperm, hrelP⟩, r1, r2, ?_⟩
  · obtain ⟨hr, hq⟩ := Step.reqs_of_writes hps
    rw [Step.applyEvents_requests T evs a ps (by rw [hr]; exact hps), hr, hq, hlen]
    simp [Step.Acc.queued]
  · rw [r3, hlen]; rfl

/-- T2 for an event: wherever the conditions hold, a broken invariant's name (the service's first, then each machine's
instances in key order) is the step's fault, and otherwise the step is accepted with the records, the instance tables
and the event the terms denote; it writes the requests `ps` (machines' first, then reactions') at the next wire ids
and sends them as its out lines, the pending table term denotes the pending requests (as a multiset) and the next id
term the next wire id. -/
theorem event_step {P : List AnySite} (hP : SitesUnique P) {v : ServiceV} (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce) {records sv now nextIdT pending : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId)) (hpend : PendingRel L shs (pending.denote M) s.pending)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    {et cw : Term} (hwr : encodeWrap ec sv = .ok (et, cw)) (hcw : Holds M cw)
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : EventsOut} {c : Term}
    (henc : encodeEvents L T v shs dE dP dopt ec.apply now [(tt, [et])] records xs nextIdT = .ok (o, c))
    (hc : Holds M c) {rules : List (Term × Term)} {ci : Term}
    (hi : encodeInvariants L ec.invariants o.records = .ok (rules, ci)) (hci : Holds M ci)
    {checks : List (List InstCheck)} {ck : Term}
    (hck : encodeInstChecks L T v.machines o.tables o.records now = .ok (checks, ck)) (hcck : Holds M ck)
    {pT cp : Term} (hpe : encodePending L shs pending o.news = .ok (pT, cp)) (hcp : Holds M cp) :
    let r := step T v s (.event i value)
    match brokenIn M rules ++ checksBroken L T M v.machines checks with
    | n :: _ => r = ⟨s, .fault (.invariant n), [], []⟩
    | [] => r.outcome = .accepted ∧
        (∃ ps, r.out = ps.map Step.Pending.line ∧ r.state.pending = s.pending ++ ps ∧
          r.state.nextId = s.nextId + ps.length ∧ ∃ ps', ps'.Perm r.state.pending ∧ PendingRel L shs (pT.denote M) ps') ∧
        o.nextId.denote M = .int (Int.ofNat r.state.nextId) ∧
        r.state = { s with records := r.state.records, machines := r.state.machines,
                           pending := r.state.pending, nextId := r.state.nextId } ∧
        RelV L v.records (Ty.up _ hd.records r.state.records) (o.records.denote M) ∧
        MachinesRel M L T v.machines o.tables r.state.machines ∧
        ∃ e, r.events = [e] ∧ RelV L v.event (Ty.up _ hd.event e) (et.denote M) := by
  intro r
  have he := EventCode.rel_of hd hec hce
  have hevT := wrap_rel i value hd he hsv hwr hcw
  let ev := (v.subscribes.get i).wrap.fn (value, ())
  obtain ⟨ps, happly, hperm, r1, r2, r3⟩ := events_apply (T := T) hP hvx hshs hor hd.records hd.event hd.apply he.apply
    hE hPE hopt { state := s } hinv hnow (S := [(tt, [et])]) (sv := [(true, [et.denote M])]) ⟨rfl, rfl, trivial⟩
    (by simp) (evs := [ev]) ⟨⟨_, rfl, hevT⟩, trivial⟩ hrec hms hnid henc hc hpend hpe hcp
  have hs : r = Step.finish T s (Step.applyEvents T { state := s } [ev]) .accepted := rfl
  rw [happly, finish_ok T s _ rfl] at hs
  let s' := (Step.reactAll T s [ev]).1
  have hb := invariants_rel v.invariants hd.records hd.invariants he.invariants s'.records r1 hi hci
  have hor' : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (hor m hm).2
  have hbs := instChecks_rel s'.records s.now hd.records r1 hnow v.machines _ _ r2 hor' hck hcck
  have hinvs : Step.invariants ({ ({ state := s } : Step.Acc v) with state := s', events := [] ++ [ev] }.wrote ps
      (s.nextId + ps.length)).state = brokenIn M rules ++ checksBroken L T M v.machines checks := by
    simp only [Step.Acc.wrote, Step.invariants]
    rw [hb, hbs, Step.reactAll_now]
    rfl
  rw [hinvs] at hs
  rw [hs]
  cases brokenIn M rules ++ checksBroken L T M v.machines checks with
  | cons n ns => rfl
  | nil =>
    obtain ⟨ps', hp', hrelP⟩ := hperm
    refine ⟨rfl, ⟨ps, by simp [Step.Acc.wrote], rfl, rfl, ps', hp', hrelP⟩, r3, ?_, r1, r2, ev, rfl, hevT⟩
    simp only [Step.Acc.wrote]
    rw [Step.reactAll_keeps T s [ev]]

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- `event_step`'s conditions are exact together: they hold exactly when the kept sources fit, the wrap fits at the
value, the event's applications fit (`eventsFit`), and the service's and every machine's invariants fit on the state
after it. -/
theorem event_step_exact {P : List AnySite} (hP : SitesUnique P) (hvx : ∀ x ∈ v.reactions, x.Reach P)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) (hd : EventData v i) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) {records sv now nextIdT : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    (hnid : nextIdT.denote M = .int (Int.ofNat s.nextId))
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true ∧ m.key.ordered T = true)
    {et cw : Term} (hwr : encodeWrap ec sv = .ok (et, cw))
    {dE nE dP nP dopt nopt : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (dE, nE))
    (hPE : L.find? (pendingEntry shs) = some (dP, nP))
    (hopt : L.find? (Ty.option (.dsl .effect [v.event])) = some (dopt, nopt))
    {o : EventsOut} {c : Term}
    (henc : encodeEvents L T v shs dE dP dopt ec.apply now [(tt, [et])] records xs nextIdT = .ok (o, c))
    {rules : List (Term × Term)} {ci : Term} (hi : encodeInvariants L ec.invariants o.records = .ok (rules, ci))
    {checks : List (List InstCheck)} {ck : Term}
    (hck : encodeInstChecks L T v.machines o.tables o.records now = .ok (checks, ck)) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    let s' := (Step.reactAll T s [ev]).1
    Holds M (andT ce (andT cw (andT c (andT ci ck)))) ↔
      ((v.apply.fits L.count).1 ∧ ((v.subscribes.get i).wrap.fits L.count).1 ∧ (v.invariants.fits L.count).1) ∧
      (v.subscribes.get i).wrap.appFits L.count (value, ()) ∧ eventsFit L.count T s [ev] ∧
      v.invariants.appFits L.count (s'.records, ()) ∧ instChecksFit L.count s'.records s.now s'.machines := by
  intro ev s'
  have hvm : ∀ m ∈ v.machines, m.Reach P := by
    intro m hm
    rw [← hinv.machinesOf] at hm
    obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 hm
    exact hinv.machines sm hsm
  have e0 := eventCode_exact (M := M) hec
  have e1 : ∀ hce : Holds M ce, (Holds M cw ↔ (v.subscribes.get i).wrap.appFits L.count (value, ())) :=
    fun hce => wrap_exact i value hd hec hce hsv hwr
  obtain ⟨⟨a, c1'⟩, g1, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2'⟩, g2, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3'⟩, g3, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  have hrels : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw) (hc : Holds M c),
      RelV L v.records (Ty.up _ hd.records s'.records) (o.records.denote M) ∧
        MachinesRel M L T v.machines o.tables s'.machines := fun hce hcw hc => by
    have he := EventCode.rel_of hd hec hce
    have hevT := wrap_rel i value hd he hsv hwr hcw
    obtain ⟨r1, r2, -⟩ := events_rel hP hvx hvm hshs hor hd.records hd.event hd.apply he.apply hE hPE hopt
      [(tt, [et])] [(true, [et.denote M])] ⟨rfl, rfl, trivial⟩ (by simp) [ev] ⟨⟨_, rfl, hevT⟩, trivial⟩ s hnow hrec hms
      hnid henc hc
    exact ⟨r1, r2⟩
  have e2 : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw), (Holds M c ↔ eventsFit L.count T s [ev]) :=
    fun hce hcw => by
      have he := EventCode.rel_of hd hec hce
      have hevT := wrap_rel i value hd he hsv hwr hcw
      exact events_exact (fun m hm => (hor m hm).1) hd.records hd.event g1 ((holds_andT _ _).1 hce).1
        [(tt, [et])] [(true, [et.denote M])] ⟨rfl, rfl, trivial⟩ (by simp) [ev] ⟨⟨_, rfl, hevT⟩, trivial⟩ s hnow hrec hms
        henc
  have e3 : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw) (hc : Holds M c),
      (Holds M ci ↔ v.invariants.appFits L.count (s'.records, ())) := fun hce hcw hc =>
    invariants_exact v.invariants hd.records g3 ((holds_andT _ _).1 ((holds_andT _ _).1 hce).2).2 s'.records
      (hrels hce hcw hc).1 hi
  have e4 : ∀ (hce : Holds M (andT c1' (andT c2' c3'))) (hcw : Holds M cw) (hc : Holds M c),
      (Holds M ck ↔ instChecksFit L.count s'.records s.now s'.machines) := fun hce hcw hc =>
    instChecks_exact s'.records s.now hd.records (hrels hce hcw hc).1 hnow v.machines o.tables s'.machines
      (hrels hce hcw hc).2 hck
  rw [holds_andT (andT c1' (andT c2' c3')), holds_andT cw, holds_andT c, holds_andT ci]
  constructor
  · rintro ⟨hce, hcw, hc, hci, hck⟩
    exact ⟨e0.1 hce, (e1 hce).1 hcw, (e2 hce hcw).1 hc, (e3 hce hcw hc).1 hci, (e4 hce hcw hc).1 hck⟩
  · rintro ⟨p0, p1, p2, p3, p4⟩
    have hce := e0.2 p0
    have hcw := (e1 hce).2 p1
    have hc := (e2 hce hcw).2 p2
    exact ⟨hce, hcw, hc, (e3 hce hcw hc).2 p3, (e4 hce hcw hc).2 p4⟩

end

end Tazuna.Smt
