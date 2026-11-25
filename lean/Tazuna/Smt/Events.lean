import Tazuna.Smt.Checked
import Tazuna.Smt.Reactions
import Tazuna.Smt.EventMachines
import Tazuna.Smt.Admit

/-! A list of events in one step, as a command's events, an answer's or one event: each event in turn is applied, every
machine reacts to it, then every reaction, and the requests they start are written at the next wire ids. The encoding
runs over the list's slots (`encodeEvents`); an occupied slot takes the records, instance tables and next id the slot
before it left, an empty one passes them on, and its requests' flags are and-ed with its own, so whatever its free
item holds starts nothing. The invariants are the caller's: a step checks them once, after all its events. -/

namespace Tazuna.Ir

namespace Step

variable {v : ServiceV} (T : List TypeDecl)

/-- Every event's reaction in turn, from `s`: the state after them and the effects they start, in the step's order. -/
def reactAll (s : State v) : List v.event.den0 → State v × List (Sender × EffectV v.event)
  | [] => (s, [])
  | ev :: evs => ((reactAll (react T s ev).1 evs).1, (react T s ev).2 ++ (reactAll (react T s ev).1 evs).2)

theorem react_with (s : State v) (ps : Bag (Pending v.event)) (n : Nat) (ev : v.event.den0) :
    react T { s with pending := ps, nextId := n } ev =
      ({ (react T s ev).1 with pending := ps, nextId := n }, (react T s ev).2) := rfl

/-- The reactions read neither the pending requests nor the next id. -/
theorem reactAll_with (s : State v) (ps : Bag (Pending v.event)) (n : Nat) : (evs : List v.event.den0) →
    reactAll T { s with pending := ps, nextId := n } evs =
      ({ (reactAll T s evs).1 with pending := ps, nextId := n }, (reactAll T s evs).2)
  | [] => rfl
  | ev :: evs => by
    simp only [reactAll]
    rw [react_with, reactAll_with _ _ _ evs]

/-- The reactions change only the records and the machines. -/
theorem reactAll_keeps (s : State v) : (evs : List v.event.den0) →
    (reactAll T s evs).1 = { s with records := (reactAll T s evs).1.records, machines := (reactAll T s evs).1.machines }
  | [] => rfl
  | ev :: evs => by
    simp only [reactAll]
    rw [reactAll_keeps (react T s ev).1 evs]
    rfl

theorem reactAll_pending (s : State v) (evs : List v.event.den0) : (reactAll T s evs).1.pending = s.pending := by
  rw [reactAll_keeps]

theorem reactAll_now (s : State v) (evs : List v.event.den0) : (reactAll T s evs).1.now = s.now := by
  rw [reactAll_keeps]

theorem reactAll_fresh (s : State v) (evs : List v.event.den0) : (reactAll T s evs).1.fresh = s.fresh := by
  rw [reactAll_keeps]

/-- Events whose machines and reactions start requests that externals list: the records and machines react to each in
turn, the requests are written at the next ids and sent, and the own commands and queries are queued. -/
theorem applyEvents_requests : (evs : List v.event.den0) → (a : Acc v) → (ps : List (Pending v.event)) →
    Tazuna.Smt.Forall2 (Writes v.declared) ((reqsOf (reactAll T a.state evs).2).zipIdx a.state.nextId) ps →
    applyEvents T a evs = .ok (({ a with state := (reactAll T a.state evs).1, events := a.events ++ evs }.wrote ps
      (a.state.nextId + (reqsOf (reactAll T a.state evs).2).length)).queued (queuedOf (reactAll T a.state evs).2))
  | [], a, [], _ => by
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp [applyEvents, reactAll, Acc.wrote, Acc.queued, pure, Except.pure]
  | ev :: evs, a, ps, hps => by
    simp only [reactAll, reqsOf, List.filter_append, List.zipIdx_append] at hps
    obtain ⟨ps1, ps2, rfl, h1, h2⟩ := Tazuna.Smt.forall2_split _ _ hps
    have hs : applyEvents T a (ev :: evs) =
        (start { a with state := (react T a.state ev).1, events := a.events ++ [ev] } (react T a.state ev).2) >>=
          fun a' => applyEvents T a' evs := rfl
    rw [hs, start_requests { a with state := (react T a.state ev).1, events := a.events ++ [ev] } _ ps1 h1]
    simp only [bind, Except.bind]
    let a' := (({ a with state := (react T a.state ev).1, events := a.events ++ [ev] } : Acc v).wrote ps1
      ((react T a.state ev).1.nextId + (reqsOf (react T a.state ev).2).length)).queued (queuedOf (react T a.state ev).2)
    rw [applyEvents_requests evs a' ps2 (by simp only [a', Acc.wrote, Acc.queued, reactAll_with]; exact h2)]
    obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _⟩ := a
    simp only [a', Acc.wrote, Acc.queued, reactAll_with, reactAll, reactAll_pending, reactAll_now, reactAll_fresh,
      reqsOf, queuedOf, List.filter_append, List.map_append, List.append_assoc, List.length_append,
      List.singleton_append, Except.ok.injEq]
    simp only [Nat.add_assoc]
    rfl
  | [], _, _ :: _, h => h.elim

end Step

end Tazuna.Ir

namespace Tazuna.Smt

open Tazuna.Ir

/-- What a list of events encodes: the records and instance tables after them, the next wire id after the requests
they start, those requests' pending slots, the own slots of the own commands and queries they queue, and the queue
place after them. -/
structure EventsOut (v : ServiceV) where
  records : Term
  tables : PerMachine (fun _ => Term) v.machines
  nextId : Term
  news : List PendingSlot
  owns : List OwnSlot
  queued : Term

/-- The slots with each flag and-ed with `f`. -/
def gateSlots {w : Nat} (f : Term) (S : List (Slot w)) : List (Slot w) := S.map fun (g, xs) => (Term.share (.and f g), xs)

section
variable (L : Layout) (T : List TypeDecl)

/-- The events of a list's slots in turn, from the records, instance tables, next id and queue place terms: each
occupied slot's event is applied, every machine reacts, its starts are ranked from the next id (requests) and the queue
place (own commands and queries), then every reaction's effects follow; the condition asks for each occupied slot's
applications. -/
def encodeEvents (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (now : Term) :
    List (Slot 1) → (records : Term) → (xs : PerMachine (fun _ => Term) v.machines) → (n q : Term) →
    Except Refusal (EventsOut v × Term)
  | [], records, xs, n, q => pure (⟨records, xs, n, [], [], q⟩, tt)
  | (f, ys) :: S, records, xs, n, q => do
    let ev := Term.share ys[0]
    let rc ← Code.ofTermE v.records records
    let ec ← Code.ofTermE v.event ev
    let (r', ca) ← apply (rc, ec, ())
    let rt ← Code.termE v.records r'
    let rt := Term.share rt
    let (outs, cm) ← encodeMachines L v.machines xs rt now ev
    let (news, nT, oS, qT) ← encodeStarts L T shs v.declared senv v.machines (outs.map (·.starts)) n q
    let (rnews, nR, rown, qR, cr) ← encodeReactions L shs v.declared senv.dE senv.dP v.reactions rt now ev nT qT
    let pick (a b : Term) := Term.share (.ite f a b)
    let (o, c) ← encodeEvents v shs senv apply now S (pick rt records)
      (PerMachine.zipWith pick (outs.map (·.table)) xs) (pick nR n) (pick qR q)
    pure (⟨o.records, o.tables, o.nextId, gatePending f (news ++ rnews) ++ o.news, gateOwns f (oS ++ rown) ++ o.owns,
      o.queued⟩, andT (.ite f (andT ca (andT cm cr)) tt) c)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem gate_true {f : Term} (hf : f.denote M = .bool true) {w : Nat} :
    {S : List (Slot w)} → {sv : List (Bool × List Val)} → SlotsDen M S sv → SlotsDen M (gateSlots f S) sv
  | [], [], _ => trivial
  | (g, xs) :: S, (b, vs) :: sv, ⟨hg, hxs, hS⟩ =>
    ⟨by simp [Term.denote, hf, hg, Val.toBool], hxs, gate_true hf (S := S) (sv := sv) hS⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem gatePending_slot (f : Term) (S : List PendingSlot) :
    (gatePending f S).map PendingSlot.slot = gateSlots f (S.map PendingSlot.slot) := by
  simp [gatePending, gateSlots, PendingSlot.slot]

theorem gateOwns_slot (f : Term) (S : List OwnSlot) :
    (gateOwns f S).map OwnSlot.slot = gateSlots f (S.map OwnSlot.slot) := by
  simp [gateOwns, gateSlots, OwnSlot.slot]

theorem newsRel_gate {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {f : Term}
    (hf : f.denote M = .bool true) {S : List PendingSlot} {effs : List (Sender × EffectV e)} {n0 : Nat}
    (h : NewsRel M L shs ds S effs n0) : NewsRel M L shs ds (gatePending f S) effs n0 := by
  obtain ⟨sv, zs, hS, hw, hh, xs, hp, hq⟩ := h
  exact ⟨sv, zs, by rw [gatePending_slot]; exact gate_true hf hS, hw, hh, xs, hp, hq⟩

theorem denotes_length : (xs : List Term) → (Term.denotes M xs).length = xs.length
  | [] => rfl
  | _ :: xs => congrArg (· + 1) (denotes_length xs)

/-- Slots gated by a false flag hold nothing. -/
theorem newsRel_gate_false {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {f : Term}
    (hf : f.denote M = .bool false) {S : List PendingSlot} (n0 : Nat) :
    NewsRel M L shs ds (gatePending f S) [] n0 := by
  have hS : SlotsDen M ((gatePending f S).map PendingSlot.slot)
      ((S.map PendingSlot.slot).map fun sl => (false, Term.denotes M sl.2.1)) := by
    rw [gatePending_slot]
    induction S.map PendingSlot.slot with
    | nil => trivial
    | cons sl S ih => exact ⟨by simp [Term.denote, hf, Val.toBool], rfl, ih⟩
  have hocc : occupied ((S.map PendingSlot.slot).map fun sl => (false, Term.denotes M sl.2.1)) = [] := by
    induction S with
    | nil => rfl
    | cons sl S ih => simp [occupied]
  refine ⟨_, [], hS, ?_, by rw [Holds2, hocc]; trivial, [], by simp, trivial⟩
  intro p hp
  obtain ⟨sl, -, rfl⟩ := List.mem_map.1 hp
  simp [denotes_length, sl.2.2]

theorem ownRel_gate {f : Term} (hf : f.denote M = .bool true) {S : List OwnSlot} {os : List (EffectV e)} {q0 : Nat}
    (h : OwnRel M L S os q0) : OwnRel M L (gateOwns f S) os q0 := by
  obtain ⟨sv, zs, hS, hw, hh, hp⟩ := h
  exact ⟨sv, zs, by rw [gateOwns_slot]; exact gate_true hf hS, hw, hh, hp⟩

/-- Own slots gated by a false flag hold nothing. -/
theorem ownRel_gate_false {f : Term} (hf : f.denote M = .bool false) {S : List OwnSlot}
    (q0 : Nat) : OwnRel M L (gateOwns f S) ([] : List (EffectV e)) q0 := by
  have hS : SlotsDen M ((gateOwns f S).map OwnSlot.slot)
      ((S.map OwnSlot.slot).map fun sl => (false, Term.denotes M sl.2.1)) := by
    rw [gateOwns_slot]
    induction S.map OwnSlot.slot with
    | nil => trivial
    | cons sl S ih => exact ⟨by simp [Term.denote, hf, Val.toBool], rfl, ih⟩
  have hocc : occupied ((S.map OwnSlot.slot).map fun sl => (false, Term.denotes M sl.2.1)) = [] := by
    induction S with
    | nil => rfl
    | cons sl S ih => simp [occupied]
  refine ⟨_, [], hS, ?_, by rw [Holds2, hocc]; trivial, by simp⟩
  intro p hp
  obtain ⟨sl, -, rfl⟩ := List.mem_map.1 hp
  simp [denotes_length, sl.2.2]

/-- Tables picked by a flag denote the first tables where it is true and the second where it is false. -/
theorem machinesRel_pick {v : ServiceV} {f : Term} {b : Bool} (hf : f.denote M = .bool b) :
    (ms : List (MachineV v.records v.event)) → (as xs : PerMachine (fun _ => Term) ms) →
    (sms : Step.Machines ms) → MachinesRel M L T ms (if b then as else xs) sms →
    MachinesRel M L T ms (PerMachine.zipWith (fun a x => Term.share (.ite f a x)) as xs) sms
  | [], .nil, .nil, .nil, _ => trivial
  | m :: ms, .cons a as, .cons x xs, .cons insts sms, h => by
    have hd : (Term.share (.ite f a x)).denote M = (if b then a else x).denote M := by
      cases b <;> simp [Term.denote, hf, Val.toBool]
    have h' : (∃ tbl, RelV L m.table (Ty.up _ m.table_data tbl) ((if b then a else x).denote M) ∧
        insts = instancesOf T m tbl) ∧ MachinesRel M L T ms (if b then as else xs) sms := by
      cases b <;> exact h
    obtain ⟨⟨tbl, htbl, hsm⟩, hrest⟩ := h'
    exact ⟨⟨tbl, hd ▸ htbl, hsm⟩, machinesRel_pick hf ms as xs sms hrest⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model}

/-- An occupied slot of one item holds one term, denoting the item. -/
theorem one_item {ys : SlotItems 1} {z : Val} (h : Term.denotes M ys.1 = [z]) :
    ∃ t, ys = ⟨[t], rfl⟩ ∧ t.denote M = z := by
  obtain ⟨t, rfl⟩ := ys.one
  simp only [Term.denotes, List.cons.injEq, and_true] at h; exact ⟨t, rfl, h⟩


end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- Whether the functions a list of events applies fit, event by event on the state the events before it left: the
records' `apply`, every machine's reaction and every reaction. -/
def eventsFit (S : Ty → Nat) (T : List TypeDecl) : State v → List v.event.den0 → Prop
  | _, [] => True
  | s, ev :: evs =>
    (v.apply.appFits S (s.records, ev, ()) ∧
      (∀ sm ∈ s.machines.toSigma, machineFits S sm (v.apply.fn (s.records, ev, ())) s.now ev) ∧
      ∀ x ∈ v.reactions, (x.react.fits S).1 ∧
        x.react.appFits S (.inl (v.apply.fn (s.records, ev, ()), s.now, ()), ev, ())) ∧
    eventsFit S T (Step.react T s ev).1 evs

/-- A list of events: the condition holds exactly when the functions every event applies fit, on the state the
events before it left (`eventsFit`); wherever it holds, the records and instance table terms denote the state after
every event's reaction in turn, the next id term the id after the requests they start, the pending slots hold, where
flagged, those requests at the ids from `n0`, the queue place term the place after the own commands and queries they
start, and the own slots hold those at the places from `q0`. -/
theorem events_encode {P : List AnySite} (chk : Checked P T v) {shs : List (PendingShape v.event)}
    (hshs : ∀ sh ∈ shs, sh.InSites P)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca0 : Term} (hap : v.apply.code L = .ok (apply, ca0))
    (hca0 : Holds M ca0) (senv : StepEnv L shs) {now : Term} :
    (S : List (Slot 1)) → (sv : List (Bool × List Val)) → SlotsDen M S sv →
    (evs : List v.event.den0) → Holds2 (EBag L v.event) (evs.map (Ty.up _ v.event_data)) sv →
    (s : State v) → now.denote M = .int s.now →
    {records : Term} → RelV L v.records (Ty.up _ v.records_data s.records) (records.denote M) →
    {xs : PerMachine (fun _ => Term) v.machines} → MachinesRel M L T v.machines xs s.machines → {n q : Term} →
    {o : EventsOut v} → {c : Term} → encodeEvents L T v shs senv apply now S records xs n q = .ok (o, c) →
    (Holds M c ↔ eventsFit L.count T s evs) ∧
    (∀ {n0 q0 : Nat}, n.denote M = .int n0 → q.denote M = .int q0 → Holds M c →
      RelV L v.records (Ty.up _ v.records_data (Step.reactAll T s evs).1.records) (o.records.denote M) ∧
      MachinesRel M L T v.machines o.tables (Step.reactAll T s evs).1.machines ∧
      o.nextId.denote M = .int ((n0 + (Step.reqsOf (Step.reactAll T s evs).2).length : Nat) : Int) ∧
      NewsRel M L shs v.declared o.news (Step.reqsOf (Step.reactAll T s evs).2) n0 ∧
      o.queued.denote M = .int ((q0 + (Step.queuedOf (Step.reactAll T s evs).2).length : Nat) : Int) ∧
      OwnRel M L o.owns (Step.queuedOf (Step.reactAll T s evs).2) q0)
  | [], [], _, evs, hev, s, _, records, hrec, xs, hms, n, q, o, c, henc => by
    cases evs with
    | cons _ _ => exact hev.elim
    | nil =>
      simp only [encodeEvents, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
      obtain ⟨rfl, rfl⟩ := henc
      refine ⟨by simp [holds_tt, eventsFit], fun hn hq _ => ?_⟩
      exact ⟨hrec, hms, by simpa [Step.reactAll] using hn, ⟨[], [], trivial, by simp, by simp [Holds2, occupied, Forall2],
        [], by simp [Step.reactAll], trivial⟩, by simpa [Step.reactAll] using hq, ownRel_nil _⟩
  | (f, ys) :: S, (b, vs) :: sv, ⟨hf, hys, hS⟩, evs, hev, s, hnow, records, hrec, xs, hms, n, q, o, c, henc => by
    have hor : ∀ m ∈ v.machines, m.key.orderable = true := fun m hm => (chk.keys m hm).1
    have happ := v.apply.code_fn v.apply.ht hap hca0
    obtain ⟨rc, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨ec, h2, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨r', ca⟩, h3, henc⟩ := bind_ok.1 henc
    obtain ⟨rt, h4, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨outs, cm⟩, h5, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨news, nT, oS, qT⟩, h6, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨rnews, nR, rown, qR, cr⟩, h7, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o', c'⟩, h8, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    refine ⟨?_, fun {n0 q0} hn hq hc => ?_⟩
    · rw [holds_andT]
      cases b with
      | false =>
        have hrec' : RelV L v.records (Ty.up _ v.records_data s.records)
            ((Term.share (.ite f (Term.share rt) records)).denote M) := by
          simpa [Term.denote, hf, Val.toBool] using hrec
        have hms' := machinesRel_pick (T := T) hf v.machines (outs.map (·.table)) xs s.machines
          (by simpa using hms)
        rw [holds_ite_tt (b := false) (by simp [hf, Val.toBool])]
        simp only [Bool.false_eq_true, false_implies, true_and]
        exact (events_encode chk hshs hap hca0 senv S sv hS evs (by simpa [Holds2, occupied] using hev) s hnow hrec'
          hms' h8).1
      | true =>
        match evs, hev with
        | ev :: evs, ⟨⟨z, hz, hez⟩, hrest⟩ =>
          obtain ⟨t, rfl, ht⟩ := one_item (hys.trans hz)
          rw [holds_ite_tt (b := true) (by simp [hf, Val.toBool])]
          simp only [true_implies, eventsFit]
          have hevT : RelV L v.event (Ty.up _ v.event_data ev) ((Term.share (⟨[t], rfl⟩ : SlotItems 1)[0]).denote M) := by
            simpa [ht] using hez
          let recs' := v.apply.fn (s.records, ev, ())
          have hrc : Smt.Rel M L v.records (Ty.up _ v.records_data s.records) rc := (rel_ofTerm (need_ok.1 h1) _).2 hrec
          have hec : Smt.Rel M L v.event (Ty.up _ v.event_data ev) ec := (rel_ofTerm (need_ok.1 h2) _).2 hevT
          have e1 : Holds M ca ↔ v.apply.appFits L.count (s.records, ev, ()) :=
            v.apply.app_exact hap hca0 (by
              intro t ht
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
              rcases ht with rfl | rfl
              · exact ofTerm_notFn (need_ok.1 h1)
              · exact ofTerm_notFn (need_ok.1 h2)) _ _ (rels2 v.records_data v.event_data v.apply.args_data hrc hec) h3
          have hrt : Holds M ca → RelV L v.records (Ty.up _ v.records_data recs') ((Term.share rt).denote M) := fun hca => by
            have hr' := happ (Ty.up _ v.records_data s.records, Ty.up _ v.event_data ev, ()) (rc, ec, ()) ⟨hrc, hec, trivial⟩ r' ca h3 hca
            rw [up_app2 v.records_data v.event_data v.apply.ht] at hr'
            rw [Term.denote_share]; exact (rel_term (need_ok.1 h4) _).1 hr'
          have e2 : ∀ hca : Holds M ca, (Holds M cm ↔ ∀ sm ∈ s.machines.toSigma, machineFits L.count sm recs' s.now ev) :=
            fun hca => (machines_encode (T := T) recs' s.now ev (hrt hca) hnow hevT v.machines xs s.machines outs hms
              hor h5).1
          have e3 : ∀ hca : Holds M ca, (Holds M cr ↔ ∀ x ∈ v.reactions, (x.react.fits L.count).1 ∧
              x.react.appFits L.count (.inl (recs', s.now, ()), ev, ())) :=
            fun hca => (reactions_encode chk.sites hshs senv.hE senv.hPE recs' s.now ev v.records_data v.event_data
              (hrt hca) hnow hevT v.reactions chk.reactions h7).1
          have e4 : ∀ (hca : Holds M ca) (hcm : Holds M cm), (Holds M c' ↔ eventsFit L.count T (Step.react T s ev).1 evs) :=
            fun hca hcm => by
              have hrel := (machines_encode (T := T) recs' s.now ev (hrt hca) hnow hevT v.machines xs s.machines
                outs hms hor h5).2 hcm
              have hrec' : RelV L v.records (Ty.up _ v.records_data recs')
                  ((Term.share (.ite f (Term.share rt) records)).denote M) := by
                simpa [Term.denote, hf, Val.toBool] using hrt hca
              have hms' := machinesRel_pick (T := T) hf v.machines (outs.map (·.table)) xs _
                (by simpa using hrel)
              have hre := react_eq (T := T) s ev
              exact (events_encode chk hshs hap hca0 senv S sv hS evs hrest (Step.react T s ev).1 hnow
                (by rw [hre]; exact hrec') (by rw [hre]; exact hms') h8).1
          rw [holds_andT, holds_andT]
          constructor
          · rintro ⟨⟨p0, p1, p2⟩, p3⟩
            exact ⟨⟨e1.1 p0, (e2 p0).1 p1, (e3 p0).1 p2⟩, (e4 p0 p1).1 p3⟩
          · rintro ⟨⟨p0, p1, p2⟩, p3⟩
            have hca := e1.2 p0
            have hcm := (e2 hca).2 p1
            exact ⟨⟨hca, hcm, (e3 hca).2 p2⟩, (e4 hca hcm).2 p3⟩
    · obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
      have hfl : ∀ a b : List (Sender × EffectV v.event), Step.reqsOf (a ++ b) = Step.reqsOf a ++ Step.reqsOf b ∧
          Step.queuedOf (a ++ b) = Step.queuedOf a ++ Step.queuedOf b := fun _ _ => by
        simp [Step.reqsOf, Step.queuedOf, List.filter_append]
      cases b with
      | false =>
        have hrec' : RelV L v.records (Ty.up _ v.records_data s.records)
            ((Term.share (.ite f (Term.share rt) records)).denote M) := by
          simpa [Term.denote, hf, Val.toBool] using hrec
        have hms' := machinesRel_pick (T := T) hf v.machines (outs.map (·.table)) xs s.machines
          (by simpa using hms)
        have hn' : (Term.share (.ite f nR n)).denote M = .int n0 := by simpa [Term.denote, hf, Val.toBool] using hn
        have hq' : (Term.share (.ite f qR q)).denote M = .int q0 := by simpa [Term.denote, hf, Val.toBool] using hq
        obtain ⟨r1, r2, r3, r4, r5, r6⟩ := (events_encode chk hshs hap hca0 senv S sv hS evs
          (by simpa [Holds2, occupied] using hev) s hnow hrec' hms' h8).2 hn' hq' hc2
        refine ⟨r1, r2, r3, ?_, r5, ?_⟩
        · have := newsRel_append (newsRel_gate_false (L := L) (shs := shs) (ds := v.declared) hf (S := news ++ rnews) n0) (by simpa using r4)
          simpa using this
        · have := ownRel_append (ownRel_gate_false (M := M) (L := L) (e := v.event) hf (S := oS ++ rown) q0) (by simpa using r6)
          simpa using this
      | true =>
        match evs, hev with
        | ev :: evs, ⟨⟨z, hz, hez⟩, hrest⟩ =>
          obtain ⟨t, rfl, ht⟩ := one_item (hys.trans hz)
          have hc1' : Holds M (andT ca (andT cm cr)) := by simpa [Holds, Term.denote, hf, Val.toBool] using hc1
          obtain ⟨hca, hcm, hcr⟩ : Holds M ca ∧ Holds M cm ∧ Holds M cr := by
            rw [holds_andT, holds_andT] at hc1'; exact hc1'
          have hevT : RelV L v.event (Ty.up _ v.event_data ev) ((Term.share (⟨[t], rfl⟩ : SlotItems 1)[0]).denote M) := by
            simpa [ht] using hez
          let recs' := v.apply.fn (s.records, ev, ())
          have hrc : Smt.Rel M L v.records (Ty.up _ v.records_data s.records) rc := (rel_ofTerm (need_ok.1 h1) _).2 hrec
          have hec : Smt.Rel M L v.event (Ty.up _ v.event_data ev) ec := (rel_ofTerm (need_ok.1 h2) _).2 hevT
          have hr' := happ (Ty.up _ v.records_data s.records, Ty.up _ v.event_data ev, ()) (rc, ec, ()) ⟨hrc, hec, trivial⟩ r' ca h3 hca
          rw [up_app2 v.records_data v.event_data v.apply.ht] at hr'
          have hrt : RelV L v.records (Ty.up _ v.records_data recs') ((Term.share rt).denote M) := by
            rw [Term.denote_share]; exact (rel_term (need_ok.1 h4) _).1 hr'
          have hrel := (machines_encode (T := T) recs' s.now ev hrt hnow hevT v.machines xs s.machines outs hms
            (fun m hm => (chk.keys m hm).1) h5).2 hcm
          obtain ⟨effss, hstarts, hfls⟩ := machines_starts (T := T) recs' s.now ev hrt hnow hevT v.machines xs
            s.machines outs hms chk.keys h5 hcm
          have hreach : ∀ x ∈ effss.toList.flatten, x.2.Reach P := by
            intro x hx
            rw [hfls] at hx
            obtain ⟨effs, he, hx⟩ := List.mem_flatten.1 hx
            obtain ⟨sm, hsm, rfl⟩ := List.mem_map.1 he
            exact Step.machineStep_reach T recs' s.now ev sm.1 sm.2 (chk.machines _ (PerMachine.fst_mem hsm)) x hx
          obtain ⟨hnT, hnews1, hqT, hown1⟩ := starts_rel chk.sites hshs senv v.machines _ _ hstarts hreach hn hq h6
          rw [hfls] at hnT hnews1 hqT hown1
          have hnews1' : NewsRel M L shs v.declared news (Step.reqsOf (startedBy T s recs' ev)) n0 := hnews1
          have hown1' : OwnRel M L oS (Step.queuedOf (startedBy T s recs' ev)) q0 := hown1
          obtain ⟨hnR, hnews2, hqR, hown2⟩ := (reactions_encode chk.sites hshs senv.hE senv.hPE recs' s.now ev
            v.records_data v.event_data hrt hnow hevT v.reactions chk.reactions h7).2 hnT hqT hcr
          have hrec' : RelV L v.records (Ty.up _ v.records_data recs')
              ((Term.share (.ite f (Term.share rt) records)).denote M) := by
            simpa [Term.denote, hf, Val.toBool] using hrt
          have hms' := machinesRel_pick (T := T) hf v.machines (outs.map (·.table)) xs _
            (by simpa using hrel)
          have e1 : (Step.reqsOf (startedBy T s recs' ev)).length =
              (Step.reqsOf (s.machines.toSigma.map fun sm => (Step.machineStep T recs' s.now ev sm.1 sm.2).2).flatten).length := rfl
          have e2 : (Step.queuedOf (startedBy T s recs' ev)).length =
              (Step.queuedOf (s.machines.toSigma.map fun sm => (Step.machineStep T recs' s.now ev sm.1 sm.2).2).flatten).length := rfl
          have e3 : reactedBy s recs' ev = reactionEffects v.reactions ev recs' s.now := rfl
          have hn' : (Term.share (.ite f nR n)).denote M =
              .int ((n0 + (Step.reqsOf (startedBy T s recs' ev ++ reactedBy s recs' ev)).length : Nat) : Int) := by
            simp only [Term.denote_share, Term.denote, hf, Val.toBool, ite_true, hnR, (hfl _ _).1, List.length_append, e3]
            congr 2
            omega
          have hq' : (Term.share (.ite f qR q)).denote M =
              .int ((q0 + (Step.queuedOf (startedBy T s recs' ev ++ reactedBy s recs' ev)).length : Nat) : Int) := by
            simp only [Term.denote_share, Term.denote, hf, Val.toBool, ite_true, hqR, (hfl _ _).2, List.length_append, e3]
            congr 2
            omega
          have hre := react_eq (T := T) s ev
          obtain ⟨r1, r2, r3, r4, r5, r6⟩ := (events_encode chk hshs hap hca0 senv S sv hS evs
            hrest (Step.react T s ev).1 hnow (by rw [hre]; exact hrec') (by rw [hre]; exact hms')
            h8).2 hn' hq' hc2
          have hlen : (Step.react T s ev).2 = startedBy T s recs' ev ++ reactedBy s recs' ev := by rw [hre]
          simp only [Step.reactAll]
          rw [(hfl _ _).1, (hfl _ _).2]
          refine ⟨r1, r2, ?_, ?_, ?_, ?_⟩
          · rw [r3, hlen]
            simp only [List.length_append]
            congr 2
            omega
          · rw [hlen]
            have hA := newsRel_append hnews1' (e3 ▸ hnews2)
            rw [← (hfl _ _).1] at hA
            exact newsRel_append (newsRel_gate hf hA) r4
          · rw [r5, hlen]
            simp only [List.length_append]
            congr 2
            omega
          · rw [hlen]
            have hA := ownRel_append hown1' (e3 ▸ hown2)
            rw [← (hfl _ _).2] at hA
            exact ownRel_append (ownRel_gate hf hA) r6
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _, _, _, _, _
  | _ :: _, [], h, _, _, _, _, _, _, _, _, _, _, _, _, _ => h.elim

end

end Tazuna.Smt
