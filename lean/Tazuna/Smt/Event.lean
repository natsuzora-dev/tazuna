import Tazuna.Smt.Finish

/-! The event step: the subscription wraps the received value into an event, the events loop applies it (machines and
reactions react), and the step ends (`encodeFinish`). `event_encode` proves T2 and the exactness of the condition. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The codes of the functions an event step reads. -/
structure EventCode (v : ServiceV) (i : Fin v.subscribes.length) where
  apply : Code (Ty.fn [v.records, v.event] v.records)
  wrap : Code (Ty.fn [(v.subscribes.get i).event] v.event)
  invariants : Code (Ty.fn [v.records] Ty.rules)

/-- An event step's types are data, as the `service` and `subscription` built-ins demand. -/
structure EventData (v : ServiceV) (i : Fin v.subscribes.length) : Prop where
  records : v.records.isData = true
  event : v.event.isData = true
  value : (v.subscribes.get i).event.isData = true

/-- An event step's types are data, since the service's `apply` and the subscription's wrap are. -/
theorem _root_.Tazuna.Ir.ServiceV.eventData (v : ServiceV) (i : Fin v.subscribes.length) : EventData v i :=
  ⟨v.records_data, v.event_data, (v.subscribes.get i).event_data⟩

section
variable {v : ServiceV} {i : Fin v.subscribes.length} (hd : EventData v i)
include hd

theorem EventData.apply : (Ty.fn [v.records, v.event] v.records).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.records, hd.event]
theorem EventData.wrap : (Ty.fn [(v.subscribes.get i).event] v.event).isData = true := by
  simp only [Ty.isData, Ty.isDatas, hd.value, hd.event, Bool.and_self]
theorem EventData.wrapArgs : (Ty.tuple [(v.subscribes.get i).event]).isData = true := by
  simp only [Ty.isData, Ty.isDatas, hd.value, Bool.and_self]
theorem EventData.invariants : (Ty.fn [v.records] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.records]

end

/-- The codes relate to the service's and the subscription's functions in the model. -/
structure EventCode.Rel (M : Model) (L : Layout) {v : ServiceV} {i : Fin v.subscribes.length}
    (ec : EventCode v i) : Prop where
  apply : Smt.Rel M L _ (Ty.up _ v.apply.ht v.apply.fn) ec.apply
  wrap : Smt.Rel M L _ (Ty.up _ ((v.eventData i)).wrap (v.subscribes.get i).wrap.fn) ec.wrap
  invariants : Smt.Rel M L _ (Ty.up _ ((v.eventData i)).invariants v.invariants.fn) ec.invariants

/-- An event step's codes, from the sources the service and the subscription keep, with their condition. -/
def EventCode.of (L : Layout) (v : ServiceV) (i : Fin v.subscribes.length) : Except Refusal (EventCode v i × Term) := do
  let (a, c1) ← v.apply.code L
  let (w, c2) ← (v.subscribes.get i).wrap.code L
  let (n, c3) ← v.invariants.code L
  pure (⟨a, w, n⟩, andT c1 (andT c2 c3))

theorem EventCode.rel_of {M : Model} {L : Layout} {v : ServiceV} {i : Fin v.subscribes.length}
    {ec : EventCode v i} {ce : Term} (h : EventCode.of L v i = .ok (ec, ce)) (hc : Holds M ce) : ec.Rel M L := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨w, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hc := (holds_andT _ _).1 hc
  have hc' := (holds_andT _ _).1 hc.2
  exact ⟨v.apply.code_fn _ h1 hc.1, (v.subscribes.get i).wrap.code_fn _ h2 hc'.1, v.invariants.code_fn _ h3 hc'.2⟩

section
variable (L : Layout)

/-- The event a subscription wraps the received value into, with its condition. -/
def encodeWrap {v : ServiceV} {i : Fin v.subscribes.length} (ec : EventCode v i) (value : Term) :
    Except Refusal (Term × Term) := do
  let vc ← need "a value that has no term" (Code.ofTerm? _ value)
  let (ev, c) ← ec.wrap (vc, ())
  let et ← need "an event that has no term" (Code.term? _ ev)
  pure (et, c)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model}

/-- The wrap: its condition holds exactly when the wrap fits at the value, and wherever it holds the event term
denotes the event the wrap gives. -/
theorem wrap_encode {v : ServiceV} (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0) {ec : EventCode v i} {ce : Term} (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce)
    {sv : Term} (hsv : RelV L _ (Ty.up _ ((v.eventData i)).value value) (sv.denote M)) {et c : Term}
    (henc : encodeWrap ec sv = .ok (et, c)) :
    (Holds M c ↔ (v.subscribes.get i).wrap.appFits L.count (value, ())) ∧
    (Holds M c → RelV L v.event (Ty.up _ v.event_data ((v.subscribes.get i).wrap.fn (value, ()))) (et.denote M)) := by
  have he := EventCode.rel_of hec hce
  obtain ⟨⟨a, c1'⟩, -, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2'⟩, g2, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3'⟩, -, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  obtain ⟨-, hcwn⟩ := (holds_andT _ _).1 hce
  obtain ⟨hcw, -⟩ := (holds_andT _ _).1 hcwn
  obtain ⟨vc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ev, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨et', h3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvc : Smt.Rel M L _ (Ty.up _ ((v.eventData i)).value value) vc := (rel_ofTerm (need_ok.1 h1) _).2 hsv
  refine ⟨(v.subscribes.get i).wrap.app_exact g2 hcw (by simpa using ofTerm_notFn (need_ok.1 h1)) _ _
    (rels1 ((v.eventData i)).value ((v.eventData i)).wrapArgs hvc) h2, fun hc => ?_⟩
  have hev := he.wrap _ (vc, ()) (rels1 ((v.eventData i)).value ((v.eventData i)).wrapArgs hvc) ev c h2 hc
  erw [Ty.up_fn _ _ _ ((v.eventData i)).wrapArgs v.event_data] at hev
  exact (rel_term (need_ok.1 h3) _).1 hev

end

section
variable {L : Layout} {M : Model}

/-- An event step's codes' own condition is exact: it holds exactly when the three kept sources fit. -/
theorem eventCode_exact {v : ServiceV} {i : Fin v.subscribes.length} {ec : EventCode v i} {ce : Term}
    (h : EventCode.of L v i = .ok (ec, ce)) :
    Holds M ce ↔ (v.apply.fits L.count).1 ∧ ((v.subscribes.get i).wrap.fits L.count).1 ∧ (v.invariants.fits L.count).1 := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨w, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  rw [holds_andT, holds_andT, (v.apply.code_exact (M := M) h1).1, ((v.subscribes.get i).wrap.code_exact (M := M) h2).1,
    (v.invariants.code_exact (M := M) h3).1]

end

section
variable (L : Layout) (T : List TypeDecl)

/-- The terms of an event step: the event the subscription wraps the value into, what the events loop over it leaves,
and the step's end. -/
structure EventOut (v : ServiceV) where
  event : Term
  after : EventsOut v
  finish : FinishOut v

/-- An event step's terms, its condition and the codes' condition, from the subscription's and the service's codes
and the terms of the state and the received value. -/
def encodeEvent (P : List AnySite) (v : ServiceV) (shs : List (PendingShape v.event)) (senv : StepEnv L shs)
    {i : Fin v.subscribes.length} (ec : EventCode v i) (S : SymState v) (value : Term) : Except Refusal (Encoded (EventOut v)) := do
  let (et, cw) ← encodeWrap ec value
  let (o, c) ← encodeEvents L T v shs senv ec.apply S.now [(tt, ⟨[et], rfl⟩)] S.records S.machines S.nextId (.int 0)
  let ⟨fo, cf, cx⟩ ← encodeFinish L T P v shs senv ec.apply ec.invariants S.now S.fresh S.pending o
  pure ⟨⟨et, o, fo⟩, andT cw (andT c cf), cx⟩

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- An event step: where the codes' condition holds, its condition holds exactly when the wrap fits at the value, the
event's applications fit and the step's end fits, and wherever it holds the step ends as the end terms say. -/
theorem event_encode {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (s : State v) (hinv : Step.Inv P s) (i : Fin v.subscribes.length)
    (value : (v.subscribes.get i).event.den0) {ec : EventCode v i} {ce : Term}
    (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce) {S : SymState v} (hR : StateRel M L T shs S s) {sv : Term}
    (hsv : RelV L _ (Ty.up _ ((v.eventData i)).value value) (sv.denote M))
    (senv : StepEnv L shs)
    {o : EventOut v} {c cx : Term}
    (henc : encodeEvent L T P v shs senv ec S sv = .ok ⟨o, c, cx⟩)
    (hcx : Holds M cx) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    (Holds M c ↔ (v.subscribes.get i).wrap.appFits L.count (value, ()) ∧ eventsFit L.count T s [ev] ∧
      finishFits L.count T shs (Step.applyEvents T { state := s } [ev])) ∧
    (Holds M c → Finished M L T shs o.finish s { state := s } .accepted (step T v s (.event i value))) := by
  intro ev
  have he := EventCode.rel_of hec hce
  obtain ⟨⟨a, c1⟩, g1, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2⟩, -, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3⟩, g3, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  obtain ⟨hc1, -, hc3⟩ : Holds M c1 ∧ Holds M c2 ∧ Holds M c3 := by rw [holds_andT, holds_andT] at hce; exact hce
  obtain ⟨⟨et, cw⟩, hwr, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨eo, ce'⟩, hev, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cx'⟩, hf, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have ew := wrap_encode i value hec hce hsv hwr
  have hevT : Holds M cw → Forall2 (fun ev y => ∃ z, y = [z] ∧ RelV L v.event (Ty.up _ v.event_data ev) z) [ev]
      (occupied [(true, [et.denote M])]) := fun hcw => ⟨⟨_, rfl, ew.2 hcw⟩, trivial⟩
  have e2 : ∀ hcw : Holds M cw, (Holds M ce' ↔ eventsFit L.count T s [ev]) := fun hcw =>
    (events_encode chk hshs g1 hc1 senv [(tt, ⟨[et], rfl⟩)] [(true, [et.denote M])]
      ⟨rfl, rfl, trivial⟩ [ev] (hevT hcw) s hR.now hR.records hR.machines hev).1
  have ef := fun (hcw : Holds M cw) (hc : Holds M ce') =>
    finish_encode chk hshs g1 hc1 g3 hc3 senv s
      .accepted { state := s } rfl hinv hR.now hR.pending
      (loop_acc (T := T) chk hshs g1 hc1 senv
        { state := s } hR.now (S := [(tt, ⟨[et], rfl⟩)]) (sv := [(true, [et.denote M])]) ⟨rfl, rfl, trivial⟩
        (evs := [ev]) (hevT hcw) hR.records hR.machines hR.nextId (q := .int 0) (q0 := 0) rfl hR.fresh hev hc)
      (applyEvents_ok chk.reach _ rfl hinv _) hf hcx
  rw [holds_andT, holds_andT]
  refine ⟨⟨fun ⟨hcw, hc, hcf⟩ => ⟨ew.1.1 hcw, (e2 hcw).1 hc, ((ef hcw hc).1).1 hcf⟩, fun ⟨p1, p2, p3⟩ => ?_⟩,
    fun ⟨hcw, hc, hcf⟩ => (ef hcw hc).2 hcf⟩
  have hcw := ew.1.2 p1
  have hc := (e2 hcw).2 p2
  exact ⟨hcw, hc, (ef hcw hc).1.2 p3⟩

end

end Tazuna.Smt
