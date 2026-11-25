import Tazuna.Smt.PairSame
import Tazuna.Smt.InternalDispatch
import Tazuna.Smt.Names
import Tazuna.Smt.Pairs
import Tazuna.Semantics.PairCommute

/-! The question T5 asks of a listed pair of own kinds (`Step.PairCommutes`, `Layout.ownPairs`): from a symbolic state,
the first effect runs then the second (order A), and the second runs at the next counter then the first at the
current one (the canonical order, `Step.canonPair`), each internal step encoded for its kind. The two orders commute
when the first does not fault, or when the second faults first and still faults after it, or when both orders fault,
or when both end with records and instance tables Gleam's `==` finds equal, each effect applying the same events in
the same slots, and no step sending a request or queueing an own effect. The last clause is stricter than the
semantics: a pair whose steps send requests or queue own effects is reported as not commuting even where it does, so
the question can only say "do not commute" too often, never "commute" wrongly (`pair_sound`). Comparing what such
steps send needs the wire ids the canonical order renumbers and the kept functions requests hold, and is left out. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout)

/-- Each machine's instance tables compared by Gleam's `==`. -/
def tablesEqT {r e : Ty} : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → PerMachine (fun _ => Term) ms →
    Except Refusal Term
  | [], .nil, .nil => .ok tt
  | m :: ms, .cons x xs, .cons y ys => do
    let f ← eqFn L m.table
    pure (.and (f x y) (← tablesEqT ms xs ys))

/-- The flags of the slots a step's requests and own effects fill. -/
def StepTerms.sent {v : ServiceV} (t : StepTerms v) : List Term := t.done.news.map (·.flag) ++ t.done.owns.map (·.flag)

/-- A pair question's terms: whether the two orders do not commute, the condition that every step reached fits, and
the codes' condition. -/
structure PairOut where
  viol : Term
  cond : Term
  codes : Term

variable (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))

/-- The pair of own kinds `k1`, `k2` (places among the own kinds) from the symbolic state `S`, with the effects
`e1` and `e2`, in order A and in the canonical order. -/
def encodePair (S : SymState v) (e1 e2 : Term) (k1 k2 : Nat) : Except Refusal PairOut := do
  let (apply, ca) ← v.apply.code L
  let nR := (L.effectsOf v.event).length
  let key1 ← need (.layout (.effectKind s!"own kind {k1}")) (L.ownsOf v.event)[k1]?
  let key2 ← need (.layout (.effectKind s!"own kind {k2}")) (L.ownsOf v.event)[k2]?
  let step (records fresh n q eff : Term) (xs : PerMachine (fun _ => Term) v.machines) (j : Nat) (key : OwnKey) :=
    encodeOwnKind L T P v (shapes v) senv nR apply records S.now fresh n q eff xs j key
  let ⟨⟨_, a1⟩, c1, x1⟩ ← step S.records S.fresh S.nextId (.int 0) e1 S.machines k1 key1
  let ⟨⟨_, a2⟩, c2, x2⟩ ← step a1.done.records a1.fresh a1.done.nextId a1.done.queued e2 a1.done.tables k2 key2
  let ⟨⟨_, b1⟩, c3, x3⟩ ← step S.records (.add S.fresh (.int 1)) S.nextId (.int 0) e2 S.machines k2 key2
  let ⟨⟨_, b2⟩, c4, x4⟩ ← step b1.done.records S.fresh b1.done.nextId b1.done.queued e1 b1.done.tables k1 key1
  let recEq ← eqFn L v.records
  let tabEq ← tablesEqT L v.machines a2.done.tables b2.done.tables
  let same := allT [recEq a2.done.records b2.done.records, tabEq, slotsEqT a1.done.events b2.done.events,
    slotsEqT a2.done.events b1.done.events, noneT (a1.sent ++ a2.sent ++ b1.sent ++ b2.sent)]
  let viol := Term.and (.not a1.fault) (.or (.and b1.fault (.not a2.fault))
    (.and (.not b1.fault) (.and (.not (.and a2.fault b2.fault)) (.not (.and (.not a2.fault) (.and (.not b2.fault) same))))))
  pure ⟨viol, allT [c1, c3, .ite a1.fault tt c2, .ite b1.fault tt c4], allT [ca, x1, x2, x3, x4]⟩

/-- The types of a pair question's variables: the state's, then the two effects. -/
def pairTys : List Ty := stateTys v (shapes v) ++ [.dsl .effect [v.event], .dsl .effect [v.event]]

/-- The place of the first effect's variable, after the state's. -/
def pairVar : Nat := (stateTys v (shapes v)).length

/-- A pair's two questions, over a well-formed state whose names are below its counter and pending ids below its next
id, and effects of the two kinds: the bound question, whether the codes' condition or a step reached leaves the
slots; and the target question, whether the two orders do not commute where everything fits. -/
def pairQuestions (k1 k2 : Nat) : Except Refusal (Script × Script) := do
  let S : SymState v := SymState.vars 0
  let n := pairVar v
  let o ← encodePair L T P v senv S (.var n) (.var (n + 1)) k1 k2
  let wf ← need (.layout (.type v.records)) (S.wf L (shapes v))
  let below ← pendingBelowT L (shapes v) S.pending S.nextId
  let names ← need (.layout (.type v.records)) (namesStateT L S)
  let nR := (L.effectsOf v.event).length
  let tests := [Term.is senv.dE (nR + k1) (.var n), .is senv.dE (nR + k2) (.var (n + 1))]
  let vars ← (pairTys v).mapM fun ty => need (.layout (.type ty)) (L.srt? ty)
  let dts ← need (.layout (.type v.records)) L.datatypes?
  let script (asserts : List Term) : Script :=
    { datatypes := dts, vars, asserts := [wf, below, names] ++ tests ++ asserts, shows := List.range (pairTys v).length }
  pure (script [.or (.not o.codes) (.not o.cond)], script [o.codes, o.cond, o.viol])

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- Two steps in progress that keep `a0`'s pending requests, out lines and own effects, whose records and instances are
the same, and whose events after `a0`'s are the same in some order, are the same up to renaming. -/
theorem same_of_quiet {a0 A C : Step.Acc v} {W : PBij} (h0 : Step.Acc.Rel ⟨PBij.refl, W⟩ a0 a0)
    (hr : Ty.rel0 PBij.refl v.records A.state.records C.state.records)
    (hm : Step.Machines.Rel PBij.refl A.state.machines C.state.machines)
    (hpA : A.state.pending = a0.state.pending) (hpC : C.state.pending = a0.state.pending)
    (hnA : A.state.now = a0.state.now) (hnC : C.state.now = a0.state.now)
    (hiA : A.state.nextId = a0.state.nextId) (hiC : C.state.nextId = a0.state.nextId)
    (hoA : A.out = a0.out) (hoC : C.out = a0.out) (hwA : A.own = a0.own) (hwC : C.own = a0.own)
    {EA EC : List v.event.den0} (heA : A.events = a0.events ++ EA) (heC : C.events = a0.events ++ EC)
    (he : Multi (Ty.rel0 PBij.refl v.event) EA EC) (hf : A.state.fresh = C.state.fresh) : Step.Same A C := by
  obtain ⟨⟨-, -, hp, -, hb, -⟩, hev, hout, ho, -, hown⟩ := h0
  refine .base ⟨⟨PBij.refl, W⟩, ⟨⟨hr, hm, ?_, hnA.trans hnC.symm, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hf,
    hiA.trans hiC.symm, fun _ _ => rfl⟩
  · rw [hpA, hpC]; exact hp
  · rw [hpA, hiA]; exact hb
  · rw [hpC, hiC]; exact hb
  · rw [heA, heC]; exact hev.append he
  · rw [hoA, hoC]; exact hout
  · rw [hoA, hiA]; exact ho
  · rw [hoC, hiC]; exact ho
  · rw [hwA, hwC]; exact hown

/-- A run that sends no request and queues nothing, as `AccRel` says of it with no flag of its news and own slots
holding. -/
theorem quiet_run {shs : List (PendingShape v.event)} {a : Step.Acc v} {o : EventsOut v} {f : Term} {q0 : Nat}
    {r : Except Fault (Step.Acc v)} (h : AccRel M L T shs a o f q0 r)
    (hq : Holds M (noneT (o.news.map (·.flag) ++ o.owns.map (·.flag)))) :
    ∃ (recs : v.records.den0) (ms : Step.Machines v.machines) (fr : Nat) (evs : List v.event.den0), r = .ok ⟨{ a.state with records := recs, machines := ms, fresh := fr },
        a.events ++ evs, a.out, a.own⟩ ∧
      RelV L v.records (Ty.up _ v.records_data recs) (o.records.denote M) ∧ MachinesRel M L T v.machines o.tables ms ∧
      f.denote M = .int (fr : Int) ∧ o.nextId.denote M = .int (Int.ofNat a.state.nextId) ∧
      o.queued.denote M = .int (q0 : Int) ∧ EventsRel M L o.events evs := by
  obtain ⟨recs, ms, fr, evs, effs, os, hr, r1, r2, r3, r4, r5, r6, r7, r8⟩ := h
  simp only [noneT, List.map_append, holds_allT, List.mem_append] at hq
  have he := news_nil r5 (by simp only [noneT, holds_allT]; exact fun c hc => hq c (.inl hc))
  have ho := owns_nil r7 (by simp only [noneT, holds_allT]; exact fun c hc => hq c (.inr hc))
  subst he ho
  refine ⟨recs, ms, fr, evs, ?_, r1, r2, r3, by simpa using r4, by simpa using r6, r8⟩
  rw [hr [] trivial]
  simp

/-- The variant test of an own kind's place and an effect's code give the kind's facts of the effect. -/
theorem own_key {x : EffectV v.event} (hown : x.isRequest = false) {senv : StepEnv L (shapes v)} {z : Val}
    (hx : RelV L (.dsl .effect [v.event]) x z) {k : Nat} {t : Term}
    (ht : Holds M (.is senv.dE ((L.effectsOf v.event).length + k) t)) (hz : t.denote M = z) {key : OwnKey}
    (hkey : (L.ownsOf v.event)[k]? = some key) :
    ∃ vals, z = .ctor senv.dE ((L.effectsOf v.event).length + k) vals ∧ key.Holds L x vals := by
  have hx' : EffRel L x z := hx
  obtain ⟨d, nn, hd, hx'⟩ := hx'
  cases (Prod.mk.inj (Option.some.inj (senv.hE.symm.trans hd))).1
  rcases hx' with ⟨_, _, _, -, -, hh⟩ | ⟨k', key', vals, hk', rfl, hh⟩
  · cases x with
    | request => simp [EffectV.isRequest] at hown
    | command => exact hh.elim
    | query => exact hh.elim
  · simp only [Holds, Term.denote, hz, Val.toBool, beq_self_eq_true, Bool.true_and, beq_iff_eq] at ht
    have hk : k' = k := by omega
    subst hk
    rw [hkey] at hk'
    cases hk'
    exact ⟨vals, rfl, hh⟩

/-- Instance tables compared equal hold the same instances, read as multisets. -/
theorem machines_of_eq : (ms : List (MachineV v.records v.event)) →
    (∀ m ∈ ms, m.key.comparable = true ∧ m.state.comparable = true) →
    {xs ys : PerMachine (fun _ => Term) ms} → {sa sb : Step.Machines ms} → MachinesRel M L T ms xs sa →
    MachinesRel M L T ms ys sb → {c : Term} → tablesEqT L ms xs ys = .ok c → Holds M c →
    Step.Machines.Rel PBij.refl sa sb
  | [], _, .nil, .nil, .nil, .nil, _, _, _, _, _ => trivial
  | m :: ms, hc, .cons x xs, .cons y ys, .cons ia sa, .cons ib sb, ⟨⟨ta, hta, hia⟩, ha⟩, ⟨⟨tb, htb, hib⟩, hb⟩, c, h,
      hh => by
    subst hia hib
    obtain ⟨f, hf, h⟩ := bind_ok.1 h
    obtain ⟨c', hc', h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_and] at hh
    have hm := hc m (List.mem_cons_self ..)
    have htc : m.table.comparable = true := by
      simp only [MachineV.table, Ty.comparable, Bool.and_eq_true]
      exact ⟨hm.1, instEntry_comparable hm.2⟩
    exact ⟨insts_of_table (rel0_of_eqFn m.table_data htc hta htb hf hh.1),
      machines_of_eq ms (fun m' hm' => hc m' (List.mem_cons_of_mem _ hm')) ha hb hc' hh.2⟩

theorem wireSwap_self (n i : Nat) : wireSwap n n n i = i := by
  unfold wireSwap
  split <;> (try split) <;> omega

theorem mapWire_self (n : Nat) (a : Step.Acc v) : a.mapWire (wireSwap n n n) = a := by
  simp [Step.Acc.mapWire, wireSwap_self]

theorem noneT_append (xs ys : List Term) : Holds M (noneT (xs ++ ys)) ↔ Holds M (noneT xs) ∧ Holds M (noneT ys) := by
  simp only [noneT, List.map_append, holds_allT, List.mem_append]
  exact ⟨fun h => ⟨fun c hc => h c (.inl hc), fun c hc => h c (.inr hc)⟩, fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

theorem fault_true {t : Term} {o : Option Fault} (h : t.denote M = .bool o.isSome) : Holds M t ↔ o.isSome := by
  simp [Holds, h, Val.toBool]

/-- A pair question's terms: where the codes' condition and the condition hold and the two orders are not reported as
not commuting, the two effects commute from every step in progress whose state the symbolic state denotes and which
relates to itself under every renaming keeping its counters (`Step.PairCommutes`). -/
theorem pair_commutes {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) (hrc : v.records.comparable = true)
    (hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true)
    {S : SymState v} {a0 : Step.Acc v} (hR : StateRel M L T (shapes v) S a0.state)
    (hsa : Step.SelfAt a0.state.fresh a0) {t1 t2 : Term} {x1 x2 : EffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1 (t1.denote M)) (hx2 : RelV L (.dsl .effect [v.event]) x2 (t2.denote M))
    (hown1 : x1.isRequest = false) (hown2 : x2.isRequest = false) (hreach1 : x1.Reach P) (hreach2 : x2.Reach P)
    {k1 k2 : Nat} (ht1 : Holds M (.is senv.dE ((L.effectsOf v.event).length + k1) t1))
    (ht2 : Holds M (.is senv.dE ((L.effectsOf v.event).length + k2) t2))
    {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o)
    (hcodes : Holds M o.codes) (hcond : Holds M o.cond) (hviol : ¬ Holds M o.viol) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨key1, hkey1, henc⟩ := bind_ok.1 henc
  obtain ⟨key2, hkey2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko1, a1⟩, c1, y1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko2, a2⟩, c2, y2⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko3, b1⟩, c3, y3⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko4, b2⟩, c4, y4⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨recEq, hrecEq, henc⟩ := bind_ok.1 henc
  obtain ⟨tabEq, htabEq, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcodes hcond
  obtain ⟨hca, hy1, hy2, hy3, hy4⟩ := hcodes
  obtain ⟨hc1, hc3, hc2, hc4⟩ := hcond
  have hshs : ∀ sh ∈ shapes v, sh.InSites P := fun _ => shapes_inSites chk.reach
  obtain ⟨vals1, he1, hk1⟩ := own_key hown1 hx1 ht1 rfl (need_ok.1 hkey1)
  obtain ⟨vals2, he2, hk2⟩ := own_key hown2 hx2 ht2 rfl (need_ok.1 hkey2)
  have hq0 : (Term.int 0).denote M = .int ((0 : Nat) : Int) := rfl
  have eA1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0
    hR.machines x1 hreach1 he1 hk1 h1 hy1
  obtain ⟨hfA1, hA1⟩ := eA1.2 hc1
  have hn0 : a0.state.nextId = a0.state.nextId := rfl
  generalize hf : a0.state.fresh = f at hsa
  intro b hb
  -- The first effect runs to its end in order A.
  revert hA1
  cases hko1 : ko1.fault? M with
  | some g => intro hA1; rw [hA1] at hb; cases hb
  | none =>
  intro hA1
  rw [hb] at hA1
  have hfa1 : ¬ Holds M a1.fault := by rw [fault_true hfA1, hko1]; simp
  have hc2' : Holds M c2 := by
    rw [holds_ite] at hc2
    simpa [show (a1.fault.denote M).toBool = false by simpa [Holds] using hfa1] using hc2
  obtain ⟨hbr, hbm, hbf, hbn, hbnow, os1, hbo, hbq, -⟩ := hA1.ends
  have eA2 := ownKind_encode chk hshs (shapesHold_shapes v) b happ hca senv hbr (hR.now.trans (by rw [hbnow])) hbf hbn
    hbq hbm x2 hreach2 he2 hk2 h2 hy2
  obtain ⟨hfA2, hA2⟩ := eA2.2 hc2'
  have hfr1 : (Term.add S.fresh (.int 1)).denote M = .int (Int.ofNat (a0.withFresh (a0.state.fresh + 1)).state.fresh) := by
    simp only [Term.denote, hR.fresh, Val.toInt, Step.Acc.withFresh]; push_cast; rfl
  have eC1 := ownKind_encode chk hshs (shapesHold_shapes v) (a0.withFresh (a0.state.fresh + 1)) happ hca senv hR.records
    hR.now hfr1 hR.nextId hq0 hR.machines x2 hreach2 he2 hk2 h3 hy3
  obtain ⟨hfC1, hC1⟩ := eC1.2 hc3
  simp only [Step.Acc.withFresh, hf] at hC1 ⊢
  refine ⟨fun c hc => ?_, fun g hg => ?_⟩
  · revert hC1
    cases hko3 : ko3.fault? M with
    | some g => intro hC1; rw [hC1] at hc; cases hc
    | none =>
    intro hC1
    rw [hc] at hC1
    have hfb1 : ¬ Holds M b1.fault := by rw [fault_true hfC1, hko3]; simp
    have hc4' : Holds M c4 := by
      rw [holds_ite] at hc4
      simpa [show (b1.fault.denote M).toBool = false by simpa [Holds] using hfb1] using hc4
    obtain ⟨hcr, hcm, -, hcn, hcnow, os3, hco, hcq, -⟩ := hC1.ends
    have hff : S.fresh.denote M = .int (Int.ofNat (c.withFresh f).state.fresh) := by
      simp only [Step.Acc.withFresh]; rw [hR.fresh, hf]
    have eC2 := ownKind_encode chk hshs (shapesHold_shapes v) (c.withFresh f) happ hca senv hcr
      (hR.now.trans (by rw [← hcnow]; rfl)) hff hcn hcq hcm x1 hreach1 he1 hk1 h4 hy4
    obtain ⟨hfC2, hC2⟩ := eC2.2 hc4'
    simp only [Step.canonPair, Step.Acc.withFresh, hf, hc, bind, Except.bind] at hC2 ⊢
    simp only [holds_and, holds_or, holds_not, not_and, not_or, Classical.not_not] at hviol
    have hv := (hviol hfa1).2 hfb1
    have key : (Holds M a2.fault ∧ Holds M b2.fault) ∨ (¬ Holds M a2.fault ∧ ¬ Holds M b2.fault ∧
        Holds M (allT [recEq a2.done.records b2.done.records, tabEq, slotsEqT a1.done.events b2.done.events,
          slotsEqT a2.done.events b1.done.events, noneT (a1.sent ++ a2.sent ++ b1.sent ++ b2.sent)])) := by
      by_cases ha : Holds M a2.fault <;> by_cases hb' : Holds M b2.fault
      · exact .inl ⟨ha, hb'⟩
      · exact absurd (fun hna _ => absurd ha hna) (hv fun _ => hb')
      · exact absurd (fun _ hnb => absurd hb' hnb) (hv fun h => absurd h ha)
      · exact .inr ⟨ha, hb', Classical.byContradiction fun hs => hv (fun h => absurd h ha) fun _ _ => hs⟩
    rcases key with ⟨ha2, hb2⟩ | ⟨ha2, hb2, hsame⟩
    · obtain ⟨g2, hg2⟩ := Option.isSome_iff_exists.1 ((fault_true hfA2).1 ha2)
      obtain ⟨g4, hg4⟩ := Option.isSome_iff_exists.1 ((fault_true hfC2).1 hb2)
      rw [hg2] at hA2
      rw [hg4] at hC2
      simp only at hA2 hC2
      rw [hA2, hC2]
      exact .inr ⟨trivial, trivial⟩
    · have hg2 : ko2.fault? M = none := Option.not_isSome_iff_eq_none.1 fun h => ha2 ((fault_true hfA2).2 h)
      have hg4 : ko4.fault? M = none := Option.not_isSome_iff_eq_none.1 fun h => hb2 ((fault_true hfC2).2 h)
      rw [hg2] at hA2
      rw [hg4] at hC2
      simp only at hA2 hC2
      simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        noneT_append] at hsame
      obtain ⟨hrq, htq, he14, he23, ⟨⟨hq1, hq2⟩, hq3⟩, hq4⟩ := hsame
      obtain ⟨r1, m1, fr1, ev1, hb1, -, -, -, -, -, hev1⟩ := quiet_run hA1 hq1
      obtain ⟨r2, m2, fr2, ev2, hb2', hr2, hm2, -, -, -, hev2⟩ := quiet_run hA2 hq2
      obtain ⟨r3, m3, fr3, ev3, hc3', -, -, -, -, -, hev3⟩ := quiet_run hC1 hq3
      obtain ⟨r4, m4, fr4, ev4, hd4, hr4, hm4, -, -, -, hev4⟩ := quiet_run hC2 hq4
      have hfb := Step.runOwn_fresh T hown1 hb
      have hfa := Step.runOwn_fresh T hown2 hb2'
      obtain rfl := Except.ok.inj hb1
      obtain rfl := Except.ok.inj hc3'
      rw [hb2', hd4]
      simp only at hfa hfb ⊢
      rw [mapWire_self]
      obtain ⟨W, h0⟩ := hsa PBij.refl fun _ _ => rfl
      refine .inl (same_of_quiet h0 (rel0_of_eqFn v.records_data hrc hr2 hr4 hrecEq hrq)
        (machines_of_eq v.machines hmc hm2 hm4 htabEq htq) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (EA := ev1 ++ ev2) (EC := ev3 ++ ev4) (by simp) (by simp) ?_ (by rw [hfa, hfb, hf]))
      exact (Multi.of_forall2 (forall2_append (events_of_slotsEq hev1 hev4 he14) (events_of_slotsEq hev2 hev3 he23))).perm_right
        List.perm_append_comm
  · revert hC1
    cases hko3 : ko3.fault? M with
    | none =>
      intro hC1
      obtain ⟨_, ha'⟩ := hC1.ok
      rw [hg] at ha'
      cases ha'
    | some g3 =>
    intro _
    have hfb1 : Holds M b1.fault := by rw [fault_true hfC1, hko3]; rfl
    simp only [holds_and, holds_or, holds_not, not_and, not_or, Classical.not_not] at hviol
    have ha2 : Holds M a2.fault := (hviol hfa1).1 hfb1
    obtain ⟨g2, hg2⟩ := Option.isSome_iff_exists.1 ((fault_true hfA2).1 ha2)
    rw [hg2] at hA2
    simp only at hA2
    rw [hA2]
    trivial
/-- T5's pair hypothesis from a pair's questions: where both are unsat, the two effects of the pair's kinds commute from
every step in progress whose state a model's values decode to, with its pending ids below its next id and its names
below its counter, and which relates to itself under every renaming keeping its counters. -/
theorem pair_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hrc : v.records.comparable = true) (hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true)
    {k1 k2 : Nat} {bq tq : Script} (hq : pairQuestions L T P v senv k1 k2 = .ok (bq, tq))
    (hbq : Unsat L (pairTys v) bq) (htq : Unsat L (pairTys v) tq)
    (hM : ∀ n (h : n < (pairTys v).length), Sorted L (pairTys v)[n] (M.vars n))
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hbelow : ∀ p ∈ s.pending, p.id < s.nextId) (hsupp : Step.StateSupp s)
    {a0 : Step.Acc v} (has : a0.state = s) (hsa : Step.SelfAt a0.state.fresh a0) {x1 x2 : EffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1 (M.vars (pairVar v)))
    (hx2 : RelV L (.dsl .effect [v.event]) x2 (M.vars (pairVar v + 1)))
    (hown1 : x1.isRequest = false) (hown2 : x2.isRequest = false) (hreach1 : x1.Reach P) (hreach2 : x2.Reach P)
    (ht1 : Holds M (.is senv.dE ((L.effectsOf v.event).length + k1) (.var (pairVar v))))
    (ht2 : Holds M (.is senv.dE ((L.effectsOf v.event).length + k2) (.var (pairVar v + 1)))) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨o, ho, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, hbl, hq⟩ := bind_ok.1 hq
  obtain ⟨names, hnames, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hR := decode_state hS
  have hwfH : Holds M wf := wf_of_decodeState (need_ok.1 hwf) hS
  have hblH : Holds M below := (pendingBelow_iff hR.pending hR.nextId hbl).2 hbelow
  have hnH : Holds M names := stateSupp_names hR hsupp hrc hmc (need_ok.1 hnames)
  have hpre : ∀ a ∈ [wf, below, names, Term.is senv.dE ((L.effectsOf v.event).length + k1) (.var (pairVar v)),
      .is senv.dE ((L.effectsOf v.event).length + k2) (.var (pairVar v + 1))], Holds M a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl)
    · exact hwfH
    · exact hblH
    · exact hnH
    · exact ht1
    · exact ht2
  obtain ⟨a, ha, hna⟩ := hbq M hM
  rcases List.mem_append.1 ha with ha | ha
  · exact (hna (hpre a ha)).elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  simp only [holds_or, holds_not, not_or, Classical.not_not] at hna
  obtain ⟨a, ha, hna'⟩ := htq M hM
  rcases List.mem_append.1 ha with ha | ha
  · exact (hna' (hpre a ha)).elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact (hna' hna.1).elim
  · exact (hna' hna.2).elim
  subst has
  exact pair_commutes chk senv hrc hmc hR hsa (t1 := .var (pairVar v)) (t2 := .var (pairVar v + 1)) hx1 hx2 hown1 hown2
    hreach1 hreach2 ht1 ht2 ho hna.1 hna.2 hna'

/-- T5's pair hypothesis for any two own effects: where every listed pair of own kinds has both questions unsat, any
two own effects a model codes commute from every step in progress `pair_sound` covers (the pairs cover every two own
effects, `ownPairs_complete`). -/
theorem pairs_sound {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hrc : v.records.comparable = true) (hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true)
    (hall : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L T P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) bq ∧ Unsat L (pairTys v) tq)
    (hM : ∀ n (h : n < (pairTys v).length), Sorted L (pairTys v)[n] (M.vars n))
    {s : State v} (hS : (SymState.vars (v := v) 0).decode M L T (shapes v) = some s)
    (hbelow : ∀ p ∈ s.pending, p.id < s.nextId) (hsupp : Step.StateSupp s)
    {a0 : Step.Acc v} (has : a0.state = s) (hsa : Step.SelfAt a0.state.fresh a0) {x1 x2 : EffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1 (M.vars (pairVar v)))
    (hx2 : RelV L (.dsl .effect [v.event]) x2 (M.vars (pairVar v + 1)))
    (hown1 : x1.isRequest = false) (hown2 : x2.isRequest = false) (hreach1 : x1.Reach P) (hreach2 : x2.Reach P) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨p, hp, d, n, vals1, vals2, hd, hz1, hz2⟩ := ownPairs_complete hx1 hx2 hown1 hown2
  obtain rfl := find_det hd senv.hE
  obtain ⟨bq, tq, hq, hb, ht⟩ := hall p hp
  have htest : ∀ (j : Nat) (vals : List Val) (i : Nat), M.vars i = .ctor senv.dE ((L.effectsOf v.event).length + j) vals →
      Holds M (.is senv.dE ((L.effectsOf v.event).length + j) (.var i)) := fun j vals i h => by
    simp [Holds, Term.denote, h, Val.toBool]
  exact pair_sound chk senv hrc hmc hq hb ht hM hS hbelow hsupp has hsa hx1 hx2 hown1 hown2 hreach1 hreach2
    (htest _ _ _ hz1) (htest _ _ _ hz2)

end

end Tazuna.Smt
