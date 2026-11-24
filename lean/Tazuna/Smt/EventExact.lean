import Tazuna.Smt.ReactExact
import Tazuna.Smt.EventStep

/-! The conditions `event_step` (T2 for an event with machines) takes are exact: each holds exactly when the
functions the step applies fit the layout's slot counts. The service's part applies the subscription's wrap, `apply`
and the invariants; each machine's part its reaction (`react_exact`) and every instance's invariants. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem instCheckAt_cond (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)} {de : Nat}
    {records now f : Term} {xs : List Term} {c : InstCheck} {cj : Term}
    (hg : instCheckAt L m inv de records now (f, xs) = .ok (c, cj)) : ∃ X, cj = .ite f X tt := by
  repeat obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  exact ⟨_, rfl⟩

theorem forall2_snd {α β γ : Type} {R : α → β × γ → Prop} : {as : List α} → {bs : List (β × γ)} → Forall2 R as bs →
    Forall2 (fun a c => ∃ b, R a (b, c)) as (bs.map (·.2))
  | [], [], _ => trivial
  | _ :: _, (b, _) :: _, ⟨h, hs⟩ => ⟨⟨b, h⟩, forall2_snd hs⟩

/-- One occupied slot's instance invariant check: its condition holds exactly when the invariants fit at that
instance. -/
theorem instCheck_exact (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)} {ci : Term}
    (hci : m.invariants.code L = .ok (inv, ci)) (hcic : Holds M ci) (recs : r.den0) (tnow : Int) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {de : Nat} (hde : tupleD L [m.state, Ty.option (.tuple [.int, m.state])] = .ok de)
    {f : Term} {xs : List Term} {zk zv : Val} (hf : f.denote M = .bool true) (hxs : Term.denotes M xs = [zk, zv])
    (k0 : m.key.den0) (e0 : (instEntry m.state).den0)
    (hk : RelV L m.key (Ty.up _ m.key_data k0) zk)
    (he : RelV L (instEntry m.state) (Ty.up _ m.entry_data e0) zv)
    {c : InstCheck} {cj : Term} (hg : instCheckAt L m inv de records now (f, xs) = .ok (c, cj)) :
    Holds M cj ↔ m.invariants.appFits L.count (.inl (k0, e0.1, recs, tnow, ()), ()) := by
  obtain ⟨tk, te, rfl⟩ : ∃ tk te, xs = [tk, te] := by
    match xs, hxs with
    | [tk, te], _ => exact ⟨tk, te, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨htk, hte⟩ := hxs
  obtain ⟨ctx, h1, hg⟩ := bind_ok.1 hg
  obtain ⟨cx, h2, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨rs, c1⟩, h3, hg⟩ := bind_ok.1 hg
  obtain ⟨rules, h4, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at h1
  have hst : Ty.isData m.state = true := m.state_data
  have hopt : (Ty.tuple [Ty.option (.tuple [.int, m.state])]).isData = true := by
    simp [Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass, hst]
  obtain ⟨d', n', vals, hfd, hzv, hvals⟩ := he
  obtain ⟨n'', hfd'⟩ := tupleD_ok hde
  have := find_det hfd hfd'
  subst this
  erw [Ty.up_tuple _ _ _ hst hopt] at hvals
  obtain ⟨v0, vs0, rfl, hv0, -⟩ := hvals
  have hsel : (Term.sel d' 0 0 te).denote M = v0 := by rw [sel_ctor _ (hte.trans hzv)]; rfl
  have hctx := adtCtor_rel (L := L) (M := M) (vs := [[m.key, m.state, r, .int]]) ⟨0, by simp⟩ _ _ h1
    (Ty.up _ m.key_data k0, Ty.up _ m.state_data e0.1, Ty.up _ m.records_data recs, tnow, ())
    ⟨_, _, rfl, htk ▸ hk, _, _, rfl, hsel ▸ hv0, _, _, rfl, hrec, _, _, rfl, hnow, rfl⟩
  rw [← up_mctx m m.ctx_data] at hctx
  have hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data (.inl (k0, e0.1, recs, tnow, ()))) cx :=
    (rel_ofTerm (need_ok.1 h2) _).2 hctx
  have hite : Holds M (.ite f c1 tt) ↔ Holds M c1 := by simp [holds_ite, hf, Val.toBool]
  rw [hite]
  exact m.invariants.app_exact hci hcic (by simp [Ty.machineCtx, Ty.isFn]) _ _ (ctx_rels m hcx _) h3

/-- The condition of the instances' invariant checks is exact: it holds exactly when the invariants fit at every
instance the table holds. -/
theorem instInvariants_exact (m : MachineV r e) {inv : Code (Ty.fn [Ty.machineCtx m.key m.state r] Ty.rules)}
    {ci : Term} (hci : m.invariants.code L = .ok (inv, ci)) (hcic : Holds M ci) (recs : r.den0) (tnow : Int)
    {records now : Term} (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M))
    (hnow : now.denote M = .int tnow) {x : Term} (tbl : m.table.den0)
    (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {checks : List InstCheck} {cond : Term} (henc : encodeInstInvariants L T m inv x records now = .ok (checks, cond)) :
    Holds M cond ↔ ∀ i ∈ instancesOf T m tbl, m.invariants.appFits L.count (.inl (i.key, i.state, recs, tnow, ()), ()) := by
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨cs, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨p0, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, hw, hp, hh⟩ := table_view htbl' h1
  let inst : m.key.den × (instEntry m.state).den → Step.Instance m :=
    fun y => instOf m (Ty.down _ m.key_data y.1) (Ty.down _ m.entry_data y.2)
  have hF : Forall2 (fun sl c => ∃ ch, instCheckAt L m inv de records now sl = .ok (ch, c)) (slotsOf d dt n 2 x)
      (cs.map (·.2)) := forall2_snd (mapM_ok _ _ _ h3)
  rw [allT_slots_exact (P := fun y => m.invariants.appFits L.count (.inl ((inst y).key, (inst y).state, recs, tnow, ()), ()))
    _ ?_ hS hh hF]
  · have hperm : (ys.map inst).Perm (instancesOf T m tbl) := by
      have := hp.map inst
      erw [Ty.up_table m.key (instEntry m.state) m.table_data m.key_data m.entry_data tbl, List.map_map] at this
      refine (this.trans (List.Perm.of_eq (List.map_congr_left fun q _ => ?_))).trans (List.mergeSort_perm _ _).symm
      simp [inst, Ty.down_up]
    constructor
    · intro h i hi
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hperm.mem_iff.2 hi)
      exact h y hy
    · intro h y hy
      exact h (inst y) (hperm.mem_iff.1 (List.mem_map.2 ⟨y, hy, rfl⟩))
  · rintro ⟨f, xs⟩ cj ⟨ch, hg⟩
    obtain ⟨X, hX⟩ := instCheckAt_cond m hg
    refine ⟨fun hf => ?_, fun y hf hey => ?_⟩
    · simp only at hf
      rw [hX]; simp [holds_ite, hf, Val.toBool, holds_tt]
    · obtain ⟨zk, zv, hz, hk, he⟩ := hey
      exact instCheck_exact m hci hcic recs tnow hrec hnow h2 hf hz (Ty.down _ m.key_data y.1)
        (Ty.down _ m.entry_data y.2) (by rw [Ty.up_down]; exact hk) (by rw [Ty.up_down]; exact he) hg

end


section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The condition of one machine's part of an event step is exact: it holds exactly when the machine's kept sources
fit, its reaction fits (`react_exact`), and its invariants fit at every instance after the step. -/
theorem machine_exact (m : MachineV r e) (hor : m.key.orderable = true)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now evT : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {mo : MachineOut} {c : Term} (henc : encodeMachine L T m x records now evT = .ok (mo, c)) :
    Holds M c ↔ ((m.instances.fits L.count).1 ∧ (m.on.fits L.count).1 ∧ (m.after.fits L.count).1 ∧
        (m.effect.fits L.count).1) ∧
      (m.instances.appFits L.count (recs, ()) ∧
        allFit (m.instances.fn (recs, ())) (keyFits L.count m (instancesOf T m tbl) recs tnow ev)) ∧
      (m.invariants.fits L.count).1 ∧
      ∀ i ∈ (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2,
        m.invariants.appFits L.count (.inl (i.key, i.state, recs, tnow, ()), ()) := by
  have hpl := Ty.plain_of_orderable _ hor
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rc, c0⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨o, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨inv, c2⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨checks, c3⟩, h4, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  rw [holds_andT, holds_andT, holds_andT, ← reactCode_exact (M := M) m h1, ← (m.invariants.code_exact (M := M) h3).1]
  have hB : ∀ (hc0 : Holds M c0), (Holds M c1 ↔ m.instances.appFits L.count (recs, ()) ∧
      allFit (m.instances.fn (recs, ())) (keyFits L.count m (instancesOf T m tbl) recs tnow ev)) := fun hc0 =>
    react_exact (T := T) m hpl h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2
  have hD : ∀ (hc0 : Holds M c0) (hc1 : Holds M c1) (hc2 : Holds M c2), (Holds M c3 ↔
      ∀ i ∈ (Step.machineStep T recs tnow ev ⟨m, instancesOf T m tbl⟩).1.2,
        m.invariants.appFits L.count (.inl (i.key, i.state, recs, tnow, ()), ())) := fun hc0 hc1 hc2 => by
    obtain ⟨⟨tbl', ht', hi'⟩, -⟩ := react_step (T := T) m hor h1 hc0 recs tnow ev hrec hnow hevT tbl htbl h2 hc1
    rw [← hi']
    exact instInvariants_exact m h3 hc2 recs tnow hrec hnow tbl' ht' h4
  constructor
  · rintro ⟨hc0, hc1, hc2, hc3⟩
    exact ⟨hc0, (hB hc0).1 hc1, hc2, (hD hc0 hc1 hc2).1 hc3⟩
  · rintro ⟨hc0, p1, hc2, p3⟩
    have hc1 := (hB hc0).2 p1
    exact ⟨hc0, hc1, hc2, (hD hc0 hc1 hc2).2 p3⟩

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

/-- The condition of an event's service part is exact: it holds exactly when the subscription's wrap fits at the
value, `apply` at the records and the event, and the invariants at the records after. -/
theorem event_exact {v : ServiceV} (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
    (hd : EventData v i) {ec : EventCode v i} {ce : Term} (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce)
    {recs : v.records.den0} {records sv : Term} (hrec : RelV L v.records (Ty.up _ hd.records recs) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M))
    {o : EventOut} {cond : Term} (henc : encodeEvent L ec records sv = .ok (o, cond)) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    Holds M cond ↔ (v.subscribes.get i).wrap.appFits L.count (value, ()) ∧ v.apply.appFits L.count (recs, ev, ()) ∧
      v.invariants.appFits L.count (v.apply.fn (recs, ev, ()), ()) := by
  intro _
  have he := EventCode.rel_of hd hec hce
  obtain ⟨⟨a, c1'⟩, g1, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2'⟩, g2, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3'⟩, g3, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  obtain ⟨hca, hcwn⟩ := (holds_andT _ _).1 hce
  obtain ⟨hcw, hcn⟩ := (holds_andT _ _).1 hcwn
  obtain ⟨vc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ev, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rc, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rr, c2⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c3⟩, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨rt, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨et, h8, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvc : Smt.Rel M L _ (Ty.up _ hd.value value) vc := (rel_ofTerm (need_ok.1 h1) _).2 hsv
  have hargs : Smt.Rels M L [(v.subscribes.get i).event]
      (Ty.up (.tuple [(v.subscribes.get i).event]) hd.wrapArgs (value, ())) (vc, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [(v.subscribes.get i).event]) hd.wrapArgs (value, ())).1 vc ∧ True
    erw [Ty.up_tuple _ _ _ hd.value rfl]; exact ⟨hvc, trivial⟩
  have e1 : Holds M c1 ↔ (v.subscribes.get i).wrap.appFits L.count (value, ()) :=
    (v.subscribes.get i).wrap.app_exact g2 hcw (by simpa using ofTerm_notFn (need_ok.1 h1)) _ _ hargs h2
  have hrc : Smt.Rel M L _ (Ty.up _ hd.records recs) rc := (rel_ofTerm (need_ok.1 h3) _).2 hrec
  have hevNF : v.event.isFn = false := term_notFn (need_ok.1 h8)
  have e2 : ∀ (hc1 : Holds M c1), (Holds M c2 ↔ v.apply.appFits L.count (recs, (v.subscribes.get i).wrap.fn (value, ()), ())) := by
    intro hc1
    have hev := he.wrap _ (vc, ()) hargs ev c1 h2 hc1
    erw [Ty.up_fn _ _ _ hd.wrapArgs hd.event] at hev
    have hargs2 : Smt.Rels M L [v.records, v.event]
        (Ty.up (.tuple [v.records, v.event]) hd.applyArgs (recs, (v.subscribes.get i).wrap.fn (value, ()), ()))
        (rc, Code.share _ ev, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [v.records, v.event]) hd.applyArgs
        (recs, (v.subscribes.get i).wrap.fn (value, ()), ())).1 rc ∧
        Smt.Rels M L [v.event] (Ty.up (.tuple [v.records, v.event]) hd.applyArgs
          (recs, (v.subscribes.get i).wrap.fn (value, ()), ())).2 (Code.share _ ev, ())
      erw [Ty.up_tuple _ _ _ hd.records (by simp [Ty.isData, Ty.isDatas, hd.event])]
      refine ⟨hrc, ?_⟩
      show Smt.Rel M L _ (Ty.up (.tuple [v.event]) (by simp only [Ty.isData, Ty.isDatas, hd.event, Bool.and_self])
        ((v.subscribes.get i).wrap.fn (value, ()), ())).1 _ ∧ True
      erw [Ty.up_tuple _ _ _ hd.event rfl]; exact ⟨rel_share hev, trivial⟩
    refine v.apply.app_exact g1 hca (fun t ht => ?_) _ _ hargs2 h4
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ofTerm_notFn (need_ok.1 h3)
    · exact hevNF
  have e3 : ∀ (hc1 : Holds M c1) (hc2 : Holds M c2), (Holds M c3 ↔
      v.invariants.appFits L.count (v.apply.fn (recs, (v.subscribes.get i).wrap.fn (value, ()), ()), ())) := by
    intro hc1 hc2
    have hev := he.wrap _ (vc, ()) hargs ev c1 h2 hc1
    erw [Ty.up_fn _ _ _ hd.wrapArgs hd.event] at hev
    have hargs2 : Smt.Rels M L [v.records, v.event]
        (Ty.up (.tuple [v.records, v.event]) hd.applyArgs (recs, (v.subscribes.get i).wrap.fn (value, ()), ()))
        (rc, Code.share _ ev, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [v.records, v.event]) hd.applyArgs
        (recs, (v.subscribes.get i).wrap.fn (value, ()), ())).1 rc ∧
        Smt.Rels M L [v.event] (Ty.up (.tuple [v.records, v.event]) hd.applyArgs
          (recs, (v.subscribes.get i).wrap.fn (value, ()), ())).2 (Code.share _ ev, ())
      erw [Ty.up_tuple _ _ _ hd.records (by simp [Ty.isData, Ty.isDatas, hd.event])]
      refine ⟨hrc, ?_⟩
      show Smt.Rel M L _ (Ty.up (.tuple [v.event]) (by simp only [Ty.isData, Ty.isDatas, hd.event, Bool.and_self])
        ((v.subscribes.get i).wrap.fn (value, ()), ())).1 _ ∧ True
      erw [Ty.up_tuple _ _ _ hd.event rfl]; exact ⟨rel_share hev, trivial⟩
    have hr := he.apply _ _ hargs2 rr c2 h4 hc2
    erw [Ty.up_fn _ _ _ hd.applyArgs hd.records] at hr
    have hargs3 : Smt.Rels M L [v.records]
        (Ty.up (.tuple [v.records]) hd.invArgs (v.apply.fn (recs, (v.subscribes.get i).wrap.fn (value, ()), ()), ()))
        (Code.share _ rr, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [v.records]) hd.invArgs
        (v.apply.fn (recs, (v.subscribes.get i).wrap.fn (value, ()), ()), ())).1 _ ∧ True
      erw [Ty.up_tuple _ _ _ hd.records rfl]; exact ⟨rel_share hr, trivial⟩
    exact v.invariants.app_exact g3 hcn (by simpa using ofTerm_notFn (need_ok.1 h3)) _ _ hargs3 h5
  rw [holds_andT, holds_andT]
  constructor
  · rintro ⟨hc1, hc2, hc3⟩
    exact ⟨e1.1 hc1, (e2 hc1).1 hc2, (e3 hc1 hc2).1 hc3⟩
  · rintro ⟨p1, p2, p3⟩
    have hc1 := e1.2 p1
    have hc2 := (e2 hc1).2 p2
    exact ⟨hc1, hc2, (e3 hc1 hc2).2 p3⟩

end


section
variable {r e : Ty}

/-- Whether the functions one machine's part of an event step applies fit: its kept sources, its reaction
(`keyFits` for each key of the bag `instances` returns) and its invariants at every instance after the step. -/
def machineFits (S : Ty → Nat) (T : List TypeDecl) (sm : Step.MachineState r e) (recs : r.den0) (tnow : Int)
    (ev : e.den0) : Prop :=
  ((sm.1.instances.fits S).1 ∧ (sm.1.on.fits S).1 ∧ (sm.1.after.fits S).1 ∧ (sm.1.effect.fits S).1) ∧
    (sm.1.instances.appFits S (recs, ()) ∧ allFit (sm.1.instances.fn (recs, ())) (keyFits S sm.1 sm.2 recs tnow ev)) ∧
    (sm.1.invariants.fits S).1 ∧
    ∀ i ∈ (Step.machineStep T recs tnow ev sm).1.2,
      sm.1.invariants.appFits S (.inl (i.key, i.state, recs, tnow, ()), ())

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {v : ServiceV}

/-- The condition of the machines' part of an event step is exact: it holds exactly when every machine's part fits. -/
theorem machines_exact (recs : v.records.den0) (tnow : Int) (ev : v.event.den0) {records now evT : Term}
    (hrd : v.records.isData = true) (hed : v.event.isData = true)
    (hrec : RelV L v.records (Ty.up _ hrd recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    (hevT : RelV L v.event (Ty.up _ hed ev) (evT.denote M)) :
    (ms : List (MachineV v.records v.event)) → (xs : List Term) → (sms : List (Step.MachineState v.records v.event)) →
    (outs : List MachineOut) → {c : Term} → MachinesRel M L T ms xs sms →
    (∀ m ∈ ms, m.key.orderable = true) → encodeMachines L T ms xs records now evT = .ok (outs, c) →
    (Holds M c ↔ ∀ sm ∈ sms, machineFits L.count T sm recs tnow ev)
  | [], [], [], outs, c, _, _, henc => by
    simp only [encodeMachines, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at henc
    obtain ⟨-, rfl⟩ := henc
    simp [holds_tt]
  | m :: ms, x :: xs, sm :: sms, outs, c, ⟨⟨tbl, htbl, hsm⟩, hrest⟩, hor, henc => by
    obtain ⟨⟨a, c1⟩, h1, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨as, c2⟩, h2, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    subst hsm
    rw [holds_andT, machine_exact (T := T) m (hor m (by simp)) recs tnow ev hrec hnow hevT tbl htbl h1,
      machines_exact recs tnow ev hrd hed hrec hnow hevT ms xs sms as hrest (fun m' hm => hor m' (by simp [hm])) h2]
    simp only [List.mem_cons, forall_eq_or_imp]
    rfl
  | [], [], _ :: _, _, _, h, _, _ | [], _ :: _, _, _, _, h, _, _ | _ :: _, [], _, _, _, h, _, _
  | _ :: _, _ :: _, [], _, _, h, _, _ => h.elim

/-- The conditions `event_step` takes are exact together: the codes', the service part's and the machines' hold
exactly when the kept sources fit, the service's functions fit where the step applies them, and every machine's part
fits on the records after the event. -/
theorem event_step_exact (s : State v) (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
    (hd : EventData v i) {ec : EventCode v i} {ce : Term} (hec : EventCode.of L v i = .ok (ec, ce)) {records sv now : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) (hnow : now.denote M = .int s.now)
    {xs : List Term} (hms : MachinesRel M L T v.machines xs s.machines)
    (hor : ∀ m ∈ v.machines, m.key.orderable = true)
    {o : EventOut} {cond : Term} (henc : encodeEvent L ec records sv = .ok (o, cond))
    {outs : List MachineOut} {cm : Term} (hm : encodeMachines L T v.machines xs o.records now o.event = .ok (outs, cm)) :
    let ev := (v.subscribes.get i).wrap.fn (value, ())
    let recs' := v.apply.fn (s.records, ev, ())
    Holds M (andT ce (andT cond cm)) ↔
      ((v.apply.fits L.count).1 ∧ ((v.subscribes.get i).wrap.fits L.count).1 ∧ (v.invariants.fits L.count).1) ∧
      ((v.subscribes.get i).wrap.appFits L.count (value, ()) ∧ v.apply.appFits L.count (s.records, ev, ()) ∧
        v.invariants.appFits L.count (recs', ())) ∧
      ∀ sm ∈ s.machines, machineFits L.count T sm recs' s.now ev := by
  intro ev recs'
  rw [holds_andT, holds_andT, eventCode_exact (M := M) hec]
  have e2 : ∀ (hce : Holds M ce), (Holds M cond ↔ _) := fun hce => event_exact i value hd hec hce hrec hsv henc
  have e3 : ∀ (hce : Holds M ce) (hc : Holds M cond), (Holds M cm ↔ ∀ sm ∈ s.machines, machineFits L.count T sm recs' s.now ev) :=
    fun hce hc => by
      obtain ⟨hr', he', -⟩ := event_rel i value hd hec hce hrec hsv henc hc
      exact machines_exact _ s.now _ hd.records hd.event hr' hnow he' v.machines xs s.machines outs hms hor hm
  constructor
  · rintro ⟨p0, hc, hcm⟩
    have hce := (eventCode_exact (M := M) hec).2 p0
    exact ⟨p0, (e2 hce).1 hc, (e3 hce hc).1 hcm⟩
  · rintro ⟨p0, p1, p2⟩
    have hce := (eventCode_exact (M := M) hec).2 p0
    have hc := (e2 hce).2 p1
    exact ⟨p0, hc, (e3 hce hc).2 p2⟩

end

end Tazuna.Smt
