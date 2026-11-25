import Tazuna.Smt.Machines
import Tazuna.Smt.Exact

/-! The condition of a machine's reaction is exact: it holds exactly when every function the step applies fits the
layout's slot counts, where the step applies it: `instances` at the records, `on` at each key with an instance,
`after` and `effect` only where the instance enters a state. An over-strong guard (as before f86c272f, which asked
`after` on every instance) makes this theorem false. -/

namespace Tazuna.Smt

open Tazuna.Ir

theorem _root_.Tazuna.Ir.Fun.args_data {ps : List Ty} {r : Ty} (f : Fun (.fn ps r)) : (Ty.tuple ps).isData = true := by
  have := f.ht
  simp only [Ty.isData, Bool.and_eq_true] at this ⊢
  exact this.1

/-- Whether a kept function's application to data fits. -/
def _root_.Tazuna.Ir.Fun.appFits (S : Ty → Nat) {ps : List Ty} {r : Ty} (f : Fun (.fn ps r))
    (xs : (Ty.tuple ps).den0) : Prop :=
  ((f.fits S).2 (Ty.up _ f.args_data xs) (FTs.dflt ps)).1

/-- The same for a kept function that returns effects. -/
def _root_.Tazuna.Ir.EffectFun.appFits (S : Ty → Nat) {ps : List Ty} {r : Ty} (f : EffectFun ps r)
    (xs : (Ty.tuple ps).den0) : Prop :=
  ((f.fits S).2 (Ty.up _ f.hps xs) (FTs.dflt ps)).1

section
variable {M : Model} {L : Layout}

theorem _root_.Tazuna.Ir.Fun.app_exact {ps : List Ty} {r : Ty} (f : Fun (.fn ps r)) {s : Code (.fn ps r)} {c : Term}
    (h : f.code L = .ok (s, c)) (hc : Holds M c) (hnf : ∀ t ∈ ps, t.isFn = false) (xs : (Ty.tuple ps).den0)
    (cs : Codes ps) (hxs : Rels M L ps (Ty.up _ f.args_data xs) cs) {o : Code r} {c' : Term} (ho : s cs = .ok (o, c')) :
    Holds M c' ↔ f.appFits L.count xs := by
  have hf := (f.code_exact (M := M) h).2 hc
  exact (hf _ _ cs hxs (frels_of_notFn hnf _ _ _) o c' ho).1

theorem _root_.Tazuna.Ir.EffectFun.app_exact {ps : List Ty} {r : Ty} (f : EffectFun ps r) {s : Code (.fn ps r)}
    {c : Term} (h : f.code L = .ok (s, c)) (hc : Holds M c) (hnf : ∀ t ∈ ps, t.isFn = false) (xs : (Ty.tuple ps).den0)
    (cs : Codes ps) (hxs : Rels M L ps (Ty.up _ f.hps xs) cs) {o : Code r} {c' : Term} (ho : s cs = .ok (o, c')) :
    Holds M c' ↔ f.appFits L.count xs := by
  have hf := (f.code_exact (M := M) h).2 hc
  exact (hf _ _ cs hxs (frels_of_notFn hnf _ _ _) o c' ho).1

end

section
variable {r e : Ty}

/-- Whether the functions the step applies to the key `k` fit: `on` where an instance has the key, and `after` and
`effect` at the state the instance enters (`initial` for a new one), only where it enters one. -/
def keyFits (S : Ty → Nat) (m : MachineV r e) (insts : List (Step.Instance m)) (recs : r.den0) (tnow : Int)
    (ev : e.den0) (k : m.key.den0) : Prop :=
  match insts.find? ((Ty.semWith Dsl.base m.key).2 k ·.key) with
  | some i => m.on.appFits S (.inl (i.key, i.state, recs, tnow, ()), ev, ()) ∧
    match m.on.fn (.inl (i.key, i.state, recs, tnow, ()), ev, ()) with
    | .inr (.inl (s, ())) => m.after.appFits S (.inl (k, s, recs, tnow, ()), ()) ∧
        m.effect.appFits S (.inl (k, s, recs, tnow, ()), ())
    | _ => True
  | none => m.after.appFits S (.inl (k, m.initial, recs, tnow, ()), ()) ∧
      m.effect.appFits S (.inl (k, m.initial, recs, tnow, ()), ())

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

theorem ctx_rels (m : MachineV r e) {x : (Ty.machineCtx m.key m.state r).den0} {cx : Code _}
    (hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx) (h : (Ty.tuple [Ty.machineCtx m.key m.state r]).isData = true) :
    Smt.Rels M L [Ty.machineCtx m.key m.state r] (Ty.up (.tuple [_]) h (x, ())) (cx, ()) := by
  show Smt.Rel M L _ (Ty.up (.tuple [Ty.machineCtx m.key m.state r]) h (x, ())).1 cx ∧ True
  erw [Ty.up_tuple _ _ _ m.ctx_data rfl]; exact ⟨hcx, trivial⟩

theorem ctx_ev_rels (m : MachineV r e) {x : (Ty.machineCtx m.key m.state r).den0} {ev : e.den0} {cx : Code _}
    {evc : Code e} (hcx : Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx) (hev : Smt.Rel M L e (Ty.up _ m.event_data ev) evc)
    (h : (Ty.tuple [Ty.machineCtx m.key m.state r, e]).isData = true) :
    Smt.Rels M L [Ty.machineCtx m.key m.state r, e] (Ty.up (.tuple [_, _]) h (x, ev, ())) (cx, evc, ()) := by
  show Smt.Rel M L _ (Ty.up (.tuple [Ty.machineCtx m.key m.state r, e]) h (x, ev, ())).1 cx ∧
    Smt.Rels M L [e] (Ty.up (.tuple [Ty.machineCtx m.key m.state r, e]) h (x, ev, ())).2 (evc, ())
  erw [Ty.up_tuple _ _ _ m.ctx_data (by simp [Ty.isData, Ty.isDatas, m.event_data])]
  refine ⟨hcx, ?_⟩
  show Smt.Rel M L _ (Ty.up (.tuple [e]) (by simp [Ty.isData, Ty.isDatas, m.event_data]) (ev, ())).1 evc ∧ True
  erw [Ty.up_tuple _ _ _ m.event_data rfl]; exact ⟨hev, trivial⟩

/-- The exactness of the three codes a reaction slot applies, at related arguments. -/
structure ReactExact (m : MachineV r e) (rc : ReactCode m) : Prop where
  on : ∀ (x : (Ty.machineCtx m.key m.state r).den0) (ev : e.den0) cx evc,
    Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx → Smt.Rel M L e (Ty.up _ m.event_data ev) evc →
    ∀ o c, rc.on (cx, evc, ()) = .ok (o, c) → (Holds M c ↔ m.on.appFits L.count (x, ev, ()))
  after : ∀ (x : (Ty.machineCtx m.key m.state r).den0) cx, Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx →
    ∀ o c, rc.after (cx, ()) = .ok (o, c) → (Holds M c ↔ m.after.appFits L.count (x, ()))
  effect : ∀ (x : (Ty.machineCtx m.key m.state r).den0) cx, Smt.Rel M L _ (Ty.up _ m.ctx_data x) cx →
    ∀ o c, rc.effect (cx, ()) = .ok (o, c) → (Holds M c ↔ m.effect.appFits L.count (x, ()))

/-- One occupied slot of the instances bag, holding the key `k`: its condition holds exactly when the functions the
step applies to `k` fit. -/
theorem react_at_exact (m : MachineV r e) (hpl : m.key.plain = true) (rc : ReactCode m)
    (hon : Smt.Rel M L _ (Ty.up _ m.on.ht m.on.fn) rc.on) (hx : ReactExact (M := M) (L := L) m rc)
    (recs : r.den0) (tnow : Int) (ev : e.den0) {records now : Term}
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {evc : Code e} (hev : Smt.Rel M L e (Ty.up _ m.event_data ev) evc)
    (tbl : m.table.den0) {So : List Slot} {sv : List (Bool × List Val)} {ys : List (m.key.den × (instEntry m.state).den)}
    (hS : SlotsDen M So sv) (hw : ∀ p ∈ sv, p.2.length = 2) (hp : ys.Perm (Ty.up _ m.table_data tbl).1)
    (hh : Holds2 (ETab L m.key (instEntry m.state)) ys sv)
    {de nde dn nn : Nat} (hde : L.find? (instEntry m.state) = some (de, nde)) (hdn : L.find? (Ty.next m.state) = some (dn, nn))
    {init : Val} (hinit : embedV L m.state (Ty.up _ m.state_data m.initial) = some init) (dflt noneT : Term)
    {f first : Term} {xs : List Term} {zk : Val} (hf : f.denote M = .bool true) (hxs : Term.denotes M xs = [zk])
    (k : m.key.den0) (hk : RelV L m.key (Ty.up _ m.key_data k) zk)
    {sl : Slot} {fx cj : Term}
    (hg : reactAt L m rc de dn So init dflt noneT records now evc ((f, xs), first) = .ok ((sl, fx), cj)) :
    Holds M cj ↔ keyFits L.count m (instancesOf T m tbl) recs tnow ev k := by
  obtain ⟨kt, rfl⟩ : ∃ kt, xs = [kt] := by
    match xs, hxs with
    | [kt], _ => exact ⟨kt, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨kc, h1, hg⟩ := bind_ok.1 hg
  obtain ⟨hits, h2, hg⟩ := bind_ok.1 hg
  obtain ⟨octxT, h3, hg⟩ := bind_ok.1 hg
  obtain ⟨octx, h4, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨o, c1⟩, h5, hg⟩ := bind_ok.1 hg
  obtain ⟨ot, h6, hg⟩ := bind_ok.1 hg
  obtain ⟨nctxT, h7, hg⟩ := bind_ok.1 hg
  obtain ⟨nctx, h8, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨a, c2⟩, h9, hg⟩ := bind_ok.1 hg
  obtain ⟨at_, h10, hg⟩ := bind_ok.1 hg
  obtain ⟨tmT, h11, hg⟩ := bind_ok.1 hg
  obtain ⟨⟨xo, c3⟩, h12, hg⟩ := bind_ok.1 hg
  obtain ⟨xt, h13, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  simp only [List.headD_cons] at h1 h3 h7
  have hkr : RelV L m.key (Ty.up _ m.key_data k) (kt.denote M) := hxs ▸ hk
  have hkc : Smt.Rel M L m.key (Ty.up _ m.key_data k) kc := (rel_ofTerm (need_ok.1 h1) _).2 hkr
  obtain ⟨hfound, hpick⟩ := lookup_slots m hkc dflt So sv hits ys hS hw (mapM_ok _ _ _ h2) hh
  have hlook := lookup_eq (T := T) m hpl tbl hp k
  rw [any_find?, hlook] at hfound
  have hcj : Holds M (Term.ite f (andT (.ite (anyT (hits.map fun (g, h, _) => .and g h)) c1 tt)
      (.ite (.or (.not (anyT (hits.map fun (g, h, _) => .and g h))) (.is dn 1 ot)) (andT c2 c3) tt)) tt) ↔
      Holds M (andT (.ite (anyT (hits.map fun (g, h, _) => .and g h)) c1 tt)
        (.ite (.or (.not (anyT (hits.map fun (g, h, _) => .and g h))) (.is dn 1 ot)) (andT c2 c3) tt)) := by
    simp [holds_ite, hf, Val.toBool]
  rw [hcj, holds_andT]
  unfold keyFits
  cases hfind : (instancesOf T m tbl).find? (fun i => (Ty.semWith Dsl.base m.key).2 k i.key) with
  | none =>
    rw [hfind] at hfound
    have hfd : (anyT (hits.map fun (g, h, _) => .and g h)).denote M = .bool false := hfound
    have hst : (Term.ite (anyT (hits.map fun (g, h, _) => .and g h)) (.ite (.is dn 1 ot) (.sel dn 1 0 ot)
        (.sel de 0 0 (pickT dflt hits))) init.term).denote M = init := by
      simp only [Term.denote, hfd, Val.toBool, Bool.false_eq_true, ite_false, Val.denote_term]
    have hstr : RelV L m.state (Ty.up _ m.state_data m.initial) init := embed_rel _ _ _ hinit
    have hcx := ctx_rel m hkr (hst ▸ hstr) hrec hnow h7 (need_ok.1 h8)
    have e1 : Holds M (.ite (anyT (hits.map fun (g, h, _) => .and g h)) c1 tt) := by
      simp [holds_ite, hfd, Val.toBool, holds_tt]
    have e2 : Holds M (.ite (.or (.not (anyT (hits.map fun (g, h, _) => .and g h))) (.is dn 1 ot)) (andT c2 c3) tt) ↔
        Holds M (andT c2 c3) := by
      simp [holds_ite, Term.denote, hfd, Val.toBool]
    simp only
    rw [e2, holds_andT, hx.after _ _ hcx a c2 h9, hx.effect _ _ hcx xo c3 h12]
    exact ⟨fun h => h.2, fun h => ⟨e1, h⟩⟩
  | some i =>
    rw [hfind] at hfound hlook
    have hfd : (anyT (hits.map fun (g, h, _) => .and g h)).denote M = .bool true := hfound
    have hki : i.key = k := by
      have := List.find?_some hfind
      exact ((Ty.beq_plain _ hpl _ _).1 this).symm
    subst hki
    have hold := hpick _ (by rw [hlook]; rfl)
    obtain ⟨v0, v1, hv, hv0, hv1⟩ := (entry_rel_iff m hde _ _ _).1 hold
    have hsel0 : (Term.sel de 0 0 (pickT dflt hits)).denote M = v0 := by rw [sel_ctor _ hv]; rfl
    have hocx := ctx_rel m hkr (hsel0 ▸ hv0) hrec hnow h3 (need_ok.1 h4)
    have e1 : Holds M (.ite (anyT (hits.map fun (g, h, _) => .and g h)) c1 tt) ↔ Holds M c1 := by
      simp [holds_ite, hfd, Val.toBool]
    simp only
    rw [e1]
    constructor
    · rintro ⟨hc1, hrest⟩
      refine ⟨(hx.on _ _ _ _ hocx hev o c1 h5).1 hc1, ?_⟩
      have hoo := on_app m hon hocx hev h5 hc1
      have hot := (rel_term (need_ok.1 h6) _).1 hoo
      cases hon' : m.on.fn (.inl (i.key, i.state, recs, tnow, ()), ev, ()) with
      | inl u => trivial
      | inr x => match x with
        | .inl (s', ()) =>
          rw [hon'] at hot
          obtain ⟨vs, hvs, hvsr⟩ := next_rel m hdn _ _ hot
          have hst : (Term.ite (anyT (hits.map fun (g, h, _) => .and g h)) (.ite (.is dn 1 ot) (.sel dn 1 0 ot)
              (.sel de 0 0 (pickT dflt hits))) init.term).denote M = vs := by
            simp [Term.denote, hfd, hvs, Val.toBool]
          have hcx := ctx_rel m hkr (by rw [hst]; exact hvsr) hrec hnow h7 (need_ok.1 h8)
          have e2 : Holds M (.ite (.or (.not (anyT (hits.map fun (g, h, _) => .and g h))) (.is dn 1 ot)) (andT c2 c3) tt) ↔
              Holds M (andT c2 c3) := by
            simp [holds_ite, Term.denote, hfd, hvs, Val.toBool]
          rw [e2, holds_andT, hx.after _ _ hcx a c2 h9, hx.effect _ _ hcx xo c3 h12] at hrest
          exact hrest
        | .inr y => nomatch y
    · rintro ⟨p1, hrest⟩
      have hc1 := (hx.on _ _ _ _ hocx hev o c1 h5).2 p1
      refine ⟨hc1, ?_⟩
      have hoo := on_app m hon hocx hev h5 hc1
      have hot := (rel_term (need_ok.1 h6) _).1 hoo
      cases hon' : m.on.fn (.inl (i.key, i.state, recs, tnow, ()), ev, ()) with
      | inl u =>
        rw [hon'] at hot
        have hnext : ot.denote M = .ctor dn 0 [] := next_rel m hdn _ _ hot
        simp [holds_ite, Term.denote, hfd, hnext, Val.toBool, holds_tt]
      | inr x => match x with
        | .inl (s', ()) =>
          rw [hon'] at hot hrest
          obtain ⟨vs, hvs, hvsr⟩ := next_rel m hdn _ _ hot
          have hst : (Term.ite (anyT (hits.map fun (g, h, _) => .and g h)) (.ite (.is dn 1 ot) (.sel dn 1 0 ot)
              (.sel de 0 0 (pickT dflt hits))) init.term).denote M = vs := by
            simp [Term.denote, hfd, hvs, Val.toBool]
          have hcx := ctx_rel m hkr (by rw [hst]; exact hvsr) hrec hnow h7 (need_ok.1 h8)
          have e2 : Holds M (.ite (.or (.not (anyT (hits.map fun (g, h, _) => .and g h))) (.is dn 1 ot)) (andT c2 c3) tt) ↔
              Holds M (andT c2 c3) := by
            simp [holds_ite, Term.denote, hfd, hvs, Val.toBool]
          rw [e2, holds_andT, hx.after _ _ hcx a c2 h9, hx.effect _ _ hcx xo c3 h12]
          exact hrest
        | .inr y => nomatch y

end


section
variable {L : Layout} {T : List TypeDecl} {M : Model} {r e : Ty}

/-- The codes a reaction applies are exact where their own conditions hold. -/
theorem reactExact_of (m : MachineV r e) (he : e.isFn = false) {rc : ReactCode m} {crc : Term}
    (hrc : ReactCode.of L m = .ok (rc, crc)) (hcrc : Holds M crc) : ReactExact (M := M) (L := L) m rc := by
  obtain ⟨⟨ic, c1⟩, g1, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨oc, c2⟩, g2, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨ac, c3⟩, g3, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨xc, c4⟩, g4, hrc⟩ := bind_ok.1 hrc
  cases pure_ok.1 hrc
  obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hcrc
  obtain ⟨hc2, hc34⟩ := (holds_andT _ _).1 hc23
  obtain ⟨hc3, hc4⟩ := (holds_andT _ _).1 hc34
  have hctx : ∀ t ∈ [Ty.machineCtx m.key m.state r], t.isFn = false := by simp [Ty.machineCtx, Ty.isFn]
  refine ⟨fun x ev cx evc hcx hev o c h => ?_, fun x cx hcx o c h => ?_, fun x cx hcx o c h => ?_⟩
  · refine m.on.app_exact g2 hc2 (fun t ht => ?_) _ _ (ctx_ev_rels m hcx hev _) h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · rfl
    · exact he
  · exact m.after.app_exact g3 hc3 hctx _ _ (ctx_rels m hcx _) h
  · exact m.effect.app_exact g4 hc4 hctx _ _ (ctx_rels m hcx _) h

/-- A reaction's codes' own condition is exact: it holds exactly when the four kept functions' sources fit. -/
theorem reactCode_exact (m : MachineV r e) {rc : ReactCode m} {crc : Term} (hrc : ReactCode.of L m = .ok (rc, crc)) :
    Holds M crc ↔ (m.instances.fits L.count).1 ∧ (m.on.fits L.count).1 ∧ (m.after.fits L.count).1 ∧
      (m.effect.fits L.count).1 := by
  obtain ⟨⟨ic, c1⟩, g1, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨oc, c2⟩, g2, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨ac, c3⟩, g3, hrc⟩ := bind_ok.1 hrc
  obtain ⟨⟨xc, c4⟩, g4, hrc⟩ := bind_ok.1 hrc
  cases pure_ok.1 hrc
  rw [holds_andT, holds_andT, holds_andT, (m.instances.code_exact (M := M) g1).1, (m.on.code_exact (M := M) g2).1,
    (m.after.code_exact (M := M) g3).1, (m.effect.code_exact (M := M) g4).1]

theorem firstSlots_length (t : Ty) : (prev S : List Slot) → (fs : List Term) → firstSlots L t prev S = .ok fs →
    fs.length = S.length
  | _, [], fs, h => by cases h; rfl
  | prev, (f, xs) :: rest, fs, h => by
    simp only [firstSlots] at h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨fs', h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    simp [firstSlots_length t _ rest fs' h3]

/-- Conditions of the form "where the slot is occupied": their conjunction holds exactly when the property each
occupied slot's condition decides holds of every item. -/
theorem allT_slots_exact {α : Type} {E : α → List Val → Prop} {P : α → Prop} (G : Slot → Term → Prop)
    (hG : ∀ sl c, G sl c → (sl.1.denote M = .bool false → Holds M c) ∧
      (∀ y, sl.1.denote M = .bool true → E y (Term.denotes M sl.2) → (Holds M c ↔ P y))) :
    {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List α} → {cs : List Term} →
    SlotsDen M S sv → Holds2 E ys sv → Forall2 G S cs → (Holds M (allT cs) ↔ ∀ y ∈ ys, P y)
  | [], [], [], [], _, _, _ => by simp [allT, Holds, tt, Term.denote, Val.toBool]
  | [], [], _ :: _, [], _, h, _ => nomatch h
  | (f, xs) :: S, (false, vs) :: sv, ys, c :: cs, ⟨hf, hx, h⟩, he, ⟨hc, hR⟩ => by
    have ih := allT_slots_exact G hG h (by simpa [Holds2, occupied] using he) hR
    rw [← ih, show allT (c :: cs) = .and c (allT cs) from rfl, holds_and]
    exact ⟨fun h => h.2, fun h => ⟨(hG _ c hc).1 hf, h⟩⟩
  | (f, xs) :: S, (true, vs) :: sv, y :: ys, c :: cs, ⟨hf, hx, h⟩, he, ⟨hc, hR⟩ => by
    simp only [Holds2, occupied, ite_true, List.filterMap_cons, Forall2] at he
    have ih := allT_slots_exact G hG h he.2 hR
    have hy := (hG _ c hc).2 y hf (by rw [hx]; exact he.1)
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [← ih, ← hy, show allT (c :: cs) = .and c (allT cs) from rfl, holds_and]
  | (_, _) :: _, (true, _) :: _, [], _, _, he, _ => by simp [Holds2, occupied, Forall2] at he

theorem reactAt_cond (m : MachineV r e) {rc : ReactCode m} {de dn : Nat} {So : List Slot} {init : Val}
    {dflt noneT records now : Term} {evc : Code e} {f first : Term} {xs : List Term} {sl : Slot} {fx cj : Term}
    (hg : reactAt L m rc de dn So init dflt noneT records now evc ((f, xs), first) = .ok ((sl, fx), cj)) :
    ∃ X, cj = .ite f X tt := by
  repeat obtain ⟨_, _, hg⟩ := bind_ok.1 hg
  cases pure_ok.1 hg
  exact ⟨_, rfl⟩

/-- The condition of a machine's reaction is exact: where the reaction's codes' own condition holds, it holds exactly
when `instances` fits at the records and the functions the step applies to each key of its bag fit
(`keyFits`). -/
theorem react_exact (m : MachineV r e) (hpl : m.key.plain = true) {rc : ReactCode m}
    {crc : Term} (hrc : ReactCode.of L m = .ok (rc, crc)) (hcrc : Holds M crc) (recs : r.den0) (tnow : Int) (ev : e.den0)
    {records now evT : Term} (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M))
    (hnow : now.denote M = .int tnow) (hevT : RelV L e (Ty.up _ m.event_data ev) (evT.denote M))
    (tbl : m.table.den0) {x : Term} (htbl : RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M))
    {o : ReactOut} {cond : Term} (henc : encodeReact L m rc x records now evT = .ok (o, cond)) :
    Holds M cond ↔ m.instances.appFits L.count (recs, ()) ∧
      allFit (m.instances.fn (recs, ())) (keyFits L.count m (instancesOf T m tbl) recs tnow ev) := by
  have hkd := m.key_data
  have hcodes := hrc
  obtain ⟨⟨ic, c1⟩, g1, hrc'⟩ := bind_ok.1 hcodes
  obtain ⟨⟨oc, c2⟩, g2, hrc'⟩ := bind_ok.1 hrc'
  obtain ⟨⟨ac, c3⟩, g3, hrc'⟩ := bind_ok.1 hrc'
  obtain ⟨⟨xc, c4⟩, g4, hrc'⟩ := bind_ok.1 hrc'
  cases pure_ok.1 hrc'
  obtain ⟨hc1, hc23⟩ := (holds_andT _ _).1 hcrc
  obtain ⟨hc2, -⟩ := (holds_andT _ _).1 hc23
  have hbagd : (Ty.fn [r] (.bag m.key)).isData = true := m.instances.ht
  have hi := m.instances.code_fn hbagd g1 hc1
  have hon := m.on.code_fn m.on.ht g2 hc2
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨de, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dn, nn⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dopt, nopt⟩, h3', henc⟩ := bind_ok.1 henc
  obtain ⟨rcd, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨evc, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨bag, c0⟩, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨bagT, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨db, nb, dtb⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨init, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨dflt, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨firsts, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨slots, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨kd, h14, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨nde, hde⟩ := tupleD_ok h2
  have hx := reactExact_of (M := M) m (ofTerm_notFn (need_ok.1 h5)) hcodes hcrc
  have hrcd : Smt.Rel M L r (Ty.up _ m.records_data recs) rcd := (rel_ofTerm (need_ok.1 h4) _).2 hrec
  have hevc : Smt.Rel M L e (Ty.up _ m.event_data ev) evc := (rel_ofTerm (need_ok.1 h5) _).2 hevT
  have hargs : (Ty.tuple [r]).isData = true := by simp [Ty.isData, Ty.isDatas, m.records_data]
  have hrels : Smt.Rels M L [r] (Ty.up (.tuple [r]) hargs (recs, ())) (rcd, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [r]) hargs (recs, ())).1 rcd ∧ True
    erw [Ty.up_tuple _ _ _ m.records_data rfl]; exact ⟨hrcd, trivial⟩
  have hc0x : Holds M c0 ↔ m.instances.appFits L.count (recs, ()) :=
    m.instances.app_exact g1 hc1 (by simpa using ofTerm_notFn (need_ok.1 h4)) _ _ hrels h6
  rw [holds_andT, hc0x]
  refine and_congr_right fun hfit => ?_
  have hc0 := hc0x.2 hfit
  have hbagT : (Ty.bag m.key).isData = true := by simp [Ty.isData, hkd]
  have hbag : Smt.Rel M L (.bag m.key) (Ty.up _ hbagT (m.instances.fn (recs, ()))) bag := by
    have := hi _ _ hrels bag c0 h6 hc0
    erw [Ty.up_fn _ _ _ hargs hbagT] at this
    exact this
  have hbag' : Smt.Rel M L (.bag m.key) (Ty.up _ hbagT (m.instances.fn (recs, ()))) bagT :=
    (rel_term (need_ok.1 h7) _).1 hbag
  obtain ⟨svB, ysB, hSB, -, -, hpB, hyB⟩ := bag_view hbag' h8
  have htbl' : Smt.Rel M L (.table m.key (instEntry m.state)) (Ty.up _ m.table_data tbl) x := htbl
  obtain ⟨sv, ys, hS, -, hw, hp, hh⟩ := table_view htbl' h1
  have hlen : (slotsOf db dtb nb 1 bagT).length ≤ firsts.length := by
    rw [firstSlots_length (L := L) m.key [] _ firsts h11]; exact Nat.le_refl _
  have hF := forall2_zip_left hlen (mapM_ok _ _ _ h12)
  rw [allT_slots_exact (P := fun y => keyFits L.count m (instancesOf T m tbl) recs tnow ev (Ty.down _ hkd y)) _ ?_ hSB
    hyB hF]
  · rw [Ty.up_bag _ hbagT hkd] at hpB
    constructor
    · intro h k hk
      have := h _ (hpB.mem_iff.2 (List.mem_map.2 ⟨k, hk, rfl⟩))
      rwa [Ty.down_up] at this
    · intro h y hy
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (hpB.mem_iff.1 hy)
      rw [Ty.down_up]; exact h k hk
  · rintro ⟨f, xs⟩ cj ⟨first, ⟨⟨sl, fx⟩, c⟩, hg, rfl⟩
    obtain ⟨X, hX⟩ := reactAt_cond m hg
    refine ⟨fun hf => ?_, fun y hf hey => ?_⟩
    · simp only at hf
      rw [hX]; simp [holds_ite, hf, Val.toBool, holds_tt]
    · obtain ⟨zk, hzk, hzr⟩ := hey
      have hzr' : RelV L m.key (Ty.up _ hkd (Ty.down _ hkd y)) zk := by rw [Ty.up_down]; exact hzr
      exact react_at_exact (T := T) m hpl _ hon hx recs tnow ev hrec hnow hevc tbl hS hw hp hh hde (need_ok.1 h3)
        (need_ok.1 h9) dflt _ hf hzk (Ty.down _ hkd y) hzr' hg

end

end Tazuna.Smt
