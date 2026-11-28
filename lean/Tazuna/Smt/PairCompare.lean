import Tazuna.Smt.CodeInjective
import Tazuna.Smt.Fire
import Tazuna.Smt.Decide
import Tazuna.Smt.Verdict
import Tazuna.Semantics.StepRename

/-! What the pair questions compare, and what a comparison that holds says of the two results. Records and instance
tables are compared by Gleam's `==` (`eqFn`), which reads bags and tables as multisets; the events two runs apply, the
requests they send and the own effects they queue are compared as multisets of their codes (`bagEqT`), a request
without its wire id, as `Step.Same` reads them. A comparison that holds gives the relation the results are compared by
with every counter kept and the wire ids the runs sent matched one to one (`wire_match`); a request or own effect keeps
kept functions, which one code fixes only with the unique sites `P` they are records of (`eff_same`,
`pendingOf_alike`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The slots with only each item's second term: a request's entry without its wire id, an own effect without its
place in the queue. -/
def seconds (S : List (Slot 2)) : List (Slot 1) := S.map fun sl => (sl.1, ⟨[sl.2[1]], rfl⟩)

/-- The slots with each flag and item shared: a multiset comparison reads each of them once for every slot. -/
def shareSlots {w : Nat} (S : List (Slot w)) : List (Slot w) :=
  S.map fun sl => (sl.1.share, ⟨sl.2.1.map Term.share, by simp [sl.2.2]⟩)

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

theorem slotsDen_share {w : Nat} : {S : List (Slot w)} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    SlotsDen M (shareSlots S) sv
  | [], [], _ => trivial
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hx, h⟩ =>
    ⟨by simp [hf], by rw [← hx]; simp [denotes_eq_map], slotsDen_share h⟩

theorem seconds_den : {S : List (Slot 2)} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    ∃ sv', SlotsDen M (seconds S) sv' ∧
      Forall2 (fun vs vs' => ∃ a b, vs = [a, b] ∧ vs' = [b]) (occupied sv) (occupied sv')
  | [], [], _ => ⟨[], trivial, trivial⟩
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hx, h⟩ => by
    obtain ⟨sv', h1, h2⟩ := seconds_den h
    obtain ⟨a, c, rfl⟩ := xs.two
    refine ⟨(b, [c.denote M]) :: sv', ⟨hf, by simp [Term.denotes], h1⟩, ?_⟩
    simp only [Term.denotes] at hx
    cases b
    · simpa [occupied] using h2
    · simpa [occupied, Forall2, ← hx] using h2

/-- Items held one per slot, each a value `R` relates to its item. -/
theorem forall2_ones {α : Type} {R : α → Val → Prop} : {ys : List α} → {os : List (List Val)} →
    Forall2 (fun y vs => ∃ z, vs = [z] ∧ R y z) ys os →
    ∃ zs, Forall2 R ys zs ∧ Forall2 (fun z vs => vs = [z]) zs os
  | [], [], _ => ⟨[], trivial, trivial⟩
  | _ :: _, _ :: _, ⟨⟨z, rfl, hz⟩, h⟩ => by
    obtain ⟨zs, h1, h2⟩ := forall2_ones h
    exact ⟨z :: zs, ⟨hz, h1⟩, ⟨rfl, h2⟩⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- Slots that `bagEqT` with SMT-LIB's `=` finds equal hold the same items as multisets. -/
theorem bagEqT_perm {A B : List (Slot 1)} {svA svB : List (Bool × List Val)} {ysA ysB : List Val}
    (hA : SlotsDen M A svA) (hB : SlotsDen M B svB) (hhA : Holds2 (fun z vs => vs = [z]) ysA svA)
    (hhB : Holds2 (fun z vs => vs = [z]) ysB svB) (h : Holds M (bagEqT .eq A B)) : ysA.Perm ysB := by
  have hc : ∀ {S : List (Slot 1)} {sv : List (Bool × List Val)} {ys : List Val} (x : Term), SlotsDen M S sv →
      Holds2 (fun z vs => vs = [z]) ys sv → (countEqT .eq x S).denote M = .int (ys.filter (Val.beq (x.denote M))).length :=
    fun x hS hh => countT_den (aligned_map (V := fun y v => v = .bool (Val.beq (x.denote M) y)) (fun xs => .eq x xs[0])
      (fun y xs he => by
        obtain ⟨t, rfl⟩ := xs.one
        simp only [Term.denotes, List.cons.injEq] at he
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, he.1]
        rfl) hS hh)
  have hq : Aligned M (fun z vs => vs = [z]) (fun z => countBy Val.beq z ysA == countBy Val.beq z ysB) A
      (A.map fun sl => .eq (countEqT .eq sl.2[0] A) (countEqT .eq sl.2[0] B)) svA ysA :=
    aligned_map (fun xs => .eq (countEqT .eq xs[0] A) (countEqT .eq xs[0] B)) (fun z xs he => by
      obtain ⟨t, rfl⟩ := xs.one
      simp only [Term.denotes, List.cons.injEq] at he
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, hc t hA hhA, hc t hB hhB, he.1]
      show Val.bool (Val.beq _ _) = _
      simp only [Val.beq, countBy, natCast_beq]) hA hhA
  have hb : bagBeq Val.beq ysA ysB = true := by
    have := h
    simp only [Holds, bagEqT, Term.denote, sizeT_den hA, sizeT_den hB, allSlotT_den hq, ← holds2_length hhA,
      ← holds2_length hhB, Val.toBool, Bool.and_eq_true] at this
    have h1 : Val.beq (.int ysA.length) (.int ysB.length) = true := this.1
    simp only [Val.beq, natCast_beq] at h1
    simp only [bagBeq, Bool.and_eq_true]
    exact ⟨h1, this.2⟩
  have hiff : ∀ x y, Val.beq x y = true ↔ id x = id y := fun x y =>
    ⟨Val.eq_of_beq x y, fun e => by simp only [id] at e; subst e; exact Val.beq_refl x⟩
  simpa using (bagBeq_iff hiff ysA ysB).1 hb

/-- Items whose codes are the same as multisets relate as multisets, where items of one code relate. -/
theorem multi_of_codes {α β : Type} {R : α → Val → Prop} {R' : β → Val → Prop} {r : α → β → Prop}
    (hr : ∀ x y z, R x z → R' y z → r x y) {xs : List α} {ys : List β} {zs zs' : List Val}
    (hx : Forall2 R xs zs) (hz : zs.Perm zs') (hy : Forall2 R' ys zs') : Multi r xs ys := by
  obtain ⟨ys', hp, h'⟩ := forall2_perm hz.symm hy
  exact ⟨ys', forall2_imp (fun x y ⟨z, h1, h2⟩ => hr x y z h1 h2) (forall2_comp hx (forall2_flip h')), hp⟩

/-- Event slots `bagEqT` finds equal hold events that are the same as multisets. -/
theorem events_multi {v : ServiceV} {S S' : List (Slot 1)} {evs evs' : List v.event.den0}
    (h : EventsRel M L S evs) (h' : EventsRel M L S' evs')
    (he : Holds M (bagEqT .eq (shareSlots S) (shareSlots S'))) :
    Multi (Ty.rel0 PBij.refl v.event) evs evs' := by
  obtain ⟨sv, hS, hh⟩ := h
  obtain ⟨sv', hS', hh'⟩ := h'
  obtain ⟨zs, hz, hzo⟩ := forall2_ones hh
  obtain ⟨zs', hz', hzo'⟩ := forall2_ones hh'
  have hm := multi_of_codes (r := fun a b => Ty.rel0 PBij.refl v.event (Ty.down _ v.event_data a)
      (Ty.down _ v.event_data b)) (fun x y z h1 h2 =>
      rel0_same v.event_data (by rwa [Ty.up_down]) (by rwa [Ty.up_down])) hz
      (bagEqT_perm (slotsDen_share hS) (slotsDen_share hS') hzo hzo' he) hz'
  exact Multi.of_map (fun a b h => by simpa [Ty.down_up] using h) hm

/-- Two stored values whose terms Gleam's `==` finds equal are the same value, read as `==` reads it. -/
theorem rel0_of_eqFn {t : Ty} (hd : t.isData = true) (hc : t.comparable = true) {x y : t.den0} {a b : Term}
    (hx : RelV L t (Ty.up t hd x) (a.denote M)) (hy : RelV L t (Ty.up t hd y) (b.denote M))
    {f : Term → Term → Term} (hf : eqFn L t = .ok f) (he : Holds M (f a b)) : Ty.rel0 PBij.refl t x y := by
  have h := eqFn_ok t hf _ _ a b hx hy
  simp only [Holds, h, Val.toBool] at he
  rw [show Ty.deq t (Ty.up t hd x) (Ty.up t hd y) = Ty.deq0 t x y from Ty.deq_up t hd x y] at he
  exact Ty.rel0_deq_right hc (Ty.rel0_refl t hc x) he

/-- An instance from related table entries. -/
theorem instOf_rel {r e : Ty} {m : MachineV r e} {R : PBij} {k k' : m.key.den0} {x x' : m.state.den0}
    (hk : Ty.rel0 R m.key k k') (hx : Ty.rel0 R m.state x x') :
    Step.Instance.Rel R (instOf m k x) (instOf m k' x') := by
  exact ⟨hk, hx⟩

theorem keysDistinct_instancesOf {r e : Ty} (m : MachineV r e) (tbl : m.table.den0) :
    Step.KeysDistinct (instancesOf T m tbl) := by
  have h := (instancesOf_ok (T := T) m tbl).2
  unfold KeysUnique instEntries at h
  unfold Step.KeysDistinct
  rw [List.pairwise_map] at h
  exact h.imp fun hab => hab.1

/-- Related instance tables hold related instances. -/
theorem insts_of_table {r e : Ty} {m : MachineV r e} {R : PBij} {t t' : m.table.den0} (h : Ty.rel0 R m.table t t') :
    Step.Insts.Rel R (instancesOf T m t) (instancesOf T m t') := by
  have hm : Multi (Step.Instance.Rel R) (t.1.map fun (k, x) => instOf m k x) (t'.1.map fun (k, x) => instOf m k x) :=
    Multi.map (fun a b hab => instOf_rel hab.1 hab.2) h
  refine ⟨((hm.perm_left (List.mergeSort_perm _ _).symm).perm_right (List.mergeSort_perm _ _).symm),
    keysDistinct_instancesOf m t, keysDistinct_instancesOf m t'⟩

/-! What the comparisons of the requests and own effects two orders leave say of them, with every id renamed to
itself: a kept function written at one site relates to itself under related captured values, so requests and own
effects with one code relate. -/

/-- Two pending requests that are the same up to `R` on ids, but for their wire ids. -/
def PendingAlike {e : Ty} (R : PBij) (p q : Step.Pending e) : Prop :=
  Sender.Rel R p.sender q.sender ∧ p.external = q.external ∧ RequestV.Rel R p.request q.request

/-- A site's closure records with related captured values relate. -/
theorem _root_.Tazuna.Ir.Site.fn_rel {R : PBij} {Γ : List Ty} {t : Ty} (s : Site Γ t) {env env' : (Ty.tuple Γ).den0}
    (h : Ty.rel0 R (.tuple Γ) env env') : Fun.Rel R (s.fn env) (s.fn env') :=
  Ty.rel0_down s.ht (Expr.eval_rel s.defs (Defs.eval_rel s.defs) s.body ((Ty.relsV_up Γ s.hΓ env env').2 h))

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
theorem ensuresFn_rel {R : PBij} {t : Ty} : (ens : Option ((Γ : List Ty) × Site Γ t)) →
    {a b : (Ty.tuple ((ens.map (·.1)).getD [])).den0} → Ty.rel0 R (.tuple ((ens.map (·.1)).getD [])) a b →
    Option.Rel (Fun.Rel R) (ensuresFn ens a) (ensuresFn ens b)
  | none, _, _, _ => .none
  | some ⟨_, s⟩, _, _, h => .some (s.fn_rel h)

theorem senderShape_rel {R : PBij} : {ks : List Ty} → (sd : SenderShape ks) → {k k' : (Ty.tuple ks).den0} →
    Ty.rel0 R (.tuple ks) k k' → Sender.Rel R (sd.sender k) (sd.sender k')
  | _, .machine n _, (_, ()), (_, ()), h => .machine n (.mk h.1)
  | _, .reaction n, (), (), _ => .reaction n

/-- The pending requests a shape makes of related fields are alike. -/
theorem pendingShape_alike {R : PBij} {e : Ty} (sh : PendingShape e) (i j : Nat) {x y : Ty.dens sh.fields}
    (h : Ty.relV R (.tuple sh.fields) x y) : PendingAlike R (sh.pending i x) (sh.pending j y) := by
  obtain ⟨hk, hi, he, ha, -⟩ := Ty.rel0_down sh.hdata h
  exact ⟨senderShape_rel sh.sender hk, rfl, .mk _ _ _ _ hi (ensuresFn_rel sh.ensures he) (sh.onAnswer.fn_rel ha)⟩

/-- The pending requests related entries code are alike. -/
theorem pendingOf_alike {R : PBij} {e : Ty} : (shs : List (PendingShape e)) → (i j : Nat) →
    {y y' : Ty.alts (shs.map PendingShape.fields)} →
    Ty.relAltsWith Dsl.val (Dsl.relV R) R (shs.map PendingShape.fields) y y' →
    PendingAlike R (pendingOf shs i y) (pendingOf shs j y')
  | sh :: _, i, j, .inl _, .inl _, h => pendingShape_alike sh i j h
  | _ :: shs, i, j, .inr _, .inr _, h => pendingOf_alike shs i j h
  | _ :: _, _, _, .inl _, .inr _, h | _ :: _, _, _, .inr _, .inl _, h => h.elim

/-- The requests a step writes from the wire id `n0` have the ids from `n0` on, one each, in order. -/
theorem writes_ids_range {ds : List (String × DeclaredV)} {e : Ty} : {effs : List (Sender × EffectV e)} → {n0 : Nat} →
    {ps : List (Step.Pending e)} → Forall2 (Step.Writes ds) (effs.zipIdx n0) ps →
    ps.map (·.id) = List.range' n0 ps.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, ⟨⟨_, _, _, _, rfl⟩, h⟩ => by
    simp only [List.map_cons, List.length_cons, List.range'_succ]
    exact congrArg _ (writes_ids_range h)
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim

/-- Pairs whose first components are distinct give each first component one second component. -/
theorem fst_unique : {l : List (Nat × Nat)} → (l.map Prod.fst).Nodup → {a b b' : Nat} → (a, b) ∈ l → (a, b') ∈ l →
    b = b'
  | [], _, _, _, _, hb, _ => by simp at hb
  | p :: l, h, a, b, b', hb, hb' => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hb with e | hb1 <;> rcases List.mem_cons.1 hb' with e' | hb1'
    · exact (Prod.mk.inj (e.trans e'.symm)).2
    · exact absurd (List.mem_map_of_mem (f := Prod.fst) hb1') (by rw [← e] at h; exact h.1)
    · exact absurd (List.mem_map_of_mem (f := Prod.fst) hb1) (by rw [← e'] at h; exact h.1)
    · exact fst_unique h.2 hb1 hb1'

theorem forall2_zip_mem {α β : Type} {r : α → β → Prop} : {xs : List α} → {ys : List β} → Forall2 r xs ys →
    Forall2 (fun x y => r x y ∧ (x, y) ∈ xs.zip ys) xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ =>
    ⟨⟨h, List.mem_cons_self⟩, forall2_imp (fun _ _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩) (forall2_zip_mem hs)⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- Requests alike as multisets, each list with distinct wire ids from `n0` on, relate one to one under a renaming of
wire ids that keeps every id below `n0` and nothing else below it. -/
theorem wire_match {e : Ty} {n0 : Nat} {xs ys : List (Step.Pending e)} (h : Multi (PendingAlike PBij.refl) xs ys)
    (hx : (xs.map (·.id)).Nodup) (hy : (ys.map (·.id)).Nodup) (hxn : ∀ p ∈ xs, n0 ≤ p.id)
    (hyn : ∀ p ∈ ys, n0 ≤ p.id) :
    ∃ W : PBij, W.shift = none ∧ (∀ i < n0, W.rel i i) ∧ (∀ {i j}, W.rel i j → i < n0 → j = i) ∧
      Multi (Step.Pending.Rel ⟨PBij.refl, W⟩) xs ys := by
  obtain ⟨zs, hz, hzp⟩ := h
  have hl := forall2_length hz
  let ps : List (Nat × Nat) := (xs.zip zs).map fun pq => (pq.1.id, pq.2.id)
  have hfst : ps.map Prod.fst = xs.map (·.id) := by
    have := List.map_fst_zip (l₁ := xs) (l₂ := zs) (by omega)
    simp only [ps, List.map_map]
    conv => rhs; rw [← this, List.map_map]
    rfl
  have hsnd : (ps.map Prod.swap).map Prod.fst = zs.map (·.id) := by
    have := List.map_snd_zip (l₁ := xs) (l₂ := zs) (by omega)
    simp only [ps, List.map_map]
    conv => rhs; rw [← this, List.map_map]
    rfl
  have hzn : (zs.map (·.id)).Nodup := (hzp.map _).nodup_iff.2 hy
  have hpn : ∀ pr ∈ ps, n0 ≤ pr.1 ∧ n0 ≤ pr.2 := by
    intro pr hpr
    obtain ⟨⟨p, q⟩, hm, rfl⟩ := List.mem_map.1 hpr
    exact ⟨hxn p (List.of_mem_zip hm).1, hyn q (hzp.mem_iff.1 (List.of_mem_zip hm).2)⟩
  let W : PBij := {
    rel := fun i j => (i < n0 ∧ j = i) ∨ (i, j) ∈ ps
    func := by
      rintro i j j' (⟨hi, rfl⟩ | h1) (⟨hi', rfl⟩ | h2)
      · rfl
      · have := (hpn _ h2).1; simp only at this; omega
      · have := (hpn _ h1).1; simp only at this; omega
      · exact fst_unique (hfst ▸ hx) h1 h2
    inj := by
      rintro i i' j (⟨hi, e⟩ | h1) (⟨hi', e'⟩ | h2)
      · omega
      · have := (hpn _ h2).2; simp only at this; omega
      · have := (hpn _ h1).2; simp only at this; omega
      · exact fst_unique (hsnd ▸ hzn) (List.mem_map_of_mem (f := Prod.swap) h1)
          (List.mem_map_of_mem (f := Prod.swap) h2) }
  refine ⟨W, rfl, fun i hi => .inl ⟨hi, rfl⟩, fun {i j} hij hi => ?_, zs, ?_, hzp⟩
  · rcases hij with ⟨-, rfl⟩ | hij
    · rfl
    · have := (hpn _ hij).1; simp only at this; omega
  · exact forall2_imp (fun p q ⟨ha, hm⟩ => ⟨.inr (List.mem_map_of_mem (f := fun pq : Step.Pending e × Step.Pending e =>
      (pq.1.id, pq.2.id)) hm), ha⟩) (forall2_zip_mem hz)

/-- Kept functions written at one site of the unique sites `P`, whose captured values have one code, relate. -/
theorem fun_same {P : List AnySite} (hP : SitesUnique P) {t : Ty} {f g : Fun t} (hf : f.asSite ∈ P)
    (hg : g.asSite ∈ P) (hs : f.site = g.site) {z : Val} (hzf : CapRel L f z) (hzg : CapRel L g z) :
    Fun.Rel PBij.refl f g := by
  obtain ⟨e, hgf⟩ := Fun.eq_siteFn hP g f.toSite hg hf hs.symm
  obtain ⟨site, G, defs, Γ, env, hΓ, ht, body⟩ := f
  obtain ⟨site', G', defs', Γ', env', hΓ', ht', body'⟩ := g
  dsimp only at e hgf
  subst e
  rw [hgf]
  rw [hgf] at hzg
  exact Site.fn_rel ⟨site, G, defs, hΓ, ht, body⟩ (relD_same _ hzf hzg)

/-- Two own commands or queries of the unique sites `P` with one code relate with every id renamed to itself. -/
theorem eff_same {P : List AnySite} (hP : SitesUnique P) {e : Ty} {x y : EffectV e} {z : Val}
    (hx : RelV L (.dsl .effect [e]) x z) (hy : RelV L (.dsl .effect [e]) y z) (hrx : x.Reach P) (hry : y.Reach P)
    (hown : x.isRequest = false) : EffectV.Rel PBij.refl x y := by
  obtain ⟨d, n, hd, hx⟩ := (hx : EffRel L x z)
  obtain ⟨d', n', hd', hy⟩ := (hy : EffRel L y z)
  rw [hd] at hd'
  cases hd'
  rcases hx with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, rfl, hh⟩
  · cases x with
    | request => simp [EffectV.isRequest] at hown
    | command => exact hh.elim
    | query => exact hh.elim
  rcases hy with ⟨k', key', vals', hk', e', -⟩ | ⟨k', key', vals', hk', e', hh'⟩
  · have := (List.getElem?_eq_some_iff.1 hk').1
    simp only [Val.ctor.injEq] at e'
    omega
  simp only [Val.ctor.injEq, true_and] at e'
  obtain ⟨hkk, rfl⟩ := e'
  obtain rfl : k' = k := by omega
  rw [hk] at hk'
  cases hk'
  cases key with
  | command =>
    cases x with
    | command =>
      cases y with
      | command =>
        obtain ⟨rfl, rfl, rfl, rfl, hs, -, vi, va, rfl, hv, ha⟩ := hh
        obtain ⟨h1, h2, h3, h4, hs', -, vi', va', e, hv', ha'⟩ := hh'
        subst h1 h2 h3 h4
        simp only [List.cons.injEq, and_true] at e
        obtain ⟨rfl, rfl⟩ := e
        exact .command _ _ _ _ (relD_same _ hv hv') (fun_same hP hrx hry (hs.trans hs'.symm) ha ha')
      | _ => exact hh'.elim
    | _ => exact hh.elim
  | query =>
    cases x with
    | query =>
      cases y with
      | query =>
        obtain ⟨rfl, rfl, rfl, rfl, hs, -, vi, va, rfl, hv, ha⟩ := hh
        obtain ⟨h1, h2, h3, h4, hs', -, vi', va', e, hv', ha'⟩ := hh'
        subst h1 h2 h3 h4
        simp only [List.cons.injEq, and_true] at e
        obtain ⟨rfl, rfl⟩ := e
        exact .query _ _ _ _ (relD_same _ hv hv') (fun_same hP hrx hry (hs.trans hs'.symm) ha ha')
      | _ => exact hh'.elim
    | _ => exact hh.elim

/-- News slots `bagEqT` finds equal, read without their wire ids, hold requests written from the first wire ids `nA`
and `nC` that are alike as multisets. -/
theorem news_multi {e : Ty} {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {A C : List PendingSlot}
    {effsA effsC : List (Sender × EffectV e)} {nA nC : Nat} (hA : NewsRel M L shs ds A effsA nA)
    (hC : NewsRel M L shs ds C effsC nC)
    (h : Holds M (bagEqT .eq (shareSlots (seconds (A.map (·.slot)))) (shareSlots (seconds (C.map (·.slot)))))) :
    ∃ psA psC, Forall2 (Step.Writes ds) (effsA.zipIdx nA) psA ∧ Forall2 (Step.Writes ds) (effsC.zipIdx nC) psC ∧
      Multi (PendingAlike PBij.refl) psA psC := by
  obtain ⟨svA, zsA, hSA, -, hhA, xsA, hpA, hqA⟩ := hA
  obtain ⟨svC, zsC, hSC, -, hhC, xsC, hpC, hqC⟩ := hC
  have entries {zs : List ((Ty.dsl .fresh []).den × (pendingEntry shs).den)} {sv : List (Bool × List Val)}
      {sv' : List (Bool × List Val)} (hh : Holds2 (ETab L (.dsl .fresh []) (pendingEntry shs)) zs sv)
      (h2 : Forall2 (fun vs vs' => ∃ a b, vs = [a, b] ∧ vs' = [b]) (occupied sv) (occupied sv')) :
      ∃ es, Forall2 (fun z e => RelV L (pendingEntry shs) z.2 e) zs es ∧ Holds2 (fun z vs => vs = [z]) es sv' :=
    forall2_ones (forall2_imp (fun _ _ ⟨vs, ⟨ka, ea, e1, _, hea⟩, ⟨a, b, e2, e3⟩⟩ => by
      rw [e1, List.cons.injEq, List.cons.injEq] at e2
      obtain ⟨-, rfl, -⟩ := e2
      exact ⟨_, e3, hea⟩) (forall2_comp hh h2))
  obtain ⟨svA', hSA', h2A⟩ := seconds_den hSA
  obtain ⟨svC', hSC', h2C⟩ := seconds_den hSC
  obtain ⟨esA, hzA, heA⟩ := entries hhA h2A
  obtain ⟨esC, hzC, heC⟩ := entries hhC h2C
  have hz : Multi (fun zA zC => Ty.relV PBij.refl (pendingEntry shs) zA.2 zC.2) zsA zsC :=
    multi_of_codes (r := fun zA zC => Ty.relV PBij.refl (pendingEntry shs) zA.2 zC.2)
      (fun _ _ _ h1 h2 => relV_same _ (pendingEntry_data shs) h1 h2) hzA
      (bagEqT_perm (slotsDen_share hSA') (slotsDen_share hSC') heA heC h) hzC
  let pend (y : (Ty.dsl .fresh []).den × (pendingEntry shs).den) : Step.Pending e := pendingOf shs y.1 y.2
  obtain ⟨psA, hpsA, hwA⟩ := forall2_perm_left hpA (forall2_map_right pend (fun _ _ h => h.2) hqA)
  obtain ⟨psC, hpsC, hwC⟩ := forall2_perm_left hpC (forall2_map_right pend (fun _ _ h => h.2) hqC)
  exact ⟨psA, psC, hwA, hwC, ((hz.map (f := pend) (g := pend) fun _ _ h => pendingOf_alike shs _ _ h).perm_left
    hpsA).perm_right hpsC⟩

/-- Own slots `bagEqT` finds equal, read without their places in the queue, hold own commands and queries of the
unique sites `P` that relate as multisets with every id renamed to itself. -/
theorem ownsE_multi {P : List AnySite} (hP : SitesUnique P) {e : Ty} {A C : List OwnSlot} {osA osC : List (EffectV e)}
    {qA qC : Nat} (hA : OwnRelE M L A osA qA) (hC : OwnRelE M L C osC qC)
    (h : Holds M (bagEqT .eq (shareSlots (seconds (A.map (·.slot)))) (shareSlots (seconds (C.map (·.slot))))))
    (hrA : ∀ x ∈ osA, x.isRequest = false ∧ x.Reach P) (hrC : ∀ x ∈ osC, x.Reach P) :
    Multi (EffectV.Rel PBij.refl) osA osC := by
  obtain ⟨svA, zsA, hSA, -, hhA, hpA⟩ := hA
  obtain ⟨svC, zsC, hSC, -, hhC, hpC⟩ := hC
  have codes {zs : List (EffectV e × Nat)} {sv : List (Bool × List Val)} {sv' : List (Bool × List Val)}
      (hh : Holds2 (EOwn L e) zs sv)
      (h2 : Forall2 (fun vs vs' => ∃ a b, vs = [a, b] ∧ vs' = [b]) (occupied sv) (occupied sv')) :
      ∃ cs, Forall2 (fun z c => RelV L (.dsl .effect [e]) z.1 c) zs cs ∧ Holds2 (fun z vs => vs = [z]) cs sv' :=
    forall2_ones (forall2_imp (fun _ _ ⟨vs, ⟨zx, e1, hzx⟩, ⟨a, b, e2, e3⟩⟩ => by
      rw [e1, List.cons.injEq, List.cons.injEq] at e2
      obtain ⟨-, rfl, -⟩ := e2
      exact ⟨_, e3, hzx⟩) (forall2_comp hh h2))
  obtain ⟨svA', hSA', h2A⟩ := seconds_den hSA
  obtain ⟨svC', hSC', h2C⟩ := seconds_den hSC
  obtain ⟨csA, hzA, hcA⟩ := codes hhA h2A
  obtain ⟨csC, hzC, hcC⟩ := codes hhC h2C
  have hz : Multi (fun zA zC => ∃ z, RelV L (.dsl .effect [e]) zA.1 z ∧ RelV L (.dsl .effect [e]) zC.1 z) zsA zsC :=
    multi_of_codes (fun _ _ z h1 h2 => ⟨z, h1, h2⟩) hzA
      (bagEqT_perm (slotsDen_share hSA') (slotsDen_share hSC') hcA hcC h) hzC
  have hmem {os : List (EffectV e)} {q : Nat} {zs : List (EffectV e × Nat)} (hp : zs.Perm (os.zipIdx q)) :
      ∀ z ∈ zs, z.1 ∈ os := fun z hz => by
    have := List.mem_map_of_mem (f := Prod.fst) (hp.mem_iff.1 hz)
    rwa [List.zipIdx_map_fst] at this
  have hm := hz.imp_mem (r' := fun zA zC => EffectV.Rel PBij.refl zA.1 zC.1)
    fun zA hzA zC hzC ⟨_, h1, h2⟩ =>
      eff_same hP h1 h2 (hrA _ (hmem hpA zA hzA)).2 (hrC _ (hmem hpC zC hzC)) (hrA _ (hmem hpA zA hzA)).1
  have hfst {os : List (EffectV e)} {q : Nat} {zs : List (EffectV e × Nat)} (hp : zs.Perm (os.zipIdx q)) :
      (zs.map Prod.fst).Perm os := by
    have := hp.map Prod.fst
    rwa [List.zipIdx_map_fst] at this
  exact ((hm.map (f := Prod.fst) (g := Prod.fst) fun _ _ h => h).perm_left (hfst hpA)).perm_right (hfst hpC)

theorem owns_multi {P : List AnySite} (hP : SitesUnique P) {e : Ty} {A C : List OwnSlot} {osA osC : List (OwnEffectV e)}
    {qA qC : Nat} (hA : OwnRel M L A osA qA) (hC : OwnRel M L C osC qC)
    (h : Holds M (bagEqT .eq (shareSlots (seconds (A.map (·.slot)))) (shareSlots (seconds (C.map (·.slot))))))
    (hrA : ∀ x ∈ osA, x.effect.Reach P) (hrC : ∀ x ∈ osC, x.effect.Reach P) :
    Multi (OwnEffectV.Rel PBij.refl) osA osC :=
  Multi.of_map (r' := EffectV.Rel PBij.refl) (f := OwnEffectV.effect) (g := OwnEffectV.effect)
    (fun _ _ h => OwnEffectV.rel_iff.2 h) (ownsE_multi hP hA hC h
    (fun x hx => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
      exact ⟨by cases o <;> rfl, hrA o ho⟩)
    (fun x hx => by obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx; exact hrC o ho))

end

end Tazuna.Smt
