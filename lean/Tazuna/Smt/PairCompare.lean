import Tazuna.Smt.CodeInjective
import Tazuna.Smt.Fire
import Tazuna.Smt.Decide
import Tazuna.Smt.Verdict
import Tazuna.Semantics.StepRename

/-! What the pair questions compare, and what a comparison that holds says of the two results. Records and instance
tables are compared by Gleam's `==` (`eqFn`), which reads bags and tables as multisets, so two results that hold the
same rows in other slots compare equal; the events each effect applies, the requests it sends and the own effects it
queues are compared slot by slot by their codes (`slotsCmpT`), requests at the same distance from the wire id their
step starts at. Each comparison that holds gives the relation the results are compared by with every id renamed to
itself (`PBij.refl`), so the solver searches for no renaming; a request or own effect keeps kept functions, which one
code fixes only with the unique sites `P` they are records of (`eff_same`, `pendingOf_alike`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Two slot lists compared place by place: the same flags, and where flagged, `cmp` of the two slots' items. -/
def slotsCmpT {w : Nat} (cmp : SlotItems w → SlotItems w → Term) : List (Slot w) → List (Slot w) → Term
  | [], [] => tt
  | (f, xs) :: S, (g, ys) :: S' => .and (.and (.eq f g) (.or (.not f) (cmp xs ys))) (slotsCmpT cmp S S')
  | _, _ => .bool false

/-- The slots of two event lists hold the same events in the same places. -/
def slotsEqT : List (Slot 1) → List (Slot 1) → Term := slotsCmpT fun xs ys => .eq xs[0] ys[0]

/-- Two steps' news slots hold the same requests in the same places, each as far from its step's first wire id (`nA`,
`nC`) as the other: a step sends the same requests at the same ids relative to where it starts, whichever step runs
first. -/
def newsEqT (nA nC : Term) (A C : List PendingSlot) : Term :=
  slotsCmpT (fun xs ys => .and (.eq (.add xs[0] nC) (.add ys[0] nA)) (.eq xs[1] ys[1])) (A.map (·.slot)) (C.map (·.slot))

/-- Two steps' own slots hold the same own commands and queries in the same places. Their queue places are not
compared: the queue is a multiset to the comparison, and the other step's effects come first in one order. -/
def ownsEqT (A C : List OwnSlot) : Term := slotsCmpT (fun xs ys => .eq xs[1] ys[1]) (A.map (·.slot)) (C.map (·.slot))

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

theorem holds_eq {a b : Term} (h : Holds M (.eq a b)) : a.denote M = b.denote M :=
  Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at h; exact h)

/-- Slots compared place by place hold, where occupied, items `cmp` relates. -/
theorem occupied_cmp {w : Nat} {cmp : SlotItems w → SlotItems w → Term} {Rv : List Val → List Val → Prop}
    (hcmp : ∀ xs ys : SlotItems w, Holds M (cmp xs ys) → Rv (Term.denotes M xs.1) (Term.denotes M ys.1)) :
    {S S' : List (Slot w)} → {sv sv' : List (Bool × List Val)} → SlotsDen M S sv → SlotsDen M S' sv' →
    Holds M (slotsCmpT cmp S S') → Forall2 Rv (occupied sv) (occupied sv')
  | [], [], [], [], _, _, _ => trivial
  | (f, xs) :: S, (g, ys) :: S', (b, vs) :: sv, (b', vs') :: sv', ⟨hf, hx, h⟩, ⟨hg, hy, h'⟩, he => by
    simp only [slotsCmpT, holds_and, holds_or, holds_not] at he
    obtain ⟨⟨hfg, hxy⟩, he⟩ := he
    have hb : b = b' := by have := holds_eq hfg; rw [hf, hg] at this; cases this; rfl
    subst hb
    have ih := occupied_cmp hcmp h h' he
    cases b with
    | false => simpa [occupied] using ih
    | true =>
      have hfT : Holds M f := by simp [Holds, hf, Val.toBool]
      have hr := hcmp xs ys (hxy.resolve_left (fun h => h hfT))
      rw [hx, hy] at hr
      simp only [occupied, List.filterMap_cons, ite_true] at ih ⊢
      exact ⟨hr, ih⟩
  | [], _ :: _, _, _, _, _, he | _ :: _, [], _, _, _, _, he => by simp [slotsCmpT, Holds, Term.denote, Val.toBool] at he
  | [], [], _ :: _, _, h, _, _ | _ :: _, _ :: _, [], _, h, _, _ => nomatch h
  | [], [], [], _ :: _, _, h', _ | _ :: _, _ :: _, _ :: _, [], _, h', _ => nomatch h'

/-- Slots compared equal hold the same items where occupied. -/
theorem occupied_of_slotsEq {S S' : List (Slot 1)} {sv sv' : List (Bool × List Val)} (h : SlotsDen M S sv)
    (h' : SlotsDen M S' sv') (he : Holds M (slotsEqT S S')) : occupied sv = occupied sv' :=
  forall2_eq (occupied_cmp (fun xs ys hxy => by
    obtain ⟨x, rfl⟩ := xs.one
    obtain ⟨y, rfl⟩ := ys.one
    simp only [SlotItems.getElem_mk, List.getElem_cons_zero] at hxy
    simp [Term.denotes, holds_eq hxy]) h h' he)

/-- Event slots compared equal hold events that are the same value one by one. -/
theorem events_of_slotsEq {v : ServiceV} {S S' : List (Slot 1)} {evs evs' : List v.event.den0}
    (h : EventsRel M L S evs) (h' : EventsRel M L S' evs') (he : Holds M (slotsEqT S S')) :
    Forall2 (Ty.rel0 PBij.refl v.event) evs evs' := by
  obtain ⟨sv, hS, hh⟩ := h
  obtain ⟨sv', hS', hh'⟩ := h'
  have hocc := occupied_of_slotsEq hS hS' he
  unfold Holds2 at hh hh'
  rw [← hocc] at hh'
  have hf := holds2_same (r := fun a b => Ty.rel0 PBij.refl v.event (Ty.down _ v.event_data a) (Ty.down _ v.event_data b))
    (fun x y vs ⟨z, e1, h1⟩ ⟨z', e2, h2⟩ => by
      rw [e1] at e2; cases e2
      have := rel0_same v.event_data (x := Ty.down _ v.event_data x) (y := Ty.down _ v.event_data y)
        (by rwa [Ty.up_down]) (by rwa [Ty.up_down])
      exact this) hh hh'
  exact forall2_imp (fun a b h => by simpa [Ty.down_up] using h) (forall2_map_iff.1 hf)

/-- Two stored values whose terms Gleam's `==` finds equal are the same value, read as `==` reads it. -/
theorem rel0_of_eqFn {t : Ty} (hd : t.isData = true) (hc : t.comparable = true) {x y : t.den0} {a b : Term}
    (hx : RelV L t (Ty.up t hd x) (a.denote M)) (hy : RelV L t (Ty.up t hd y) (b.denote M))
    {f : Term → Term → Term} (hf : eqFn L t = .ok f) (he : Holds M (f a b)) : Ty.rel0 PBij.refl t x y := by
  have h := eqFn_ok t hf _ _ a b hx hy
  simp only [Holds, h, Val.toBool] at he
  rw [show Ty.deq t (Ty.up t hd x) (Ty.up t hd y) = Ty.deq0 t x y from Ty.deq_up t hd x y] at he
  exact Ty.rel0_deq_right hc (Ty.rel0_refl t hc x) he

/-- An instance from related table entries. -/
theorem instOf_rel {r e : Ty} {m : MachineV r e} {R : PBij} {k k' : m.key.den0} {x x' : (instEntry m.state).den0}
    (hk : Ty.rel0 R m.key k k') (hx : Ty.rel0 R (instEntry m.state) x x') :
    Step.Instance.Rel R (instOf m k x) (instOf m k' x') := by
  obtain ⟨s, t, u⟩ := x
  obtain ⟨s', t', u'⟩ := x'
  obtain ⟨hs, ht, -⟩ := hx
  refine ⟨hk, hs, ?_⟩
  match t, t', ht with
  | .inl ((_, _, ()), ()), .inl ((_, _, ()), ()), h => exact .some ⟨h.1.1, h.1.2.1⟩
  | .inr (.inl ()), .inr (.inl ()), _ => exact .none
  | .inl _, .inr _, h | .inr _, .inl _, h => exact h.elim

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

/-- The requests a step writes from the wire id `n0` have the ids from `n0` on. -/
theorem writes_ids {ds : List (String × DeclaredV)} {e : Ty} : {effs : List (Sender × EffectV e)} → {n0 : Nat} →
    {ps : List (Step.Pending e)} → Forall2 (Step.Writes ds) (effs.zipIdx n0) ps →
    ∀ p ∈ ps, n0 ≤ p.id ∧ p.id < n0 + ps.length
  | [], _, [], _ => by simp
  | _ :: _, _, _ :: _, ⟨⟨_, _, _, _, rfl⟩, h⟩ => by
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · simp
    · have := writes_ids h q hq; simp only [List.length_cons]; omega
  | [], _, _ :: _, h | _ :: _, _, [], h => h.elim

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

/-- Two steps' news slots compared equal hold requests written from their first wire ids `nA` and `nC` that are alike,
each as far from its step's first id as the other. -/
theorem news_same {e : Ty} {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {A C : List PendingSlot}
    {effsA effsC : List (Sender × EffectV e)} {nA nC : Nat} (hA : NewsRel M L shs ds A effsA nA)
    (hC : NewsRel M L shs ds C effsC nC) {tA tC : Term} (htA : tA.denote M = .int nA) (htC : tC.denote M = .int nC)
    (h : Holds M (newsEqT tA tC A C)) :
    ∃ psA psC, Forall2 (Step.Writes ds) (effsA.zipIdx nA) psA ∧ Forall2 (Step.Writes ds) (effsC.zipIdx nC) psC ∧
      Multi (fun p q => p.id + nC = q.id + nA ∧ PendingAlike PBij.refl p q) psA psC := by
  obtain ⟨svA, zsA, hSA, -, hhA, xsA, hpA, hqA⟩ := hA
  obtain ⟨svC, zsC, hSC, -, hhC, xsC, hpC, hqC⟩ := hC
  have hocc := occupied_cmp (Rv := fun vs vs' => ∃ a b c d, vs = [a, b] ∧ vs' = [c, d] ∧
      a.toInt + nC = c.toInt + nA ∧ b = d) (fun xs ys hxy => by
    obtain ⟨a, b, rfl⟩ := xs.two
    obtain ⟨c, d, rfl⟩ := ys.two
    simp only [SlotItems.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ, holds_and] at hxy
    have h1 := holds_eq hxy.1
    simp only [Term.denote, htA, htC, Val.toInt, Val.int.injEq] at h1
    exact ⟨_, _, _, _, rfl, rfl, h1, holds_eq hxy.2⟩) hSA hSC h
  have hz : Forall2 (fun zA zC => zA.1 + nC = zC.1 + nA ∧ Ty.relV PBij.refl (pendingEntry shs) zA.2 zC.2) zsA zsC :=
    forall2_imp (fun zA zC ⟨vs', ⟨vs, ⟨ka, ea, e1, hka, hea⟩, ⟨a, b, c, d, e2, e3, hn, hbd⟩⟩, ⟨kc, ec, e4, hkc, hec⟩⟩ => by
      subst hbd
      rw [e1, List.cons.injEq, List.cons.injEq] at e2
      rw [e4, List.cons.injEq, List.cons.injEq] at e3
      obtain ⟨rfl, rfl, -⟩ := e2
      obtain ⟨rfl, rfl, -⟩ := e3
      change ka = .int (Int.ofNat zA.1) at hka
      change kc = .int (Int.ofNat zC.1) at hkc
      subst hka hkc
      simp only [Val.toInt] at hn
      exact ⟨Int.ofNat.inj (by simp only [Int.ofNat_eq_natCast] at hn ⊢; exact hn), relV_same _ (pendingEntry_data shs) hea hec⟩)
      (forall2_comp (forall2_comp hhA hocc) (forall2_flip hhC))
  let pend (y : (Ty.dsl .fresh []).den × (pendingEntry shs).den) : Step.Pending e := pendingOf shs y.1 y.2
  obtain ⟨psA, hpsA, hwA⟩ := forall2_perm_left hpA (forall2_map_right pend (fun _ _ h => h.2) hqA)
  obtain ⟨psC, hpsC, hwC⟩ := forall2_perm_left hpC (forall2_map_right pend (fun _ _ h => h.2) hqC)
  refine ⟨psA, psC, hwA, hwC, ((Multi.of_forall2 (forall2_map2 (fun zA zC h => ?_) hz)).perm_left hpsA).perm_right hpsC⟩
  refine ⟨?_, pendingOf_alike shs _ _ h.2⟩
  erw [pendingOf_id, pendingOf_id]
  exact h.1

/-- Two steps' own slots compared equal hold own commands and queries of the unique sites `P` that relate as
multisets with every id renamed to itself. -/
theorem ownsE_same {P : List AnySite} (hP : SitesUnique P) {e : Ty} {A C : List OwnSlot} {osA osC : List (EffectV e)}
    {qA qC : Nat} (hA : OwnRelE M L A osA qA) (hC : OwnRelE M L C osC qC) (h : Holds M (ownsEqT A C))
    (hrA : ∀ x ∈ osA, x.isRequest = false ∧ x.Reach P) (hrC : ∀ x ∈ osC, x.Reach P) :
    Multi (EffectV.Rel PBij.refl) osA osC := by
  obtain ⟨svA, zsA, hSA, -, hhA, hpA⟩ := hA
  obtain ⟨svC, zsC, hSC, -, hhC, hpC⟩ := hC
  have hocc := occupied_cmp (Rv := fun vs vs' => ∃ a b c d, vs = [a, b] ∧ vs' = [c, d] ∧ b = d) (fun xs ys hxy => by
    obtain ⟨a, b, rfl⟩ := xs.two
    obtain ⟨c, d, rfl⟩ := ys.two
    simp only [SlotItems.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ] at hxy
    exact ⟨_, _, _, _, rfl, rfl, holds_eq hxy⟩) hSA hSC h
  have hz : Forall2 (fun zA zC => ∃ z, RelV L (.dsl .effect [e]) zA.1 z ∧ RelV L (.dsl .effect [e]) zC.1 z) zsA zsC :=
    forall2_imp (fun zA zC ⟨vs', ⟨vs, ⟨za, e1, hza⟩, ⟨a, b, c, d, e2, e3, hbd⟩⟩, ⟨zc, e4, hzc⟩⟩ => by
      subst hbd
      rw [e1, List.cons.injEq, List.cons.injEq] at e2
      rw [e4, List.cons.injEq, List.cons.injEq] at e3
      obtain ⟨-, rfl, -⟩ := e2
      obtain ⟨-, rfl, -⟩ := e3
      exact ⟨_, hza, hzc⟩)
      (forall2_comp (forall2_comp hhA hocc) (forall2_flip hhC))
  have hmem {os : List (EffectV e)} {q : Nat} {zs : List (EffectV e × Nat)} (hp : zs.Perm (os.zipIdx q)) :
      ∀ z ∈ zs, z.1 ∈ os := fun z hz => by
    have := List.mem_map_of_mem (f := Prod.fst) (hp.mem_iff.1 hz)
    rwa [List.zipIdx_map_fst] at this
  have hm := (Multi.of_forall2 hz).imp_mem (r' := fun zA zC => EffectV.Rel PBij.refl zA.1 zC.1)
    fun zA hzA zC hzC ⟨_, h1, h2⟩ =>
      eff_same hP h1 h2 (hrA _ (hmem hpA zA hzA)).2 (hrC _ (hmem hpC zC hzC)) (hrA _ (hmem hpA zA hzA)).1
  have hfst {os : List (EffectV e)} {q : Nat} {zs : List (EffectV e × Nat)} (hp : zs.Perm (os.zipIdx q)) :
      (zs.map Prod.fst).Perm os := by
    have := hp.map Prod.fst
    rwa [List.zipIdx_map_fst] at this
  exact ((hm.map (f := Prod.fst) (g := Prod.fst) fun _ _ h => h).perm_left (hfst hpA)).perm_right (hfst hpC)

theorem owns_same {P : List AnySite} (hP : SitesUnique P) {e : Ty} {A C : List OwnSlot} {osA osC : List (OwnEffectV e)}
    {qA qC : Nat} (hA : OwnRel M L A osA qA) (hC : OwnRel M L C osC qC) (h : Holds M (ownsEqT A C))
    (hrA : ∀ x ∈ osA, x.effect.Reach P) (hrC : ∀ x ∈ osC, x.effect.Reach P) :
    Multi (OwnEffectV.Rel PBij.refl) osA osC :=
  Multi.of_map (r' := EffectV.Rel PBij.refl) (f := OwnEffectV.effect) (g := OwnEffectV.effect)
    (fun _ _ h => OwnEffectV.rel_iff.2 h) (ownsE_same hP hA hC h
    (fun x hx => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
      exact ⟨by cases o <;> rfl, hrA o ho⟩)
    (fun x hx => by obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx; exact hrC o ho))

end

end Tazuna.Smt
