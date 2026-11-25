import Tazuna.Smt.SameCode
import Tazuna.Smt.Fire
import Tazuna.Smt.Decide
import Tazuna.Smt.Verdict

/-! What the pair questions compare, and what a comparison that holds says of the two results. Records and instance
tables are compared by Gleam's `==` (`eqFn`), which reads bags and tables as multisets, so two results that hold the
same rows in other slots compare equal; the events each effect applies are compared slot by slot, since the events
loop keeps them in order. Each comparison that holds gives the relation the results are compared by with every id
renamed to itself (`PBij.refl`), so the solver searches for no renaming. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The slots of two event lists hold the same events in the same places. -/
def slotsEqT : List (Slot 1) → List (Slot 1) → Term
  | [], [] => tt
  | (f, xs) :: S, (g, ys) :: S' => .and (.and (.eq f g) (.or (.not f) (.eq xs[0] ys[0]))) (slotsEqT S S')
  | _, _ => .bool false

/-- No flag holds. -/
def noneT (fs : List Term) : Term := allT (fs.map .not)

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

theorem holds_eq {a b : Term} (h : Holds M (.eq a b)) : a.denote M = b.denote M :=
  Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at h; exact h)

/-- Slots compared equal hold the same items where occupied. -/
theorem occupied_of_slotsEq : {S S' : List (Slot 1)} → {sv sv' : List (Bool × List Val)} → SlotsDen M S sv →
    SlotsDen M S' sv' → Holds M (slotsEqT S S') → occupied sv = occupied sv'
  | [], [], [], [], _, _, _ => rfl
  | (f, xs) :: S, (g, ys) :: S', (b, vs) :: sv, (b', vs') :: sv', ⟨hf, hx, h⟩, ⟨hg, hy, h'⟩, he => by
    simp only [slotsEqT, holds_and, holds_or, holds_not] at he
    obtain ⟨⟨hfg, hxy⟩, he⟩ := he
    have hb : b = b' := by have := holds_eq hfg; rw [hf, hg] at this; cases this; rfl
    subst hb
    have ih := occupied_of_slotsEq h h' he
    cases b with
    | false => simpa [occupied] using ih
    | true =>
      have hfT : Holds M f := by simp [Holds, hf, Val.toBool]
      have he0 := holds_eq (hxy.resolve_left (fun h => h hfT))
      obtain ⟨x, rfl⟩ := xs.one
      obtain ⟨y, rfl⟩ := ys.one
      simp only [Term.denotes] at hx hy
      subst hx hy
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero] at he0
      simp only [occupied, List.filterMap_cons, ite_true] at ih ⊢
      rw [he0]; exact congrArg _ ih
  | [], _ :: _, _, _, _, _, he | _ :: _, [], _, _, _, _, he => by simp [slotsEqT, Holds, Term.denote, Val.toBool] at he
  | [], [], _ :: _, _, h, _, _ | _ :: _, _ :: _, [], _, h, _, _ => nomatch h
  | [], [], [], _ :: _, _, h', _ | _ :: _, _ :: _, _ :: _, [], _, h', _ => nomatch h'

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

theorem occupied_nil_of_none {w : Nat} : {S : List (Slot w)} → {sv : List (Bool × List Val)} → SlotsDen M S sv →
    Holds M (noneT (S.map (·.1))) → occupied sv = []
  | [], [], _, _ => rfl
  | (f, _) :: S, (b, _) :: sv, ⟨hf, _, h⟩, hn => by
    simp only [noneT, List.map_cons, holds_allT, List.mem_cons, forall_eq_or_imp] at hn
    have hb : b = false := by
      have := hn.1
      simp only [Holds, Term.denote, hf, Val.toBool] at this
      simpa using this
    subst hb
    simpa [occupied] using occupied_nil_of_none h (by
      simp only [noneT, holds_allT]
      exact hn.2)
  | [], _ :: _, h, _ | _ :: _, [], h, _ => nomatch h

/-- News slots none of whose flags holds name no request. -/
theorem news_nil {e : Ty} {shs : List (PendingShape e)} {ds : List (String × DeclaredV)} {news : List PendingSlot}
    {effs : List (Sender × EffectV e)} {n0 : Nat} (h : NewsRel M L shs ds news effs n0)
    (hn : Holds M (noneT (news.map (·.flag)))) : effs = [] := by
  obtain ⟨sv, zs, hS, -, hh, xs, hp, hq⟩ := h
  have ho := occupied_nil_of_none hS (by rw [List.map_map]; exact hn)
  unfold Holds2 at hh
  rw [ho] at hh
  cases zs with
  | cons _ _ => exact hh.elim
  | nil =>
    cases xs with
    | cons _ _ => exact hq.elim
    | nil => simpa using hp.symm.eq_nil

/-- Own slots none of whose flags holds queue nothing. -/
theorem owns_nil {e : Ty} {S : List OwnSlot} {os : List (EffectV e)} {q0 : Nat} (h : OwnRel M L S os q0)
    (hn : Holds M (noneT (S.map (·.flag)))) : os = [] := by
  obtain ⟨sv, zs, hS, -, hh, hp⟩ := h
  have ho := occupied_nil_of_none hS (by rw [List.map_map]; exact hn)
  unfold Holds2 at hh
  rw [ho] at hh
  cases zs with
  | cons _ _ => exact hh.elim
  | nil => simpa using hp.symm.eq_nil

/-- Two stored values whose terms Gleam's `==` finds equal are the same value, read as `==` reads it. -/
theorem rel0_of_eqFn {t : Ty} (hd : t.isData = true) (hc : t.comparable = true) {x y : t.den0} {a b : Term}
    (hx : RelV L t (Ty.up t hd x) (a.denote M)) (hy : RelV L t (Ty.up t hd y) (b.denote M))
    {f : Term → Term → Term} (hf : eqFn L t = .ok f) (he : Holds M (f a b)) : Ty.rel0 PBij.refl t x y := by
  have h := eqFn_ok t hf _ _ a b hx hy
  simp only [Holds, h, Val.toBool] at he
  rw [show Ty.deq t (Ty.up t hd x) (Ty.up t hd y) = Ty.deq0 t x y from Ty.deq_up t hd x y] at he
  exact Ty.rel0_deq_right hc (rel0_same hd hx hx) he

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

end

end Tazuna.Smt
