import Tazuna.Smt.State
import Tazuna.Smt.CodeInjective
import Tazuna.Semantics.Valid

/-! Which names a stored value holds, as a term: every fresh id it holds was made before the counter `n`, and so was
every counter it holds (`namesT`). A state on valid inputs holds no other names (`Step.StateSupp`), which the
semantics says as "the value relates to itself under the renaming that keeps exactly the counters below `n`", so the
term is exact against that relation (`names_iff`). The pair questions of T5 assume it of their symbolic state, as the
step questions assume the wire-id invariant. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) (n : Term)

mutual
/-- Every fresh id and counter the value `x` of type `t` holds is below `n`; none for a type without a code. -/
def namesT : Ty → Term → Option Term
  | .int, _ | .str, _ | .date, _ | .adt 0 _ _, _ => some tt
  | .dsl .fresh _, x => some (.lt x n)
  | .id, x => (L.find? .id).map fun (d, _) => .or (.not (.is d 0 x)) (.lt (.sel d 0 0 x) n)
  | .adt (i + 1) a vs, x => (L.find? (.adt (i + 1) a vs)).bind fun (d, _) => namesAlts d 0 vs x
  | .tuple ts, x => (L.find? (.tuple ts)).bind fun (d, _) => namesFields d 0 ts x 0
  | .bag t, x => match L.find? (.bag t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, m), some (dt, _) =>
      ((slotsOf d dt m 1 x).mapM fun sl : Slot 1 => (namesT t sl.2[0]).map (Term.or (.not sl.1) ·)).map allT
    | _, _ => none
  | .list t, x => match L.find? (.list t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, m), some (dt, _) =>
      ((slotsOf d dt m 1 x).mapM fun sl : Slot 1 => (namesT t sl.2[0]).map (Term.or (.not sl.1) ·)).map allT
    | _, _ => none
  | .table k w, x => match L.find? (.table k w), L.find? (.tuple [Ty.bool, k, w]) with
    | some (d, m), some (dt, _) =>
      ((slotsOf d dt m 2 x).mapM fun sl : Slot 2 => ((namesT k sl.2[0]).bind fun ck =>
        (namesT w sl.2[1]).map fun cw => Term.and ck cw).map (Term.or (.not sl.1) ·)).map allT
    | _, _ => none
  | _, _ => none
/-- The fields' names, from field `j` of constructor `k` of datatype `d`. -/
def namesFields (d k : Nat) : List Ty → Term → Nat → Option Term
  | [], _, _ => some tt
  | t :: ts, x, j => (namesT t (.sel d k j x)).bind fun c => (namesFields d k ts x (j + 1)).map (.and c)
/-- The names of whichever constructor, from `k`, built `x`. -/
def namesAlts (d : Nat) : Nat → List (List Ty) → Term → Option Term
  | _, [], _ => some tt
  | k, fs :: vs, x => (namesFields d k fs x 0).bind fun c => (namesAlts d (k + 1) vs x).map (.ite (.is d k x) c)
end

end

section
variable {M : Model} {L : Layout} {N : Nat}

/-- A relation whose related values relate to themselves holds of a list against itself as a multiset exactly when it
holds of each item against itself. -/
theorem multi_self_iff {α : Type} {r : α → α → Prop} (hs : ∀ a b, r a b → r a a) {xs : List α} :
    Multi r xs xs ↔ ∀ y ∈ xs, r y y :=
  ⟨fun ⟨_, h, _⟩ y hy => let ⟨_, _, hz⟩ := forall2_mem_left h y hy; hs _ _ hz,
    fun h => Multi.of_forall2 (forall2_refl_of h)⟩

/-- Values related under the renaming that keeps the counters below `N` each relate to themselves. -/
theorem relV_self_below {t : Ty} (hc : t.comparable = true) {x y : t.den} (h : Ty.relV (PBij.below N) t x y) :
    Ty.relV (PBij.below N) t x x := by
  have hd := Ty.isData_of_comparable t hc
  have h0 := Ty.self_of_below (PBij.below_fixes N) t hc (Ty.rel0_down hd h)
  have h1 := Ty.relV_up_of hd h0
  rwa [Ty.up_down] at h1

/-- The slot-wise part of the names: where the slots hold the items `ys`, a term per slot that holds when the slot is
free or the item `R` holds of has its names below. -/
theorem slots_names {α : Type} {w : Nat} {g : SlotItems w → Option Term} {E : α → List Val → Prop}
    {R : α → Prop}
    (hg : ∀ (xs : SlotItems w) c y, g xs = some c → E y (Term.denotes M xs.1) → (Holds M c ↔ R y)) :
    (S : List (Slot w)) → (sv : List (Bool × List Val)) → SlotsDen M S sv → (ys : List α) → Holds2 E ys sv →
    (cs : List Term) → S.mapM (fun sl : Slot w => (g sl.2).map (Term.or (.not sl.1) ·)) = some cs →
    (Holds M (allT cs) ↔ ∀ y ∈ ys, R y)
  | [], [], _, ys, hy, cs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    cases ys with
    | nil => simp [Holds, allT, tt, Term.denote, Val.toBool]
    | cons => exact hy.elim
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩, ys, hy, cs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c0, h0, cs', hcs, rfl⟩ := h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h0
    simp only [allT]
    rw [holds_and, holds_or_not f c b hf]
    cases b with
    | false =>
      rw [slots_names hg S sv hS ys (by simpa [Holds2, occupied] using hy) cs' hcs]
      simp
    | true =>
      match ys, hy with
      | y :: ys, ⟨hy1, hy2⟩ =>
        rw [slots_names hg S sv hS ys hy2 cs' hcs, hg xs c y hc (hxs ▸ hy1)]
        simp
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => h.elim

variable {n : Term}

theorem holds_lt (hn : n.denote M = .int (N : Int)) {x : Term} {a : Nat} (hx : x.denote M = .int (a : Int)) :
    Holds M (.lt x n) ↔ a < N := by
  simp [Holds, Term.denote, hx, hn, Val.toBool, Val.toInt]

mutual
/-- The names term holds exactly when the value relates to itself under the renaming that keeps exactly the counters
below `N`, that is, when every fresh id and counter it holds is below `N`. -/
theorem names_iff (hn : n.denote M = .int (N : Int)) : (t : Ty) → t.comparable = true → (x c : Term) →
    namesT L n t x = some c → {v : t.den} → RelV L t v (x.denote M) → (Holds M c ↔ Ty.relV (PBij.below N) t v v)
  | .int, _, _, c, h, _, _ | .str, _, _, c, h, _, _ | .date, _, _, c, h, _, _ => by
    simp only [namesT, Option.some.injEq] at h
    subst h
    exact iff_of_true holds_tt rfl
  | .adt 0 _ vs, _, _, c, h, v, ⟨hvs, _⟩ => by
    simp only [namesT, Option.some.injEq] at h
    subst h hvs
    refine iff_of_true holds_tt ?_
    rcases v with _ | _ | e
    · trivial
    · trivial
    · exact nomatch e
  | .dsl k _, hc, x, c, h, v, hx => by
    cases k <;> simp [Ty.comparable] at hc
    simp only [namesT, Option.some.injEq] at h
    subst h
    change _ = Val.int (Int.ofNat v) at hx
    rw [holds_lt hn (a := v) hx]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | .id, _, x, c, h, v, ⟨d, _, hf, hx⟩ => by
    simp only [namesT, hf, Option.map_some, Option.some.injEq] at h
    subst h
    cases v with
    | named s =>
      refine iff_of_true ?_ (.inl ⟨s, rfl, rfl⟩)
      simp [Holds, Term.denote, hx, idVal, Val.toBool]
    | fresh c i =>
      have hsel : (Term.sel d 0 0 x).denote M = .int (c : Int) := by simp [Term.denote, hx, idVal]
      have hl : Holds M (.or (.not (.is d 0 x)) (.lt (.sel d 0 0 x) n)) ↔ Holds M (.lt (.sel d 0 0 x) n) := by
        simp [Holds, Term.denote, hx, idVal, Val.toBool]
      rw [hl, holds_lt hn hsel]
      constructor
      · intro h; exact .inr ⟨c, c, i, ⟨rfl, h⟩, rfl, rfl⟩
      · rintro (⟨_, h, -⟩ | ⟨c', c'', i', ⟨rfl, h⟩, e, -⟩)
        · cases h
        · cases e; exact h
  | .adt (_ + 1) _ vs, hc, x, c, h, v, ⟨d, _, hf, hx⟩ => by
    simp only [namesT, hf, Option.bind_some] at h
    exact namesAlts_iff hn d 0 vs hc x c h hx
  | .tuple ts, hc, x, c, h, v, ⟨d, _, vals, hf, hx, hvs⟩ => by
    simp only [namesT, hf, Option.bind_some] at h
    exact namesFields_iff hn d 0 ts hc x vals hx 0 c h (by simpa using hvs)
  | .bag t, hc, x, c, h, v, ⟨d, m, dt, _, sv, hf, hft, hm, hx, hw, ys, hp, hh⟩ => by
    simp only [namesT, hf, hft] at h
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
    subst hm
    have hS := slotsOf_den d dt 1 x sv hx hw
    rw [slots_names (g := fun xs => namesT L n t xs[0]) (fun xs c' y hc' ⟨z, hz, hyz⟩ => by
        obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero] at hc'
        exact names_iff hn t hc x0 c' hc' (hx0 ▸ hyz)) _ sv hS ys hh cs hcs]
    refine Iff.trans ?_ (multi_self_iff (r := Ty.relV (PBij.below N) t) (fun _ _ h => relV_self_below (t := t) hc h)
      (xs := v)).symm
    exact ⟨fun h y hy => h y (hp.mem_iff.2 hy), fun h y hy => h y (hp.mem_iff.1 hy)⟩
  | .list t, hc, x, c, h, v, ⟨d, m, dt, _, sv, hf, hft, hm, hx, hw, hh⟩ => by
    simp only [namesT, hf, hft] at h
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
    subst hm
    have hS := slotsOf_den d dt 1 x sv hx hw
    rw [slots_names (g := fun xs => namesT L n t xs[0]) (fun xs c' y hc' ⟨z, hz, hyz⟩ => by
        obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero] at hc'
        exact names_iff hn t hc x0 c' hc' (hx0 ▸ hyz)) _ sv hS v hh cs hcs]
    exact ⟨forall2_refl_of, forall2_self⟩
  | .table k w, hc, x, c, h, v, ⟨d, m, dt, _, sv, hf, hft, hm, hx, hw, ys, hp, hh⟩ => by
    simp only [Ty.comparable, Bool.and_eq_true] at hc
    simp only [namesT, hf, hft] at h
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
    subst hm
    have hS := slotsOf_den d dt 2 x sv hx hw
    rw [slots_names (g := fun xs : SlotItems 2 => (namesT L n k xs[0]).bind fun ck =>
        (namesT L n w xs[1]).map fun cw => Term.and ck cw)
      (R := fun e => Ty.relV (PBij.below N) k e.1 e.1 ∧ Ty.relV (PBij.below N) w e.2 e.2)
      (fun xs c' e hc' ⟨zk, zv, hz, hk, hv⟩ => by
        obtain ⟨x0, x1, rfl, hx0, hx1⟩ := pair_terms hz
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ] at hc'
        obtain ⟨ck, hck, hc'⟩ := Option.bind_eq_some_iff.1 hc'
        obtain ⟨cw, hcw, rfl⟩ := Option.map_eq_some_iff.1 hc'
        rw [holds_and, names_iff hn k hc.1 x0 ck hck (hx0 ▸ hk), names_iff hn w hc.2 x1 cw hcw (hx1 ▸ hv)])
      _ sv hS ys hh cs hcs]
    refine Iff.trans ?_ (multi_self_iff
      (r := fun (e e' : k.den × w.den) => Ty.relV (PBij.below N) k e.1 e'.1 ∧ Ty.relV (PBij.below N) w e.2 e'.2)
      (fun _ _ h => ⟨relV_self_below (t := k) hc.1 h.1, relV_self_below (t := w) hc.2 h.2⟩)
      (xs := v.1)).symm
    exact ⟨fun h y hy => h y (hp.mem_iff.2 hy), fun h y hy => h y (hp.mem_iff.1 hy)⟩
  | .fn .., hc, _, _, _, _, _ | .param _, _, _, _, _, _, hx => by first | simp [Ty.comparable] at hc | exact hx.elim
theorem namesFields_iff (hn : n.denote M = .int (N : Int)) (d k : Nat) : (ts : List Ty) →
    Ty.comparables ts = true → (x : Term) → (vs : List Val) → x.denote M = .ctor d k vs → (j : Nat) →
    (c : Term) → namesFields L n d k ts x j = some c → {v : Ty.dens ts} → RelVs L ts v (vs.drop j) →
    (Holds M c ↔ Ty.relsWith Dsl.val (Dsl.relV (PBij.below N)) (PBij.below N) ts v v)
  | [], _, x, vs, hx, j, c, h, _, _ => by
    simp only [namesFields, Option.some.injEq] at h
    subst h
    exact iff_of_true holds_tt trivial
  | t :: ts, hc, x, vs, hx, j, c, h, (v, vr), ⟨w, ws, hd, hw, hws⟩ => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    have hj : vs[j]? = some w := by
      have := List.getElem?_drop (xs := vs) (i := j) (j := 0); rw [hd] at this; simpa using this.symm
    have hj1 : vs.drop (j + 1) = ws := by rw [← List.drop_drop, hd]; rfl
    obtain ⟨c1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
    have hsel : (Term.sel d k j x).denote M = w := by simp [sel_ctor j hx, hj]
    rw [holds_and, names_iff hn t hc.1 _ c1 h1 (hsel ▸ hw),
      namesFields_iff hn d k ts hc.2 x vs hx (j + 1) c2 h2 (hj1 ▸ hws)]
    rfl
theorem namesAlts_iff (hn : n.denote M = .int (N : Int)) (d : Nat) : (k : Nat) → (vs : List (List Ty)) →
    Ty.comparabless vs = true → (x c : Term) → namesAlts L n d k vs x = some c → {v : Ty.alts vs} →
    RelAlts L d k vs v (x.denote M) →
    (Holds M c ↔ Ty.relAltsWith Dsl.val (Dsl.relV (PBij.below N)) (PBij.below N) vs v v)
  | k, fs :: vs, hc, x, c, h, .inl v, ⟨vals, hx, hvs⟩ => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    obtain ⟨c1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
    have hl : Holds M (.ite (.is d k x) c1 c2) ↔ Holds M c1 := by simp [Holds, Term.denote, hx, Val.toBool]
    rw [hl]
    exact namesFields_iff hn d k fs hc.1 x vals hx 0 c1 h1 (by simpa using hvs)
  | k, _ :: vs, hc, x, c, h, .inr v, hv => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    obtain ⟨c1, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨j, _, hx, hj⟩ := relAlts_index d (k + 1) vs v _ hv
    have hl : Holds M (.ite (.is d k x) c1 c2) ↔ Holds M c2 := by
      simp [Holds, Term.denote, hx, Val.toBool, show j ≠ k by omega]
    rw [hl]
    exact namesAlts_iff hn d (k + 1) vs hc.2 x c2 h2 hv
end

/-- `names_iff` for stored data. -/
theorem names_rel0 (hn : n.denote M = .int (N : Int)) {t : Ty} (hc : t.comparable = true) {x c : Term}
    (h : namesT L n t x = some c) {v : t.den0}
    (hv : RelV L t (Ty.up t (Ty.isData_of_comparable t hc) v) (x.denote M)) :
    Holds M c ↔ Ty.rel0 (PBij.below N) t v v :=
  (names_iff hn t hc x c h hv).trans (Ty.relV_up t _ v v)

end

section
variable (L : Layout) (n : Term)

/-- Every machine's instance table holds only names below `n`. -/
def namesMachinesT {r e : Ty} : (ms : List (MachineV r e)) → PerMachine (fun _ => Term) ms → Option Term
  | [], .nil => some tt
  | m :: ms, .cons x xs => (namesT L n m.table x).bind fun c => (namesMachinesT ms xs).map (.and c)

/-- The symbolic state's records and instance tables hold only names below its counter. Pending requests are not
read: their table's keys are wire ids, and what a request keeps is related by meaning, not by its captured values. -/
def namesStateT {v : ServiceV} (S : SymState v) : Option Term :=
  (namesT L S.fresh v.records S.records).bind fun c => (namesMachinesT L S.fresh v.machines S.machines).map (.and c)

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {N : Nat} {r e : Ty}

theorem instance_self {m : MachineV r e} (hk : m.key.comparable = true) (hs : m.state.comparable = true)
    {i j : Step.Instance m} (h : Step.Instance.Rel (PBij.below N) i j) : Step.Instance.Rel (PBij.below N) i i := by
  obtain ⟨h1, h2, h3⟩ := h
  have ht : ∀ {a b : Option (Int × m.state.den0)},
      Option.Rel (fun a b => a.1 = b.1 ∧ Ty.rel0 (PBij.below N) m.state a.2 b.2) a b →
      Option.Rel (fun a b => a.1 = b.1 ∧ Ty.rel0 (PBij.below N) m.state a.2 b.2) a a := by
    intro a b h
    cases h with
    | none => exact .none
    | some hab => exact .some ⟨rfl, Ty.self_of_below (PBij.below_fixes N) _ hs hab.2⟩
  exact ⟨Ty.self_of_below (PBij.below_fixes N) _ hk h1, Ty.self_of_below (PBij.below_fixes N) _ hs h2, ht h3⟩

theorem instEntry_comparable {st : Ty} (hs : st.comparable = true) : (instEntry st).comparable = true := by
  simp [instEntry, Ty.option, Ty.comparable, Ty.comparables, Ty.comparabless, hs]

/-- A table whose instances keep their names below `N` keeps them itself. -/
theorem table_self {m : MachineV r e} (hk : m.key.comparable = true) (hs : m.state.comparable = true)
    (tbl : m.table.den0) (h : Step.Insts.Rel (PBij.below N) (instancesOf T m tbl) (instancesOf T m tbl)) :
    Ty.rel0 (PBij.below N) m.table tbl tbl := by
  have hi := (multi_self_iff (fun _ _ h => instance_self hk hs h)).1 h.1
  refine Multi.of_forall2 (forall2_refl_of fun e he => ?_)
  obtain ⟨h1, h2, h3⟩ := hi (instOf m e.1 e.2) (List.mem_mergeSort.2 (List.mem_map_of_mem he))
  obtain ⟨k, st, t, ⟨⟩⟩ := e
  refine ⟨h1, h2, ?_, trivial⟩
  match t, h3 with
  | .inl ((_, _, ()), ()), .some hab => exact ⟨⟨rfl, hab.2, trivial⟩, trivial⟩
  | .inr (.inl ()), _ => trivial

variable {n : Term} {v : ServiceV} (hn : n.denote M = .int (N : Int))
include hn

/-- Instances whose names are below `N` make the tables' names term hold. -/
theorem machines_names : (ms : List (MachineV v.records v.event)) →
    (∀ m ∈ ms, m.key.comparable = true ∧ m.state.comparable = true) →
    (xs : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) → MachinesRel M L T ms xs sms →
    Step.Machines.Rel (PBij.below N) sms sms → {c : Term} → namesMachinesT L n ms xs = some c → Holds M c
  | [], _, .nil, .nil, _, _, c, h => by
    simp only [namesMachinesT, Option.some.injEq] at h
    subst h
    exact holds_tt
  | m :: ms, hc, .cons x xs, .cons insts sms, ⟨⟨tbl, ht, hi⟩, hr⟩, ⟨hrel, hrels⟩, c, h => by
    obtain ⟨c1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
    have hm := hc m (List.mem_cons_self ..)
    have htc : m.table.comparable = true := by
      simp only [MachineV.table, Ty.comparable, Bool.and_eq_true]
      exact ⟨hm.1, instEntry_comparable hm.2⟩
    subst hi
    rw [holds_and]
    exact ⟨(names_rel0 hn htc h1 ht).2 (table_self hm.1 hm.2 tbl hrel),
      machines_names ms (fun m' hm' => hc m' (List.mem_cons_of_mem _ hm')) xs sms hr hrels h2⟩

end

/-- A state whose names are below its counter, as every state on valid inputs is, makes the symbolic state's names
term hold. -/
theorem stateSupp_names {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {shs : List (PendingShape v.event)}
    {S : SymState v} {s : State v} (hS : StateRel M L T shs S s) (hs : Step.StateSupp s)
    (hrc : v.records.comparable = true)
    (hms : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true)
    {c : Term} (h : namesStateT L S = some c) : Holds M c := by
  obtain ⟨c1, h1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hr, hm⟩ := hs.data (PBij.below s.fresh) (PBij.below_fixes _)
  rw [holds_and]
  exact ⟨(names_rel0 hS.fresh hrc h1 hS.records).2 hr, machines_names hS.fresh _ hms _ _ hS.machines hm h2⟩

end Tazuna.Smt
