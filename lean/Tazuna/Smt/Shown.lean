import Tazuna.Smt.Names
import Tazuna.Smt.Verdict

/-! The ids a value holds, as terms: each id position of the value's term with the condition under which the value
holds an id there (`idsT`). A position under a constructor the value was not built with, or in a free slot, has a
false condition, so the positions whose conditions hold are exactly the ids the value holds (`ids_exact`, against
`idsV`, which `Trace.idsOf` agrees with up to order, `idsOf_up`). A type without a datatype in the layout has no
position: a value of it has no term, so nothing is lost and nothing is refused. An unrolled run asks of each input that
every id it carries that the service made is one an earlier step's out lines showed (`knownT`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The positions with each condition and-ed with `g`. -/
def guardIds (g : Term) (ps : List (Term × Term)) : List (Term × Term) := ps.map fun p => (andT g p.1, p.2)

section
variable (L : Layout)

-- A type with no datatype in the layout has no value with a term, so it has no id position.
set_option linter.tazuna.silentDefault false in
mutual
/-- Each id position of the value `x` of type `t`, with the condition under which the value holds an id there. -/
def idsT : Ty → Term → List (Term × Term)
  | .id, x => [(tt, x)]
  | .adt (i + 1) a vs, x => match L.find? (.adt (i + 1) a vs) with
    | some (d, _) => idsAlts d 0 vs x
    | none => []
  | .tuple ts, x => match L.find? (.tuple ts) with
    | some (d, _) => idsFields d 0 ts x 0
    | none => []
  | .bag t, x => match L.find? (.bag t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, m), some (dt, _) => (slotsOf d dt m 1 x).flatMap fun sl => guardIds sl.1 (idsT t sl.2[0])
    | _, _ => []
  | .list t, x => match L.find? (.list t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, m), some (dt, _) => (slotsOf d dt m 1 x).flatMap fun sl => guardIds sl.1 (idsT t sl.2[0])
    | _, _ => []
  | .table k w, x => match L.find? (.table k w), L.find? (.tuple [Ty.bool, k, w]) with
    | some (d, m), some (dt, _) =>
      (slotsOf d dt m 2 x).flatMap fun sl => guardIds sl.1 (idsT k sl.2[0] ++ idsT w sl.2[1])
    | _, _ => []
  | _, _ => []
/-- The fields' id positions, from field `j` of constructor `k` of datatype `d`. -/
def idsFields (d k : Nat) : List Ty → Term → Nat → List (Term × Term)
  | [], _, _ => []
  | t :: ts, x, j => idsT t (.sel d k j x) ++ idsFields d k ts x (j + 1)
/-- The id positions of each constructor from `k`, each under the condition that it built `x`. -/
def idsAlts (d : Nat) : Nat → List (List Ty) → Term → List (Term × Term)
  | _, [], _ => []
  | k, fs :: vs, x => guardIds (.is d k x) (idsFields d k fs x 0) ++ idsAlts d (k + 1) vs x
end

/-- Every id the value `x` of type `t` holds that the service made is the value of a position of `shown` whose
condition holds. -/
def knownT (shown : List (Term × Term)) (t : Ty) (x : Term) : Term :=
  match L.find? .id with
  | some (d, _) => allT ((idsT L t x).map fun p =>
      .or (.not p.1) (.or (.not (.is d 0 p.2)) (anyT (shown.map fun q => andT q.1 (.eq q.2 p.2)))))
  | none => tt

end

mutual
/-- The ids a value holds, as a data value at the structure level holds them. -/
def idsV : (t : Ty) → t.den → List IdV
  | .id, x => [x]
  | .list t, xs => xs.flatMap (idsV t)
  | .bag t, xs => xs.flatMap (idsV t)
  | .table k w, x => x.1.flatMap fun e => idsV k e.1 ++ idsV w e.2
  | .tuple ts, x => idsVs ts x
  | .adt _ _ vs, x => idsAltsV vs x
  | .int, _ | .str, _ | .date, _ | .fn .., _ | .param _, _ | .dsl .., _ => []
def idsVs : (ts : List Ty) → Ty.dens ts → List IdV
  | [], _ => []
  | t :: ts, (x, xs) => idsV t x ++ idsVs ts xs
def idsAltsV : (vs : List (List Ty)) → Ty.alts vs → List IdV
  | [], x => nomatch x
  | fs :: _, .inl x => idsVs fs x
  | _ :: vs, .inr y => idsAltsV vs y
end

/-- The positions whose conditions hold are exactly the ids `l` holds: each such position's value is one of them, and
each of them is some such position's value. -/
def IdsExact (M : Model) (L : Layout) (ps : List (Term × Term)) (l : List IdV) : Prop :=
  (∀ p ∈ ps, Holds M p.1 → ∃ i ∈ l, RelV L .id i (p.2.denote M)) ∧
    ∀ i ∈ l, ∃ p ∈ ps, Holds M p.1 ∧ RelV L .id i (p.2.denote M)

section
variable {M : Model} {L : Layout}

theorem IdsExact.nil : IdsExact M L [] [] := ⟨nofun, nofun⟩

theorem IdsExact.append {ps qs : List (Term × Term)} {l m : List IdV} (h : IdsExact M L ps l) (h' : IdsExact M L qs m) :
    IdsExact M L (ps ++ qs) (l ++ m) := by
  refine ⟨fun p hp hc => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨i, hi, e⟩ := h.1 p hp hc; exact ⟨i, List.mem_append_left _ hi, e⟩
    · obtain ⟨i, hi, e⟩ := h'.1 p hp hc; exact ⟨i, List.mem_append_right _ hi, e⟩
  · rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨p, hp, e⟩ := h.2 i hi; exact ⟨p, List.mem_append_left _ hp, e⟩
    · obtain ⟨p, hp, e⟩ := h'.2 i hi; exact ⟨p, List.mem_append_right _ hp, e⟩

theorem IdsExact.congr {ps : List (Term × Term)} {l m : List IdV} (h : IdsExact M L ps l) (e : ∀ i, i ∈ l ↔ i ∈ m) :
    IdsExact M L ps m :=
  ⟨fun p hp hc => let ⟨i, hi, h1⟩ := h.1 p hp hc; ⟨i, (e i).1 hi, h1⟩, fun i hi => h.2 i ((e i).2 hi)⟩

theorem IdsExact.guard {g : Term} {ps : List (Term × Term)} {l : List IdV} (hg : Holds M g) (h : IdsExact M L ps l) :
    IdsExact M L (guardIds g ps) l := by
  refine ⟨fun p hp hc => ?_, fun i hi => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact h.1 q hq ((holds_andT _ _).1 hc).2
  · obtain ⟨q, hq, hc, e⟩ := h.2 i hi
    exact ⟨_, List.mem_map_of_mem hq, (holds_andT _ _).2 ⟨hg, hc⟩, e⟩

theorem IdsExact.guard_neg {g : Term} (hg : ¬ Holds M g) (ps : List (Term × Term)) :
    IdsExact M L (guardIds g ps) [] := by
  refine ⟨fun p hp hc => ?_, nofun⟩
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
  exact absurd ((holds_andT _ _).1 hc).1 hg

/-- Exact positions name each id they hold by one value: a position whose condition holds and whose value is `i`'s is
one exactly when `i` is held. -/
theorem relV_id_inj {i j : IdV} {w : Val} (h : RelV L .id i w) (h' : RelV L .id j w) : i = j := by
  obtain ⟨d, n, hf, e⟩ := h
  obtain ⟨d', n', hf', e'⟩ := h'
  obtain ⟨rfl, -⟩ : d = d' ∧ n = n' := by simpa using hf.symm.trans hf'
  exact idVal_inj (e.symm.trans e')

theorem IdsExact.held {ps : List (Term × Term)} {l : List IdV} (h : IdsExact M L ps l) (i : IdV) :
    (∃ p ∈ ps, Holds M p.1 ∧ RelV L .id i (p.2.denote M)) ↔ i ∈ l :=
  ⟨fun ⟨p, hp, hc, e⟩ => let ⟨_, hj, e'⟩ := h.1 p hp hc; relV_id_inj e e' ▸ hj, h.2 i⟩

/-- The slot-wise part of the positions: where the slots hold the items `ys`, each slot's positions guarded by its
flag are exactly the ids the items hold. -/
theorem slots_ids {α : Type} {w : Nat} {g : SlotItems w → List (Term × Term)} {E : α → List Val → Prop}
    {f : α → List IdV} (hg : ∀ (xs : SlotItems w) y, E y (Term.denotes M xs.1) → IdsExact M L (g xs) (f y)) :
    (S : List (Slot w)) → (sv : List (Bool × List Val)) → SlotsDen M S sv → (ys : List α) → Holds2 E ys sv →
    IdsExact M L (S.flatMap fun sl => guardIds sl.1 (g sl.2)) (ys.flatMap f)
  | [], [], _, ys, hy => by
    cases ys with
    | nil => exact .nil
    | cons => exact hy.elim
  | (fl, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩, ys, hy => by
    simp only [List.flatMap_cons]
    cases b with
    | false =>
      have h := (IdsExact.guard_neg (M := M) (L := L) (g := fl) (by simp [Holds, hf, Val.toBool]) (g xs)).append
        (slots_ids hg S sv hS ys (by simpa [Holds2, occupied] using hy))
      simpa using h
    | true =>
      match ys, hy with
      | y :: ys, ⟨hy1, hy2⟩ =>
        simp only [List.flatMap_cons]
        exact (IdsExact.guard (by simp [Holds, hf, Val.toBool]) (hg xs y (hxs ▸ hy1))).append
          (slots_ids hg S sv hS ys hy2)
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- No position of the constructors from `k` on holds once `x` is built by an earlier one. -/
theorem idsAlts_none {d' j : Nat} {x : Term} {vals : List Val} (hx : x.denote M = .ctor d' j vals) :
    (k : Nat) → j < k → (vs : List (List Ty)) → IdsExact M L (idsAlts L d' k vs x) []
  | _, _, [] => .nil
  | k, hk, fs :: vs => by
    have h := (IdsExact.guard_neg (M := M) (L := L) (g := .is d' k x)
      (by simp [Holds, Term.denote, hx, Val.toBool, show j ≠ k by omega]) (idsFields L d' k fs x 0)).append
      (idsAlts_none hx (k + 1) (by omega) vs)
    simpa [idsAlts] using h

theorem mem_flatMap_perm {α β : Type} {f : α → List β} {l l' : List α} (hp : l.Perm l') (b : β) :
    b ∈ l.flatMap f ↔ b ∈ l'.flatMap f := by
  simp only [List.mem_flatMap, hp.mem_iff]

theorem mem_flatMap_map {α β γ : Type} {g : α → List γ} {h : β → List γ} {c : γ} (f : α → β)
    (e : ∀ a, c ∈ g a ↔ c ∈ h (f a)) (l : List α) : c ∈ l.flatMap g ↔ c ∈ (l.map f).flatMap h := by
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨fun ⟨a, ha, hc⟩ => ⟨f a, ⟨a, ha, rfl⟩, (e a).1 hc⟩, fun ⟨_, ⟨a, ha, rfl⟩, hc⟩ => ⟨a, ha, (e a).2 hc⟩⟩

mutual
/-- The positions of a value's term whose conditions hold are exactly the ids the value holds. -/
theorem ids_exact : (t : Ty) → (x : Term) → {v : t.den} → RelV L t v (x.denote M) →
    IdsExact M L (idsT L t x) (idsV t v)
  | .id, x, v, hx => by
    refine ⟨fun p hp _ => ?_, fun i hi => ?_⟩
    · simp only [idsT, List.mem_singleton] at hp; subst hp
      exact ⟨v, List.Mem.head _, hx⟩
    · rcases hi with _ | ⟨_, ⟨⟩⟩
      exact ⟨_, List.Mem.head _, holds_tt, hx⟩
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ => by simpa [idsT, idsV] using IdsExact.nil
  | .adt 0 _ vs, _, v, ⟨hvs, _⟩ => by
    subst hvs
    rcases v with _ | _ | e
    · simpa [idsT, idsV, idsAltsV, idsVs] using IdsExact.nil
    · simpa [idsT, idsV, idsAltsV, idsVs] using IdsExact.nil
    · exact nomatch e
  | .dsl k _, _, _, _ => by simpa [idsT, idsV] using IdsExact.nil
  | .adt (_ + 1) _ vs, x, v, ⟨d', _, hf, hx⟩ => by
    simp only [idsT, hf, idsV]
    exact idsAlts_exact d' 0 vs x hx
  | .tuple ts, x, v, ⟨d', _, vals, hf, hx, hvs⟩ => by
    simp only [idsT, hf, idsV]
    exact idsFields_exact d' 0 ts x vals hx 0 (by simpa using hvs)
  | .bag t, x, v, ⟨d', m, dt, _, sv, hf, hft, hm, hx, hw, ys, hp, hh⟩ => by
    simp only [idsT, hf, hft, idsV]
    subst hm
    refine (slots_ids (g := fun xs => idsT L t xs[0]) (f := idsV t) (fun xs y ⟨z, hz, hyz⟩ => by
        obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero]
        exact ids_exact t x0 (hx0 ▸ hyz)) _ sv (slotsOf_den d' dt 1 x sv hx hw) ys hh).congr fun i => mem_flatMap_perm hp i
  | .list t, x, v, ⟨d', m, dt, _, sv, hf, hft, hm, hx, hw, hh⟩ => by
    simp only [idsT, hf, hft, idsV]
    subst hm
    exact slots_ids (g := fun xs => idsT L t xs[0]) (f := idsV t) (fun xs y ⟨z, hz, hyz⟩ => by
        obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero]
        exact ids_exact t x0 (hx0 ▸ hyz)) _ sv (slotsOf_den d' dt 1 x sv hx hw) v hh
  | .table k w, x, v, ⟨d', m, dt, _, sv, hf, hft, hm, hx, hw, ys, hp, hh⟩ => by
    simp only [idsT, hf, hft, idsV]
    subst hm
    refine (slots_ids (g := fun xs : SlotItems 2 => idsT L k xs[0] ++ idsT L w xs[1])
      (f := fun e => idsV k e.1 ++ idsV w e.2) (fun xs e ⟨zk, zv, hz, hk, hv⟩ => by
        obtain ⟨x0, x1, rfl, hx0, hx1⟩ := pair_terms hz
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ]
        exact (ids_exact k x0 (hx0 ▸ hk)).append (ids_exact w x1 (hx1 ▸ hv))) _ sv
      (slotsOf_den d' dt 2 x sv hx hw) ys hh).congr fun i => mem_flatMap_perm hp i
  | .fn .., _, _, hx | .param _, _, _, hx => hx.elim
theorem idsFields_exact (d' k : Nat) : (ts : List Ty) → (x : Term) →
    (vs : List Val) → x.denote M = .ctor d' k vs → (j : Nat) → {v : Ty.dens ts} → RelVs L ts v (vs.drop j) →
    IdsExact M L (idsFields L d' k ts x j) (idsVs ts v)
  | [], _, _, _, _, _, _ => by simpa [idsFields, idsVs] using IdsExact.nil
  | t :: ts, x, vs, hx, j, (v, vr), ⟨w, ws, hdr, hw, hws⟩ => by
    have hj : vs[j]? = some w := by
      have := List.getElem?_drop (xs := vs) (i := j) (j := 0); rw [hdr] at this; simpa using this.symm
    have hj1 : vs.drop (j + 1) = ws := by rw [← List.drop_drop, hdr]; rfl
    have hsel : (Term.sel d' k j x).denote M = w := by simp [sel_ctor j hx, hj]
    simp only [idsFields, idsVs]
    exact (ids_exact t _ (hsel ▸ hw)).append (idsFields_exact d' k ts x vs hx (j + 1) (hj1 ▸ hws))
theorem idsAlts_exact (d' : Nat) : (k : Nat) → (vs : List (List Ty)) →
    (x : Term) → {v : Ty.alts vs} → RelAlts L d' k vs v (x.denote M) → IdsExact M L (idsAlts L d' k vs x) (idsAltsV vs v)
  | k, fs :: vs, x, .inl v, ⟨vals, hx, hvs⟩ => by
    have h := (IdsExact.guard (g := .is d' k x) (by simp [Holds, Term.denote, hx, Val.toBool])
      (idsFields_exact d' k fs x vals hx 0 (by simpa using hvs))).append
      (idsAlts_none (L := L) hx (k + 1) (by omega) vs)
    simpa [idsAlts, idsAltsV] using h
  | k, fs :: vs, x, .inr v, hv => by
    obtain ⟨j, _, hx, hj⟩ := relAlts_index d' (k + 1) vs v _ hv
    have h := (IdsExact.guard_neg (M := M) (L := L) (g := .is d' k x)
      (by simp [Holds, Term.denote, hx, Val.toBool, show j ≠ k by omega]) (idsFields L d' k fs x 0)).append
      (idsAlts_exact d' (k + 1) vs x hv)
    simpa [idsAlts, idsAltsV] using h
end

end

section
variable (T : List TypeDecl)

mutual
/-- The trace writer's ids of a data value are the ids it holds at the structure level, up to order. -/
theorem idsOf_up : (t : Ty) → (h : t.isData = true) → (x : t.den0) → ∀ i, (i ∈ Trace.idsOf T t x ↔ i ∈ idsV t (Ty.up t h x))
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ | .id, _, _, _ | .param _, _, _, _ => Iff.rfl
  | .list t, h, xs, i => by
    have ht : t.isData = true := h
    rw [Ty.up_list t h ht]
    exact mem_flatMap_map (Ty.up t ht) (fun y => idsOf_up t ht y i) xs
  | .bag t, h, xs, i => by
    have ht : t.isData = true := h
    rw [Ty.up_bag t h ht]
    exact (mem_flatMap_perm (List.mergeSort_perm _ _) i).trans
      (mem_flatMap_map (Ty.up t ht) (fun y => idsOf_up t ht y i) xs)
  | .table k w, h, x, i => by
    have hk : k.isData = true := (Bool.and_eq_true _ _ ▸ h).1
    have hw : w.isData = true := (Bool.and_eq_true _ _ ▸ h).2
    show _ ↔ i ∈ (Ty.up _ h x).1.flatMap _
    rw [Ty.up_table k w h hk hw]
    exact (mem_flatMap_perm (List.mergeSort_perm _ _) i).trans (mem_flatMap_map _ (fun e => by
      simp only [List.mem_append]; exact or_congr (idsOf_up k hk e.1 i) (idsOf_up w hw e.2 i)) x.1)
  | .tuple ts, h, x, i => idsOfs_up ts h x i
  | .adt k a vs, h, x, i => idsOfAlts_up k a vs h x i
  | .fn .., _, _, _ | .dsl .., _, _, _ => by simp [Trace.idsOf, idsV]
theorem idsOfs_up : (ts : List Ty) → (h : (Ty.tuple ts).isData = true) → (x : (Ty.tuple ts).den0) →
    ∀ i, (i ∈ Trace.idsOfs T ts x ↔ i ∈ idsVs ts (Ty.up (.tuple ts) h x))
  | [], _, (), _ => by simp [Trace.idsOfs, idsVs]
  | t :: ts, h, x, i => by
    have ht : t.isData = true := (Bool.and_eq_true _ _ ▸ h).1
    have hts : (Ty.tuple ts).isData = true := (Bool.and_eq_true _ _ ▸ h).2
    rw [Ty.up_tuple t ts h ht hts x]
    obtain ⟨a, b⟩ := x
    simp only [Trace.idsOfs, idsVs, List.mem_append]
    exact or_congr (idsOf_up t ht a i) (idsOfs_up ts hts b i)
theorem idsOfAlts_up (k : Nat) (a : List Ty) : (vs : List (List Ty)) → (h : (Ty.adt k a vs).isData = true) →
    (x : (Ty.adt k a vs).den0) → ∀ i, (i ∈ Trace.idsOfAlts T vs x ↔ i ∈ idsAltsV vs (Ty.up _ h x))
  | [], _, x, _ => nomatch x
  | fs :: vs, h, .inl x, i => by
    have hfs : (Ty.tuple fs).isData = true := (Bool.and_eq_true _ _ ▸ h).1
    rw [Ty.up_inl k a fs vs h hfs x]
    exact idsOfs_up fs hfs x i
  | fs :: vs, h, .inr y, i => by
    have hvs : (Ty.adt k a vs).isData = true := (Bool.and_eq_true _ _ ▸ h).2
    rw [Ty.up_inr k a fs vs h hvs y]
    exact idsOfAlts_up k a vs hvs y i
end

theorem idsOf_down {t : Ty} (h : t.isData = true) (x : t.den) (i : IdV) :
    i ∈ Trace.idsOf T t (Ty.down t h x) ↔ i ∈ idsV t x := by
  rw [idsOf_up T t h, Ty.up_down]

end

section
variable {M : Model} {L : Layout}

/-- The input check is exact: where `shown` is exact for `seen`, `knownT` holds exactly when every id the value holds
is from outside or among `seen`. -/
theorem knownT_iff {shown : List (Term × Term)} {seen : List IdV} (hs : IdsExact M L shown seen) {t : Ty} {x : Term}
    {v : t.den} (hv : RelV L t v (x.denote M)) : Holds M (knownT L shown t x) ↔ ∀ i ∈ idsV t v, i.Known seen := by
  have hx := ids_exact t x hv
  unfold knownT
  split
  · rename_i d nd hd
    have hid : ∀ i w, RelV L .id i w → w = idVal d i := fun i w ⟨d', n', hf, e⟩ => by
      obtain ⟨rfl, -⟩ : d = d' ∧ nd = n' := by simpa using hd.symm.trans hf
      exact e
    have his : ∀ i : IdV, ∀ y : Term, RelV L .id i (y.denote M) → (Holds M (.is d 0 y) ↔ ∃ c n, i = .fresh c n) :=
      fun i y hy => by cases i <;> simp [Holds, Term.denote, hid _ _ hy, idVal, Val.toBool]
    have hany : ∀ y : Term, Holds M (anyT (shown.map fun q => andT q.1 (.eq q.2 y))) ↔
        ∃ q ∈ shown, Holds M q.1 ∧ q.2.denote M = y.denote M := fun y => by
      rw [holds_anyT]
      constructor
      · rintro ⟨_, hm, hh⟩
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
        obtain ⟨h1, h2⟩ := (holds_andT _ _).1 hh
        exact ⟨q, hq, h1, Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at h2; exact h2)⟩
      · rintro ⟨q, hq, h1, h2⟩
        refine ⟨_, List.mem_map_of_mem hq, (holds_andT _ _).2 ⟨h1, ?_⟩⟩
        show Val.beq _ _ = true; rw [h2]; exact Val.beq_refl _
    simp only [holds_allT, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, holds_or, holds_not]
    constructor
    · intro h i hi
      obtain ⟨p, hp, hc, e⟩ := hx.2 i hi
      rcases h p hp with h | h | h
      · exact absurd hc h
      · cases i with
        | named _ => trivial
        | fresh c n => exact absurd ((his _ _ e).2 ⟨c, n, rfl⟩) h
      · cases i with
        | named _ => trivial
        | fresh c n =>
          obtain ⟨q, hq, hq1, hq2⟩ := (hany _).1 h
          exact (hs.held _).1 ⟨q, hq, hq1, hq2 ▸ e⟩
    · intro h p hp
      by_cases hc : Holds M p.1
      · obtain ⟨i, hi, e⟩ := hx.1 p hp hc
        cases i with
        | named s => exact .inr (.inl fun h' => by obtain ⟨_, _, h''⟩ := (his _ _ e).1 h'; cases h'')
        | fresh c n =>
          obtain ⟨q, hq, hq1, hq2⟩ := hs.2 _ (h _ hi)
          exact .inr (.inr ((hany _).2 ⟨q, hq, hq1, (hid _ _ hq2).trans (hid _ _ e).symm⟩))
      · exact .inl hc
  · rename_i hd
    refine iff_of_true holds_tt fun i hi => ?_
    obtain ⟨p, -, -, d', n', hf, -⟩ := hx.2 i hi
    exact absurd (hd.symm.trans hf) (by simp)

end

end Tazuna.Smt
