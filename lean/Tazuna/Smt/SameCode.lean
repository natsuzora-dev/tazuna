import Tazuna.Smt.EncodeThm
import Tazuna.Semantics.Valid

/-! Two data values with one code are the same value, reading bags and tables as multisets: the code of a bag or a
table holds its items in some order, so it fixes the items but not the order the value keeps them in. This is what
lets a solver compare two results by their codes alone (`relV_same`, `rel0_same`): equal codes give the relation the
results are compared by with every id renamed to itself, so the solver never searches for a renaming. -/

namespace Tazuna.Smt

open Tazuna.Ir

variable {L : Layout}

theorem slotsVal_inj {d dt : Nat} {sv sv' : List (Bool × List Val)} (h : slotsVal d dt sv = slotsVal d dt sv') :
    sv = sv' := by
  simp only [slotsVal, Val.ctor.injEq, true_and] at h
  induction sv generalizing sv' with
  | nil => cases sv' <;> simp_all
  | cons p sv ih =>
    cases sv' with
    | nil => simp at h
    | cons q sv' =>
      simp only [List.map_cons, List.cons.injEq, Val.ctor.injEq, true_and, Val.bool.injEq] at h
      rw [ih h.2]
      obtain ⟨b, vs⟩ := p
      obtain ⟨b', vs'⟩ := q
      simp only at h
      rw [h.1.1, h.1.2]

theorem idVal_inj {d : Nat} {x y : IdV} (h : idVal d x = idVal d y) : x = y := by
  cases x <;> cases y <;> simp_all [idVal, Int.natCast_inj]

theorem IdV.rel_refl (x : IdV) : IdV.Rel PBij.refl x x := by
  cases x with
  | named s => exact .inl ⟨s, rfl, rfl⟩
  | fresh c i => exact .inr ⟨c, c, i, rfl, rfl, rfl⟩

/-- Items held by the same occupied slots relate pointwise. -/
theorem holds2_same {α : Type} {E : α → List Val → Prop} {r : α → α → Prop}
    (h : ∀ x y vs, E x vs → E y vs → r x y) {xs ys : List α} {sv : List (Bool × List Val)}
    (hx : Holds2 E xs sv) (hy : Holds2 E ys sv) : Forall2 r xs ys :=
  forall2_imp (fun _ _ ⟨_, h1, h2⟩ => h _ _ _ h1 h2) (forall2_comp hx (forall2_flip hy))

mutual
/-- Two data values with one code relate with every id renamed to itself: they are the same value, bags and tables
read as multisets. -/
theorem relV_same : (t : Ty) → t.isData = true → {x y : t.den} → {z : Val} → RelV L t x z → RelV L t y z →
    Ty.relV PBij.refl t x y
  | .int, _, _, _, _, hx, hy | .str, _, _, _, _, hx, hy | .date, _, _, _, _, hx, hy => by
    simp only [RelV] at hx hy
    rw [hx] at hy
    cases hy
    rfl
  | .id, _, x, y, _, ⟨d, _, hf, hx⟩, ⟨d', _, hf', hy⟩ => by
    obtain rfl := find_det hf hf'
    rw [hx] at hy
    obtain rfl := idVal_inj hy
    exact IdV.rel_refl x
  | .adt 0 _ vs, _, x, y, _, ⟨h, hx⟩, ⟨_, hy⟩ => by
    subst h
    rw [hx] at hy
    rcases x with _ | _ | e <;> rcases y with _ | _ | e' <;>
      first | trivial | exact nomatch e | exact nomatch e' | simp [altsBool] at hy
  | .adt (_ + 1) _ vs, hd, _, _, _, ⟨d, _, hf, hx⟩, ⟨d', _, hf', hy⟩ => by
    obtain rfl := find_det hf hf'
    exact relAlts_same d 0 vs hd hx hy
  | .tuple ts, hd, _, _, _, ⟨d, _, vals, hf, hx, hvs⟩, ⟨d', _, vals', hf', hy, hvs'⟩ => by
    obtain rfl := find_det hf hf'
    rw [hx] at hy
    cases hy
    exact relVs_same ts hd hvs hvs'
  | .bag t, hd, _, _, _, ⟨d, _, dt, _, sv, hf, hft, _, hx, _, ys, hp, hh⟩,
      ⟨d', _, dt', _, sv', hf', hft', _, hy, _, ys', hp', hh'⟩ => by
    obtain rfl := find_det hf hf'
    obtain rfl := find_det hft hft'
    rw [hx] at hy
    obtain rfl := slotsVal_inj hy
    have hs : Forall2 (Ty.relV PBij.refl t) ys ys' := holds2_same (fun _ _ _ ⟨_, e1, h1⟩ ⟨_, e2, h2⟩ => by
      rw [e1, List.cons.injEq] at e2
      exact relV_same t hd h1 (e2.1 ▸ h2)) hh hh'
    exact ((Multi.of_forall2 hs).perm_left hp).perm_right hp'
  | .table k w, hd, _, _, _, ⟨d, _, dt, _, sv, hf, hft, _, hx, _, ys, hp, hh⟩,
      ⟨d', _, dt', _, sv', hf', hft', _, hy, _, ys', hp', hh'⟩ => by
    simp only [Ty.isData, Bool.and_eq_true] at hd
    obtain rfl := find_det hf hf'
    obtain rfl := find_det hft hft'
    rw [hx] at hy
    obtain rfl := slotsVal_inj hy
    have hs : Forall2 (fun e e' => Ty.relV PBij.refl k e.1 e'.1 ∧ Ty.relV PBij.refl w e.2 e'.2) ys ys' :=
      holds2_same (fun _ _ _ ⟨_, _, e1, hk1, hw1⟩ ⟨_, _, e2, hk2, hw2⟩ => by
        rw [e1, List.cons.injEq, List.cons.injEq] at e2
        exact ⟨relV_same k hd.1 hk1 (e2.1 ▸ hk2), relV_same w hd.2 hw1 (e2.2.1 ▸ hw2)⟩) hh hh'
    exact ((Multi.of_forall2 hs).perm_left hp).perm_right hp'
  | .list t, hd, _, _, _, ⟨d, _, dt, _, sv, hf, hft, _, hx, _, hh⟩, ⟨d', _, dt', _, sv', hf', hft', _, hy, _, hh'⟩ => by
    obtain rfl := find_det hf hf'
    obtain rfl := find_det hft hft'
    rw [hx] at hy
    obtain rfl := slotsVal_inj hy
    exact holds2_same (fun _ _ _ ⟨_, e1, h1⟩ ⟨_, e2, h2⟩ => by
      rw [e1, List.cons.injEq] at e2
      exact relV_same t hd h1 (e2.1 ▸ h2)) hh hh'
  | .dsl k _, hd, x, y, _, hx, hy => by
    cases k <;> simp [Ty.isData] at hd
    change _ = Val.int (Int.ofNat x) at hx
    change _ = Val.int (Int.ofNat y) at hy
    rw [hx] at hy
    cases hy
    rfl
  | .fn .., _, _, _, _, hx, _ | .param _, _, _, _, _, hx, _ => hx.elim
theorem relVs_same : (ts : List Ty) → Ty.isDatas ts = true → {x y : Ty.dens ts} → {vals : List Val} →
    RelVs L ts x vals → RelVs L ts y vals → Ty.relsWith Dsl.val (Dsl.relV PBij.refl) PBij.refl ts x y
  | [], _, _, _, _, _, _ => trivial
  | t :: ts, hd, _, _, _, ⟨_, _, e, h, hs⟩, ⟨_, _, e', h', hs'⟩ => by
    simp only [Ty.isDatas, Bool.and_eq_true] at hd
    rw [e, List.cons.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    exact ⟨relV_same t hd.1 h h', relVs_same ts hd.2 hs hs'⟩
theorem relAlts_same (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.isDatass vs = true → {x y : Ty.alts vs} →
    {z : Val} → RelAlts L d k vs x z → RelAlts L d k vs y z →
    Ty.relAltsWith Dsl.val (Dsl.relV PBij.refl) PBij.refl vs x y
  | k, fs :: _, hd, .inl _, .inl _, _, ⟨_, e, h⟩, ⟨_, e', h'⟩ => by
    simp only [Ty.isDatass, Bool.and_eq_true] at hd
    rw [e, Val.ctor.injEq] at e'
    obtain ⟨-, -, rfl⟩ := e'
    exact relVs_same fs hd.1 h h'
  | k, _ :: vs, hd, .inr _, .inr _, _, h, h' => by
    simp only [Ty.isDatass, Bool.and_eq_true] at hd
    exact relAlts_same d (k + 1) vs hd.2 h h'
  | k, _ :: vs, _, .inl _, .inr y, _, ⟨_, e, _⟩, h' => by
    obtain ⟨j, _, e', hj⟩ := relAlts_index d (k + 1) vs y _ h'
    rw [e, Val.ctor.injEq] at e'
    omega
  | k, _ :: vs, _, .inr x, .inl _, _, h, ⟨_, e', _⟩ => by
    obtain ⟨j, _, e, hj⟩ := relAlts_index d (k + 1) vs x _ h
    rw [e, Val.ctor.injEq] at e'
    omega
end

/-- Two stored data values whose codes are one value are the same, bags and tables read as multisets. -/
theorem rel0_same {t : Ty} (hd : t.isData = true) {x y : t.den0} {z : Val} (hx : RelV L t (Ty.up t hd x) z)
    (hy : RelV L t (Ty.up t hd y) z) : Ty.rel0 PBij.refl t x y := by
  have h := Ty.rel0_down hd (relV_same t hd hx hy)
  rwa [Ty.down_up, Ty.down_up] at h

end Tazuna.Smt
