import Tazuna.Smt.EncodeThm
import Tazuna.Semantics.Equivariance

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

theorem relDAlts_index (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) →
    {w : Val} → RelDAlts L d k vs x w → ∃ j vals, w = .ctor d j vals ∧ k ≤ j
  | k, _ :: _, .inl _, _, ⟨vals, e, _⟩ => ⟨k, vals, e, Nat.le_refl k⟩
  | k, _ :: vs, .inr y, _, h => by
    obtain ⟨j, vals, e, hj⟩ := relDAlts_index d (k + 1) vs y h
    exact ⟨j, vals, e, by omega⟩

mutual
/-- Two values as a step holds them with one code relate with every id renamed to itself: they are the same value,
bags and tables read as multisets. A type that is not data has no code, so no value of it relates to one. -/
theorem relD_same : (t : Ty) → {x y : t.den0} → {z : Val} → RelD L t x z → RelD L t y z → Ty.rel0 PBij.refl t x y
  | .int, _, _, _, hx, hy | .str, _, _, _, hx, hy | .date, _, _, _, hx, hy => by
    simp only [RelD] at hx hy
    rw [hx] at hy
    cases hy
    rfl
  | .id, x, y, _, ⟨d, _, hf, hx⟩, ⟨d', _, hf', hy⟩ => by
    obtain rfl := find_det hf hf'
    rw [hx] at hy
    obtain rfl := idVal_inj hy
    exact IdV.rel_refl x
  | .adt 0 _ vs, x, y, _, ⟨h, hx⟩, ⟨_, hy⟩ => by
    subst h
    rw [hx] at hy
    rcases x with _ | _ | e <;> rcases y with _ | _ | e' <;>
      first | trivial | exact nomatch e | exact nomatch e' | simp [altsBool0] at hy
  | .adt (_ + 1) _ vs, _, _, _, ⟨d, _, hf, hx⟩, ⟨d', _, hf', hy⟩ => by
    obtain rfl := find_det hf hf'
    exact relDAlts_same d 0 vs hx hy
  | .tuple ts, _, _, _, ⟨d, _, vals, hf, hx, hvs⟩, ⟨d', _, vals', hf', hy, hvs'⟩ => by
    obtain rfl := find_det hf hf'
    rw [hx] at hy
    cases hy
    exact relDs_same ts hvs hvs'
  | .bag t, _, _, _, ⟨d, _, dt, _, sv, hf, hft, _, hx, _, ys, hp, hh⟩,
      ⟨d', _, dt', _, sv', hf', hft', _, hy, _, ys', hp', hh'⟩ => by
    obtain rfl := find_det hf hf'
    obtain rfl := find_det hft hft'
    rw [hx] at hy
    obtain rfl := slotsVal_inj hy
    have hs : Forall2 (Ty.rel0 PBij.refl t) ys ys' := holds2_same (fun _ _ _ ⟨_, e1, h1⟩ ⟨_, e2, h2⟩ => by
      rw [e1, List.cons.injEq] at e2
      exact relD_same t h1 (e2.1 ▸ h2)) hh hh'
    exact ((Multi.of_forall2 hs).perm_left hp).perm_right hp'
  | .table k w, _, _, _, ⟨d, _, dt, _, sv, hf, hft, _, hx, _, ys, hp, hh⟩,
      ⟨d', _, dt', _, sv', hf', hft', _, hy, _, ys', hp', hh'⟩ => by
    obtain rfl := find_det hf hf'
    obtain rfl := find_det hft hft'
    rw [hx] at hy
    obtain rfl := slotsVal_inj hy
    have hs : Forall2 (fun e e' => Ty.rel0 PBij.refl k e.1 e'.1 ∧ Ty.rel0 PBij.refl w e.2 e'.2) ys ys' :=
      holds2_same (fun _ _ _ ⟨_, _, e1, hk1, hw1⟩ ⟨_, _, e2, hk2, hw2⟩ => by
        rw [e1, List.cons.injEq, List.cons.injEq] at e2
        exact ⟨relD_same k hk1 (e2.1 ▸ hk2), relD_same w hw1 (e2.2.1 ▸ hw2)⟩) hh hh'
    exact ((Multi.of_forall2 hs).perm_left hp).perm_right hp'
  | .list t, _, _, _, ⟨d, _, dt, _, sv, hf, hft, _, hx, _, hh⟩, ⟨d', _, dt', _, sv', hf', hft', _, hy, _, hh'⟩ => by
    obtain rfl := find_det hf hf'
    obtain rfl := find_det hft hft'
    rw [hx] at hy
    obtain rfl := slotsVal_inj hy
    exact holds2_same (fun _ _ _ ⟨_, e1, h1⟩ ⟨_, e2, h2⟩ => by
      rw [e1, List.cons.injEq] at e2
      exact relD_same t h1 (e2.1 ▸ h2)) hh hh'
  | .dsl k _, x, y, _, hx, hy => by
    cases k <;> simp only [RelD] at hx
    change _ = Val.int (Int.ofNat y) at hy
    rw [hx] at hy
    cases hy
    rfl
  | .fn .., _, _, _, hx, _ | .param _, _, _, _, hx, _ => hx.elim
theorem relDs_same : (ts : List Ty) → {x y : (Ty.semsWith Dsl.base ts).1} → {vals : List Val} → RelDs L ts x vals →
    RelDs L ts y vals → Ty.relsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl ts x y
  | [], _, _, _, _, _ => trivial
  | t :: ts, _, _, _, ⟨_, _, e, h, hs⟩, ⟨_, _, e', h', hs'⟩ => by
    rw [e, List.cons.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    exact ⟨relD_same t h h', relDs_same ts hs hs'⟩
theorem relDAlts_same (d : Nat) : (k : Nat) → (vs : List (List Ty)) → {x y : (Ty.semAltsWith Dsl.base vs).1} →
    {z : Val} → RelDAlts L d k vs x z → RelDAlts L d k vs y z →
    Ty.relAltsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl vs x y
  | k, fs :: _, .inl _, .inl _, _, ⟨_, e, h⟩, ⟨_, e', h'⟩ => by
    rw [e, Val.ctor.injEq] at e'
    obtain ⟨-, -, rfl⟩ := e'
    exact relDs_same fs h h'
  | k, _ :: vs, .inr _, .inr _, _, h, h' => relDAlts_same d (k + 1) vs h h'
  | k, _ :: vs, .inl _, .inr y, _, ⟨_, e, _⟩, h' => by
    obtain ⟨j, _, e', hj⟩ := relDAlts_index d (k + 1) vs y h'
    rw [e, Val.ctor.injEq] at e'
    omega
  | k, _ :: vs, .inr x, .inl _, _, h, ⟨_, e', _⟩ => by
    obtain ⟨j, _, e, hj⟩ := relDAlts_index d (k + 1) vs x h
    rw [e, Val.ctor.injEq] at e'
    omega
end

/-- Two stored data values whose codes are one value are the same, bags and tables read as multisets. -/
theorem rel0_same {t : Ty} (hd : t.isData = true) {x y : t.den0} {z : Val} (hx : RelV L t (Ty.up t hd x) z)
    (hy : RelV L t (Ty.up t hd y) z) : Ty.rel0 PBij.refl t x y :=
  relD_same t (relV_up t hd _ _ hx) (relV_up t hd _ _ hy)

/-- `relD_same` for data values as an expression holds them. -/
theorem relV_same (t : Ty) (hd : t.isData = true) {x y : t.den} {z : Val} (hx : RelV L t x z) (hy : RelV L t y z) :
    Ty.relV PBij.refl t x y := by
  rw [← Ty.up_down t hd x] at hx
  rw [← Ty.up_down t hd y] at hy
  have h := Ty.relV_up_of (R := PBij.refl) hd (rel0_same hd hx hy)
  rwa [Ty.up_down, Ty.up_down] at h

end Tazuna.Smt
