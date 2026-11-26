import Tazuna.Smt.Decode
import Tazuna.Smt.CodeInjective
import Tazuna.Smt.Wf

/-! Decoding is total on codes: an SMT value that codes a value of a comparable type decodes, to a value the
relation `relV_same` compares by equals to the coded one (`decode_of_relV`). A bag's or a table's code holds its items
in some order, so the decoded collection is the coded one up to that order. A table's code holds each key once, since
the coded table does, which is what makes its decoding succeed: so a model value related to a real value is never one
`decodeV` refuses, and an assertion of well-formedness (`wfT`, `wf_iff`) holds of it. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout}

theorem relAlts_ge {d : Nat} : (k : Nat) → (vs : List (List Ty)) → {x : Ty.alts vs} → {z : Val} →
    RelAlts L d k vs x z → ∃ k' vals, z = .ctor d k' vals ∧ k ≤ k'
  | _, [], x, _, _ => nomatch x
  | k, _ :: _, .inl _, _, ⟨vals, h, _⟩ => ⟨k, vals, h, Nat.le_refl k⟩
  | k, _ :: vs, .inr _, _, h => by
    obtain ⟨k', vals, hz, hle⟩ := relAlts_ge (k + 1) vs h
    exact ⟨k', vals, hz, by omega⟩

/-- Pairwise distinct keys carry over along a relation that keeps key comparisons. -/
theorem pairwise_keys_forall2 {α β : Type} {E : α → β → Prop} {f : α → α → Bool} {g : β → β → Bool}
    (hfg : ∀ a b a' b', E a b → E a' b' → f a a' = g b b') :
    {as : List α} → {bs : List β} → Forall2 E as bs →
    bs.Pairwise (fun b b' => g b b' = false ∧ g b' b = false) → as.Pairwise (fun a a' => f a a' = false ∧ f a' a = false)
  | [], [], _, _ => .nil
  | a :: as, b :: bs, ⟨hab, hr⟩, hp => by
    rw [List.pairwise_cons] at hp ⊢
    refine ⟨fun a' ha' => ?_, pairwise_keys_forall2 hfg hr hp.2⟩
    obtain ⟨b', hb', hab'⟩ := forall2_mem_left hr a' ha'
    rw [hfg a b a' b' hab hab', hfg a' b' a b hab' hab]
    exact hp.1 b' hb'
  | [], _ :: _, h, _ | _ :: _, [], h, _ => nomatch h

mutual
/-- A code of a value of a comparable type decodes. -/
theorem decode_isSome_of_relV : (t : Ty) → t.comparable = true → (x : t.den) → (z : Val) → RelV L t x z →
    (decodeV L t z).isSome = true
  | .int, _, _, _, h | .date, _, _, _, h => by cases h; rfl
  | .str, _, _, _, h => by cases h; rfl
  | .dsl .fresh _, _, x, _, h => by
    cases h
    have hm : ∀ m : Nat, (if 0 ≤ Int.ofNat m then some (Int.ofNat m).toNat else none).isSome = true := by
      intro m; simp
    exact hm x
  | .id, _, x, _, ⟨d, n, hf, h⟩ => by cases h; cases x <;> simp [idVal, decodeV, hf, decodeId] <;> rfl
  | .adt 0 _ vs, _, x, _, ⟨e, h⟩ => by
    subst e; cases h
    match x with
    | .inl () => rfl
    | .inr (.inl ()) => rfl
  | .adt (i + 1) a vs, hc, x, z, ⟨d, n, hf, h⟩ => by
    simp only [decodeV, hf]
    exact decodeAlts_isSome_of_relV d 0 vs (by simpa [Ty.comparable] using hc) x z h
  | .tuple ts, hc, x, _, ⟨d, n, vals, hf, hz, h⟩ => by
    subst hz
    simp only [decodeV, hf, and_self]
    exact decodeVs_isSome_of_relVs ts (by simpa [Ty.comparable] using hc) x vals h
  | .bag t, hc, _, _, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys, _, hh⟩ => by
    subst h3 h4
    have ht : t.comparable = true := by simpa [Ty.comparable] using hc
    simp only [decodeV, h1, h2, collView_slots sv h5]
    show ((occupied sv).mapM (fun | [z] => decodeV L t z | _ => none)).isSome = true
    rw [mapM_isSome, List.all_eq_true]
    intro vs hvs
    obtain ⟨y, -, z, rfl, hr⟩ := forall2_mem_right hh vs hvs
    exact decode_isSome_of_relV t ht y z hr
  | .list t, hc, _, _, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, hh⟩ => by
    subst h3 h4
    have ht : t.comparable = true := by simpa [Ty.comparable] using hc
    simp only [decodeV, h1, h2, collView_slots sv h5]
    show ((occupied sv).mapM (fun | [z] => decodeV L t z | _ => none)).isSome = true
    rw [mapM_isSome, List.all_eq_true]
    intro vs hvs
    obtain ⟨y, -, z, rfl, hr⟩ := forall2_mem_right hh vs hvs
    exact decode_isSome_of_relV t ht y z hr
  | .table k w, hc, x, _, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys, hp, hh⟩ => by
    subst h3 h4
    have hk : k.comparable = true := by simp only [Ty.comparable, Bool.and_eq_true] at hc; exact hc.1
    have hw : w.comparable = true := by simp only [Ty.comparable, Bool.and_eq_true] at hc; exact hc.2
    have hkd := Ty.isData_of_comparable k hk
    let g : List Val → Option (k.den × w.den) := fun
      | [zk, zv] => (decodeV L k zk).bind fun a => (decodeV L w zv).map fun b => (a, b)
      | _ => none
    have hdec : ∀ (e : k.den × w.den) (vs : List Val), (∃ zk zv, vs = [zk, zv] ∧ RelV L k e.1 zk ∧ RelV L w e.2 zv) →
        ∃ q, g vs = some q ∧ Ty.relV PBij.refl k q.1 e.1 := by
      rintro e vs ⟨zk, zv, rfl, hrk, hrw⟩
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (decode_isSome_of_relV k hk e.1 zk hrk)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (decode_isSome_of_relV w hw e.2 zv hrw)
      exact ⟨(a, b), by simp [g, ha, hb], relV_same k hkd (decode_rel k zk a ha) hrk⟩
    have hmap : ∀ {es : List (k.den × w.den)} {occ : List (List Val)},
        Forall2 (fun e vs => ∃ zk zv, vs = [zk, zv] ∧ RelV L k e.1 zk ∧ RelV L w e.2 zv) es occ →
        ∃ qs, occ.mapM g = some qs ∧ Forall2 (fun q e => Ty.relV PBij.refl k q.1 e.1) qs es := by
      intro es occ h
      induction es generalizing occ with
      | nil => cases occ with
        | nil => exact ⟨[], rfl, trivial⟩
        | cons => exact h.elim
      | cons e es ih => cases occ with
        | nil => exact h.elim
        | cons vs occ =>
          obtain ⟨q, hq, hrq⟩ := hdec e vs h.1
          obtain ⟨qs, hqs, hr⟩ := ih h.2
          exact ⟨q :: qs, by simp [List.mapM_cons, hq, hqs], hrq, hr⟩
    obtain ⟨qs, hqs, hr⟩ := hmap hh
    simp only [decodeV, h1, h2, collView_slots sv h5]
    show (((occupied sv).mapM g).bind (uniqueKeys (Ty.semWith Dsl.val k).2)).isSome = true
    rw [hqs]
    have hys : ys.Pairwise fun a b => (Ty.semWith Dsl.val k).2 a.1 b.1 = false ∧ (Ty.semWith Dsl.val k).2 b.1 a.1 = false :=
      (hp.pairwise_iff fun h => ⟨h.2, h.1⟩).2 x.2
    have hq := pairwise_keys_forall2 (f := fun q q' : k.den × w.den => (Ty.semWith Dsl.val k).2 q.1 q'.1)
      (g := fun e e' : k.den × w.den => (Ty.semWith Dsl.val k).2 e.1 e'.1)
      (fun q e q' e' h h' => Ty.relV_deq hk h h') hr hys
    simp [uniqueKeys, hq]
  | .fn .., hc, _, _, _ => by simp [Ty.comparable] at hc
  | .param _, _, _, _, h => h.elim
  | .dsl .effect _, hc, _, _, _ | .dsl .spec _, hc, _, _, _ | .dsl .service _, hc, _, _, _
  | .dsl .command _, hc, _, _, _ | .dsl .query _, hc, _, _, _ | .dsl .machine _, hc, _, _, _
  | .dsl .reaction _, hc, _, _, _ | .dsl .external _, hc, _, _, _ | .dsl .externalCommand _, hc, _, _, _
  | .dsl .externalQuery _, hc, _, _, _ | .dsl .source _, hc, _, _, _ | .dsl .declared _, hc, _, _, _
  | .dsl .subscription _, hc, _, _, _ | .dsl .bounds _, hc, _, _, _ | .dsl .create _, hc, _, _, _
  | .dsl .response _, hc, _, _, _ | .dsl .scenario _, hc, _, _, _ | .dsl .step _, hc, _, _, _
  | .dsl .sender _, hc, _, _, _ | .dsl .closure _, hc, _, _, _ => by simp [Ty.comparable] at hc
theorem decodeVs_isSome_of_relVs : (ts : List Ty) → Ty.comparables ts = true → (x : Ty.dens ts) → (vals : List Val) →
    RelVs L ts x vals → (decodeVs L ts vals).isSome = true
  | [], _, _, _, h => by cases h; rfl
  | t :: ts, hc, (x, xs), _, ⟨z, zs, e, h1, h2⟩ => by
    subst e
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (decode_isSome_of_relV t hc.1 x z h1)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (decodeVs_isSome_of_relVs ts hc.2 xs zs h2)
    simp [decodeVs, ha, hb]; rfl
theorem decodeAlts_isSome_of_relV (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.comparabless vs = true →
    (x : Ty.alts vs) → (z : Val) → RelAlts L d k vs x z → (decodeAlts L d k vs z).isSome = true
  | _, [], _, x, _, _ => nomatch x
  | k, fs :: _, hc, .inl x, _, ⟨vals, hz, h⟩ => by
    subst hz
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    simp only [decodeAlts, and_self, ite_true]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (decodeVs_isSome_of_relVs fs hc.1 x vals h)
    simp only [hy]; rfl
  | k, _ :: vs, hc, .inr y, z, h => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    have ih := decodeAlts_isSome_of_relV d (k + 1) vs hc.2 y z h
    obtain ⟨k', vals, rfl, hle⟩ := relAlts_ge (k + 1) vs h
    have hne : k' ≠ k := by omega
    simp only [decodeAlts, hne, and_false, ite_false]
    obtain ⟨y', hy⟩ := Option.isSome_iff_exists.1 ih
    simp only [hy]; rfl
end

/-- A code of a value of a comparable type decodes to a value equal to it as `relV_same` compares, collections up to
order. -/
theorem decode_of_relV {t : Ty} (hc : t.comparable = true) {x : t.den} {z : Val} (h : RelV L t x z) :
    ∃ y, decodeV L t z = some y ∧ Ty.relV PBij.refl t y x := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (decode_isSome_of_relV t hc x z h)
  exact ⟨y, hy, relV_same t (Ty.isData_of_comparable t hc) (decode_rel t z y hy) h⟩

end

end Tazuna.Smt
