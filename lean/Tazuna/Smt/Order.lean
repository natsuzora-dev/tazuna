import Tazuna.Smt.Wf
import Tazuna.Semantics.Order

/-! The canonical order as terms: for two terms of a type, whether the first comes before the second and whether no
later, in Erlang term order (`Tazuna.Semantics.Order`). Ints and dates compare as numbers, strings by code points
(`str.<`), ids fresh before named, tuples and records of one variant field by field, and an enumeration by its
variants' atoms, an order fixed before any solver runs. Other types (bags, tables, lists, variants with fields among
others) have no order term. `ordT_rel` proves the terms denote the order on the values the terms denote, so a step
encoding that orders instances by these terms orders them as the step does. -/

namespace Tazuna.Smt

open Tazuna.Ir

def ff : Term := .bool false

/-- Two orders combined lexicographically: before when the first is, or when it ties and the second is. -/
def lexT (a b : Term × Term) : Term × Term :=
  let eq := Term.and a.2 (.not a.1)
  (.or a.1 (.and eq b.1), .or a.1 (.and eq b.2))

-- Every index comes from `List.range ats.length`, so the default is never read (`getD_map_range`).
set_option linter.tazuna.silentDefault false in
/-- Pairs of variant indices below `n` whose atoms stand in `rel`. -/
def atomPairs (ats : List String) (rel : String → String → Bool) : List (Nat × Nat) :=
  (List.range ats.length).flatMap fun k => (List.range ats.length).filterMap fun j =>
    if rel (ats.getD k "") (ats.getD j "") then some (k, j) else none

/-- An enumeration's order: `isK k x` says `x` is variant `k`, and variants compare by their atoms `ats`. -/
def enumOrd (isK : Nat → Term → Term) (ats : List String) (x y : Term) : Term × Term :=
  let anyOf (ps : List (Nat × Nat)) := anyT (ps.map fun (k, j) => Term.and (isK k x) (isK j y))
  (anyOf (atomPairs ats fun a b => decide (a < b)), anyOf (atomPairs ats fun a b => decide (a < b ∨ a = b)))

/-- An id's order: fresh ids by their step's counter, then their index, before named ones, which compare by name. -/
def idOrd (d : Nat) (x y : Term) : Term × Term :=
  let fx := Term.is d 0 x
  let fy := Term.is d 0 y
  let sx := Term.sel d 0 0 x
  let sy := Term.sel d 0 0 y
  let ix := Term.sel d 0 1 x
  let iy := Term.sel d 0 1 y
  let fr := lexT (.lt sx sy, .le sx sy) (.lt ix iy, .le ix iy)
  let nx := Term.sel d 1 0 x
  let ny := Term.sel d 1 0 y
  (.ite fx (.ite fy fr.1 tt) (.ite fy ff (.slt nx ny)),
   .ite fx (.ite fy fr.2 tt) (.ite fy ff (.or (.slt nx ny) (.eq nx ny))))

/-- Whether Bool's value `x` is variant `k`: True is variant 0. -/
def boolIs (k : Nat) (x : Term) : Term := if k = 0 then x else .not x

section
variable (L : Layout) (T : List TypeDecl)

mutual
/-- Whether `x` comes before `y`, and whether no later, in the canonical order of `t`. -/
def ordT : (t : Ty) → Term → Term → Option (Term × Term)
  | .int, x, y | .point _, x, y => some (.lt x y, .le x y)
  | .str, x, y => some (.slt x y, .or (.slt x y) (.eq x y))
  | .id, x, y => (L.find? .id).map fun (d, _) => idOrd d x y
  | .tuple ts, x, y => (L.find? (.tuple ts)).bind fun (d, _) => ordFields d ts x y 0
  | .adt 0 _ [[], []], x, y => some (enumOrd boolIs ((List.range 2).map (atomAt (variantsAt T 0))) x y)
  | .adt (i + 1) a [fs], x, y => (L.find? (.adt (i + 1) a [fs])).bind fun (d, _) => ordFields d fs x y 0
  | .adt (i + 1) a vs, x, y =>
    if vs.all (·.isEmpty) then (L.find? (.adt (i + 1) a vs)).map fun (d, _) =>
      enumOrd (Term.is d) ((List.range vs.length).map (atomAt (variantsAt T (i + 1)))) x y
    else none
  | _, _, _ => none
/-- The fields of constructor 0 of datatype `d` from field `j` on, compared in order. -/
def ordFields (d : Nat) : List Ty → Term → Term → Nat → Option (Term × Term)
  | [], _, _, _ => some (ff, tt)
  | t :: ts, x, y, j => do
    let a ← ordT t (.sel d 0 j x) (.sel d 0 j y)
    let b ← ordFields d ts x y (j + 1)
    pure (lexT a b)
end

end

/-! The terms denote the order. -/

section
variable {M : Model}

/-- What the pair of terms says of an order `o`: before, and no later. -/
def OrdDen (M : Model) (p : Term × Term) (o : Ordering) : Prop :=
  p.1.denote M = .bool (o == .lt) ∧ p.2.denote M = .bool o.isLE

theorem lexT_den {a b : Term × Term} {o o' : Ordering} (ha : OrdDen M a o) (hb : OrdDen M b o') :
    OrdDen M (lexT a b) (o.then o') := by
  obtain ⟨h1, h2⟩ := ha
  obtain ⟨h3, h4⟩ := hb
  simp only [OrdDen, lexT, Term.denote, h1, h2, h3, h4, Val.toBool]
  cases o <;> cases o' <;> exact ⟨rfl, rfl⟩

theorem string_cmp (a b : String) : (compare a b == .lt) = decide (a < b) ∧ (compare a b).isLE = decide (a < b ∨ a = b) := by
  simp only [compare, String.compare, compareOfLessAndEq]
  by_cases h : a < b
  · simp [h]
  · by_cases e : a = b <;> simp [h, e]

theorem int_cmp (a b : Int) : (compare a b == .lt) = decide (a < b) ∧ (compare a b).isLE = decide (a ≤ b) := by
  simp only [compare, compareOfLessAndEq]
  by_cases h : a < b
  · simp [h]; omega
  · by_cases e : a = b
    · simp [e]
    · simp [h, e]; omega

-- Every index comes from `List.range ats.length`, so the default is never read (`getD_map_range`).
set_option linter.tazuna.silentDefault false in
theorem mem_atomPairs {ats : List String} {rel : String → String → Bool} {k j : Nat} :
    (k, j) ∈ atomPairs ats rel ↔ k < ats.length ∧ j < ats.length ∧ rel (ats.getD k "") (ats.getD j "") = true := by
  simp only [atomPairs, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  constructor
  · rintro ⟨k', hk', j', hj', h⟩
    split at h
    · cases h; exact ⟨hk', hj', by assumption⟩
    · cases h
  · rintro ⟨hk, hj, h⟩; exact ⟨k, hk, j, hj, by simp only [h, ite_true]⟩

/-- Under `isK`, `x` is variant `kx` and `y` variant `ky` of `n`: the pairs' disjunction holds exactly when the pair
is listed. -/
theorem anyPairs_den {isK : Nat → Term → Term} {x y : Term} {n kx ky : Nat}
    (hx : ∀ k < n, (isK k x).denote M = .bool (k == kx)) (hy : ∀ k < n, (isK k y).denote M = .bool (k == ky))
    (ps : List (Nat × Nat)) (hps : ∀ p ∈ ps, p.1 < n ∧ p.2 < n) :
    (anyT (ps.map fun (k, j) => Term.and (isK k x) (isK j y))).denote M = .bool (decide ((kx, ky) ∈ ps)) := by
  rw [anyT_denote]
  congr 1
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨_, hm, h⟩
    obtain ⟨⟨k, j⟩, hkj, rfl⟩ := List.mem_map.1 hm
    have hb := hps _ hkj
    simp only [Term.denote, hx k hb.1, hy j hb.2, Val.toBool, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hkj
  · intro h
    have hb := hps _ h
    exact ⟨_, List.mem_map.2 ⟨(kx, ky), h, rfl⟩, by simp [Term.denote, hx kx hb.1, hy ky hb.2, Val.toBool]⟩

-- Every index comes from `List.range ats.length`, so the default is never read (`getD_map_range`).
set_option linter.tazuna.silentDefault false in
theorem enumOrd_den {isK : Nat → Term → Term} {x y : Term} {kx ky : Nat} (ats : List String)
    (hkx : kx < ats.length) (hky : ky < ats.length)
    (hx : ∀ k < ats.length, (isK k x).denote M = .bool (k == kx))
    (hy : ∀ k < ats.length, (isK k y).denote M = .bool (k == ky)) :
    OrdDen M (enumOrd isK ats x y) (compare (ats.getD kx "") (ats.getD ky "")) := by
  have hps (rel : String → String → Bool) : ∀ p ∈ atomPairs ats rel, p.1 < ats.length ∧ p.2 < ats.length :=
    fun ⟨k, j⟩ h => by have := mem_atomPairs.1 h; exact ⟨this.1, this.2.1⟩
  simp only [OrdDen, enumOrd, anyPairs_den hx hy _ (hps _), mem_atomPairs, hkx, hky, true_and,
    (string_cmp _ _).1, (string_cmp _ _).2]
  simp

/-- An enumeration's value is its variant's constructor without fields, and its term the variant's atom. -/
theorem enum_rel (L : Layout) (T : List TypeDecl) (decl : List Variant) (d i : Nat) (a : List Ty) : (k0 : Nat) → (vs : List (List Ty)) →
    vs.all (·.isEmpty) = true → (x : (Ty.semAltsWith Dsl.base vs).1) → (h : (Ty.adt i a vs).isData = true) →
    (v : Val) → RelAlts L d k0 vs (Ty.up (.adt i a vs) h x) v →
    ∃ k < vs.length, v = .ctor d (k0 + k) [] ∧ Ty.erlAlts T decl k0 vs x = .atom (atomAt decl (k0 + k))
  | _, [], _, x, _, _, _ => nomatch x
  | k0, [] :: vs, he, .inl u, h, v, hv => by
    have e := Ty.up_inl i a [] vs h rfl u
    erw [e] at hv
    obtain ⟨vals, rfl, hvals⟩ := hv
    simp only [RelVs] at hvals; subst hvals
    exact ⟨0, by simp, rfl, rfl⟩
  | k0, [] :: vs, he, .inr y, h, v, hv => by
    have hvs : (Ty.adt i a vs).isData = true := by simpa [Ty.isData, Ty.isDatass, Ty.isDatas] using h
    rw [Ty.up_inr i a [] vs h hvs] at hv
    obtain ⟨k, hk, rfl, he'⟩ := enum_rel L T decl d i a (k0 + 1) vs (by simpa using he) y hvs v hv
    exact ⟨k + 1, by simp; omega, by rw [show k0 + (k + 1) = k0 + 1 + k by omega], by
      simp only [Ty.erlAlts]; rw [he', show k0 + (k + 1) = k0 + 1 + k by omega]⟩
  | _, (_ :: _) :: _, he, _, _, _, _ => by simp at he

theorem erls_length (T : List TypeDecl) : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) →
    (Ty.erls T ts x).length = ts.length
  | [], () => rfl
  | _ :: ts, (_, xs) => by simp [Ty.erls, erls_length T ts xs]

theorem val_str_beq (a b : String) : (Val.str a == Val.str b) = decide (a = b) := by
  show Val.beq _ _ = _
  simp only [Val.beq]; rw [Bool.eq_iff_iff]; simp

theorem int_ord {x y : Term} {a b : Int} (ha : x.denote M = .int a) (hb : y.denote M = .int b) :
    OrdDen M (.lt x y, .le x y) (Erl.cmp (.int a) (.int b)) := by
  simp only [OrdDen, Term.denote]; rw [ha, hb]
  simp only [Val.toInt, Erl.cmp_int, (int_cmp a b).1, (int_cmp a b).2]; exact ⟨rfl, rfl⟩

theorem str_ord {x y : Term} {a b : String} (ha : x.denote M = .str a) (hb : y.denote M = .str b) :
    OrdDen M (.slt x y, .or (.slt x y) (.eq x y)) (Erl.cmp (.bin a) (.bin b)) := by
  simp only [OrdDen, Term.denote]; rw [ha, hb]
  simp only [Val.toStr, Erl.cmp_bin, (string_cmp a b).1, (string_cmp a b).2, val_str_beq, Val.toBool]
  refine ⟨rfl, ?_⟩
  congr 1

theorem erl_compare (a b : Erl) : compare a b = Erl.cmp a b := rfl

theorem string_compare_self (s : String) : compare s s = .eq := by
  simp only [compare, String.compare, compareOfLessAndEq]; simp

-- The lemma that shows the default unread.
set_option linter.tazuna.silentDefault false in
theorem getD_map_range (f : Nat → String) {k n : Nat} (h : k < n) : ((List.range n).map f).getD k "" = f k := by
  simp [List.getD_eq_getElem?_getD, h]

theorem id_ord (T : List TypeDecl) {x y : Term} {d : Nat} (a b : IdV) (ha : x.denote M = idVal d a)
    (hb : y.denote M = idVal d b) : OrdDen M (idOrd d x y) (Ty.cmp T .id a b) := by
  cases a with
  | fresh s i =>
    cases b with
    | fresh s' i' =>
      have hl := lexT_den (int_ord (M := M) (x := .sel d 0 0 x) (y := .sel d 0 0 y) (a := s) (b := s')
          (by simp [Term.denote, ha, idVal]) (by simp [Term.denote, hb, idVal]))
        (int_ord (M := M) (x := .sel d 0 1 x) (y := .sel d 0 1 y) (a := i) (b := i')
          (by simp [Term.denote, ha, idVal]) (by simp [Term.denote, hb, idVal]))
      obtain ⟨h1, h2⟩ := hl
      simp only [OrdDen, idOrd, Term.denote, ha, hb, idVal, Ty.cmp, Ty.erl, erl_compare, Erl.cmp_pair]
      simp [Val.toBool, h1, h2]
    | named n =>
      simp only [OrdDen, idOrd, Term.denote, ha, hb, idVal, Ty.cmp, Ty.erl]
      simp [Val.toBool, tt, Term.denote, erl_compare, Erl.cmp_tuple_bin]
  | named n =>
    cases b <;> simp only [OrdDen, idOrd, Term.denote, ha, hb, idVal, Ty.cmp, Ty.erl] <;>
      simp [Val.toBool, Val.toStr, Term.denote, ff, erl_compare, val_str_beq, Erl.cmp_bin, Erl.cmp_bin_tuple,
        (string_cmp _ _).1, (string_cmp _ _).2]

mutual
/-- The order terms denote the canonical order of the values the compared terms denote. -/
theorem ordT_rel (L : Layout) (T : List TypeDecl) : (t : Ty) → (x y : Term) → (p : Term × Term) →
    ordT L T t x y = some p → (ht : t.isData = true) → (a b : t.den0) →
    RelV L t (Ty.up t ht a) (x.denote M) → RelV L t (Ty.up t ht b) (y.denote M) → OrdDen M p (Ty.cmp T t a b)
  | .int, x, y, p, h, _, a, b, ha, hb => by
    simp only [ordT, Option.some.injEq] at h; subst h
    change x.denote M = .int a at ha; change y.denote M = .int b at hb
    exact int_ord ha hb
  | .point _, x, y, p, h, _, a, b, ha, hb => by
    simp only [ordT, Option.some.injEq] at h; subst h
    change x.denote M = .int a at ha; change y.denote M = .int b at hb
    exact int_ord ha hb
  | .str, x, y, p, h, _, a, b, ha, hb => by
    simp only [ordT, Option.some.injEq] at h; subst h
    change x.denote M = .str a.1 at ha; change y.denote M = .str b.1 at hb
    exact str_ord ha hb
  | .id, x, y, p, h, _, a, b, ha, hb => by
    obtain ⟨d, n, hf, ha⟩ := ha
    obtain ⟨d', n', hf', hb⟩ := hb
    rw [hf] at hf'; cases hf'
    simp only [ordT, hf, Option.map_some, Option.some.injEq] at h; subst h
    exact id_ord T a b ha hb
  | .tuple ts, x, y, p, h, ht, a, b, ha, hb => by
    obtain ⟨d, n, xv, hf, hxv, ha⟩ := ha
    obtain ⟨d', n', yv, hf', hyv, hb⟩ := hb
    rw [hf] at hf'; cases hf'
    simp only [ordT, hf, Option.bind_some] at h
    have hfo := ordFields_rel L T d ts x y 0 p h ht a b xv yv ha hb
      (fun i hi => by rw [Nat.zero_add, sel_ctor i hxv]; simp [hi])
      (fun i hi => by rw [Nat.zero_add, sel_ctor i hyv]; simp [hi])
    show OrdDen M p (Erl.cmp (.tuple (Ty.erls T ts a)) (.tuple (Ty.erls T ts b)))
    rw [Erl.cmp_tuple, ite_eq_left_of_eq_true _ _ (eq_true ((erls_length T ts a).trans (erls_length T ts b).symm))]
    exact hfo
  | .adt 0 args [[], []], x, y, p, h, ht, a, b, ha, hb => by
    simp only [ordT, Option.some.injEq] at h; subst h
    have hvs : (Ty.adt 0 args [[]]).isData = true := by simp [Ty.isData, Ty.isDatass, Ty.isDatas]
    have key : ∀ (u : (Ty.adt 0 args [[], []]).den0) (z : Term), RelV L _ (Ty.up _ ht u) (z.denote M) →
        ∃ k < 2, (∀ j < 2, (boolIs j z).denote M = .bool (j == k)) ∧
          Ty.erl T (.adt 0 args [[], []]) u = .atom (atomAt (variantsAt T 0) k) := by
      intro u z hz
      obtain ⟨_, hz⟩ := hz
      rcases u with u | u | u
      · erw [Ty.up_inl 0 args [] [[]] ht rfl u] at hz
        refine ⟨0, by decide, fun j hj => ?_, by cases u; rfl⟩
        match j, hj with
        | 0, _ => simp [boolIs, hz, altsBool]
        | 1, _ => simp [boolIs, Term.denote, hz, altsBool, Val.toBool]
      · erw [Ty.up_inr 0 args [] [[]] ht hvs (.inl u), Ty.up_inl 0 args [] [] hvs rfl u] at hz
        refine ⟨1, by decide, fun j hj => ?_, by cases u; rfl⟩
        match j, hj with
        | 0, _ => simp [boolIs, hz, altsBool]
        | 1, _ => simp [boolIs, Term.denote, hz, altsBool, Val.toBool]
      · exact nomatch u
    obtain ⟨kx, hkx, hx, ex⟩ := key a x ha
    obtain ⟨ky, hky, hy, ey⟩ := key b y hb
    have hlen : ((List.range 2).map (atomAt (variantsAt T 0))).length = 2 := by simp
    have := enumOrd_den (isK := boolIs) (x := x) (y := y) ((List.range 2).map (atomAt (variantsAt T 0)))
      (by rw [hlen]; exact hkx) (by rw [hlen]; exact hky) (by rw [hlen]; exact hx) (by rw [hlen]; exact hy)
    rw [getD_map_range _ hkx, getD_map_range _ hky] at this
    show OrdDen M _ (Erl.cmp _ _)
    rw [ex, ey, Erl.cmp_atom]; exact this
  | .adt (i + 1) args [fs], x, y, p, h, ht, a, b, ha, hb => by
    obtain ⟨d, n, hf, ha⟩ := ha
    obtain ⟨d', n', hf', hb⟩ := hb
    rw [hf] at hf'; cases hf'
    simp only [ordT, hf, Option.bind_some] at h
    have hfs : (Ty.tuple fs).isData = true := by simpa [Ty.isData, Ty.isDatass, Ty.isDatas] using ht
    match a, b, ha, hb with
    | .inr a, _, _, _ => exact nomatch a
    | .inl _, .inr b, _, _ => exact nomatch b
    | .inl a, .inl b, ha, hb =>
    erw [Ty.up_inl (i + 1) args fs [] ht hfs a] at ha
    erw [Ty.up_inl (i + 1) args fs [] ht hfs b] at hb
    obtain ⟨xv, hxv, ha⟩ := ha
    obtain ⟨yv, hyv, hb⟩ := hb
    have hfo := ordFields_rel L T d fs x y 0 p h hfs a b xv yv ha hb
      (fun i hi => by rw [Nat.zero_add, sel_ctor i hxv]; simp [hi])
      (fun i hi => by rw [Nat.zero_add, sel_ctor i hyv]; simp [hi])
    cases fs with
    | nil =>
      show OrdDen M p (Erl.cmp (.atom _) (.atom _))
      rw [Erl.cmp_atom, string_compare_self]; exact hfo
    | cons f fs =>
      show OrdDen M p (Erl.cmp (.tuple (.atom _ :: Ty.erls T (f :: fs) a)) (.tuple (.atom _ :: Ty.erls T (f :: fs) b)))
      rw [Erl.cmp_tuple, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [List.length_cons]; rw [erls_length, erls_length]))]
      simp only [Erl.cmps, Erl.cmp_atom, string_compare_self, Ordering.then]; exact hfo
  | .adt (_ + 1) _ [], _, _, _, _, _, a, _, _, _ => nomatch a
  | .adt (i + 1) args (f1 :: f2 :: vs), x, y, p, h, ht, a, b, ha, hb => by
    simp only [ordT] at h
    split at h
    · rename_i he
      obtain ⟨d, n, hf, ha⟩ := ha
      obtain ⟨d', n', hf', hb⟩ := hb
      rw [hf] at hf'; cases hf'
      simp only [hf, Option.map_some, Option.some.injEq] at h; subst h
      obtain ⟨kx, hkx, hxv, ex⟩ := enum_rel L T (variantsAt T (i + 1)) d (i + 1) args 0 _ he a ht _ ha
      obtain ⟨ky, hky, hyv, ey⟩ := enum_rel L T (variantsAt T (i + 1)) d (i + 1) args 0 _ he b ht _ hb
      simp only [Nat.zero_add] at hxv hyv ex ey
      have hlen : ((List.range (f1 :: f2 :: vs).length).map (atomAt (variantsAt T (i + 1)))).length =
          (f1 :: f2 :: vs).length := by simp
      have hisx : ∀ k, (Term.is d k x).denote M = .bool (k == kx) := fun k => by
        simp only [Term.denote, hxv, beq_self_eq_true, Bool.true_and]
        exact congrArg Val.bool (Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact eq_comm))
      have hisy : ∀ k, (Term.is d k y).denote M = .bool (k == ky) := fun k => by
        simp only [Term.denote, hyv, beq_self_eq_true, Bool.true_and]
        exact congrArg Val.bool (Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact eq_comm))
      have := enumOrd_den (isK := Term.is d) (x := x) (y := y)
        ((List.range (f1 :: f2 :: vs).length).map (atomAt (variantsAt T (i + 1))))
        (by rw [hlen]; exact hkx) (by rw [hlen]; exact hky) (fun k _ => hisx k) (fun k _ => hisy k)
      rw [getD_map_range _ hkx, getD_map_range _ hky] at this
      show OrdDen M _ (Erl.cmp (Ty.erlAlts T (variantsAt T (i + 1)) 0 _ a) (Ty.erlAlts T (variantsAt T (i + 1)) 0 _ b))
      rw [ex, ey, Erl.cmp_atom]; exact this
    · cases h
  | .list _, _, _, _, h, _, _, _, _, _ | .bag _, _, _, _, h, _, _, _, _, _ | .table .., _, _, _, h, _, _, _, _, _
  | .fn .., _, _, _, h, _, _, _, _, _ | .param _, _, _, _, h, _, _, _, _, _ | .dsl .., _, _, _, h, _, _, _, _, _ => by
    simp [ordT] at h
theorem ordFields_rel (L : Layout) (T : List TypeDecl) (d : Nat) : (ts : List Ty) → (x y : Term) → (j : Nat) →
    (p : Term × Term) → ordFields L T d ts x y j = some p → (hts : (Ty.tuple ts).isData = true) →
    (a b : (Ty.tuple ts).den0) → (xv yv : List Val) → RelVs L ts (Ty.up _ hts a) xv → RelVs L ts (Ty.up _ hts b) yv →
    (∀ i (hi : i < xv.length), (Term.sel d 0 (j + i) x).denote M = xv[i]) →
    (∀ i (hi : i < yv.length), (Term.sel d 0 (j + i) y).denote M = yv[i]) →
    OrdDen M p (Erl.cmps (Ty.erls T ts a) (Ty.erls T ts b))
  | [], _, _, _, p, h, _, _, _, _, _, _, _, _, _ => by
    simp only [ordFields, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl⟩
  | t :: ts, x, y, j, p, h, hts, (a, as), (b, bs), xv, yv, ha, hb, hx, hy => by
    have ht : t.isData = true := by simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at hts; exact hts.1
    have hts' : (Ty.tuple ts).isData = true := by
      simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at hts ⊢; exact hts.2
    erw [Ty.up_tuple t ts hts ht hts'] at ha hb
    obtain ⟨v, vs, rfl, hav, has⟩ := ha
    obtain ⟨w, ws, rfl, hbw, hbs⟩ := hb
    obtain ⟨p1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨p2, h2, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have e0 := hx 0 (by simp); have f0 := hy 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at e0 f0
    have r1 := ordT_rel L T t _ _ p1 h1 ht a b (by rw [e0]; exact hav) (by rw [f0]; exact hbw)
    have r2 := ordFields_rel L T d ts x y (j + 1) p2 h2 hts' as bs vs ws has hbs
      (fun i hi => by have := hx (i + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      (fun i hi => by have := hy (i + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    exact lexT_den r1 r2
end

end

end Tazuna.Smt
