import Tazuna.Semantics.Rename

/-! Moving every instant by one amount keeps the canonical order. Two values of one type related by a renaming that
keeps every name (`Ty.rel0 R` with `R.rel` equality) differ only in their instants, each moved by `R`'s shift, and
they compare as the originals do (`Ty.cmp_shift`): at a place where the two terms first differ both hold instants, or
both hold the same tag, size or name, and moving both instants by one amount keeps their order. So a machine's keys
sort the same way after a time shift, whatever instants they hold. -/

namespace Tazuna.Ir

namespace Erl

theorem cmp_list_nil_cons (y : Erl) (ys : List Erl) : cmp (.list []) (.list (y :: ys)) = .lt := by
  simp [cmp, ser, serl, List.compareLex_cons_cons, Tok.cmp]; rfl

theorem cmp_list_cons_nil (x : Erl) (xs : List Erl) : cmp (.list (x :: xs)) (.list []) = .gt := by
  simp [cmp, ser, serl, List.compareLex_cons_cons, Tok.cmp]; rfl

theorem cmp_list_cons (x y : Erl) (xs ys : List Erl) :
    cmp (.list (x :: xs)) (.list (y :: ys)) = (cmp x y).then (cmp (.list xs) (.list ys)) := by
  have e : ∀ a : Int, Tok.cmp (.num a) (.num a) = .eq := fun a => by
    unfold Tok.cmp; exact Std.ReflCmp.compare_self (cmp := (compare : Int → Int → Ordering))
  simp only [cmp, ser, serl, List.compareLex_cons_cons, e, Ordering.then]
  exact ser_then x y _ _

/-- A table's term compares by size, then keys, then values. -/
theorem cmp_map (ks vs ks' vs' : List Erl) (h : ks.length = vs.length) (h' : ks'.length = vs'.length) :
    cmp (.map ks vs) (.map ks' vs') =
      if ks.length = ks'.length then (cmps ks ks').then (cmps vs vs') else compare ks.length ks'.length := by
  simp only [cmp, ser, List.compareLex_cons_cons, Tok.cmp]
  split
  · rename_i hl
    have hv : vs.length = vs'.length := h.symm.trans (hl.trans h')
    have cs : ∀ a : Int, compare a a = .eq := fun _ => Std.ReflCmp.compare_self (cmp := (compare : Int → Int → Ordering))
    rw [hl, sers_then ks ks' hl, hv]
    simp only [List.compareLex_cons_cons, Tok.cmp, cs, Ordering.then]
    have := sers_then vs vs' hv [] []
    simp only [List.append_nil, List.compareLex_nil_nil] at this
    rw [this]
    cases cmps ks ks' <;> cases cmps vs vs' <;> rfl
  · rename_i hl
    have hc : compare (ks.length : Int) ks'.length = compare ks.length ks'.length := by
      simp only [compare, compareOfLessAndEq]
      split <;> split <;> (try split) <;> (try split) <;> first | rfl | omega
    have h' : compare (ks.length : Int) ks'.length ≠ .eq := by
      intro e; exact hl (by have := Std.LawfulEqCmp.eq_of_compare e; omega)
    simp only [Ordering.then]
    rw [← hc]
    cases compare (ks.length : Int) ks'.length <;> simp_all

/-- A term's head as a variant writes it: an atom alone, or a tuple of an atom and its fields. Terms with the same
head and as many fields compare with any other term by the head alone, when the other's atom differs. -/
def SameHead (e e' : Erl) : Prop :=
  (∃ a, e = .atom a ∧ e' = .atom a) ∨ ∃ a xs xs', e = .tuple (.atom a :: xs) ∧ e' = .tuple (.atom a :: xs') ∧
    xs.length = xs'.length

theorem then_of_ne {o : Ordering} (h : o ≠ .eq) (o' : Ordering) : o.then o' = o := by
  cases o <;> first | rfl | exact absurd rfl h

theorem cmp_heads {e1 e1' e2 e2' : Erl} (h1 : SameHead e1 e1') (h2 : SameHead e2 e2') (ht : e1.tag ≠ e2.tag) :
    cmp e1 e2 = cmp e1' e2' := by
  rcases h1 with ⟨a, rfl, rfl⟩ | ⟨a, xs, xs', rfl, rfl, hx⟩ <;>
    rcases h2 with ⟨b, rfl, rfl⟩ | ⟨b, ys, ys', rfl, rfl, hy⟩
  · rfl
  · simp [cmp, ser, List.compareLex_cons_cons, Tok.cmp]
  · simp [cmp, ser, List.compareLex_cons_cons, Tok.cmp]
  · have hab : a ≠ b := fun e => ht (by simp [tag, e])
    have hne : cmp (.atom a) (.atom b) ≠ .eq := by
      rw [cmp_atom]; exact fun e => hab (Std.LawfulEqCmp.eq_of_compare e)
    rw [cmp_tuple, cmp_tuple]
    simp only [List.length_cons, hx, hy]
    split
    · simp only [cmps, then_of_ne hne]
    · rfl

/-- Lists related item by item by `E`, which keeps comparisons, compare alike. -/
theorem cmp_list_congr {E : Erl → Erl → Prop} (hE : ∀ a a' b b', E a a' → E b b' → cmp a b = cmp a' b') :
    {xs xs' ys ys' : List Erl} → Forall2 E xs xs' → Forall2 E ys ys' →
      cmp (.list xs) (.list ys) = cmp (.list xs') (.list ys')
  | [], [], [], [], _, _ => rfl
  | [], [], _ :: _, _ :: _, _, _ => by rw [cmp_list_nil_cons, cmp_list_nil_cons]
  | _ :: _, _ :: _, [], [], _, _ => by rw [cmp_list_cons_nil, cmp_list_cons_nil]
  | _ :: _, _ :: _, _ :: _, _ :: _, ⟨hx, hxs⟩, ⟨hy, hys⟩ => by
    rw [cmp_list_cons, cmp_list_cons, hE _ _ _ _ hx hy, cmp_list_congr hE hxs hys]
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ | _, _, [], _ :: _, _, h | _, _, _ :: _, [], _, h => h.elim

theorem cmps_congr {E : Erl → Erl → Prop} (hE : ∀ a a' b b', E a a' → E b b' → cmp a b = cmp a' b') :
    {xs xs' ys ys' : List Erl} → Forall2 E xs xs' → Forall2 E ys ys' → cmps xs ys = cmps xs' ys'
  | [], [], _, _, _, _ => by cases ‹List Erl› <;> cases ‹List Erl› <;> rfl
  | _ :: _, _ :: _, [], [], _, _ => rfl
  | _ :: _, _ :: _, _ :: _, _ :: _, ⟨hx, hxs⟩, ⟨hy, hys⟩ => by
    simp only [cmps, hE _ _ _ _ hx hy, cmps_congr hE hxs hys]
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ | _ :: _, _ :: _, [], _ :: _, _, h
  | _ :: _, _ :: _, _ :: _, [], _, h => h.elim

/-- Sorting lists related item by item by `E`, which keeps comparisons, keeps them related item by item. -/
theorem sort_forall2 {α : Type} [Ord α] {E : α → α → Prop}
    (hE : ∀ a a' b b', E a a' → E b b' → compare a b = compare a' b') {xs xs' : List α} (h : Forall2 E xs xs') :
    Forall2 E (sort xs) (sort xs') :=
  forall2_mergeSort h fun a b a' b' ha hb => by rw [hE a a' b b' ha hb]

end Erl

section
variable (T : List TypeDecl) {R : PBij}
attribute [local instance] lexOrd

/-- Erlang terms of values of `t` related by `R`. -/
def ErlRel (R : PBij) (t : Ty) (e e' : Erl) : Prop := ∃ a a', Ty.rel0 R t a a' ∧ e = t.erl T a ∧ e' = t.erl T a'

theorem erls_length : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (Ty.erls T ts x).length = ts.length
  | [], () => rfl
  | _ :: ts, (_, xs) => by simp only [Ty.erls, List.length_cons, erls_length ts xs]

theorem Ty.erlAlts_sameHead (decl : List Variant) : (j : Nat) → (vs : List (List Ty)) →
    {x x' : (Ty.semAltsWith Dsl.base vs).1} → Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x x' →
    Erl.SameHead (Ty.erlAlts T decl j vs x) (Ty.erlAlts T decl j vs x')
  | _, [], x, _, _ => nomatch x
  | _, [] :: _, .inl (), .inl (), _ => .inl ⟨_, rfl, rfl⟩
  | _, (f :: fs) :: _, .inl x, .inl x', _ =>
    .inr ⟨_, _, _, rfl, rfl, by rw [erls_length, erls_length]⟩
  | j, _ :: vs, .inr _, .inr _, h => by simp only [Ty.erlAlts]; exact Ty.erlAlts_sameHead decl (j + 1) vs h
  | _, _ :: _, .inl _, .inr _, h | _, _ :: _, .inr _, .inl _, h => h.elim

theorem cmp_int_add (a b d : Int) : Erl.cmp (.int (a + d)) (.int (b + d)) = Erl.cmp (.int a) (.int b) := by
  rw [Erl.cmp_int, Erl.cmp_int]
  simp only [compare, compareOfLessAndEq]
  split <;> split <;> (try split) <;> (try split) <;> first | rfl | omega

/-- A renaming that keeps the order of the counters it relates, as a rank does: the canonical order compares fresh ids
by their counters, so such a renaming keeps it. -/
def _root_.Tazuna.Ir.PBij.Mono (R : PBij) : Prop := ∀ {a b a' b'}, R.rel a b → R.rel a' b' → compare a a' = compare b b'

theorem _root_.Tazuna.Ir.PBij.mono_of_eq {R : PBij} (hR : ∀ {a b}, R.rel a b → a = b) : R.Mono := by
  intro a b a' b' h h'
  obtain rfl := hR h
  obtain rfl := hR h'
  rfl

theorem cmp_nat_mono (hR : R.Mono) {a b a' b' : Nat} (h : R.rel a b) (h' : R.rel a' b') :
    Erl.cmp (.int a) (.int a') = Erl.cmp (.int b) (.int b') := by
  rw [Erl.cmp_int, Erl.cmp_int, Erl.compare_int_nat, Erl.compare_int_nat, hR h h']

mutual
/-- Values related by a renaming that keeps every name compare as the originals do. -/
theorem Ty.cmp_shift (hR : R.Mono) : (t : Ty) → t.ordered T = true → {x x' y y' : t.den0} → Ty.rel0 R t x x' →
    Ty.rel0 R t y y' → Erl.cmp (t.erl T x) (t.erl T y) = Erl.cmp (t.erl T x') (t.erl T y')
  | .int, _, _, _, _, _, hx, hy | .str, _, _, _, _, _, hx, hy => by
    have hx : _ = _ := hx; have hy : _ = _ := hy; subst hx hy; rfl
  | .point .day, _, _, _, _, _, hx, hy => by
    have hx : _ = _ := hx; have hy : _ = _ := hy; subst hx hy; rfl
  | .point .ms, _, x, x', y, y', hx, hy => by
    show Erl.cmp (.int x) (.int y) = Erl.cmp (.int x') (.int y')
    rw [PBij.point_ms_eq hx, PBij.point_ms_eq hy]
    exact (cmp_int_add x y R.shiftMs).symm
  | .id, _, _, _, _, _, hx, hy => by
    rcases hx with ⟨s, rfl, rfl⟩ | ⟨c, c', i, hc, rfl, rfl⟩ <;>
      rcases hy with ⟨s', rfl, rfl⟩ | ⟨e, e', j, he, rfl, rfl⟩
    · rfl
    · show Erl.cmp (.bin _) (.tuple _) = Erl.cmp (.bin _) (.tuple _)
      rw [Erl.cmp_bin_tuple, Erl.cmp_bin_tuple]
    · show Erl.cmp (.tuple _) (.bin _) = Erl.cmp (.tuple _) (.bin _)
      rw [Erl.cmp_tuple_bin, Erl.cmp_tuple_bin]
    · show Erl.cmp (.tuple [.int c, .int i]) (.tuple [.int e, .int j]) =
        Erl.cmp (.tuple [.int c', .int i]) (.tuple [.int e', .int j])
      rw [Erl.cmp_pair, Erl.cmp_pair, cmp_nat_mono hR hc he]
  | .param _, _, _, _, _, _, _, _ => rfl
  | .dsl k _, h, x, x', y, y', hx, hy => by
    cases k <;> simp [Ty.ordered] at h
    exact cmp_nat_mono hR hx hy
  | .fn .., h, _, _, _, _, _, _ => by simp [Ty.ordered] at h
  | .list t, h, xs, xs', ys, ys', hx, hy => by
    have hE : ∀ a a' b b', ErlRel T R t a a' → ErlRel T R t b b' → Erl.cmp a b = Erl.cmp a' b' := by
      rintro _ _ _ _ ⟨a, a', ha, rfl, rfl⟩ ⟨b, b', hb, rfl, rfl⟩
      exact Ty.cmp_shift hR t h ha hb
    have rel : ∀ {l l'}, Forall2 (Ty.rel0 R t) l l' → Forall2 (ErlRel T R t) (l.map (t.erl T)) (l'.map (t.erl T)) :=
      fun hl => forall2_map2 (fun a a' ha => ⟨a, a', ha, rfl, rfl⟩) hl
    exact Erl.cmp_list_congr hE (rel hx) (rel hy)
  | .bag t, h, xs, xs', ys, ys', hx, hy => by
    have hE : ∀ a a' b b', ErlRel T R t a a' → ErlRel T R t b b' → Erl.cmp a b = Erl.cmp a' b' := by
      rintro _ _ _ _ ⟨a, a', ha, rfl, rfl⟩ ⟨b, b', hb, rfl, rfl⟩
      exact Ty.cmp_shift hR t h ha hb
    have rel : ∀ {l l'}, Multi (Ty.rel0 R t) l l' →
        Forall2 (ErlRel T R t) (Erl.sort (l.map (t.erl T))) (Erl.sort (l'.map (t.erl T))) := by
      rintro l l' ⟨zs, hz, hp⟩
      rw [← (Erl.sort_eq_iff _ _).2 (hp.map (t.erl T))]
      exact Erl.sort_forall2 hE (forall2_map2 (fun a a' ha => ⟨a, a', ha, rfl, rfl⟩) hz)
    exact Erl.cmp_list_congr hE (rel hx) (rel hy)
  | .table k v, h, x, x', y, y', hx, hy => by
    simp only [Ty.ordered, Bool.and_eq_true] at h
    let P (e e' : Erl × Erl) : Prop := ErlRel T R k e.1 e'.1 ∧ ErlRel T R v e.2 e'.2
    have hEk : ∀ a a' b b', ErlRel T R k a a' → ErlRel T R k b b' → Erl.cmp a b = Erl.cmp a' b' := by
      rintro _ _ _ _ ⟨a, a', ha, rfl, rfl⟩ ⟨b, b', hb, rfl, rfl⟩
      exact Ty.cmp_shift hR k h.1 ha hb
    have hEv : ∀ a a' b b', ErlRel T R v a a' → ErlRel T R v b b' → Erl.cmp a b = Erl.cmp a' b' := by
      rintro _ _ _ _ ⟨a, a', ha, rfl, rfl⟩ ⟨b, b', hb, rfl, rfl⟩
      exact Ty.cmp_shift hR v h.2 ha hb
    have hP : ∀ p p' q q', P p p' → P q q' → compare p q = compare p' q' := by
      intro p p' q q' hp hq
      show (Erl.cmp p.1 q.1).then (Erl.cmp p.2 q.2) = (Erl.cmp p'.1 q'.1).then (Erl.cmp p'.2 q'.2)
      rw [hEk _ _ _ _ hp.1 hq.1, hEv _ _ _ _ hp.2 hq.2]
    let pairs (z : (Ty.table k v).den0) : List (Erl × Erl) := z.1.map fun e => (k.erl T e.1, v.erl T e.2)
    have rel : ∀ {z z' : (Ty.table k v).den0}, Ty.rel0 R (.table k v) z z' →
        Forall2 P (Erl.sort (pairs z)) (Erl.sort (pairs z')) := by
      rintro z z' ⟨zs, hz, hp⟩
      show Forall2 P (Erl.sort (z.1.map _)) (Erl.sort (z'.1.map _))
      rw [← (Erl.sort_eq_iff _ _).2 (hp.map (fun e => (k.erl T e.1, v.erl T e.2)))]
      exact Erl.sort_forall2 hP (forall2_map2 (fun a a' ha => ⟨⟨a.1, a'.1, ha.1, rfl, rfl⟩, ⟨a.2, a'.2, ha.2, rfl, rfl⟩⟩) hz)
    have hrx := rel hx
    have hry := rel hy
    show Erl.cmp (.map ((Erl.sort (pairs x)).map (·.1)) ((Erl.sort (pairs x)).map (·.2)))
        (.map ((Erl.sort (pairs y)).map (·.1)) ((Erl.sort (pairs y)).map (·.2))) =
      Erl.cmp (.map ((Erl.sort (pairs x')).map (·.1)) ((Erl.sort (pairs x')).map (·.2)))
        (.map ((Erl.sort (pairs y')).map (·.1)) ((Erl.sort (pairs y')).map (·.2)))
    rw [Erl.cmp_map _ _ _ _ (by simp) (by simp), Erl.cmp_map _ _ _ _ (by simp) (by simp)]
    simp only [List.length_map, forall2_length hrx, forall2_length hry]
    split
    · rw [Erl.cmps_congr hEk (forall2_map2 (fun _ _ h => h.1) hrx) (forall2_map2 (fun _ _ h => h.1) hry),
        Erl.cmps_congr hEv (forall2_map2 (fun _ _ h => h.2) hrx) (forall2_map2 (fun _ _ h => h.2) hry)]
    · rfl
  | .tuple ts, h, x, x', y, y', hx, hy => by
    show Erl.cmp (.tuple (Ty.erls T ts x)) (.tuple (Ty.erls T ts y)) =
      Erl.cmp (.tuple (Ty.erls T ts x')) (.tuple (Ty.erls T ts y'))
    rw [Erl.cmp_tuple, Erl.cmp_tuple,
      ite_eq_left_of_eq_true _ _ (eq_true ((erls_length T ts x).trans (erls_length T ts y).symm)),
      ite_eq_left_of_eq_true _ _ (eq_true ((erls_length T ts x').trans (erls_length T ts y').symm))]
    exact Ty.cmps_shift hR ts h hx hy
  | .adt i _ vs, h, x, x', y, y', hx, hy => by
    simp only [Ty.ordered, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Ty.cmpAlts_shift hR (variantsAt T i) 0 vs h.2 (by simpa using h.1) hx hy
theorem Ty.cmps_shift (hR : R.Mono) : (ts : List Ty) → Ty.ordereds T ts = true → {x x' y y' : (Ty.semsWith Dsl.base ts).1} →
    Ty.relsWith Dsl.base (Dsl.rel0 R) R ts x x' → Ty.relsWith Dsl.base (Dsl.rel0 R) R ts y y' →
    Erl.cmps (Ty.erls T ts x) (Ty.erls T ts y) = Erl.cmps (Ty.erls T ts x') (Ty.erls T ts y')
  | [], _, _, _, _, _, _, _ => rfl
  | t :: ts, h, (_, _), (_, _), (_, _), (_, _), ⟨hx, hxs⟩, ⟨hy, hys⟩ => by
    simp only [Ty.ordereds, Bool.and_eq_true] at h
    simp only [Ty.erls, Erl.cmps, Ty.cmp_shift hR t h.1 hx hy, Ty.cmps_shift hR ts h.2 hxs hys]
theorem Ty.cmpAlts_shift (hR : R.Mono) (decl : List Variant) : (j : Nat) → (vs : List (List Ty)) → Ty.orderedss T vs = true →
    ((List.range vs.length).map fun m => atomAt decl (j + m)).Nodup →
    {x x' y y' : (Ty.semAltsWith Dsl.base vs).1} → Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs x x' →
    Ty.relAltsWith Dsl.base (Dsl.rel0 R) R vs y y' →
    Erl.cmp (Ty.erlAlts T decl j vs x) (Ty.erlAlts T decl j vs y) =
      Erl.cmp (Ty.erlAlts T decl j vs x') (Ty.erlAlts T decl j vs y')
  | _, [], _, _, x, _, _, _, _, _ => nomatch x
  | _, [] :: _, _, _, .inl (), .inl (), .inl (), .inl (), _, _ => rfl
  | j, (f :: fs) :: _, h, _, .inl x, .inl x', .inl y, .inl y', hx, hy => by
    simp only [Ty.orderedss, Bool.and_eq_true] at h
    show Erl.cmp (.tuple (.atom _ :: Ty.erls T (f :: fs) x)) (.tuple (.atom _ :: Ty.erls T (f :: fs) y)) =
      Erl.cmp (.tuple (.atom _ :: Ty.erls T (f :: fs) x')) (.tuple (.atom _ :: Ty.erls T (f :: fs) y'))
    have lx : (Erl.atom (atomAt decl j) :: Ty.erls T (f :: fs) x).length =
        (Erl.atom (atomAt decl j) :: Ty.erls T (f :: fs) y).length := by
      simp only [List.length_cons]; rw [erls_length, erls_length]
    have lx' : (Erl.atom (atomAt decl j) :: Ty.erls T (f :: fs) x').length =
        (Erl.atom (atomAt decl j) :: Ty.erls T (f :: fs) y').length := by
      simp only [List.length_cons]; rw [erls_length, erls_length]
    rw [Erl.cmp_tuple, Erl.cmp_tuple, ite_eq_left_of_eq_true _ _ (eq_true lx), ite_eq_left_of_eq_true _ _ (eq_true lx')]
    simp only [Erl.cmps]
    rw [Ty.cmps_shift hR (f :: fs) h.1 hx hy]
  | j, _ :: vs, h, hd, .inr _, .inr _, .inr _, .inr _, hx, hy => by
    simp only [Ty.orderedss, Bool.and_eq_true] at h
    simp only [Ty.erlAlts]
    exact Ty.cmpAlts_shift hR decl (j + 1) vs h.2 (atoms_head hd).2 hx hy
  | j, fs :: vs, _, hd, .inl x, .inl x', .inr y, .inr y', hx, hy => by
    refine Erl.cmp_heads (Ty.erlAlts_sameHead T decl j (fs :: vs) (x := .inl x) (x' := .inl x') hx)
      (Ty.erlAlts_sameHead T decl j (fs :: vs) (x := .inr y) (x' := .inr y') hy) fun e => ?_
    obtain ⟨m, hm, ht⟩ := Ty.erlAlts_tag T decl (j + 1) vs y
    rw [Ty.erlAlts_tag_inl] at e
    simp only [Ty.erlAlts] at e
    rw [ht, Option.some.injEq] at e
    exact (atoms_head hd).1 m hm e
  | j, fs :: vs, _, hd, .inr x, .inr x', .inl y, .inl y', hx, hy => by
    refine Erl.cmp_heads (Ty.erlAlts_sameHead T decl j (fs :: vs) (x := .inr x) (x' := .inr x') hx)
      (Ty.erlAlts_sameHead T decl j (fs :: vs) (x := .inl y) (x' := .inl y') hy) fun e => ?_
    obtain ⟨m, hm, ht⟩ := Ty.erlAlts_tag T decl (j + 1) vs x
    rw [Ty.erlAlts_tag_inl] at e
    simp only [Ty.erlAlts] at e
    rw [ht, Option.some.injEq] at e
    exact (atoms_head hd).1 m hm e.symm
  | _, _ :: _, _, _, .inl _, .inr _, _, _, hx, _ | _, _ :: _, _, _, .inr _, .inl _, _, _, hx, _
  | _, _ :: _, _, _, _, _, .inl _, .inr _, _, hy | _, _ :: _, _, _, _, _, .inr _, .inl _, _, hy => by
    first | exact hx.elim | exact hy.elim
end

end

end Tazuna.Ir
