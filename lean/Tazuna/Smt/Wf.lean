import Tazuna.Smt.Decode

/-! Well-formedness: the Bool term that holds exactly when a model's value of a first-order type decodes. A script
asserts it of its symbolic state, so every model it returns is a real state, and it loses no state, since every
embedded value satisfies it. What the term asks is what decoding asks beyond the sort: the occupied slots of a table
hold distinct keys, and fresh-id counters and fresh ids are not negative. `wf_iff` proves it for every value of the
type's sort (`Sorted`), which every model of a well-sorted script gives. -/

namespace Tazuna.Smt

open Tazuna.Ir

mutual
/-- The term that writes a value as a constant. -/
def Val.term : Val → Term
  | .int n => .int n
  | .bool b => .bool b
  | .str s => .str s
  | .ctor d k args => .ctor d k (Val.terms args)
def Val.terms : List Val → List Term
  | [] => []
  | w :: ws => w.term :: Val.terms ws
end

mutual
theorem Val.denote_term (M : Model) : (w : Val) → w.term.denote M = w
  | .int _ | .bool _ | .str _ => rfl
  | .ctor d k args => by simp only [Val.term, Term.denote, Val.denotes_terms M args]
theorem Val.denotes_terms (M : Model) : (ws : List Val) → Term.denotes M (Val.terms ws) = ws
  | [] => rfl
  | w :: ws => by simp only [Val.terms, Term.denotes, Val.denote_term M w, Val.denotes_terms M ws]
end

section
variable (L : Layout)

/-- Whether no two occupied slots hold the same key (the first item), by SMT-LIB's `=` in either direction. -/
def distinctT : List Slot → Term
  | [] => tt
  | (f, xs) :: S => .and (allT (S.map fun sl : Slot =>
      .not (.and (.and f sl.1) (.or (.eq (xs.headD tt) (sl.2.headD tt)) (.eq (sl.2.headD tt) (xs.headD tt))))))
    (distinctT S)

mutual
/-- The well-formedness of the value `x` of type `t`; none for a type without a decoding, or a table whose keys'
`==` is not SMT-LIB's `=`. -/
def wfT : Ty → Term → Option Term
  | .int, _ | .str, _ | .date, _ => some tt
  | .dsl .fresh _, x => some (.le (.int 0) x)
  | .id, x => (L.find? .id).map fun (d, _) => .or (.not (.is d 0 x)) (.le (.int 0) (.sel d 0 0 x))
  | .adt 0 _ vs, _ => if (boolVs? vs).isSome then some tt else none
  | .adt (i + 1) a vs, x => (L.find? (.adt (i + 1) a vs)).bind fun (d, _) => wfAlts d 0 vs x
  | .tuple ts, x => (L.find? (.tuple ts)).bind fun (d, _) => wfFields d 0 ts x 0
  | .bag t, x => match L.find? (.bag t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, n), some (dt, _) =>
      ((slotsOf d dt n 1 x).mapM fun sl : Slot => (wfT t (sl.2.headD tt)).map (Term.or (.not sl.1) ·)).map allT
    | _, _ => none
  | .list t, x => match L.find? (.list t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, n), some (dt, _) =>
      ((slotsOf d dt n 1 x).mapM fun sl : Slot => (wfT t (sl.2.headD tt)).map (Term.or (.not sl.1) ·)).map allT
    | _, _ => none
  | .table k w, x => match L.find? (.table k w), L.find? (.tuple [Ty.bool, k, w]) with
    | some (d, n), some (dt, _) =>
      if k.eqable then
        ((slotsOf d dt n 2 x).mapM fun sl : Slot => ((wfT k (sl.2.headD tt)).bind fun ck =>
          (wfT w (sl.2.getD 1 tt)).map fun cw => Term.and ck cw).map (Term.or (.not sl.1) ·)).map fun cs =>
            .and (allT cs) (distinctT (slotsOf d dt n 2 x))
      else none
    | _, _ => none
  | _, _ => none
/-- The fields' well-formedness, from field `j` of constructor `k` of datatype `d`. -/
def wfFields (d k : Nat) : List Ty → Term → Nat → Option Term
  | [], _, _ => some tt
  | t :: ts, x, j => (wfT t (.sel d k j x)).bind fun c => (wfFields d k ts x (j + 1)).map (.and c)
/-- The well-formedness of whichever constructor, from `k`, built `x`. -/
def wfAlts (d : Nat) : Nat → List (List Ty) → Term → Option Term
  | _, [], _ => some (.bool false)
  | k, fs :: vs, x => (wfFields d k fs x 0).bind fun c => (wfAlts d (k + 1) vs x).map (.ite (.is d k x) c)
end

mutual
/-- The value has the shape of the type's sort, as every value of a well-sorted model does: slots for a bag or
table or list, a declared constructor for an ADT. The items of free slots are left open: no value reads them. -/
def Sorted : Ty → Val → Prop
  | .int, w | .date, w | .dsl .fresh _, w => ∃ n, w = .int n
  | .str, w => ∃ s, w = .str s
  | .id, w => ∃ d n, L.find? .id = some (d, n) ∧ ((∃ m, w = .ctor d 0 [.int m]) ∨ ∃ s, w = .ctor d 1 [.str s])
  | .adt 0 _ vs, w => vs = [[], []] ∧ ∃ b, w = .bool b
  | .adt (i + 1) a vs, w => ∃ d n, L.find? (.adt (i + 1) a vs) = some (d, n) ∧ SortedAlts d 0 vs w
  | .tuple ts, w => ∃ d n vals, L.find? (.tuple ts) = some (d, n) ∧ w = .ctor d 0 vals ∧ SortedVs ts vals
  | .bag t, w => ∃ d n dt m sv, L.find? (.bag t) = some (d, n) ∧ L.find? (.tuple [Ty.bool, t]) = some (dt, m) ∧
      collView d dt n 1 w = some sv ∧ ∀ p ∈ sv, p.1 = true → ∀ z, p.2 = [z] → Sorted t z
  | .list t, w => ∃ d n dt m sv, L.find? (.list t) = some (d, n) ∧ L.find? (.tuple [Ty.bool, t]) = some (dt, m) ∧
      collView d dt n 1 w = some sv ∧ ∀ p ∈ sv, p.1 = true → ∀ z, p.2 = [z] → Sorted t z
  | .table k v, w => ∃ d n dt m sv, L.find? (.table k v) = some (d, n) ∧
      L.find? (.tuple [Ty.bool, k, v]) = some (dt, m) ∧ collView d dt n 2 w = some sv ∧
      ∀ p ∈ sv, p.1 = true → ∀ zk zv, p.2 = [zk, zv] → Sorted k zk ∧ Sorted v zv
  | _, _ => False
def SortedVs : List Ty → List Val → Prop
  | [], [] => True
  | t :: ts, w :: ws => Sorted t w ∧ SortedVs ts ws
  | _, _ => False
def SortedAlts (d : Nat) : Nat → List (List Ty) → Val → Prop
  | _, [], _ => False
  | k, fs :: vs, w => ∃ k' vals, w = .ctor d k' vals ∧ ((k' = k ∧ SortedVs fs vals) ∨ (k' ≠ k ∧ SortedAlts d (k + 1) vs w))
end

end

section
variable {M : Model} {L : Layout}

theorem anyT_denote : (ts : List Term) → (anyT ts).denote M = .bool (ts.any fun t => (t.denote M).toBool)
  | [] => rfl
  | t :: ts => by simp [anyT, Term.denote, anyT_denote ts, Val.toBool]

theorem allT_denote : (ts : List Term) → (allT ts).denote M = .bool (ts.all fun t => (t.denote M).toBool)
  | [] => rfl
  | t :: ts => by simp [allT, Term.denote, allT_denote ts, Val.toBool]

theorem holds_allT (cs : List Term) : Holds M (allT cs) ↔ ∀ c ∈ cs, Holds M c := by
  simp [Holds, allT_denote, Val.toBool]

theorem holds_or_not (f c : Term) (b : Bool) (hf : f.denote M = .bool b) :
    Holds M (.or (.not f) c) ↔ (b = true → Holds M c) := by
  cases b <;> simp [Holds, Term.denote, hf, Val.toBool]

theorem headD_denote (xs : List Term) : (xs.headD tt).denote M = (Term.denotes M xs).headD (.bool true) := by
  cases xs <;> rfl

theorem getD1_denote (xs : List Term) : (xs.getD 1 tt).denote M = (Term.denotes M xs).getD 1 (.bool true) := by
  match xs with
  | [] | [_] => rfl
  | _ :: _ :: _ => rfl

theorem mapM_isSome {α β : Type} (f : α → Option β) : (xs : List α) → (xs.mapM f).isSome = xs.all fun x => (f x).isSome
  | [] => rfl
  | x :: xs => by
    cases h : f x <;> simp [List.mapM_cons, h, ← mapM_isSome f xs]; cases xs.mapM f <;> rfl

/-- The slot-wise part of well-formedness: a term per slot that holds when the slot is free or its items `P`. -/
theorem slots_all {g : List Term → Option Term} {P : List Val → Bool} {Q : List Val → Prop}
    (hg : ∀ xs c, g xs = some c → Q (Term.denotes M xs) → (Holds M c ↔ P (Term.denotes M xs) = true)) :
    (S : List Slot) → (sv : List (Bool × List Val)) → SlotsDen M S sv → (∀ p ∈ sv, p.1 = true → Q p.2) →
    (cs : List Term) →
    S.mapM (fun sl : Slot => (g sl.2).map (Term.or (.not sl.1) ·)) = some cs →
    (Holds M (allT cs) ↔ (occupied sv).all P = true)
  | [], [], _, _, cs, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp [Holds, allT, tt, Term.denote, Val.toBool, occupied]
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩, hQ, cs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c0, h0, cs', hcs, rfl⟩ := h
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h0
    have ih := slots_all hg S sv hS (fun p hp => hQ p (by simp [hp])) cs' hcs
    simp only [allT]
    rw [holds_and, holds_or_not f c b hf, ih]
    cases b with
    | false => simp [occupied]
    | true =>
      have hgc := hg xs c hc (hxs ▸ hQ (true, vs) (by simp) rfl)
      rw [hxs] at hgc
      rw [hgc]; simp [occupied]

/-- `distinctT` holds when the occupied slots' keys differ pairwise. -/
theorem distinctT_den : (S : List Slot) → (sv : List (Bool × List Val)) → SlotsDen M S sv →
    (Holds M (distinctT S) ↔ (occupied sv).Pairwise fun a b =>
      (a.headD (.bool true) == b.headD (.bool true)) = false ∧ (b.headD (.bool true) == a.headD (.bool true)) = false)
  | [], [], _ => by simp [distinctT, Holds, tt, Term.denote, Val.toBool, occupied]
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩ => by
    have ih := distinctT_den S sv hS
    have hrow : Holds M (allT (S.map fun sl : Slot =>
        .not (.and (.and f sl.1) (.or (.eq (xs.headD tt) (sl.2.headD tt)) (.eq (sl.2.headD tt) (xs.headD tt)))))) ↔
        (b = true → ∀ q ∈ occupied sv, (vs.headD (.bool true) == q.headD (.bool true)) = false ∧
          (q.headD (.bool true) == vs.headD (.bool true)) = false) := by
      clear ih
      induction S generalizing sv with
      | nil => cases sv with
        | nil => simp [allT, Holds, tt, Term.denote, Val.toBool, occupied]
        | cons _ _ => exact hS.elim
      | cons s S ih' =>
        obtain ⟨f', xs'⟩ := s
        match sv, hS with
        | (b', vs') :: sv', ⟨hf', hxs', hS'⟩ =>
          have := ih' sv' hS'
          simp only [List.map_cons, allT]
          rw [holds_and, this]
          simp only [Holds, Term.denote, hf, hf', headD_denote, hxs, hxs', Val.toBool]
          cases b <;> cases b' <;> simp [occupied]
    simp only [distinctT]
    rw [holds_and, hrow, ih]
    cases b <;> simp [occupied, List.pairwise_cons]

theorem isSome_map {α β : Type} (f : α → β) (o : Option α) : (o.map f).isSome = o.isSome := by cases o <;> rfl

theorem forall2_all {α β : Type} {E : α → β → Prop} {P : α → Prop} {R : β → Prop} (hPR : ∀ a b, E a b → (P a ↔ R b)) :
    (as : List α) → (bs : List β) → Forall2 E as bs → ((∀ a ∈ as, P a) ↔ ∀ b ∈ bs, R b)
  | [], [], _ => by simp
  | a :: as, b :: bs, ⟨hab, h⟩ => by simp only [List.mem_cons, forall_eq_or_imp, hPR a b hab, forall2_all hPR as bs h]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem pairwise_forall2 {α β : Type} {E : α → β → Prop} {P : α → α → Prop} {R : β → β → Prop}
    (hPR : ∀ a b a' b', E a b → E a' b' → (P a a' ↔ R b b')) :
    (as : List α) → (bs : List β) → Forall2 E as bs → (as.Pairwise P ↔ bs.Pairwise R)
  | [], [], _ => by simp
  | a :: as, b :: bs, ⟨hab, h⟩ => by
    rw [List.pairwise_cons, List.pairwise_cons, pairwise_forall2 hPR as bs h,
      forall2_all (fun a' b' h' => hPR a b a' b' hab h') as bs h]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem singleton_terms {xs : List Term} {z : Val} (h : Term.denotes M xs = [z]) : ∃ x, xs = [x] ∧ x.denote M = z := by
  match xs, h with
  | [x], h => exact ⟨x, rfl, by simpa [Term.denotes] using h⟩

theorem pair_terms {xs : List Term} {a b : Val} (h : Term.denotes M xs = [a, b]) :
    ∃ x y, xs = [x, y] ∧ x.denote M = a ∧ y.denote M = b := by
  match xs, h with
  | [x, y], h => simp only [Term.denotes, List.cons.injEq, and_true] at h; exact ⟨x, y, rfl, h.1, h.2⟩

mutual
/-- Well-formedness characterizes decoding: for a value of the type's sort, the term holds exactly when the value
decodes. -/
theorem wf_iff : (t : Ty) → (x : Term) → (c : Term) → wfT L t x = some c → Sorted L t (x.denote M) →
    (Holds M c ↔ (decodeV L t (x.denote M)).isSome = true)
  | .int, x, c, h, ⟨n, hn⟩ | .date, x, c, h, ⟨n, hn⟩ => by
    simp only [wfT, Option.some.injEq] at h; subst h; simp [Holds, tt, Term.denote, Val.toBool, hn, decodeV]; rfl
  | .str, x, c, h, ⟨s, hs⟩ => by
    simp only [wfT, Option.some.injEq] at h; subst h; simp [Holds, tt, Term.denote, Val.toBool, hs, decodeV]; rfl
  | .dsl .fresh _, x, c, h, ⟨n, hn⟩ => by
    simp only [wfT, Option.some.injEq] at h; subst h
    simp only [Holds, Term.denote, hn, Val.toBool, Val.toInt, decodeV, decide_eq_true_eq]
    split <;> simp_all; rfl
  | .id, x, c, h, ⟨d, n, hf, hw⟩ => by
    simp only [wfT, hf, Option.map_some, Option.some.injEq] at h; subst h
    rcases hw with ⟨m, hm⟩ | ⟨s, hs⟩
    · simp only [Holds, Term.denote, hm, Val.toBool, Val.toInt, decodeV, hf, decodeId, beq_self_eq_true,
        Bool.and_self, Bool.not_true, ite_true, Bool.false_or, decide_eq_true_eq, and_self, List.getElem?_cons_zero,
        Option.getD_some]
      by_cases h0 : 0 ≤ m <;> simp [h0] <;> rfl
    · simp [Holds, Term.denote, hs, Val.toBool, decodeV, hf, decodeId]; rfl
  | .adt 0 _ vs, x, c, h, ⟨hvs, b, hb⟩ => by
    subst hvs; simp only [wfT, boolVs?, Option.isSome_some, ite_true, Option.some.injEq] at h; subst h
    simp [Holds, tt, Term.denote, Val.toBool, hb, decodeV]
  | .adt (i + 1) a vs, x, c, h, ⟨d, n, hf, hs⟩ => by
    simp only [wfT, hf, Option.bind_some] at h
    simp only [decodeV, hf]
    exact wfAlts_iff d 0 vs x c h hs
  | .tuple ts, x, c, h, ⟨d, n, vals, hf, hx, hs⟩ => by
    simp only [wfT, hf, Option.bind_some] at h
    simp only [decodeV, hf, hx, and_self]
    exact wfFields_iff d 0 ts x vals hx 0 c h hs
  | .bag t, x, c, h, ⟨d, n, dt, m, sv, hf, hft, hsv, hQ⟩ => by
    simp only [wfT, hf, hft] at h
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hx, hn, hw⟩ := collView_eq hsv
    subst hn
    have hS := slotsOf_den d dt 1 x sv hx hw
    have hdec : (decodeV L (.bag t) (x.denote M)).isSome =
        ((occupied sv).mapM fun | [z] => decodeV L t z | _ => none).isSome := by
      simp only [decodeV, hf, hft, hsv]; rfl
    rw [hdec, mapM_isSome]
    refine slots_all (g := fun xs => wfT L t (xs.headD tt)) (Q := fun vs => ∃ z, vs = [z] ∧ Sorted L t z) ?_ _ sv
      hS ?_ cs hcs
    · intro xs c' hc' ⟨z, hz, hzs⟩
      obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
      rw [hz]
      simp only [List.headD_cons] at hc'
      have := wf_iff t x0 c' hc' (hx0 ▸ hzs)
      rw [hx0] at this
      exact this
    · intro p hp hb
      have hl := hw p hp
      match p, hl with
      | (b, [z]), _ => exact ⟨z, rfl, hQ _ hp hb z rfl⟩
  | .list t, x, c, h, ⟨d, n, dt, m, sv, hf, hft, hsv, hQ⟩ => by
    simp only [wfT, hf, hft] at h
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hx, hn, hw⟩ := collView_eq hsv
    subst hn
    have hS := slotsOf_den d dt 1 x sv hx hw
    have hdec : (decodeV L (.list t) (x.denote M)).isSome =
        ((occupied sv).mapM fun | [z] => decodeV L t z | _ => none).isSome := by
      simp only [decodeV, hf, hft, hsv]; rfl
    rw [hdec, mapM_isSome]
    refine slots_all (g := fun xs => wfT L t (xs.headD tt)) (Q := fun vs => ∃ z, vs = [z] ∧ Sorted L t z) ?_ _ sv
      hS ?_ cs hcs
    · intro xs c' hc' ⟨z, hz, hzs⟩
      obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
      rw [hz]
      simp only [List.headD_cons] at hc'
      have := wf_iff t x0 c' hc' (hx0 ▸ hzs)
      rw [hx0] at this
      exact this
    · intro p hp hb
      have hl := hw p hp
      match p, hl with
      | (b, [z]), _ => exact ⟨z, rfl, hQ _ hp hb z rfl⟩
  | .table k w, x, c, h, ⟨d, n, dt, m, sv, hf, hft, hsv, hQ⟩ => by
    simp only [wfT, hf, hft] at h
    split at h
    · rename_i hk
      obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hx, hn, hw⟩ := collView_eq hsv
      subst hn
      have hS := slotsOf_den d dt 2 x sv hx hw
      have hP : ∀ p ∈ sv, p.1 = true → ∃ zk zv, p.2 = [zk, zv] ∧ Sorted L k zk ∧ Sorted L w zv := by
        intro p hp hb
        have hl := hw p hp
        match p, hl with
        | (b, [zk, zv]), _ => exact ⟨zk, zv, rfl, hQ _ hp hb zk zv rfl⟩
      let f2 : List Val → Option (k.den × w.den) := fun
        | [zk, zv] => (decodeV L k zk).bind fun a => (decodeV L w zv).map fun b => (a, b)
        | _ => none
      have hall := slots_all (g := fun xs => (wfT L k (xs.headD tt)).bind fun ck =>
          (wfT L w (xs.getD 1 tt)).map fun cw => Term.and ck cw) (P := fun vs => (f2 vs).isSome)
        (Q := fun vs => ∃ zk zv, vs = [zk, zv] ∧ Sorted L k zk ∧ Sorted L w zv) ?_ _ sv hS hP cs ?_
      rotate_left
      · intro xs c' hc' ⟨zk, zv, hz, hsk, hsw⟩
        obtain ⟨x0, x1, rfl, hx0, hx1⟩ := pair_terms hz
        rw [hz]
        simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at hc'
        obtain ⟨ck, hck, hc'⟩ := Option.bind_eq_some_iff.1 hc'
        obtain ⟨cw, hcw, rfl⟩ := Option.map_eq_some_iff.1 hc'
        have h0 := wf_iff k x0 ck hck (hx0 ▸ hsk)
        have h1 := wf_iff w x1 cw hcw (hx1 ▸ hsw)
        rw [hx0] at h0; rw [hx1] at h1
        rw [holds_and, h0, h1]
        simp only [f2]
        cases decodeV L k zk <;> cases decodeV L w zv <;> simp
      · exact hcs
      rw [holds_and, hall, distinctT_den _ sv hS]
      have hdec : (decodeV L (.table k w) (x.denote M)).isSome =
          (((occupied sv).mapM f2).bind (uniqueKeys (Ty.semWith Dsl.val k).2)).isSome := by
        simp only [decodeV, hf, hft, hsv]; rfl
      rw [hdec]
      cases hm : (occupied sv).mapM f2 with
      | none =>
        have := mapM_isSome f2 (occupied sv)
        rw [hm] at this
        rw [← this]
        simp
      | some es =>
        have := mapM_isSome f2 (occupied sv)
        rw [hm] at this
        simp only [Option.isSome_some] at this
        rw [← this]
        simp only [true_and, Option.bind_some, uniqueKeys]
        have h2 := mapM_forall2 (E := fun e vs => ∃ zk zv, vs = [zk, zv] ∧ decodeV L k zk = some e.1 ∧
          decodeV L w zv = some e.2) (f := f2) (fun vs e he => by
            match vs, he with
            | [zk, zv], he =>
              obtain ⟨a, ha, he⟩ := Option.bind_eq_some_iff.1 he
              obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 he
              exact ⟨zk, zv, rfl, ha, hb⟩) _ _ hm
        rw [← pairwise_forall2 (P := fun (a b : k.den × w.den) => (Ty.semWith Dsl.val k).2 a.1 b.1 = false ∧
          (Ty.semWith Dsl.val k).2 b.1 a.1 = false) (fun e vs e' vs' ⟨zk, zv, h1, h2, _⟩ ⟨zk', zv', h1', h2', _⟩ => by
          subst h1 h1'
          simp only [List.headD_cons]
          rw [show (zk == zk') = Ty.deq k e.1 e'.1 from relV_beq k hk _ _ _ _ (decode_rel _ _ _ h2) (decode_rel _ _ _ h2'),
            show (zk' == zk) = Ty.deq k e'.1 e.1 from relV_beq k hk _ _ _ _ (decode_rel _ _ _ h2') (decode_rel _ _ _ h2)]) _ _ h2]
        split <;> simp_all
    · cases h
theorem wfFields_iff (d k : Nat) : (ts : List Ty) → (x : Term) → (vs : List Val) → x.denote M = .ctor d k vs →
    (j : Nat) → (c : Term) → wfFields L d k ts x j = some c → SortedVs L ts (vs.drop j) →
    (Holds M c ↔ (decodeVs L ts (vs.drop j)).isSome = true)
  | [], x, vs, hx, j, c, h, hs => by
    simp only [wfFields, Option.some.injEq] at h; subst h
    cases hd : vs.drop j with
    | nil => simp [Holds, tt, Term.denote, Val.toBool, decodeVs]; rfl
    | cons _ _ => rw [hd] at hs; exact hs.elim
  | t :: ts, x, vs, hx, j, c, h, hs => by
    cases hd : vs.drop j with
    | nil => rw [hd] at hs; exact hs.elim
    | cons w ws =>
      rw [hd] at hs
      obtain ⟨hw, hws⟩ := hs
      have hj : vs[j]? = some w := by
        have := List.getElem?_drop (xs := vs) (i := j) (j := 0); rw [hd] at this; simpa using this.symm
      have hj1 : vs.drop (j + 1) = ws := by rw [← List.drop_drop, hd]; rfl
      obtain ⟨c1, h1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
      have hsel : (Term.sel d k j x).denote M = w := by simp [sel_ctor j hx, hj]
      have ih1 := wf_iff t (.sel d k j x) c1 h1 (hsel ▸ hw)
      have ih2 := wfFields_iff d k ts x vs hx (j + 1) c2 h2 (hj1 ▸ hws)
      rw [hsel] at ih1; rw [hj1] at ih2
      rw [holds_and, ih1, ih2]
      simp only [decodeVs]
      cases decodeV L t w <;> cases decodeVs L ts ws <;> simp <;> rfl
theorem wfAlts_iff (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : Term) → (c : Term) →
    wfAlts L d k vs x = some c → SortedAlts L d k vs (x.denote M) →
    (Holds M c ↔ (decodeAlts L d k vs (x.denote M)).isSome = true)
  | _, [], _, _, _, hs => hs.elim
  | k, fs :: vs, x, c, h, ⟨k', vals, hw, hs⟩ => by
    obtain ⟨c1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c2, h2, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases hs with ⟨rfl, hs⟩ | ⟨hne, hs⟩
    · have ih := wfFields_iff d k' fs x vals hw 0 c1 h1 (by simpa using hs)
      simp only [List.drop_zero] at ih
      have hl : Holds M (.ite (.is d k' x) c1 c2) ↔ Holds M c1 := by simp [Holds, Term.denote, hw, Val.toBool]
      rw [hl, ih, hw]
      simp only [decodeAlts, and_self, ite_true]
      erw [isSome_map]
    · have ih := wfAlts_iff d (k + 1) vs x c2 h2 hs
      have hl : Holds M (.ite (.is d k x) c1 c2) ↔ Holds M c2 := by simp [Holds, Term.denote, hw, hne, Val.toBool]
      rw [hl, ih, hw]
      simp only [decodeAlts, hne, and_false, ite_false]
      erw [isSome_map]
end

theorem mem_occupied {sv : List (Bool × List Val)} {b : Bool} {vs : List Val} (hp : (b, vs) ∈ sv) (hb : b = true) :
    vs ∈ occupied sv := by
  subst hb; exact List.mem_filterMap.2 ⟨(true, vs), hp, rfl⟩

theorem mapM_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β} (h : xs.mapM f = some ys) {x : α}
    (hx : x ∈ xs) : ∃ y, f x = some y := by
  have := mapM_isSome f xs
  rw [h] at this
  have hx' := List.all_eq_true.1 this.symm x hx
  exact Option.isSome_iff_exists.1 hx'

mutual
/-- A value that decodes has the shape of its type's sort. -/
theorem decode_sorted : (t : Ty) → (v : Val) → (x : t.den) → decodeV L t v = some x → Sorted L t v
  | .int, .int n, _, _ | .date, .int n, _, _ | .dsl .fresh _, .int n, _, _ => ⟨n, rfl⟩
  | .str, .str s, _, _ => ⟨s, rfl⟩
  | .id, .ctor d' k args, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n hf
      by_cases hd : d' = d
      · subst hd
        simp only at h
        refine ⟨d', n, hf, ?_⟩
        rw [decodeId_val d' h]
        cases x with
        | fresh m => exact .inl ⟨m, rfl⟩
        | named s => exact .inr ⟨s, rfl⟩
      · simp [hd] at h
    · cases h
  | .adt 0 _ [[], []], .bool b, _, _ => ⟨rfl, b, rfl⟩
  | .adt (i + 1) a vs, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n hf; exact ⟨d, n, hf, decodeAlts_sorted d 0 vs v x h⟩
    · cases h
  | .tuple ts, .ctor d' k vals, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n hf
      by_cases hc : d' = d ∧ k = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [and_self] at h
        exact ⟨d', n, vals, hf, rfl, decodeVs_sorted ts vals x h⟩
      · simp [hc] at h
    · cases h
  | .bag t, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, hsv, h⟩ := bind_some.1 h
      refine ⟨d, n, dt, m, sv, hf, hft, hsv, fun p hp hb z hz => ?_⟩
      obtain ⟨b, vs⟩ := p
      simp only at hb hz
      subst hz
      obtain ⟨y, hy⟩ := mapM_mem h (mem_occupied hp hb)
      exact decode_sorted t z y hy
    · cases h
  | .list t, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, hsv, h⟩ := bind_some.1 h
      refine ⟨d, n, dt, m, sv, hf, hft, hsv, fun p hp hb z hz => ?_⟩
      obtain ⟨b, vs⟩ := p
      simp only at hb hz
      subst hz
      obtain ⟨y, hy⟩ := mapM_mem h (mem_occupied hp hb)
      exact decode_sorted t z y hy
    · cases h
  | .table k w, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, hsv, h⟩ := bind_some.1 h
      obtain ⟨xs, hxs, _⟩ := bind_some.1 h
      refine ⟨d, n, dt, m, sv, hf, hft, hsv, fun p hp hb zk zv hz => ?_⟩
      obtain ⟨b, vs⟩ := p
      simp only at hb hz
      subst hz
      obtain ⟨y, hy⟩ := mapM_mem hxs (mem_occupied hp hb)
      obtain ⟨y1, h1, hy⟩ := bind_some.1 hy
      obtain ⟨y2, h2, _⟩ := map_some.1 hy
      exact ⟨decode_sorted k zk y1 h1, decode_sorted w zv y2 h2⟩
    · cases h
theorem decodeVs_sorted : (ts : List Ty) → (vals : List Val) → (x : Ty.dens ts) → decodeVs L ts vals = some x →
    SortedVs L ts vals
  | [], [], _, _ => trivial
  | t :: ts, v :: vs, x, h => by
    obtain ⟨y, hy, h⟩ := bind_some.1 h
    obtain ⟨ys, hys, _⟩ := map_some.1 h
    exact ⟨decode_sorted t v y hy, decodeVs_sorted ts vs ys hys⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [decodeVs] at h
theorem decodeAlts_sorted (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (v : Val) → (x : Ty.alts vs) →
    decodeAlts L d k vs v = some x → SortedAlts L d k vs v
  | _, [], _, _, h => by simp [decodeAlts] at h
  | k, fs :: vs, .ctor d' k' vals, x, h => by
    simp only [decodeAlts] at h
    split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨y, hy, _⟩ := map_some.1 h
      exact ⟨k', vals, rfl, .inl ⟨rfl, decodeVs_sorted fs vals y hy⟩⟩
    · rename_i hc
      obtain ⟨y, hy, _⟩ := map_some.1 h
      have hs := decodeAlts_sorted d (k + 1) vs _ y hy
      have hd : d' = d := by
        match vs, hs with
        | _ :: _, ⟨_, _, hw, _⟩ => cases hw; rfl
      subst hd
      exact ⟨k', vals, rfl, .inr ⟨fun h => hc ⟨rfl, h⟩, hs⟩⟩
  | _, _ :: _, .int _, _, h | _, _ :: _, .bool _, _, h | _, _ :: _, .str _, _, h => by simp [decodeAlts] at h
end

/-- Well-formedness loses no value: every value that decodes, every embedded one among them, satisfies it. -/
theorem wf_of_decode {t : Ty} {x c : Term} (hc : wfT L t x = some c) {y : t.den} (h : decodeV L t (x.denote M) = some y) :
    Holds M c :=
  (wf_iff t x c hc (decode_sorted t _ y h)).2 (by rw [h]; rfl)

end

end Tazuna.Smt
