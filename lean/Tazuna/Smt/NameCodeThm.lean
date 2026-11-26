import Tazuna.Smt.NameCode
import Tazuna.Smt.EncodeThm

/-! Names as codes keep a script's models (`code_model`): a model of the script gives one of the variant with names as
codes, whose variables hold the model's values with each name `s` as the code `c s` (`Coded`). The names the model
compares are finitely many: those its variables hold and those the script's name terms denote. A name's code is its
rank among them (`rank`), which keeps their order, so `<` between codes says what `str.<` said between names. The
values with names as codes are kept apart (`codeV`): a name outside the ranked ones and a value that is not a name
where a name stands are kept as they are, under constructors no code takes. -/

namespace Tazuna.Smt

/-! Coding with sharing is coding. -/

theorem CodeCache.find?_ok {d : Nat} {c : CodeCache} (hc : c.Ok d) {h : UInt64} {t t' : Term}
    (hf : c.find? h t = some t') : t.code d = some t' := by
  unfold CodeCache.find? at hf
  split at hf
  · rename_i l hl
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hf
    have hs : p.1.same t = true := by simpa using List.find?_some hp
    rw [← Term.eq_of_same hs]
    exact hc h l hl p (List.mem_of_find?_eq_some hp)
  · cases hf

theorem CodeCache.add_ok {d : Nat} {c : CodeCache} (hc : c.Ok d) (h : UInt64) {t t' : Term} (ht : t.code d = some t') :
    (c.add h t t').Ok d := by
  intro h' l hl p hp
  unfold CodeCache.add at hl
  by_cases hh : h = h'
  · subst hh
    split at hl
    · rename_i l0 heq
      simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hl
      subst hl
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ht
      · exact hc h l0 heq p hp
    · simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hl
      subst hl
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ht
      · cases hp
  · split at hl <;> simp [Std.HashMap.getElem?_insert, hh] at hl <;> exact hc h' l hl p hp

theorem CodeCache.ok_empty (d : Nat) : ({} : CodeCache).Ok d := by
  intro h l hl; simp at hl

mutual
theorem Term.codeC_ok (d : Nat) : (t : Term) → (c : CodeCache) → c.Ok d →
    (t.codeC d c).1 = t.code d ∧ (t.codeC d c).2.Ok d
  | .shared h t, c, hc => by
    unfold Term.codeC
    split
    · rename_i t' hf; exact ⟨(CodeCache.find?_ok hc hf).symm, hc⟩
    · have ih := Term.codeC_ok d t c hc
      revert ih
      cases t.codeC d c with
      | mk r c' =>
        intro ih
        cases r with
        | some t' =>
          simp only at ih ⊢
          have e : (Term.shared h t).code d = some (.shared h t') := by simp [Term.code, ← ih.1]
          exact ⟨e.symm, CodeCache.add_ok ih.2 h e⟩
        | none => simp only at ih ⊢; exact ⟨by simp [Term.code, ← ih.1], ih.2⟩
  | .var _, c, hc | .int _, c, hc | .str _, c, hc | .bool _, c, hc | .ref _, c, hc => ⟨rfl, hc⟩
  | .not a, c, hc | .len a, c, hc | .is _ _ a, c, hc => by
    have ih := Term.codeC_ok d a c hc
    simp only [Term.codeC, Term.code, ih.1]
    exact ⟨by first | rfl | trivial, ih.2⟩
  | .sel e k j a, c, hc => by
    have ih := Term.codeC_ok d a c hc
    simp only [Term.codeC, Term.code]
    split
    · exact ⟨rfl, hc⟩
    · simp only [ih.1]; exact ⟨by first | rfl | trivial, ih.2⟩
  | .and a b, c, hc | .or a b, c, hc | .lt a b, c, hc | .le a b, c, hc | .add a b, c, hc
  | .sub a b, c, hc | .mul a b, c, hc | .div a b, c, hc | .mod a b, c, hc | .cat a b, c, hc => by
    have ha := Term.codeC_ok d a c hc
    have hb := Term.codeC_ok d b _ ha.2
    simp only [Term.codeC, Term.code, ha.1, hb.1]
    exact ⟨by first | rfl | trivial, hb.2⟩
  | .eq a b, c, hc | .slt a b, c, hc => by
    simp only [Term.codeC, Term.code]
    split
    · have ha := Term.codeNameC_ok d a c hc
      have hb := Term.codeNameC_ok d b _ ha.2
      simp only [ha.1, hb.1]
      exact ⟨by first | rfl | trivial, hb.2⟩
    · split
      · exact ⟨rfl, hc⟩
      · have ha := Term.codeC_ok d a c hc
        have hb := Term.codeC_ok d b _ ha.2
        simp only [ha.1, hb.1]
        exact ⟨by first | rfl | trivial, hb.2⟩
  | .ite x a b, c, hc => by
    have hx := Term.codeC_ok d x c hc
    have ha := Term.codeC_ok d a _ hx.2
    have hb := Term.codeC_ok d b _ ha.2
    simp only [Term.codeC, Term.code, hx.1, ha.1, hb.1]
    exact ⟨by first | rfl | trivial, hb.2⟩
  | .ctor e k args, c, hc => by
    have ih := Term.codesC_ok d args c hc
    simp only [Term.codeC, Term.code]
    split
    · exact ⟨rfl, hc⟩
    · simp only [ih.1]; exact ⟨by first | rfl | trivial, ih.2⟩
theorem Term.codeNameC_ok (d : Nat) : (t : Term) → (c : CodeCache) → c.Ok d →
    (t.codeNameC d c).1 = t.codeName d ∧ (t.codeNameC d c).2.Ok d
  | .shared h t, c, hc => by
    have ih := Term.codeNameC_ok d t c hc
    simp only [Term.codeNameC, Term.codeName, ih.1]
    exact ⟨by first | rfl | trivial, ih.2⟩
  | .sel e k j a, c, hc => by
    have ih := Term.codeC_ok d a c hc
    simp only [Term.codeNameC, Term.codeName]
    split
    · simp only [ih.1]; exact ⟨by first | rfl | trivial, ih.2⟩
    · exact ⟨rfl, hc⟩
  | .var _, c, hc | .int _, c, hc | .str _, c, hc | .bool _, c, hc | .ref _, c, hc | .not _, c, hc | .len _, c, hc
  | .is .., c, hc | .and .., c, hc | .or .., c, hc | .lt .., c, hc | .le .., c, hc | .add .., c, hc | .sub .., c, hc
  | .mul .., c, hc | .div .., c, hc | .mod .., c, hc | .cat .., c, hc | .eq .., c, hc | .slt .., c, hc
  | .ite .., c, hc | .ctor .., c, hc => ⟨rfl, hc⟩
theorem Term.codesC_ok (d : Nat) : (ts : List Term) → (c : CodeCache) → c.Ok d →
    (Term.codesC d ts c).1 = Term.codes d ts ∧ (Term.codesC d ts c).2.Ok d
  | [], c, hc => ⟨rfl, hc⟩
  | t :: ts, c, hc => by
    have ht := Term.codeC_ok d t c hc
    have hs := Term.codesC_ok d ts _ ht.2
    simp only [Term.codesC, Term.codes, ht.1, hs.1]
    exact ⟨by first | rfl | trivial, hs.2⟩
end

/-! Ranks keep the order of the names ranked. -/

theorem not_lt_empty (s : String) : ¬ s < "" := by
  rw [String.lt_iff]; simp

/-- The rank of `s` among the names `S`: how many of them come before it. -/
def rank (S : List String) (s : String) : Int := ((S.filter (· < s)).length : Int)

theorem rank_empty (S : List String) : rank S "" = 0 := by
  simp [rank, not_lt_empty]

theorem rank_lt {S : List String} {s t : String} (hs : s ∈ S) (h : s < t) : rank S s < rank S t := by
  unfold rank
  have e : (S.filter (· < t)).filter (· < s) = S.filter (· < s) := by
    rw [List.filter_filter]
    congr 1; funext x
    by_cases hx : x < s
    · simp [hx, String.lt_trans hx h]
    · simp [hx]
  have hl := List.length_eq_countP_add_countP (fun x => decide (x < s)) (l := S.filter (· < t))
  simp only [List.countP_eq_length_filter, e] at hl
  have hm : s ∈ (S.filter (· < t)).filter (fun x => decide ¬ (decide (x < s) = true)) := by
    simp [List.mem_filter, hs, h]
  have hp := List.length_pos_of_mem hm
  omega

theorem rank_lt_iff {S : List String} {s t : String} (hs : s ∈ S) (ht : t ∈ S) : rank S s < rank S t ↔ s < t := by
  refine ⟨fun h => ?_, rank_lt hs⟩
  by_cases hst : s < t
  · exact hst
  · by_cases hts : t < s
    · exact absurd (rank_lt ht hts) (by omega)
    · rw [String.le_antisymm hts hst] at h; omega

theorem rank_inj {S : List String} {s t : String} (hs : s ∈ S) (ht : t ∈ S) (h : rank S s = rank S t) : s = t := by
  by_cases hst : s < t
  · exact absurd (rank_lt hs hst) (by omega)
  · by_cases hts : t < s
    · exact absurd (rank_lt ht hts) (by omega)
    · exact String.le_antisymm hts hst

/-! Values with names as codes. -/

section
variable (d : Nat) (S : List String)

/-- A name as its code: its rank where it is ranked. A name outside the ranked ones, and a value that is not a name,
are kept as they are under datatype `d + 1`'s constructors 1 and 0, which no code is. -/
def codeN : Val → Val
  | .str s => if s ∈ S then .int (rank S s) else .ctor (d + 1) 1 [.str s]
  | v => .ctor (d + 1) 0 [v]

-- A constructor 1 of `d` that is not a name keeps its fields after the code of what its name selector reads, the
-- field or the default SMT-LIB leaves to the model, so `Term.denote`'s default stands here too.
set_option linter.tazuna.silentDefault false in
mutual
/-- The value with each name in datatype `d` as its code (`codeN`). -/
def codeV : Val → Val
  | .ctor e k as =>
    if e = d ∧ k = 1 then
      match as with
      | [.str s] => .ctor d 1 [codeN d S (.str s)]
      | as => .ctor d 1 (codeN d S (as[0]?.getD default) :: as)
    else .ctor e k (codeVs as)
  | v => v
def codeVs : List Val → List Val
  | [] => []
  | v :: vs => codeV v :: codeVs vs
end

end

section
variable {d : Nat} {S : List String}

theorem codeN_inj {a b : Val} (h : codeN d S a = codeN d S b) : a = b := by
  cases a <;> cases b <;> simp only [codeN] at h <;> (try split at h) <;> (try split at h) <;> simp_all
  rename_i ha hb; exact rank_inj ha hb h

theorem codeV_ctor_is (e k : Nat) (as : List Val) : ∃ bs, codeV d S (.ctor e k as) = .ctor e k bs := by
  unfold codeV
  split
  · rename_i he; obtain ⟨rfl, rfl⟩ := he; split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

mutual
theorem codeV_inj : (a b : Val) → codeV d S a = codeV d S b → a = b
  | .ctor e k as, .ctor e' k' bs, h => by
    obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e k as
    obtain ⟨ys, hy⟩ := codeV_ctor_is (d := d) (S := S) e' k' bs
    have hek : e = e' ∧ k = k' := by rw [hx, hy] at h; cases h; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hek
    unfold codeV at h
    split at h
    · rename_i he; obtain ⟨rfl, rfl⟩ := he
      split at h <;> split at h
      · simp only [Val.ctor.injEq, List.cons.injEq, and_true, true_and] at h; rw [codeN_inj h]
      · rename_i hn; simp only [Val.ctor.injEq, List.cons.injEq, true_and] at h
        obtain ⟨h1, rfl⟩ := h; cases codeN_inj h1
      · rename_i hn _; simp only [Val.ctor.injEq, List.cons.injEq, true_and] at h
        obtain ⟨h1, h2⟩ := h; subst h2; cases codeN_inj h1
      · simp only [Val.ctor.injEq, List.cons.injEq, true_and] at h; rw [h.2]
    · simp only [Val.ctor.injEq, true_and] at h; rw [codeVs_inj as bs h]
  | .ctor e k as, .int _, h | .ctor e k as, .bool _, h | .ctor e k as, .str _, h => by
    obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e k as
    rw [hx] at h; cases h
  | .int _, .ctor e k as, h | .bool _, .ctor e k as, h | .str _, .ctor e k as, h => by
    obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e k as
    rw [hx] at h; cases h
  | .int _, .int _, h | .bool _, .bool _, h | .str _, .str _, h => by simp only [codeV] at h; exact h
  | .int _, .bool _, h | .int _, .str _, h | .bool _, .int _, h | .bool _, .str _, h | .str _, .int _, h
  | .str _, .bool _, h => by simp [codeV] at h
theorem codeVs_inj : (as bs : List Val) → codeVs d S as = codeVs d S bs → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [codeVs, List.cons.injEq] at h; rw [codeV_inj a b h.1, codeVs_inj as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [codeVs] at h
end

theorem val_beq_iff {a b : Val} : Val.beq a b = true ↔ a = b :=
  ⟨Val.eq_of_beq a b, fun h => h ▸ Val.beq_refl a⟩

theorem beq_codeV (a b : Val) : (codeV d S a == codeV d S b) = (a == b) := by
  show Val.beq _ _ = Val.beq _ _
  apply Bool.eq_iff_iff.2
  rw [val_beq_iff, val_beq_iff]
  exact ⟨codeV_inj a b, fun h => h ▸ rfl⟩

theorem beq_codeN (a b : Val) : (codeN d S a == codeN d S b) = (a == b) := by
  show Val.beq _ _ = Val.beq _ _
  apply Bool.eq_iff_iff.2
  rw [val_beq_iff, val_beq_iff]
  exact ⟨codeN_inj, fun h => h ▸ rfl⟩

theorem codeV_toInt (v : Val) : (codeV d S v).toInt = v.toInt := by
  cases v with
  | ctor e k as => obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e k as; rw [hx]; rfl
  | _ => rfl

theorem codeV_toStr (v : Val) : (codeV d S v).toStr = v.toStr := by
  cases v with
  | ctor e k as => obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e k as; rw [hx]; rfl
  | _ => rfl

theorem codeV_toBool (v : Val) : (codeV d S v).toBool = v.toBool := by
  cases v with
  | ctor e k as => obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e k as; rw [hx]; rfl
  | _ => rfl

/-- A name's code orders as its rank: a value that is not a name reads as `""` in `str.<` and as 0 in `<`. -/
theorem codeN_toInt {v : Val} (h : v.toStr ∈ S) : (codeN d S v).toInt = rank S v.toStr := by
  cases v with
  | str s => simp only [Val.toStr] at h; simp [codeN, h, Val.toInt, Val.toStr]
  | _ => simp [codeN, Val.toInt, Val.toStr, rank_empty]

-- `Term.denote`'s default for a missing field.
set_option linter.tazuna.silentDefault false in
theorem codeVs_getD : (vs : List Val) → (j : Nat) →
    (codeVs d S vs)[j]?.getD default = codeV d S (vs[j]?.getD default)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: vs, j + 1 => codeVs_getD vs j

end

/-! The model with names as codes. -/

mutual
/-- The names the term's name selectors denote in the model, as `str.<` reads them: these are what its order
compares. -/
def Term.nameStrs (d : Nat) (M : Model) : Term → List String
  | .sel e k j a => (if e = d ∧ k = 1 ∧ j = 0 then [((Term.sel e k j a).denote M).toStr] else []) ++ a.nameStrs d M
  | .shared _ a | .not a | .len a | .is _ _ a => a.nameStrs d M
  | .and a b | .or a b | .eq a b | .lt a b | .le a b | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .cat a b | .slt a b => a.nameStrs d M ++ b.nameStrs d M
  | .ite c a b => c.nameStrs d M ++ a.nameStrs d M ++ b.nameStrs d M
  | .ctor _ _ args => Term.nameStrss d M args
  | .var _ | .int _ | .str _ | .bool _ | .ref _ => []
def Term.nameStrss (d : Nat) (M : Model) : List Term → List String
  | [] => []
  | t :: ts => t.nameStrs d M ++ Term.nameStrss d M ts
end

theorem Term.isName_mem {d : Nat} {M : Model} : (a : Term) → a.isName d = true → (a.denote M).toStr ∈ a.nameStrs d M
  | .shared _ a, h => by simpa [Term.isName, Term.denote, Term.nameStrs] using Term.isName_mem a h
  | .sel e k j a, h => by
    simp only [Term.isName, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    simp [Term.nameStrs]
  | .var _, h | .int _, h | .str _, h | .bool _, h | .ref _, h | .not _, h | .len _, h | .is .., h | .and .., h
  | .or .., h | .eq .., h | .lt .., h | .le .., h | .add .., h | .sub .., h | .mul .., h | .div .., h | .mod .., h
  | .cat .., h | .slt .., h | .ite .., h | .ctor .., h => by simp [Term.isName] at h

section
variable (d : Nat) (S : List String)

/-- The value `codeV` codes as `v`, where there is one. -/
noncomputable def uncodeV (v : Val) : Val := by
  classical exact if h : ∃ w, codeV d S w = v then Classical.choose h else v

theorem uncodeV_codeV (w : Val) : uncodeV d S (codeV d S w) = w := by
  have h : ∃ w', codeV d S w' = codeV d S w := ⟨w, rfl⟩
  unfold uncodeV
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact codeV_inj _ _ (Classical.choose_spec h)

/-- The model's values with names as codes; what SMT-LIB leaves to the model is the model's, read through the
codes. -/
noncomputable def codedModel (M : Model) : Model where
  vars n := codeV d S (M.vars n)
  divZero := M.divZero
  modZero := M.modZero
  selOther e k j v := if e = d ∧ k = 1 ∧ j = 0 then codeN d S (M.selOther e k j (uncodeV d S v))
    else codeV d S (M.selOther e k j (uncodeV d S v))
  defs i := codeV d S (M.defs i)

end

-- `Term.denote`'s default for a missing field.
set_option linter.tazuna.silentDefault false in
/-- What a selector reads from a value in the model, as `Term.denote` says. -/
def selOf (M : Model) (e k j : Nat) : Val → Val
  | .ctor e' k' vs => if e' = e ∧ k' = k then vs[j]?.getD default else M.selOther e k j (.ctor e' k' vs)
  | v => M.selOther e k j v

theorem denote_sel (M : Model) (e k j : Nat) (a : Term) : (Term.sel e k j a).denote M = selOf M e k j (a.denote M) := by
  simp only [Term.denote]; cases a.denote M <;> rfl

section
variable {d : Nat} {S : List String} {M : Model}

theorem selOf_codeV_other {v : Val} (atom : ∀ e k as, v ≠ .ctor e k as) (e k j : Nat) (hn : ¬ (e = d ∧ k = 1 ∧ j = 0)) :
    selOf (codedModel d S M) e k j (codeV d S v) = codeV d S (selOf M e k j v) := by
  have hc : codeV d S v = v := by cases v <;> first | rfl | exact absurd rfl (atom _ _ _)
  have hs : ∀ w, selOf M e k j w = M.selOther e k j w → selOf (codedModel d S M) e k j (codeV d S w) =
      (codedModel d S M).selOther e k j (codeV d S w) → selOf (codedModel d S M) e k j (codeV d S w) =
        codeV d S (selOf M e k j w) := by
    intro w h1 h2; rw [h2, h1]; simp only [codedModel, hn, ite_false, uncodeV_codeV]
  apply hs v
  · cases v <;> first | rfl | exact absurd rfl (atom _ _ _)
  · rw [hc]; cases v <;> first | rfl | exact absurd rfl (atom _ _ _)

-- `Term.denote`'s default for a missing field.
set_option linter.tazuna.silentDefault false in
/-- A selector other than a name's reads from a value with names as codes the read value with names as codes. -/
theorem selOf_codeV (v : Val) (e k j : Nat) (hek : ¬ (e = d ∧ k = 1)) :
    selOf (codedModel d S M) e k j (codeV d S v) = codeV d S (selOf M e k j v) := by
  have hn : ¬ (e = d ∧ k = 1 ∧ j = 0) := fun h => hek ⟨h.1, h.2.1⟩
  cases v with
  | ctor e' k' as =>
    by_cases he : e' = d ∧ k' = 1
    · obtain ⟨rfl, rfl⟩ := he
      obtain ⟨bs, hb⟩ := codeV_ctor_is (d := e') (S := S) e' 1 as
      have hne : ¬ (e' = e ∧ 1 = k) := fun h => hek ⟨h.1.symm, h.2.symm⟩
      rw [hb]
      simp only [selOf, hne, ite_false, codedModel, hn, ← hb, uncodeV_codeV]
    · have hv : codeV d S (.ctor e' k' as) = .ctor e' k' (codeVs d S as) := by simp [codeV, he]
      rw [hv]
      by_cases hm : e' = e ∧ k' = k
      · simp only [selOf, hm, and_self, ite_true, codeVs_getD]
      · simp only [selOf, hm, ite_false, codedModel, hn, ← hv, uncodeV_codeV]
  | _ => exact selOf_codeV_other (fun _ _ _ h => by cases h) e k j hn

-- `Term.denote`'s default for a missing field.
set_option linter.tazuna.silentDefault false in
/-- A name selector reads from a value with names as codes the code of what it reads. -/
theorem selOf_codeN (v : Val) : selOf (codedModel d S M) d 1 0 (codeV d S v) = codeN d S (selOf M d 1 0 v) := by
  cases v with
  | ctor e' k' as =>
    by_cases he : e' = d ∧ k' = 1
    · obtain ⟨rfl, rfl⟩ := he
      unfold codeV
      simp only [and_self, ite_true]
      split <;> simp [selOf]
    · have hv : codeV d S (.ctor e' k' as) = .ctor e' k' (codeVs d S as) := by simp [codeV, he]
      rw [hv]
      simp only [selOf, he, ite_false, codedModel, and_self, ite_true, ← hv, uncodeV_codeV]
  | _ =>
    have h : ∀ w, codeV d S w = w → (∀ e k as, w ≠ .ctor e k as) → selOf (codedModel d S M) d 1 0 (codeV d S w) =
        codeN d S (selOf M d 1 0 w) := by
      intro w hw ha
      have e1 : selOf (codedModel d S M) d 1 0 w = (codedModel d S M).selOther d 1 0 w := by
        cases w <;> first | rfl | exact absurd rfl (ha _ _ _)
      have e2 : selOf M d 1 0 w = M.selOther d 1 0 w := by cases w <;> first | rfl | exact absurd rfl (ha _ _ _)
      rw [hw, e1, e2]
      conv => lhs; rw [← hw]
      simp only [codedModel, and_self, ite_true, uncodeV_codeV]
    exact h _ rfl (fun _ _ _ h => by cases h)

end

section
variable {d : Nat} {S : List String} {M : Model}

theorem sub_left {xs ys : List String} (h : ∀ s ∈ xs ++ ys, s ∈ S) : ∀ s ∈ xs, s ∈ S :=
  fun s hm => h s (List.mem_append_left _ hm)

theorem sub_right {xs ys : List String} (h : ∀ s ∈ xs ++ ys, s ∈ S) : ∀ s ∈ ys, s ∈ S :=
  fun s hm => h s (List.mem_append_right _ hm)

theorem bind2_some {α : Type} {p q : Option α} {f : α → α → α} {t : α}
    (h : (do let x ← p; let y ← q; pure (f x y)) = some t) : ∃ x y, p = some x ∧ q = some y ∧ t = f x y := by
  cases p <;> cases q <;> simp_all [Option.bind]

theorem bind3_some {α : Type} {o p q : Option α} {f : α → α → α → α} {t : α}
    (h : (do let x ← o; let y ← p; let z ← q; pure (f x y z)) = some t) :
    ∃ x y z, o = some x ∧ p = some y ∧ q = some z ∧ t = f x y z := by
  cases o <;> cases p <;> cases q <;> simp_all [Option.bind]

theorem bindL_some {α : Type} {p : Option α} {q : Option (List α)} {t : List α}
    (h : (do let x ← p; let y ← q; pure (x :: y)) = some t) : ∃ x y, p = some x ∧ q = some y ∧ t = x :: y := by
  cases p <;> cases q <;> simp_all [Option.bind]

mutual
/-- A term's variant denotes, in the model with names as codes, the term's value with names as codes. -/
theorem code_denote : (t t' : Term) → t.code d = some t' → (∀ s ∈ t.nameStrs d M, s ∈ S) →
    t'.denote (codedModel d S M) = codeV d S (t.denote M)
  | .var n, t', h, _ | .int n, t', h, _ | .str n, t', h, _ | .bool n, t', h, _ => by cases h; rfl
  | .ref _, _, h, _ => by cases h
  | .shared _ a, t', h, hs => by
    simp only [Term.code, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simpa [Term.denote] using code_denote a a' ha hs
  | .not a, t', h, hs | .len a, t', h, hs => by
    simp only [Term.code, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp only [Term.denote, code_denote a a' ha hs, codeV_toBool, codeV_toStr]; rfl
  | .is e k a, t', h, hs => by
    simp only [Term.code, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simp only [Term.denote, code_denote a a' ha hs]
    generalize a.denote M = v
    cases v with
    | ctor e' k' as => obtain ⟨xs, hx⟩ := codeV_ctor_is (d := d) (S := S) e' k' as; rw [hx]; rfl
    | _ => rfl
  | .sel e k j a, t', h, hs => by
    simp only [Term.code] at h
    split at h
    · cases h
    · rename_i hek
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      have hs' : ∀ s ∈ a.nameStrs d M, s ∈ S := fun s hm => hs s (by
        simp only [Term.nameStrs]; exact List.mem_append_right _ hm)
      rw [denote_sel, denote_sel, code_denote a a' ha hs', selOf_codeV _ _ _ _ hek]
  | .and a b, t', h, hs | .or a b, t', h, hs | .lt a b, t', h, hs | .le a b, t', h, hs | .add a b, t', h, hs
  | .sub a b, t', h, hs | .mul a b, t', h, hs | .div a b, t', h, hs | .mod a b, t', h, hs | .cat a b, t', h, hs => by
    obtain ⟨a', b', ha, hb, rfl⟩ := bind2_some (by simpa only [Term.code] using h)
    simp only [Term.nameStrs] at hs
    simp only [Term.denote, code_denote a a' ha (sub_left hs), code_denote b b' hb (sub_right hs), codeV_toBool,
      codeV_toInt, codeV_toStr]; rfl
  | .eq a b, t', h, hs | .slt a b, t', h, hs => by
    simp only [Term.nameStrs] at hs
    simp only [Term.code] at h
    split at h
    · rename_i hn
      simp only [Bool.and_eq_true] at hn
      obtain ⟨a', b', ha, hb, rfl⟩ := bind2_some h
      have ea := codeName_denote a a' ha (sub_left hs)
      have eb := codeName_denote b b' hb (sub_right hs)
      have ma := sub_left hs _ (Term.isName_mem a hn.1)
      have mb := sub_right hs _ (Term.isName_mem b hn.2)
      simp only [Term.denote, ea, eb, beq_codeN]
      first
      | rfl
      | (rw [codeN_toInt ma, codeN_toInt mb]
         show Val.bool _ = Val.bool _
         exact congrArg Val.bool (decide_eq_decide.2 (rank_lt_iff ma mb)))
    · split at h
      · cases h
      · obtain ⟨a', b', ha, hb, rfl⟩ := bind2_some h
        simp only [Term.denote, code_denote a a' ha (sub_left hs), code_denote b b' hb (sub_right hs), beq_codeV,
          codeV_toStr]; rfl
  | .ite c a b, t', h, hs => by
    obtain ⟨c', a', b', hc, ha, hb, rfl⟩ := bind3_some (by simpa only [Term.code] using h)
    simp only [Term.nameStrs] at hs
    simp only [Term.denote, code_denote c c' hc (sub_left (sub_left hs)), codeV_toBool]
    split
    · exact code_denote a a' ha (sub_right (sub_left hs))
    · exact code_denote b b' hb (sub_right hs)
  | .ctor e k args, t', h, hs => by
    simp only [Term.code] at h
    split at h
    · cases h
    · rename_i hek
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨args', ha, rfl⟩ := h
      simp only [Term.denote, codes_denote args args' ha (by simpa [Term.nameStrs] using hs)]
      simp [codeV, hek]
theorem codeName_denote : (t t' : Term) → t.codeName d = some t' → (∀ s ∈ t.nameStrs d M, s ∈ S) →
    t'.denote (codedModel d S M) = codeN d S (t.denote M)
  | .shared _ a, t', h, hs => by
    simp only [Term.codeName, Option.map_eq_some_iff] at h
    obtain ⟨a', ha, rfl⟩ := h
    simpa [Term.denote] using codeName_denote a a' ha hs
  | .sel e k j a, t', h, hs => by
    simp only [Term.codeName] at h
    split at h
    · rename_i hek
      obtain ⟨he, hk, hj⟩ := hek
      have he' := he.symm
      subst he' hk hj
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      have hs' : ∀ s ∈ a.nameStrs d M, s ∈ S := fun s hm => hs s (by
        simp only [Term.nameStrs]; exact List.mem_append_right _ hm)
      rw [denote_sel, denote_sel, code_denote a a' ha hs', selOf_codeN]
    · cases h
  | .var _, _, h, _ | .int _, _, h, _ | .str _, _, h, _ | .bool _, _, h, _ | .ref _, _, h, _ | .not _, _, h, _
  | .len _, _, h, _ | .is .., _, h, _ | .and .., _, h, _ | .or .., _, h, _ | .lt .., _, h, _ | .le .., _, h, _
  | .add .., _, h, _ | .sub .., _, h, _ | .mul .., _, h, _ | .div .., _, h, _ | .mod .., _, h, _ | .cat .., _, h, _
  | .eq .., _, h, _ | .slt .., _, h, _ | .ite .., _, h, _ | .ctor .., _, h, _ => by cases h
theorem codes_denote : (ts ts' : List Term) → Term.codes d ts = some ts' → (∀ s ∈ Term.nameStrss d M ts, s ∈ S) →
    Term.denotes (codedModel d S M) ts' = codeVs d S (Term.denotes M ts)
  | [], ts', h, _ => by cases h; rfl
  | t :: ts, ts', h, hs => by
    obtain ⟨t', us, ht, hu, rfl⟩ := bindL_some (by simpa only [Term.codes] using h)
    simp only [Term.nameStrss] at hs
    simp only [Term.denotes, codeVs, code_denote t t' ht (sub_left hs), codes_denote ts us hu (sub_right hs)]
end

end

/-! The script with names as codes has a model wherever the script has one. -/

mutual
/-- The names a value holds in datatype `d`. -/
def Val.names (d : Nat) : Val → List String
  | .ctor e k as =>
    if e = d ∧ k = 1 then
      match as with
      | [.str s] => [s]
      | _ => []
    else Val.namess d as
  | _ => []
def Val.namess (d : Nat) : List Val → List String
  | [] => []
  | v :: vs => Val.names d v ++ Val.namess d vs
end

mutual
/-- `w` is the value `v` with each name `s` in datatype `d` as the code `c s`. Under a constructor 1 of `d` that is
not a name, `w` may hold anything: no value of a variable's type has such a constructor where its type says (`Sorted`),
and SMT-LIB reads nothing in a free slot. -/
def Coded (d : Nat) (c : String → Int) : Val → Val → Prop
  | .ctor e k as, .ctor e' k' bs =>
    e' = e ∧ k' = k ∧ if e = d ∧ k = 1 then ∀ s, as = [.str s] → bs = [.int (c s)] else CodedL d c as bs
  | .ctor .., _ => False
  | .int n, w => w = .int n
  | .bool b, w => w = .bool b
  | .str s, w => w = .str s
def CodedL (d : Nat) (c : String → Int) : List Val → List Val → Prop
  | [], [] => True
  | v :: vs, w :: ws => Coded d c v w ∧ CodedL d c vs ws
  | _, _ => False
end

section
variable {d : Nat} {S : List String}

mutual
theorem coded_codeV : (v : Val) → (∀ s ∈ v.names d, s ∈ S) → Coded d (rank S) v (codeV d S v)
  | .ctor e k as, h => by
    by_cases he : e = d ∧ k = 1
    · obtain ⟨rfl, rfl⟩ := he
      by_cases hs : ∃ s, as = [.str s]
      · obtain ⟨s, rfl⟩ := hs
        have hm : s ∈ S := h s (by simp [Val.names])
        have hv : codeV e S (.ctor e 1 [.str s]) = .ctor e 1 [.int (rank S s)] := by simp [codeV, codeN, hm]
        rw [hv]
        exact ⟨rfl, rfl, by simp only [and_self, ↓reduceIte]; intro s' h'; cases h'; rfl⟩
      · obtain ⟨bs, hb⟩ := codeV_ctor_is (d := e) (S := S) e 1 as
        rw [hb]
        exact ⟨rfl, rfl, by simp only [and_self, ↓reduceIte]; intro s' h'; exact absurd ⟨s', h'⟩ hs⟩
    · have hv : codeV d S (.ctor e k as) = .ctor e k (codeVs d S as) := by simp [codeV, he]
      rw [hv]
      exact ⟨rfl, rfl, by simp only [he, ↓reduceIte]; exact codedL_codeVs as (by simpa [Val.names, he] using h)⟩
  | .int _, _ | .bool _, _ | .str _, _ => rfl
theorem codedL_codeVs : (vs : List Val) → (∀ s ∈ Val.namess d vs, s ∈ S) → CodedL d (rank S) vs (codeVs d S vs)
  | [], _ => trivial
  | v :: vs, h => by
    simp only [Val.namess] at h
    exact ⟨coded_codeV v (sub_left h), codedL_codeVs vs (sub_right h)⟩
end

end

theorem codes_holds {d : Nat} {S : List String} {M : Model} : (ts ts' : List Term) → Term.codes d ts = some ts' →
    (∀ a ∈ ts, (a.denote M).toBool = true) → (∀ s ∈ Term.nameStrss d M ts, s ∈ S) →
    ∀ a ∈ ts', (a.denote (codedModel d S M)).toBool = true
  | [], ts', h, _, _ => by cases h; simp
  | t :: ts, ts', h, hM, hs => by
    obtain ⟨t', us, ht, hu, rfl⟩ := bindL_some (by simpa only [Term.codes] using h)
    simp only [Term.nameStrss] at hs
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [code_denote t a ht (sub_left hs), codeV_toBool]; exact hM t (List.mem_cons_self ..)
    · exact codes_holds ts us hu (fun a h => hM a (List.mem_cons_of_mem _ h)) (sub_right hs) a ha

/-- Names as codes keep models: where every assertion holds in a model, every assertion of the variant with names as
codes holds in a model whose variables `n < k` hold the model's values with names as codes, by one coding `c`. -/
theorem code_model {d : Nat} {ts ts' : List Term} (hc : Term.codes d ts = some ts') (M : Model) (k : Nat)
    (hM : ∀ a ∈ ts, (a.denote M).toBool = true) :
    ∃ (M' : Model) (c : String → Int), (∀ n < k, Coded d c (M.vars n) (M'.vars n)) ∧
      ∀ a ∈ ts', (a.denote M').toBool = true := by
  let S := ((List.range k).flatMap fun n => (M.vars n).names d) ++ Term.nameStrss d M ts
  refine ⟨codedModel d S M, rank S, fun n hn => coded_codeV _ fun s hs => ?_, ?_⟩
  · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨n, List.mem_range.2 hn, hs⟩)
  · exact codes_holds ts ts' hc hM (fun s hs => List.mem_append_right _ hs)

/-! The fixed names keep the order of the codes. -/

section
open Ir.Literal

theorem decimalDigits_ne_nil (n : Nat) : decimalDigits n ≠ [] := by
  rw [decimalDigits]; split <;> simp

theorem decimalDigits_length_le {m n : Nat} (h : m ≤ n) : (decimalDigits m).length ≤ (decimalDigits n).length := by
  induction n using Nat.strongRecOn generalizing m with
  | _ n ih =>
    rw [decimalDigits.eq_1 m, decimalDigits.eq_1 n]
    by_cases hn : n < 10
    · simp [hn, show m < 10 by omega]
    · by_cases hm : m < 10
      · have := decimalDigits_ne_nil (n / 10)
        simp only [hm, hn, ite_true, ite_false, List.length_singleton, List.length_append]
        have := List.length_pos_iff.2 this
        omega
      · simp only [hm, hn, ite_false, List.length_append, List.length_singleton]
        have := @ih (n / 10) (by omega) (m / 10) (by omega)
        omega

theorem lex_append {α : Type} [LT α] {l₁ l₂ : List α} (h : l₁ < l₂) (hl : l₁.length = l₂.length) (a b : List α) :
    l₁ ++ a < l₂ ++ b := by
  induction h with
  | nil => simp at hl
  | rel h => exact List.Lex.rel h
  | cons _ ih => exact List.Lex.cons (ih (by simpa using hl))

/-- Numbers with as many digits compare as their digits do. -/
theorem decimalDigits_lex {m n : Nat} (h : m < n) (hl : (decimalDigits m).length = (decimalDigits n).length) :
    decimalDigits m < decimalDigits n := by
  induction n using Nat.strongRecOn generalizing m with
  | _ n ih =>
    rw [decimalDigits.eq_1 m, decimalDigits.eq_1 n] at hl ⊢
    by_cases hn : n < 10
    · simp only [hn, show m < 10 by omega, ite_true]; exact List.Lex.rel h
    · by_cases hm : m < 10
      · have := List.length_pos_iff.2 (decimalDigits_ne_nil (n / 10))
        simp [hm, hn] at hl
        exact absurd hl (decimalDigits_ne_nil _)
      · simp only [hm, hn, ite_false, List.length_append, List.length_singleton] at hl ⊢
        by_cases hq : m / 10 < n / 10
        · exact lex_append (ih (n / 10) (by omega) hq (by omega)) (by omega) _ _
        · rw [show m / 10 = n / 10 by omega]
          exact List.append_left_lt (List.Lex.rel (by omega))

theorem digitChar_lt {x y : Nat} (hx : x < 10) (hy : y < 10) (h : x < y) : digitChar x < digitChar y := by
  match x, y, hx, hy with
  | 0, 0, _, _ | 0, 1, _, _ | 0, 2, _, _ | 0, 3, _, _ | 0, 4, _, _ | 0, 5, _, _ | 0, 6, _, _ | 0, 7, _, _
  | 0, 8, _, _ | 0, 9, _, _ | 1, 0, _, _ | 1, 1, _, _ | 1, 2, _, _ | 1, 3, _, _ | 1, 4, _, _ | 1, 5, _, _
  | 1, 6, _, _ | 1, 7, _, _ | 1, 8, _, _ | 1, 9, _, _ | 2, 0, _, _ | 2, 1, _, _ | 2, 2, _, _ | 2, 3, _, _
  | 2, 4, _, _ | 2, 5, _, _ | 2, 6, _, _ | 2, 7, _, _ | 2, 8, _, _ | 2, 9, _, _ | 3, 0, _, _ | 3, 1, _, _
  | 3, 2, _, _ | 3, 3, _, _ | 3, 4, _, _ | 3, 5, _, _ | 3, 6, _, _ | 3, 7, _, _ | 3, 8, _, _ | 3, 9, _, _
  | 4, 0, _, _ | 4, 1, _, _ | 4, 2, _, _ | 4, 3, _, _ | 4, 4, _, _ | 4, 5, _, _ | 4, 6, _, _ | 4, 7, _, _
  | 4, 8, _, _ | 4, 9, _, _ | 5, 0, _, _ | 5, 1, _, _ | 5, 2, _, _ | 5, 3, _, _ | 5, 4, _, _ | 5, 5, _, _
  | 5, 6, _, _ | 5, 7, _, _ | 5, 8, _, _ | 5, 9, _, _ | 6, 0, _, _ | 6, 1, _, _ | 6, 2, _, _ | 6, 3, _, _
  | 6, 4, _, _ | 6, 5, _, _ | 6, 6, _, _ | 6, 7, _, _ | 6, 8, _, _ | 6, 9, _, _ | 7, 0, _, _ | 7, 1, _, _
  | 7, 2, _, _ | 7, 3, _, _ | 7, 4, _, _ | 7, 5, _, _ | 7, 6, _, _ | 7, 7, _, _ | 7, 8, _, _ | 7, 9, _, _
  | 8, 0, _, _ | 8, 1, _, _ | 8, 2, _, _ | 8, 3, _, _ | 8, 4, _, _ | 8, 5, _, _ | 8, 6, _, _ | 8, 7, _, _
  | 8, 8, _, _ | 8, 9, _, _ | 9, 0, _, _ | 9, 1, _, _ | 9, 2, _, _ | 9, 3, _, _ | 9, 4, _, _ | 9, 5, _, _
  | 9, 6, _, _ | 9, 7, _, _ | 9, 8, _, _ | 9, 9, _, _ => first | decide | omega

/-- A digit's character comes after `!` and `-` and before `~`. -/
theorem digitChar_between {x : Nat} (hx : x < 10) : '!' < digitChar x ∧ '-' < digitChar x ∧ digitChar x < '~' := by
  match x, hx with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

/-- Digits compared after a map increasing on digits compare as before. -/
theorem lex_map_digits {f : Nat → Char} (w : ∀ x y, x < 10 → y < 10 → x < y → f x < f y) :
    {l₁ l₂ : List Nat} → (∀ x ∈ l₁, x < 10) → (∀ x ∈ l₂, x < 10) → l₁ < l₂ → l₁.map f < l₂.map f
  | [], _ :: _, _, _, _ => List.nil_lt_cons _ _
  | _ :: _, _ :: _, h₁, h₂, .rel h => List.Lex.rel (w _ _ (h₁ _ (by simp)) (h₂ _ (by simp)) h)
  | x :: l₁, _ :: l₂, h₁, h₂, .cons h =>
    List.Lex.cons (lex_map_digits w (fun y hy => h₁ y (by simp [hy])) (fun y hy => h₂ y (by simp [hy])) h)

/-- Digits of one length compared after 9 less each compare the other way. -/
theorem lex_nine_minus : {l₁ l₂ : List Nat} → (∀ x ∈ l₁, x < 10) → (∀ x ∈ l₂, x < 10) → l₁.length = l₂.length →
    l₁ < l₂ → l₂.map (9 - ·) < l₁.map (9 - ·)
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | x :: _, y :: _, h₁, h₂, _, .rel h => by
    have := h₁ x (by simp); have := h₂ y (by simp)
    exact List.Lex.rel (show 9 - y < 9 - x by omega)
  | x :: l₁, _ :: l₂, h₁, h₂, hl, .cons h =>
    List.Lex.cons (lex_nine_minus (fun y hy => h₁ y (by simp [hy])) (fun y hy => h₂ y (by simp [hy]))
      (by simpa using hl) h)

theorem nameOf_ofNat_lt {m n : Nat} (h : m < n) : nameOf (.ofNat m) < nameOf (.ofNat n) := by
  simp only [nameOf, String.lt_iff, String.toList_ofList]
  have hlen := decimalDigits_length_le (Nat.le_of_lt h)
  have hm := List.length_pos_iff.2 (decimalDigits_ne_nil m)
  by_cases he : (decimalDigits m).length = (decimalDigits n).length
  · rw [he]
    exact List.append_left_lt (lex_map_digits (fun _ _ => digitChar_lt) (decimalDigits_lt m) (decimalDigits_lt n)
      (decimalDigits_lex h he))
  · rw [show (decimalDigits n).length - 1 = ((decimalDigits m).length - 1) + ((decimalDigits n).length -
        (decimalDigits m).length) by omega, ← List.replicate_append_replicate, List.append_assoc]
    apply List.append_left_lt
    obtain ⟨k, hk⟩ : ∃ k, (decimalDigits n).length - (decimalDigits m).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      (by omega)).symm⟩
    rw [hk, List.replicate_succ, List.cons_append]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (decimalDigits_ne_nil m)
    rw [hx, List.map_cons]
    exact List.Lex.rel (digitChar_between (decimalDigits_lt m x (by simp [hx]))).2.2

theorem nameOf_negSucc_lt {m n : Nat} (h : n < m) : nameOf (.negSucc m) < nameOf (.negSucc n) := by
  simp only [nameOf, String.lt_iff, String.toList_ofList, List.cons_append]
  apply List.Lex.cons
  have hlen := decimalDigits_length_le (show n + 1 ≤ m + 1 by omega)
  have hn := List.length_pos_iff.2 (decimalDigits_ne_nil (n + 1))
  by_cases he : (decimalDigits (n + 1)).length = (decimalDigits (m + 1)).length
  · rw [he]
    apply List.append_left_lt
    have e : ∀ k, (decimalDigits k).map (fun d => digitChar (9 - d)) = ((decimalDigits k).map (9 - ·)).map digitChar :=
      fun k => by simp [List.map_map, Function.comp_def]
    rw [e, e]
    have hb : ∀ k, ∀ x ∈ (decimalDigits k).map (9 - ·), x < 10 := fun k x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx; omega
    exact lex_map_digits (fun _ _ => digitChar_lt) (hb _) (hb _)
      (lex_nine_minus (decimalDigits_lt _) (decimalDigits_lt _) he (decimalDigits_lex (by omega) he))
  · rw [show (decimalDigits (m + 1)).length - 1 = ((decimalDigits (n + 1)).length - 1) +
        ((decimalDigits (m + 1)).length - (decimalDigits (n + 1)).length) by omega,
      ← List.replicate_append_replicate, List.append_assoc]
    apply List.append_left_lt
    obtain ⟨k, hk⟩ : ∃ k, (decimalDigits (m + 1)).length - (decimalDigits (n + 1)).length = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hk, List.replicate_succ, List.cons_append]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (decimalDigits_ne_nil (n + 1))
    rw [hx, List.map_cons]
    exact List.Lex.rel (digitChar_between (show 9 - x < 10 by omega)).1

theorem nameOf_negSucc_ofNat_lt (m n : Nat) : nameOf (.negSucc m) < nameOf (.ofNat n) := by
  simp only [nameOf, String.lt_iff, String.toList_ofList, List.cons_append]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (decimalDigits_ne_nil n)
  rw [hx]
  cases (x :: xs).length - 1 with
  | zero => exact List.Lex.rel (digitChar_between (decimalDigits_lt n x (by simp [hx]))).2.1
  | succ k => exact List.Lex.rel (by decide)

/-- The names keep the order of the codes, so a model's `<` between codes says what `str.<` says between their names,
and distinct codes have distinct names. -/
theorem nameOf_lt {a b : Int} (h : a < b) : nameOf a < nameOf b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact nameOf_ofNat_lt (by simp only [Int.ofNat_eq_natCast] at h; omega)
    | negSucc n => simp only [Int.ofNat_eq_natCast, Int.negSucc_eq] at h; omega
  | negSucc m =>
    cases b with
    | ofNat n => exact nameOf_negSucc_ofNat_lt m n
    | negSucc n => exact nameOf_negSucc_lt (by simp only [Int.negSucc_eq] at h; omega)

end

end Tazuna.Smt
