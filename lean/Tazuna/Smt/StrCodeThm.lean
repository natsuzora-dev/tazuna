import Tazuna.Smt.StrCode
import Tazuna.Smt.NameCodeThm

/-! Strings as codes keep a script's models (`abs_model`): a model of the script gives one of its abstract variant.
The strings the model compares with `str.<`, with the literals and `""`, are finitely many, so ranking them keeps the
order (`rank`, as for names); every other string gets an Int below 0 that no other string has, so `=` stays exact.
`str.++` and `str.len` read their arguments back through the inverse of the codes. A value where a string belongs that
is not one, which a Lean model may hold in a free slot, is kept apart from every code and reads as `""`, as it reads
in the script. -/

namespace Tazuna.Smt

/-! Coding with sharing is coding. -/

section
variable {dts : List Datatype} {vars : List Srt} {lit : String → Option Nat}

theorem SCodeCache.find?_ok {c : SCodeCache} (hc : c.Ok dts vars lit) {h : UInt64} {t : Term} {r : Option (Term × Srt)}
    (hf : c.find? h t = some r) : t.scode dts vars lit = r := by
  unfold SCodeCache.find? at hf
  split at hf
  · rename_i l hl
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 hf
    have hs : p.1.same t = true := by simpa using List.find?_some hp
    rw [← Term.eq_of_same hs]
    exact hc h l hl p (List.mem_of_find?_eq_some hp)
  · cases hf

theorem SCodeCache.add_ok {c : SCodeCache} (hc : c.Ok dts vars lit) (h : UInt64) {t : Term} {r : Option (Term × Srt)}
    (ht : t.scode dts vars lit = r) : (c.add h t r).Ok dts vars lit := by
  intro h' l hl p hp
  unfold SCodeCache.add at hl
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

theorem SCodeCache.ok_empty : ({} : SCodeCache).Ok dts vars lit := by
  intro h l hl; simp at hl

mutual
theorem Term.scodeC_ok : (t : Term) → (c : SCodeCache) → c.Ok dts vars lit →
    (t.scodeC dts vars lit c).1 = t.scode dts vars lit ∧ (t.scodeC dts vars lit c).2.Ok dts vars lit
  | .shared h t, c, hc => by
    unfold Term.scodeC
    split
    · rename_i r hf; exact ⟨(SCodeCache.find?_ok hc hf).symm, hc⟩
    · have ih := Term.scodeC_ok t c hc
      revert ih
      cases t.scodeC dts vars lit c with
      | mk r c' =>
        intro ih
        simp only at ih ⊢
        have e : (Term.shared h t).scode dts vars lit = r.map fun (t, s) => (.shared h t, s) := by
          simp [Term.scode, ← ih.1]
        exact ⟨e.symm, SCodeCache.add_ok ih.2 h e⟩
  | .var _, c, hc | .int _, c, hc | .str _, c, hc | .bool _, c, hc | .ref _, c, hc | .app .., c, hc => ⟨rfl, hc⟩
  | .not a, c, hc | .len a, c, hc | .is _ _ a, c, hc | .sel _ _ _ a, c, hc => by
    have ih := Term.scodeC_ok a c hc
    simp only [Term.scodeC, Term.scode, ih.1]
    exact ⟨by first | rfl | trivial, ih.2⟩
  | .and a b, c, hc | .or a b, c, hc | .lt a b, c, hc | .le a b, c, hc | .add a b, c, hc | .sub a b, c, hc
  | .mul a b, c, hc | .div a b, c, hc | .mod a b, c, hc | .cat a b, c, hc | .slt a b, c, hc | .eq a b, c, hc => by
    have ha := Term.scodeC_ok a c hc
    have hb := Term.scodeC_ok b _ ha.2
    simp only [Term.scodeC, Term.scode, ha.1, hb.1]
    exact ⟨by first | rfl | trivial, hb.2⟩
  | .ite x a b, c, hc => by
    have hx := Term.scodeC_ok x c hc
    have ha := Term.scodeC_ok a _ hx.2
    have hb := Term.scodeC_ok b _ ha.2
    simp only [Term.scodeC, Term.scode, hx.1, ha.1, hb.1]
    exact ⟨by first | rfl | trivial, hb.2⟩
  | .ctor e k args, c, hc => by
    have ih := Term.scodesC_ok args c hc
    simp only [Term.scodeC, Term.scode, ih.1]
    exact ⟨by first | rfl | trivial, ih.2⟩
theorem Term.scodesC_ok : (ts : List Term) → (c : SCodeCache) → c.Ok dts vars lit →
    (Term.scodesC dts vars lit ts c).1 = Term.scodes dts vars lit ts ∧ (Term.scodesC dts vars lit ts c).2.Ok dts vars lit
  | [], c, hc => ⟨rfl, hc⟩
  | t :: ts, c, hc => by
    have ht := Term.scodeC_ok t c hc
    have hs := Term.scodesC_ok ts _ ht.2
    simp only [Term.scodesC, Term.scodes, ht.1, hs.1]
    exact ⟨by first | rfl | trivial, hs.2⟩
end

end

/-! What each coding step needs of its parts. -/

section
variable {dts : List Datatype}

theorem scode1_some {f : Term → Term} {sa sr : Srt} {x : Option (Term × Srt)} {r : Term × Srt}
    (h : scode1 f sa sr x = some r) : ∃ a, x = some (a, sa) ∧ r = (f a, sr) := by
  match x, h with
  | some (a, s), h =>
    unfold scode1 at h
    by_cases hs : s = sa
    · subst hs; simp only [ite_true, Option.some.injEq] at h; exact ⟨a, rfl, h.symm⟩
    · simp [hs] at h

theorem scode2_some {f : Term → Term → Term} {sa sb sr : Srt} {x y : Option (Term × Srt)} {r : Term × Srt}
    (h : scode2 f sa sb sr x y = some r) : ∃ a b, x = some (a, sa) ∧ y = some (b, sb) ∧ r = (f a b, sr) := by
  match x, y, h with
  | some (a, s), some (b, s'), h =>
    unfold scode2 at h
    by_cases hs : s = sa ∧ s' = sb
    · obtain ⟨rfl, rfl⟩ := hs; simp only [and_self, ite_true, Option.some.injEq] at h; exact ⟨a, b, rfl, rfl, h.symm⟩
    · simp [hs] at h

theorem scodeEq_some {x y : Option (Term × Srt)} {r : Term × Srt} (h : scodeEq x y = some r) :
    ∃ a b s, x = some (a, s) ∧ y = some (b, s) ∧ r = (.eq a b, .bool) := by
  match x, y, h with
  | some (a, s), some (b, s'), h =>
    unfold scodeEq at h
    by_cases hs : s = s'
    · subst hs; simp only [ite_true, Option.some.injEq] at h; exact ⟨a, b, s, rfl, rfl, h.symm⟩
    · simp [hs] at h

theorem scodeIte_some {x y z : Option (Term × Srt)} {r : Term × Srt} (h : scodeIte x y z = some r) :
    ∃ c a b s, x = some (c, .bool) ∧ y = some (a, s) ∧ z = some (b, s) ∧ r = (.ite c a b, s) := by
  match x, y, z, h with
  | some (c, sc), some (a, s), some (b, s'), h =>
    unfold scodeIte at h
    by_cases hs : sc = .bool ∧ s = s'
    · obtain ⟨rfl, rfl⟩ := hs; simp only [and_self, ite_true, Option.some.injEq] at h
      exact ⟨c, a, b, s, rfl, rfl, rfl, h.symm⟩
    · simp [hs] at h

theorem scodeCtor_some {e k : Nat} {xs : Option (List (Term × Srt))} {r : Term × Srt} (h : scodeCtor dts e k xs = some r) :
    ∃ ps, xs = some ps ∧ fieldsOf dts e k = some (ps.map (·.2)) ∧ r = (.ctor e k (ps.map (·.1)), .dt e) := by
  match xs, h with
  | some ps, h =>
    unfold scodeCtor at h
    by_cases hf : fieldsOf dts e k = some (ps.map (·.2))
    · simp only [hf, ite_true, Option.some.injEq] at h; exact ⟨ps, rfl, hf, h.symm⟩
    · simp [hf] at h

theorem scodeIs_some {e k : Nat} {x : Option (Term × Srt)} {r : Term × Srt} (h : scodeIs e k x = some r) :
    ∃ a, x = some (a, .dt e) ∧ r = (.is e k a, .bool) := by
  match x, h with
  | some (a, s), h =>
    unfold scodeIs at h
    by_cases hs : s = .dt e
    · subst hs; simp only [ite_true, Option.some.injEq] at h; exact ⟨a, rfl, h.symm⟩
    · simp [hs] at h

theorem scodeSel_some {e k j : Nat} {x : Option (Term × Srt)} {r : Term × Srt} (h : scodeSel dts e k j x = some r) :
    ∃ a f, x = some (a, .dt e) ∧ fieldSrt? dts e k j = some f ∧ r = (.sel e k j a, f) := by
  match x, h with
  | some (a, s), h =>
    unfold scodeSel at h
    by_cases hs : s = .dt e
    · subst hs
      simp only [ite_true, Option.map_eq_some_iff] at h
      obtain ⟨f, hf, rfl⟩ := h
      exact ⟨a, f, rfl, hf, rfl⟩
    · simp [hs] at h

theorem scodeCons_some {x : Option (Term × Srt)} {xs : Option (List (Term × Srt))} {r : List (Term × Srt)}
    (h : scodeCons x xs = some r) : ∃ p ps, x = some p ∧ xs = some ps ∧ r = p :: ps := by
  match x, xs, h with
  | some p, some ps, h => simp only [scodeCons, Option.some.injEq] at h; exact ⟨p, ps, rfl, rfl, h.symm⟩

end

/-! Codes of strings. -/

/-- A string's code: its rank among `S`, else an Int below 0 that no other string has. -/
def codeOf (S : List String) (s : String) : Int := if s ∈ S then rank S s else -1 - strNum s.toList

theorem codeOf_inj {S : List String} {s t : String} (h : codeOf S s = codeOf S t) : s = t := by
  unfold codeOf at h
  split at h <;> split at h
  · exact rank_inj ‹_› ‹_› h
  · have := rank_nonneg S s; omega
  · have := rank_nonneg S t; omega
  · exact String.ext (strNum_inj _ _ (by omega))

theorem codeOf_empty {S : List String} (h : "" ∈ S) : codeOf S "" = 0 := by
  simp [codeOf, h, rank_empty]

/-- The string of a code, where one has it. -/
noncomputable def decOf (S : List String) (n : Int) : String := by
  classical exact if h : ∃ s, codeOf S s = n then Classical.choose h else ""

theorem decOf_codeOf (S : List String) (s : String) : decOf S (codeOf S s) = s := by
  have h : ∃ s', codeOf S s' = codeOf S s := ⟨s, rfl⟩
  unfold decOf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact codeOf_inj (Classical.choose_spec h)

/-! Values with strings as codes, by the sorts the script declares. -/

section
variable (dts : List Datatype) (c : String → Int)

/-- A value that is not a string where a string belongs: under a constructor, so it is no code. -/
def wrapS (v : Val) : Val := .ctor 0 0 [v]

/-- What a missing field reads as with strings as codes: `default` as `scodeV` codes it. -/
def padOf : Srt → Val
  | .str => wrapS default
  | _ => default

mutual
/-- The value of sort `s` with each string as its code. A constructor whose fields fall short of or exceed its
datatype's keeps the fields the datatype has as they read (missing ones as `default` reads), then its own length, so
it stays apart from every other value and reads as before. -/
def scodeV : Srt → Val → Val
  | .str, .str s => .int (c s)
  | .str, .int n => wrapS (.int n)
  | .str, .bool b => wrapS (.bool b)
  | .str, .ctor e k vs => wrapS (.ctor e k vs)
  | .dt _, .ctor e k vs => match fieldsOf dts e k with
    | some fs => if vs.length = fs.length then .ctor e k (scodeVs fs vs)
      else .ctor e k (scodeVs fs vs ++ (fs.drop vs.length).map padOf ++ [.int vs.length])
    | none => .ctor e k vs
  | .dt _, .int n => .int n
  | .dt _, .bool b => .bool b
  | .dt _, .str s => .str s
  | .int, v => v
  | .bool, v => v
def scodeVs : List Srt → List Val → List Val
  | s :: fs, v :: vs => scodeV s v :: scodeVs fs vs
  | [], vs => vs
  | _ :: _, [] => []
end

end

section
variable {dts : List Datatype} {c : String → Int}

theorem scodeV_int (v : Val) : scodeV dts c .int v = v := by cases v <;> rfl
theorem scodeV_bool (v : Val) : scodeV dts c .bool v = v := by cases v <;> rfl
theorem scodeV_dt (i i' : Nat) (v : Val) : scodeV dts c (.dt i) v = scodeV dts c (.dt i') v := by cases v <;> rfl

theorem padOf_eq (s : Srt) : padOf s = scodeV dts c s default := by cases s <;> rfl

theorem scodeVs_length : (fs : List Srt) → (vs : List Val) → (scodeVs dts c fs vs).length = vs.length
  | _ :: fs, _ :: vs => by simp [scodeVs, scodeVs_length fs vs]
  | [], vs => by cases vs <;> rfl
  | _ :: _, [] => rfl

theorem scodeV_ctor_tags (i e k : Nat) (vs : List Val) : ∃ ws, scodeV dts c (.dt i) (.ctor e k vs) = .ctor e k ws := by
  simp only [scodeV]; split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem append_last {xs ys : List Val} {a b : Val} (h : xs ++ [a] = ys ++ [b]) : xs = ys ∧ a = b := by
  have hl : xs.length = ys.length := by have := congrArg List.length h; simp at this; omega
  have := List.append_inj h hl
  exact ⟨this.1, by simpa using this.2⟩

mutual
theorem scodeV_inj (hc : ∀ s t, c s = c t → s = t) : (s : Srt) → (a b : Val) → scodeV dts c s a = scodeV dts c s b → a = b
  | .int, a, b, h => by simpa [scodeV_int] using h
  | .bool, a, b, h => by simpa [scodeV_bool] using h
  | .str, a, b, h => by
    cases a <;> cases b <;> simp [scodeV, wrapS] at h ⊢ <;> first | exact hc _ _ h | exact h
  | .dt i, .ctor e k as, .ctor e' k' bs, h => by
    obtain ⟨xs, hx⟩ := scodeV_ctor_tags (dts := dts) (c := c) i e k as
    obtain ⟨ys, hy⟩ := scodeV_ctor_tags (dts := dts) (c := c) i e' k' bs
    have hek : e = e' ∧ k = k' := by rw [hx, hy] at h; cases h; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hek
    simp only [scodeV] at h
    split at h
    · rename_i fs _
      have la := scodeVs_length (dts := dts) (c := c) fs as
      have lb := scodeVs_length (dts := dts) (c := c) fs bs
      by_cases ha : as.length = fs.length <;> by_cases hb : bs.length = fs.length <;>
        simp only [ha, hb, ite_true, ite_false, Val.ctor.injEq, true_and] at h
      · rw [scodeVs_inj hc fs as bs h]
      · have := congrArg List.length h; simp [la, lb] at this; omega
      · have := congrArg List.length h; simp [la, lb] at this; omega
      · obtain ⟨h1, h2⟩ := append_last h
        have hn : as.length = bs.length := by simp only [Val.int.injEq] at h2; omega
        rw [hn] at h1
        have h3 := List.append_inj h1 (by simp [la, lb, hn])
        rw [scodeVs_inj hc fs as bs h3.1]
    · simpa using h
  | .dt i, .ctor e k as, .int _, h | .dt i, .ctor e k as, .bool _, h | .dt i, .ctor e k as, .str _, h => by
    obtain ⟨xs, hx⟩ := scodeV_ctor_tags (dts := dts) (c := c) i e k as
    rw [hx] at h; cases h
  | .dt i, .int _, .ctor e k as, h | .dt i, .bool _, .ctor e k as, h | .dt i, .str _, .ctor e k as, h => by
    obtain ⟨xs, hx⟩ := scodeV_ctor_tags (dts := dts) (c := c) i e k as
    rw [hx] at h; cases h
  | .dt _, .int _, .int _, h | .dt _, .bool _, .bool _, h | .dt _, .str _, .str _, h => by simpa [scodeV] using h
  | .dt _, .int _, .bool _, h | .dt _, .int _, .str _, h | .dt _, .bool _, .int _, h | .dt _, .bool _, .str _, h
  | .dt _, .str _, .int _, h | .dt _, .str _, .bool _, h => by simp [scodeV] at h
theorem scodeVs_inj (hc : ∀ s t, c s = c t → s = t) : (fs : List Srt) → (as bs : List Val) →
    scodeVs dts c fs as = scodeVs dts c fs bs → as = bs
  | s :: fs, a :: as, b :: bs, h => by
    simp only [scodeVs, List.cons.injEq] at h; rw [scodeV_inj hc s a b h.1, scodeVs_inj hc fs as bs h.2]
  | [], as, bs, h => by simpa [scodeVs] using h
  | _ :: _, [], [], _ => rfl
  | _ :: _, _ :: _, [], h | _ :: _, [], _ :: _, h => by simp [scodeVs] at h
end

theorem beq_scodeV (hc : ∀ s t, c s = c t → s = t) (s : Srt) (a b : Val) : (scodeV dts c s a == scodeV dts c s b) = (a == b) := by
  show Val.beq _ _ = Val.beq _ _
  apply Bool.eq_iff_iff.2
  rw [val_beq_iff, val_beq_iff]
  exact ⟨scodeV_inj hc s a b, fun h => h ▸ rfl⟩

end

/-! The model with strings as codes. -/

mutual
/-- The strings the term's `str.<` compares in the model: what the order on codes must keep. -/
def Term.sltStrs (M : Model) : Term → List String
  | .slt a b => [(a.denote M).toStr, (b.denote M).toStr] ++ a.sltStrs M ++ b.sltStrs M
  | .shared _ a | .not a | .len a | .is _ _ a | .sel _ _ _ a => a.sltStrs M
  | .and a b | .or a b | .eq a b | .lt a b | .le a b | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .cat a b => a.sltStrs M ++ b.sltStrs M
  | .ite c a b => c.sltStrs M ++ a.sltStrs M ++ b.sltStrs M
  | .ctor _ _ args | .app _ args => Term.sltStrss M args
  | .var _ | .int _ | .str _ | .bool _ | .ref _ => []
def Term.sltStrss (M : Model) : List Term → List String
  | [] => []
  | t :: ts => t.sltStrs M ++ Term.sltStrss M ts
end

section
variable (dts : List Datatype) (vars : List Srt) (litAt : Nat → Option String) (S : List String)

/-- The value `scodeV` codes as `w` at a datatype's sort, where there is one. -/
noncomputable def uncodeD (w : Val) : Val := by
  classical exact if h : ∃ v, scodeV dts (codeOf S) (.dt 0) v = w then Classical.choose h else w

-- A selector of a field no datatype has is never read: the variant selects only fields of its sorts.
set_option linter.tazuna.silentDefault false in
/-- The model's values with strings as codes: each declared variable by its sort, each literal's variable the
literal's code; `str.++` and `str.len` read their arguments back as strings; what SMT-LIB leaves to the model is the
model's, read through the codes. -/
noncomputable def scodedModel (M : Model) : Model where
  vars n := match vars[n]? with
    | some s => scodeV dts (codeOf S) s (M.vars n)
    | none => .int ((litAt n).elim 0 (codeOf S))
  divZero := M.divZero
  modZero := M.modZero
  selOther e k j w := scodeV dts (codeOf S) ((fieldSrt? dts e k j).getD .int) (M.selOther e k j (uncodeD dts S w))
  defs _ := .int 0
  funs f xs := match f, xs with
    | 0, [x, y] => codeOf S (decOf S x ++ decOf S y)
    | 1, [x] => (decOf S x).length
    | _, _ => 0

end

section
variable {dts : List Datatype} {vars : List Srt} {litAt : Nat → Option String} {S : List String} {M : Model}

@[simp] theorem scodedModel_divZero : (scodedModel dts vars litAt S M).divZero = M.divZero := rfl
@[simp] theorem scodedModel_modZero : (scodedModel dts vars litAt S M).modZero = M.modZero := rfl
theorem scodedModel_cat (x y : Int) :
    (scodedModel dts vars litAt S M).funs 0 [x, y] = codeOf S (decOf S x ++ decOf S y) := rfl
theorem scodedModel_len (x : Int) : (scodedModel dts vars litAt S M).funs 1 [x] = (decOf S x).length := rfl

theorem uncodeD_scodeV (i : Nat) (v : Val) : uncodeD dts S (scodeV dts (codeOf S) (.dt i) v) = v := by
  have h : ∃ v', scodeV dts (codeOf S) (.dt 0) v' = scodeV dts (codeOf S) (.dt i) v := ⟨v, scodeV_dt 0 i v⟩
  unfold uncodeD
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact scodeV_inj (fun _ _ => codeOf_inj) (.dt 0) _ _ ((Classical.choose_spec h).trans (scodeV_dt i 0 v))

theorem scodeV_str_toInt (h0 : "" ∈ S) (v : Val) : (scodeV dts (codeOf S) .str v).toInt = codeOf S v.toStr := by
  cases v <;> simp [scodeV, wrapS, Val.toInt, Val.toStr, codeOf_empty h0]

-- `Term.denote`'s default for a missing field.
set_option linter.tazuna.silentDefault false in
theorem scodeVs_getD : (fs : List Srt) → (vs : List Val) → (j : Nat) → (f : Srt) → fs[j]? = some f → j < vs.length →
    (scodeVs dts (codeOf S) fs vs)[j]?.getD default = scodeV dts (codeOf S) f (vs[j]?.getD default)
  | _ :: _, _ :: _, 0, f, hf, _ => by simp at hf; subst hf; rfl
  | _ :: fs, _ :: vs, j + 1, f, hf, hj => by
    simp only [scodeVs, List.getElem?_cons_succ]
    exact scodeVs_getD fs vs j f (by simpa using hf) (by simpa using hj)
  | [], _, _, _, hf, _ => by simp at hf
  | _ :: _, [], _, _, _, hj => by simp at hj

-- `Term.denote`'s default for a missing field.
set_option linter.tazuna.silentDefault false in
/-- A selector reads from a value with strings as codes the coded value it reads. -/
theorem selOf_scodeV {e k j : Nat} {f : Srt} (hf : fieldSrt? dts e k j = some f) (v : Val) :
    selOf (scodedModel dts vars litAt S M) e k j (scodeV dts (codeOf S) (.dt e) v) =
      scodeV dts (codeOf S) f (selOf M e k j v) := by
  have other : ∀ w, selOf M e k j w = M.selOther e k j w →
      selOf (scodedModel dts vars litAt S M) e k j (scodeV dts (codeOf S) (.dt e) w) =
        (scodedModel dts vars litAt S M).selOther e k j (scodeV dts (codeOf S) (.dt e) w) →
      selOf (scodedModel dts vars litAt S M) e k j (scodeV dts (codeOf S) (.dt e) w) =
        scodeV dts (codeOf S) f (selOf M e k j w) := by
    intro w h1 h2; rw [h2, h1]; simp only [scodedModel, hf, Option.getD_some, uncodeD_scodeV]
  cases v with
  | ctor e' k' vs =>
    by_cases hm : e' = e ∧ k' = k
    · obtain ⟨rfl, rfl⟩ := hm
      have hfs : ∃ fs, fieldsOf dts e' k' = some fs ∧ fs[j]? = some f := by
        unfold fieldSrt? at hf
        obtain ⟨fs, h1, h2⟩ := Option.bind_eq_some_iff.1 hf
        exact ⟨fs, h1, h2⟩
      obtain ⟨fs, hfs, hj⟩ := hfs
      have hjf : j < fs.length := (List.getElem?_eq_some_iff.1 hj).1
      simp only [scodeV, hfs]
      by_cases hl : vs.length = fs.length
      · simp only [hl, ite_true, selOf, and_self]
        exact scodeVs_getD fs vs j f hj (by omega)
      · simp only [hl, ite_false, selOf, and_self]
        by_cases hjv : j < vs.length
        · rw [List.append_assoc, List.getElem?_append_left (by rw [scodeVs_length]; exact hjv)]
          exact scodeVs_getD fs vs j f hj hjv
        · have hlen := scodeVs_length (dts := dts) (c := codeOf S) fs vs
          rw [List.append_assoc, List.getElem?_append_right (by omega), List.getElem?_append_left (by simp; omega)]
          simp only [List.getElem?_map, List.getElem?_drop, hlen, Nat.add_sub_cancel' (Nat.le_of_not_lt hjv), hj,
            Option.map_some, Option.getD_some, List.getElem?_eq_none (Nat.le_of_not_lt hjv), Option.getD_none]
          exact padOf_eq f
    · apply other
      · simp only [selOf, hm, ite_false]
      · obtain ⟨ws, hw⟩ := scodeV_ctor_tags (dts := dts) (c := codeOf S) e e' k' vs
        rw [hw]; simp only [selOf, hm, ite_false]
  | _ =>
    apply other <;> rfl

theorem scodeV_is (e e' k : Nat) (v : Val) :
    (match scodeV dts (codeOf S) (.dt e') v with | .ctor d' k' _ => d' == e && k' == k | _ => false) =
      (match v with | .ctor d' k' _ => d' == e && k' == k | _ => false) := by
  cases v with
  | ctor d' k' vs => obtain ⟨ws, hw⟩ := scodeV_ctor_tags (dts := dts) (c := codeOf S) e' d' k' vs; rw [hw]
  | _ => rfl

theorem sub_l {xs ys : List String} (h : ∀ s ∈ xs ++ ys, s ∈ S) : ∀ s ∈ xs, s ∈ S :=
  fun s hm => h s (List.mem_append_left _ hm)

theorem sub_r {xs ys : List String} (h : ∀ s ∈ xs ++ ys, s ∈ S) : ∀ s ∈ ys, s ∈ S :=
  fun s hm => h s (List.mem_append_right _ hm)

theorem denotes_len (M : Model) : (ts : List Term) → (Term.denotes M ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp [Term.denotes, denotes_len M ts]

variable {lit : String → Option Nat}

mutual
/-- A term's variant denotes, in the model with strings as codes, the term's value coded by its sort. -/
theorem scode_denote (h0 : "" ∈ S) (hlit : ∀ x i, lit x = some i → vars[i]? = none ∧ litAt i = some x) : (t : Term) → (r : Term × Srt) → t.scode dts vars lit = some r →
    (∀ s ∈ t.sltStrs M, s ∈ S) →
    r.1.denote (scodedModel dts vars litAt S M) = scodeV dts (codeOf S) r.2 (t.denote M)
  | .var n, r, h, _ => by
    simp only [Term.scode, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    simp [Term.denote, scodedModel, hs]
  | .int n, r, h, _ | .bool n, r, h, _ => by
    simp only [Term.scode, Option.some.injEq] at h; subst h; rfl
  | .str x, r, h, _ => by
    simp only [Term.scode, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hv, hl⟩ := hlit x i hi
    simp [Term.denote, scodedModel, hv, hl, scodeV]
  | .ref _, _, h, _ | .app .., _, h, _ => by simp [Term.scode] at h
  | .shared _ a, r, h, hs => by
    simp only [Term.scode, Option.map_eq_some_iff] at h
    obtain ⟨⟨a', s⟩, ha, rfl⟩ := h
    simpa [Term.denote] using scode_denote h0 hlit a _ ha hs
  | .not a, r, h, hs => by
    obtain ⟨a', ha, rfl⟩ := scode1_some h
    simp only [Term.denote, scode_denote h0 hlit a _ ha hs, scodeV_bool]
  | .len a, r, h, hs => by
    obtain ⟨a', ha, rfl⟩ := scode1_some h
    simp only [Term.denote, Term.denotes, scode_denote h0 hlit a _ ha hs, List.map, scodedModel_len, scodeV_str_toInt h0,
      decOf_codeOf, scodeV_int]
  | .and a b, r, h, hs | .or a b, r, h, hs => by
    obtain ⟨a', b', ha, hb, rfl⟩ := scode2_some h
    simp only [Term.sltStrs] at hs
    simp only [Term.denote, scode_denote h0 hlit a _ ha (sub_l hs), scode_denote h0 hlit b _ hb (sub_r hs), scodeV_bool]
  | .lt a b, r, h, hs | .le a b, r, h, hs | .add a b, r, h, hs | .sub a b, r, h, hs | .mul a b, r, h, hs
  | .div a b, r, h, hs | .mod a b, r, h, hs => by
    obtain ⟨a', b', ha, hb, rfl⟩ := scode2_some h
    simp only [Term.sltStrs] at hs
    simp only [Term.denote, scode_denote h0 hlit a _ ha (sub_l hs), scode_denote h0 hlit b _ hb (sub_r hs), scodeV_int, scodeV_bool,
      scodedModel_divZero, scodedModel_modZero]
  | .cat a b, r, h, hs => by
    obtain ⟨a', b', ha, hb, rfl⟩ := scode2_some h
    simp only [Term.sltStrs] at hs
    simp only [Term.denote, Term.denotes, scode_denote h0 hlit a _ ha (sub_l hs), scode_denote h0 hlit b _ hb (sub_r hs), List.map,
      scodedModel_cat, scodeV_str_toInt h0, decOf_codeOf, scodeV]
  | .slt a b, r, h, hs => by
    obtain ⟨a', b', ha, hb, rfl⟩ := scode2_some h
    simp only [Term.sltStrs] at hs
    have hx : (a.denote M).toStr ∈ S := hs _ (by simp)
    have hy : (b.denote M).toStr ∈ S := hs _ (by simp)
    have hs' : ∀ s ∈ a.sltStrs M ++ b.sltStrs M, s ∈ S := fun s hm => by
      rcases List.mem_append.1 hm with hm | hm
      · exact hs s (List.mem_append_left _ (List.mem_append_right _ hm))
      · exact hs s (List.mem_append_right _ hm)
    simp only [Term.denote, scode_denote h0 hlit a _ ha (sub_l hs'), scode_denote h0 hlit b _ hb (sub_r hs'), scodeV_bool,
      scodeV_str_toInt h0, codeOf, hx, hy, ite_true]
    exact congrArg Val.bool (decide_eq_decide.2 (rank_lt_iff hx hy))
  | .eq a b, r, h, hs => by
    obtain ⟨a', b', s, ha, hb, rfl⟩ := scodeEq_some h
    simp only [Term.sltStrs] at hs
    simp only [Term.denote, scode_denote h0 hlit a _ ha (sub_l hs), scode_denote h0 hlit b _ hb (sub_r hs), scodeV_bool,
      beq_scodeV (fun _ _ => codeOf_inj)]
  | .ite x a b, r, h, hs => by
    obtain ⟨x', a', b', s, hx, ha, hb, rfl⟩ := scodeIte_some h
    simp only [Term.sltStrs] at hs
    simp only [Term.denote, scode_denote h0 hlit x _ hx (sub_l (sub_l hs)), scodeV_bool]
    split
    · exact scode_denote h0 hlit a _ ha (sub_r (sub_l hs))
    · exact scode_denote h0 hlit b _ hb (sub_r hs)
  | .ctor e k args, r, h, hs => by
    obtain ⟨ps, hps, hf, rfl⟩ := scodeCtor_some h
    simp only [Term.sltStrs] at hs
    have hd := scodes_denote h0 hlit args ps hps hs
    have hl : (Term.denotes M args).length = (ps.map (·.2)).length := by
      have := congrArg List.length hd
      rw [scodeVs_length] at this
      simp only [List.length_map] at this ⊢
      have e1 := denotes_len (scodedModel dts vars litAt S M) (ps.map (·.1))
      simp only [List.length_map] at e1
      omega
    simp only [Term.denote, hd, scodeV, hf, hl, ite_true]
  | .is e k a, r, h, hs => by
    obtain ⟨a', ha, rfl⟩ := scodeIs_some h
    simp only [Term.denote, scode_denote h0 hlit a _ ha hs, scodeV_bool]
    exact congrArg Val.bool (scodeV_is e e k _)
  | .sel e k j a, r, h, hs => by
    obtain ⟨a', f, ha, hf, rfl⟩ := scodeSel_some h
    rw [denote_sel, denote_sel, scode_denote h0 hlit a _ ha hs]
    exact selOf_scodeV hf _
theorem scodes_denote (h0 : "" ∈ S) (hlit : ∀ x i, lit x = some i → vars[i]? = none ∧ litAt i = some x) :
    (ts : List Term) → (ps : List (Term × Srt)) → Term.scodes dts vars lit ts = some ps →
    (∀ s ∈ Term.sltStrss M ts, s ∈ S) →
    Term.denotes (scodedModel dts vars litAt S M) (ps.map (·.1)) =
      scodeVs dts (codeOf S) (ps.map (·.2)) (Term.denotes M ts)
  | [], ps, h, _ => by simp only [Term.scodes, Option.some.injEq] at h; subst h; rfl
  | t :: ts, ps, h, hs => by
    obtain ⟨p, ps', hp, hps, rfl⟩ := scodeCons_some h
    simp only [Term.sltStrss] at hs
    simp only [List.map, Term.denotes, scodeVs, scode_denote h0 hlit t p hp (sub_l hs), scodes_denote h0 hlit ts ps' hps (sub_r hs)]
end

end

theorem scodes_holds {dts : List Datatype} {vars : List Srt} {litAt : Nat → Option String} {S : List String}
    {M : Model} {lit : String → Option Nat} (h0 : "" ∈ S)
    (hlit : ∀ x i, lit x = some i → vars[i]? = none ∧ litAt i = some x) :
    (ts : List Term) → (ps : List (Term × Srt)) → Term.scodes dts vars lit ts = some ps → (∀ p ∈ ps, p.2 = .bool) →
    (∀ a ∈ ts, (a.denote M).toBool = true) → (∀ s ∈ Term.sltStrss M ts, s ∈ S) →
    ∀ p ∈ ps, (p.1.denote (scodedModel dts vars litAt S M)).toBool = true
  | [], ps, h, _, _, _ => by simp only [Term.scodes, Option.some.injEq] at h; subst h; simp
  | t :: ts, ps, h, hb, hM, hs => by
    obtain ⟨p, ps', hp, hps, rfl⟩ := scodeCons_some h
    simp only [Term.sltStrss] at hs
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · rw [scode_denote h0 hlit t q hp (sub_l hs), hb q (List.mem_cons_self ..), scodeV_bool]
      exact hM t (List.mem_cons_self ..)
    · exact scodes_holds h0 hlit ts ps' hps (fun p hp => hb p (List.mem_cons_of_mem _ hp))
        (fun a ha => hM a (List.mem_cons_of_mem _ ha)) (sub_r hs) q hq

/-! Strings as codes keep values in their sorts, strings being Ints where the solver reads codes. -/

section
variable {dts : List Datatype} {c : String → Int}

theorem fieldsOf_code (e k : Nat) :
    fieldsOf (dts.map Datatype.code) e k = (fieldsOf dts e k).map (·.map Srt.code) := by
  unfold fieldsOf
  rw [List.getElem?_map]
  cases dts[e]? with
  | none => rfl
  | some d => simp [Datatype.code, List.getElem?_map]

theorem fieldSrt_code (e k j : Nat) :
    fieldSrt? (dts.map Datatype.code) e k j = (fieldSrt? dts e k j).map Srt.code := by
  show (fieldsOf _ e k).bind (·[j]?) = ((fieldsOf dts e k).bind (·[j]?)).map Srt.code
  rw [fieldsOf_code]
  cases fieldsOf dts e k with
  | none => rfl
  | some fs => simp [List.getElem?_map]

theorem inSrts_length : (fs : List Srt) → (vs : List Val) → Val.InSrts dts fs vs → vs.length = fs.length
  | [], [], _ => rfl
  | _ :: fs, _ :: vs, h => by simp [inSrts_length fs vs h.2]
  | [], _ :: _, h | _ :: _, [], h => nomatch h

mutual
theorem scodeV_inSrt : (s : Srt) → (v : Val) → Val.InSrt dts s v →
    Val.InSrt (dts.map Datatype.code) s.code (scodeV dts c s v)
  | .int, .int _, _ | .bool, .bool _, _ | .str, .str _, _ => trivial
  | .dt i, .ctor e k vs, h => by
    obtain ⟨rfl, fs, hfs, hvs⟩ := h
    have hfs' : fieldsOf dts e k = some fs := hfs
    have hl := inSrts_length fs vs hvs
    simp only [scodeV, hfs', hl, ite_true, Srt.code]
    refine ⟨rfl, fs.map Srt.code, ?_, scodeVs_inSrts fs vs hvs⟩
    show fieldsOf _ e k = _
    rw [fieldsOf_code, hfs']; rfl
  | .int, .bool _, h | .int, .str _, h | .int, .ctor .., h | .bool, .int _, h | .bool, .str _, h
  | .bool, .ctor .., h | .str, .int _, h | .str, .bool _, h | .str, .ctor .., h | .dt _, .int _, h
  | .dt _, .bool _, h | .dt _, .str _, h => nomatch h
theorem scodeVs_inSrts : (fs : List Srt) → (vs : List Val) → Val.InSrts dts fs vs →
    Val.InSrts (dts.map Datatype.code) (fs.map Srt.code) (scodeVs dts c fs vs)
  | [], [], _ => trivial
  | s :: fs, v :: vs, h => ⟨scodeV_inSrt s v h.1, scodeVs_inSrts fs vs h.2⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h
end

mutual
theorem inSrt_uncode : (s : Srt) → (w : Val) → Val.InSrt (dts.map Datatype.code) s.code w → ∃ v, Val.InSrt dts s v
  | .int, _, _ => ⟨.int 0, trivial⟩
  | .bool, _, _ => ⟨.bool false, trivial⟩
  | .str, _, _ => ⟨.str "", rfl⟩
  | .dt i, .ctor e k ws, h => by
    obtain ⟨rfl, fs', hfs', hws⟩ := h
    have hf : fieldsOf (dts.map Datatype.code) e k = some fs' := hfs'
    rw [fieldsOf_code] at hf
    obtain ⟨fs, hfs, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨vs, hvs⟩ := inSrts_uncode fs ws hws
    exact ⟨.ctor e k vs, rfl, fs, hfs, hvs⟩
  | .dt _, .int _, h | .dt _, .bool _, h | .dt _, .str _, h => nomatch h
theorem inSrts_uncode : (fs : List Srt) → (ws : List Val) →
    Val.InSrts (dts.map Datatype.code) (fs.map Srt.code) ws → ∃ vs, Val.InSrts dts fs vs
  | [], [], _ => ⟨[], trivial⟩
  | s :: fs, w :: ws, h => by
    obtain ⟨v, hv⟩ := inSrt_uncode s w h.1
    obtain ⟨vs, hvs⟩ := inSrts_uncode fs ws h.2
    exact ⟨v :: vs, hv, hvs⟩
  | [], _ :: _, h | _ :: _, [], h => nomatch h
end

end

section
variable {dts : List Datatype} {vars : List Srt} {litAt : Nat → Option String} {S : List String}

/-- The model with strings as codes gives values of their fields' sorts on other constructors where the model does. -/
theorem selSorted_scoded {M : Model} (hM : SelSorted dts M) :
    SelSorted (dts.map Datatype.code) (scodedModel dts vars litAt S M) := by
  intro e k j s v hf hinh
  rw [fieldSrt_code] at hf
  obtain ⟨f, hf', rfl⟩ := Option.map_eq_some_iff.1 hf
  obtain ⟨w, hw⟩ := hinh
  obtain ⟨w', hw'⟩ := inSrt_uncode f w hw
  simp only [scodedModel, hf', Option.getD_some]
  exact scodeV_inSrt f _ (hM e k j f _ hf' ⟨w', hw'⟩)

end

/-! The variant has a model wherever the script has one. -/

theorem litVar_some {lits : List String} {base : Nat} {x : String} {i : Nat} (h : litVar lits base x = some i) :
    base ≤ i ∧ lits[i - base]? = some x := by
  unfold litVar at h
  obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hl, hx, _⟩ := List.idxOf?_eq_some_iff.1 hi
  refine ⟨Nat.le_add_right _ _, ?_⟩
  rw [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hl, hx]

theorem Script.abs_some {s s' : Script} (h : s.abs = some s') :
    ∃ ps, (Term.scodesC s.datatypes s.vars (litVar s.lits s.vars.length) s.asserts {}).1 = some ps ∧
      (ps.all fun x => x.2 == Srt.bool) = true ∧
      s' = ⟨s.datatypes.map Datatype.code, s.vars.map Srt.code ++ s.lits.map (fun _ => Srt.int), [2, 1],
        ps.map (·.1) ++ litOrder s.lits s.vars.length, List.range (s.vars.length + s.lits.length)⟩ := by
  unfold Script.abs at h
  simp only [guard] at h
  by_cases h1 : s.funs.isEmpty = true
  · by_cases h2 : s.hasStrings s.lits = true
    · cases hps : (Term.scodesC s.datatypes s.vars (litVar s.lits s.vars.length) s.asserts {}).1 with
      | none => simp [h1, h2, hps] at h
      | some ps =>
        by_cases h3 : (ps.all fun x => x.2 == Srt.bool) = true
        · simp [h1, h2, hps, h3] at h
          exact ⟨ps, rfl, h3, h.symm⟩
        · simp [h1, h2, hps, h3, show (failure : Option Unit) = none from rfl] at h
    · simp [h1, h2, show (failure : Option Unit) = none from rfl] at h
  · simp [h1, show (failure : Option Unit) = none from rfl] at h

/-- The variable of literal `n - base` among `lits`, where `n` is one. -/
def litAtOf (lits : List String) (base n : Nat) : Option String := if base ≤ n then lits[n - base]? else none

/-- Strings as codes keep models: where every assertion of a script holds in a model whose selectors on other
constructors give values of their fields' sorts, every assertion of its abstract variant holds in a model whose
declared variables hold the model's values with strings as codes, by one coding `c` and the script's sorts, whose
literals' variables hold Ints, and whose selectors on other constructors give values of their fields' sorts. -/
theorem abs_model {s s' : Script} (h : s.abs = some s') (M : Model) (hM : ∀ a ∈ s.asserts, (a.denote M).toBool = true)
    (hS : SelSorted s.datatypes M) :
    ∃ (M' : Model) (c : String → Int),
      (∀ n σ, s.vars[n]? = some σ → M'.vars n = scodeV s.datatypes c σ (M.vars n)) ∧
      (∀ n, s.vars.length ≤ n → ∃ i, M'.vars n = .int i) ∧
      SelSorted s'.datatypes M' ∧ ∀ a ∈ s'.asserts, (a.denote M').toBool = true := by
  obtain ⟨ps, hps, hall, rfl⟩ := Script.abs_some h
  rw [(Term.scodesC_ok s.asserts {} SCodeCache.ok_empty).1] at hps
  let lits := s.lits
  let base := s.vars.length
  let S := "" :: lits ++ Term.sltStrss M s.asserts
  let litAt := litAtOf lits base
  have hlit : ∀ x i, litVar lits base x = some i → s.vars[i]? = none ∧ litAt i = some x := by
    intro x i hx
    obtain ⟨hle, hl⟩ := litVar_some hx
    exact ⟨List.getElem?_eq_none hle, by simp [litAt, litAtOf, hle, hl]⟩
  have h0 : "" ∈ S := List.mem_cons_self ..
  have hlits : ∀ x ∈ lits, x ∈ S := fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  have hslt : ∀ x ∈ Term.sltStrss M s.asserts, x ∈ S := fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _ hx)
  refine ⟨scodedModel s.datatypes s.vars litAt S M, codeOf S, fun n σ hn => by simp [scodedModel, hn],
    fun n hn => by simp [scodedModel, List.getElem?_eq_none hn], selSorted_scoded hS, ?_⟩
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · -- an assertion's variant
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
    exact scodes_holds h0 hlit s.asserts ps hps (fun p hp => by simpa using List.all_eq_true.1 hall p hp) hM hslt p hp
  · -- the literals' order
    obtain ⟨⟨x, y⟩, _, hxy⟩ := List.mem_filterMap.1 ha
    by_cases hlt : x < y
    case neg => simp [hlt] at hxy
    simp only [hlt, ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hxy
    obtain ⟨i, hi, i', hi', rfl⟩ := hxy
    obtain ⟨hv, hl⟩ := hlit x i hi
    obtain ⟨hv', hl'⟩ := hlit y i' hi'
    have hx : x ∈ S := hlits x (by have := litVar_some hi; exact List.mem_of_getElem? this.2)
    have hy : y ∈ S := hlits y (by have := litVar_some hi'; exact List.mem_of_getElem? this.2)
    have e1 : (scodedModel s.datatypes s.vars litAt S M).vars i = .int (codeOf S x) := by simp [scodedModel, hv, hl]
    have e2 : (scodedModel s.datatypes s.vars litAt S M).vars i' = .int (codeOf S y) := by
      simp [scodedModel, hv', hl']
    simp only [Term.denote, e1, e2, Val.toInt, Val.toBool, decide_eq_true_eq, codeOf, hx, hy, ite_true]
    exact rank_lt hx hlt

end Tazuna.Smt
