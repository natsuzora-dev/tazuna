import Tazuna.Smt.Encode

/-! T1, `encode_agrees`: in every model where the encoding's condition holds and whose variables denote the values
of the expression's variables, a code denotes what `eval` computes. It holds for every model, so no answer of the
solver can rest on a value SMT-LIB leaves open, such as dividing by zero or a selector on another constructor. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (M : Model) (L : Layout)

/-- A condition holds in the model. -/
def Holds (c : Term) : Prop := (c.denote M).toBool = true

def altsBool : Ty.alts [[], []] → Bool
  | .inl _ => true
  | .inr _ => false

/-- An id as a value of its datatype `d`: a fresh one by its number, an outside one by its name. -/
def idVal (d : Nat) : IdV → Val
  | .fresh n => .ctor d 0 [.int n]
  | .named s => .ctor d 1 [.str s]

mutual
/-- A value of a first-order type and the SMT value that codes it. -/
def RelV : (t : Ty) → t.den → Val → Prop
  | .int, x, v => v = .int x
  | .str, x, v => v = .str x
  | .date, x, v => v = .int x
  | .id, x, v => ∃ d n, L.find? .id = some (d, n) ∧ v = idVal d x
  | .adt 0 _ vs, x, v => ∃ h : vs = [[], []], v = .bool (altsBool (h ▸ x))
  | .adt (i + 1) a vs, x, v => ∃ d n, L.find? (.adt (i + 1) a vs) = some (d, n) ∧ RelAlts d 0 vs x v
  | .tuple ts, x, v => ∃ d n vals, L.find? (.tuple ts) = some (d, n) ∧ v = .ctor d 0 vals ∧ RelVs ts x vals
  /- The slots hold the bag's items in some order. -/
  | .bag t, xs, v => ∃ d n dt m sv, L.find? (.bag t) = some (d, n) ∧ L.find? (.tuple [Ty.bool, t]) = some (dt, m) ∧
      sv.length = n ∧ v = slotsVal d dt sv ∧ (∀ p ∈ sv, p.2.length = 1) ∧
      ∃ ys : List t.den, ys.Perm xs ∧ Holds2 (fun y vs => ∃ z, vs = [z] ∧ RelV t y z) ys sv
  | .table k w, x, v => ∃ d n dt m sv, L.find? (.table k w) = some (d, n) ∧
      L.find? (.tuple [Ty.bool, k, w]) = some (dt, m) ∧ sv.length = n ∧ v = slotsVal d dt sv ∧
      (∀ p ∈ sv, p.2.length = 2) ∧ ∃ ys : List (k.den × w.den), ys.Perm x.1 ∧
        Holds2 (fun e vs => ∃ zk zv, vs = [zk, zv] ∧ RelV k e.1 zk ∧ RelV w e.2 zv) ys sv
  | .list _, _, _ | .fn .., _, _ | .param _, _, _ | .dsl .., _, _ => False
def RelVs : (ts : List Ty) → Ty.dens ts → List Val → Prop
  | [], _, vals => vals = []
  | t :: ts, (x, xs), vals => ∃ v vs, vals = v :: vs ∧ RelV t x v ∧ RelVs ts xs vs
/-- The value is constructor `k + j` of datatype `d` when it is the `j`-th variant of `vs`. -/
def RelAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.alts vs → Val → Prop
  | k, fs :: _, .inl x, v => ∃ vals, v = .ctor d k vals ∧ RelVs fs x vals
  | k, _ :: vs, .inr y, v => RelAlts d (k + 1) vs y v
end

mutual
/-- A value and its code: a term denoting the value, codes of a list's items, or a function that maps related
arguments to a related result wherever its condition holds. -/
def Rel : (t : Ty) → t.den → Code t → Prop
  | .fn ps r, f, sf => ∀ xs ss, Rels ps xs ss → ∀ s c, sf ss = .ok (s, c) → Holds M c → Rel r (f xs) s
  | .list t, xs, ss => Forall2 (Rel t) xs ss
  | .int, x, s => RelV L .int x (Term.denote M s)
  | .str, x, s => RelV L .str x (Term.denote M s)
  | .tuple ts, x, s => RelV L (.tuple ts) x (Term.denote M s)
  | .adt i a vs, x, s => RelV L (.adt i a vs) x (Term.denote M s)
  | .param k, x, s => RelV L (.param k) x (Term.denote M s)
  | .bag t, x, s => RelV L (.bag t) x (Term.denote M s)
  | .table k v, x, s => RelV L (.table k v) x (Term.denote M s)
  | .date, x, s => RelV L .date x (Term.denote M s)
  | .id, x, s => RelV L .id x (Term.denote M s)
  | .dsl k a, x, s => RelV L (.dsl k a) x (Term.denote M s)
def Rels : (ts : List Ty) → Ty.dens ts → Codes ts → Prop
  | [], _, _ => True
  | t :: ts, (x, xs), (s, ss) => Rel t x s ∧ Rels ts xs ss
end

end

section
variable {M : Model} {L : Layout}

theorem rel_term : {t : Ty} → {s : Code t} → {x : Term} → Code.term? t s = some x → (v : t.den) →
    (Rel M L t v s ↔ RelV L t v (x.denote M))
  | .fn .., _, _, h, _ | .list _, _, _, h, _ => nomatch h
  | .int, _, _, h, _ | .str, _, _, h, _ | .tuple _, _, _, h, _ | .adt .., _, _, h, _ | .param _, _, _, h, _
  | .bag _, _, _, h, _ | .table .., _, _, h, _ | .date, _, _, h, _ | .id, _, _, h, _ | .dsl .., _, _, h, _ => by
    cases h; exact Iff.rfl

theorem rel_ofTerm : {t : Ty} → {x : Term} → {s : Code t} → Code.ofTerm? t x = some s → (v : t.den) →
    (Rel M L t v s ↔ RelV L t v (x.denote M))
  | .fn .., _, _, h, _ | .list _, _, _, h, _ => nomatch h
  | .int, _, _, h, _ | .str, _, _, h, _ | .tuple _, _, _, h, _ | .adt .., _, _, h, _ | .param _, _, _, h, _
  | .bag _, _, _, h, _ | .table .., _, _, h, _ | .date, _, _, h, _ | .id, _, _, h, _ | .dsl .., _, _, h, _ => by
    cases h; exact Iff.rfl

theorem rels_terms : {ts : List Ty} → {ss : Codes ts} → {xs : List Term} → Codes.terms? ts ss = some xs →
    (vs : Ty.dens ts) → Rels M L ts vs ss → RelVs L ts vs (Term.denotes M xs)
  | [], (), _, h, _, _ => by cases h; rfl
  | t :: ts, (s, ss), xs, h, (v, vs), ⟨h1, h2⟩ => by
    cases hx : Code.term? t s with
    | none => simp [Codes.terms?, hx] at h
    | some x =>
      cases hy : Codes.terms? ts ss with
      | none => simp [Codes.terms?, hx, hy] at h
      | some ys =>
        simp only [Codes.terms?, hx, hy, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        exact ⟨_, _, rfl, (rel_term hx v).1 h1, rels_terms hy vs h2⟩

theorem rels_ofTerms : {ts : List Ty} → {xs : List Term} → {ss : Codes ts} → Codes.ofTerms? ts xs = some ss →
    (vs : Ty.dens ts) → RelVs L ts vs (Term.denotes M xs) → Rels M L ts vs ss
  | [], [], _, _, _, _ => trivial
  | t :: ts, x :: xs, ss, h, (v, vs), hr => by
    cases hx : Code.ofTerm? t x with
    | none => simp [Codes.ofTerms?, hx] at h
    | some s =>
      cases hy : Codes.ofTerms? ts xs with
      | none => simp [Codes.ofTerms?, hx, hy] at h
      | some ss' =>
        simp only [Codes.ofTerms?, hx, hy, bind, Option.bind, pure] at h
        cases h
        obtain ⟨w, ws, e, h1, h2⟩ := hr
        simp only [Term.denotes, List.cons.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨(rel_ofTerm hx v).2 h1, rels_ofTerms hy vs h2⟩
  | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _ => nomatch h

theorem var_rel : {Γ : List Ty} → {t : Ty} → (v : Var Γ t) → (ρ : Ty.dens Γ) → (σ : Codes Γ) → Rels M L Γ ρ σ →
    Rel M L t (v.get ρ) (v.code σ)
  | _ :: _, _, .here, (_, _), (_, _), h => h.1
  | _ :: _, _, .there v, (_, _), (_, _), h => var_rel v _ _ h.2

theorem rels_append : {a b : List Ty} → (x : Ty.dens a) → (y : Ty.dens b) → (s : Codes a) → (t : Codes b) →
    Rels M L a x s → Rels M L b y t → Rels M L (a ++ b) (Dens.append x y) (Codes.append s t)
  | [], _, (), _, (), _, _, h => h
  | _ :: _, _, (_, _), _, (_, _), _, h1, h2 => ⟨h1.1, rels_append _ _ _ _ h1.2 h2⟩

theorem holds_and (a b : Term) : Holds M (.and a b) ↔ Holds M a ∧ Holds M b := by
  simp [Holds, Term.denote, Val.toBool]

theorem holds_andT (a b : Term) : Holds M (andT a b) ↔ Holds M a ∧ Holds M b := by
  unfold andT
  split
  · simp [Holds, Term.denote, Val.toBool]
  · simp [Holds, Term.denote, Val.toBool]
  · exact holds_and a b

theorem holds_tt : Holds M tt := rfl

theorem holds_ite (c a b : Term) : Holds M (.ite c a b) ↔ if (c.denote M).toBool then Holds M a else Holds M b := by
  simp only [Holds, Term.denote]; split <;> simp

theorem denote_andT (a b : Term) (x y : Bool) (ha : a.denote M = .bool x) (hb : b.denote M = .bool y) :
    (andT a b).denote M = .bool (x && y) := by
  unfold andT
  split
  · simp only [Term.denote] at ha; cases ha; simpa using hb
  · simp only [Term.denote] at hb; cases hb; simpa using ha
  · simp [Term.denote, ha, hb, Val.toBool]

theorem rel_ite? {t : Ty} {c : Term} {a b r : Code t} (h : Code.ite? t c a b = some r) (x : t.den)
    (hx : Rel M L t x (if (c.denote M).toBool then a else b)) : Rel M L t x r := by
  cases hta : Code.term? t a with
  | none => simp [Code.ite?, hta] at h
  | some ta =>
    cases htb : Code.term? t b with
    | none => simp [Code.ite?, hta, htb] at h
    | some tb =>
      simp only [Code.ite?, hta, htb, bind, Option.bind] at h
      rw [rel_ofTerm h]
      simp only [Term.denote]
      split
      · rename_i hc; simp only [hc, ite_true] at hx; exact (rel_term hta x).1 hx
      · rename_i hc; simp only [hc] at hx; exact (rel_term htb x).1 hx

end

section
variable {M : Model} {L : Layout}

theorem relAlts_inj (d : Nat) : (k : Nat) → {vs : List (List Ty)} → (v : Fin vs.length) → (y : Ty.dens (vs.get v)) →
    (vals : List Val) → RelVs L (vs.get v) y vals → RelAlts L d k vs (Alts.inj v y) (.ctor d (k + v.val) vals)
  | k, _ :: _, ⟨0, _⟩, _, _, h => ⟨_, rfl, h⟩
  | k, _ :: _, ⟨j + 1, hj⟩, y, vals, h => by
    have := relAlts_inj d (k + 1) (vs := _) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ y vals h
    simp only [Alts.inj, RelAlts]
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact this

theorem relAlts_view (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : Ty.alts vs) → (w : Val) →
    RelAlts L d k vs x w →
    ∃ vals, w = .ctor d (k + (Alts.view x).1.val) vals ∧ RelVs L (vs.get (Alts.view x).1) (Alts.view x).2 vals
  | k, _ :: _, .inl _, _, ⟨vals, e, h⟩ => ⟨vals, by simpa [Alts.view] using e, h⟩
  | k, _ :: vs, .inr y, w, h => by
    obtain ⟨vals, e, hv⟩ := relAlts_view d (k + 1) vs y w h
    refine ⟨vals, ?_, ?_⟩
    · rcases hvy : Alts.view y with ⟨⟨j, hj⟩, z⟩
      rw [hvy] at e
      simp only [Alts.view, hvy]; rw [e]; congr 1; simp only at *; omega
    · simp only [Alts.view]; exact hv

theorem relAlts_proj (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : Ty.alts vs) → (w : Val) →
    RelAlts L d k vs x w → (v : Fin vs.length) →
    ∃ j vals, w = .ctor d j vals ∧ (j = k + v.val ↔ (Alts.proj x v).isSome) ∧
      ∀ y, Alts.proj x v = some y → RelVs L (vs.get v) y vals
  | k, _ :: _, .inl _, _, ⟨vals, e, h⟩, ⟨0, _⟩ =>
    ⟨k, vals, e, iff_of_true (by simp) rfl, fun y hy => by cases hy; exact h⟩
  | k, _ :: _, .inl _, _, ⟨vals, e, _⟩, ⟨j + 1, _⟩ =>
    ⟨k, vals, e, iff_of_false (by simp) (fun hh => nomatch hh), fun y hy => nomatch hy⟩
  | k, _ :: vs, .inr y, w, h, ⟨0, _⟩ => by
    obtain ⟨vals, e, _⟩ := relAlts_view d (k + 1) vs y w h
    exact ⟨_, vals, e, iff_of_false (by simp; omega) (fun hh => nomatch hh), fun y hy => nomatch hy⟩
  | k, _ :: vs, .inr y, w, h, ⟨j + 1, hj⟩ => by
    obtain ⟨i, vals, e, hi, hv⟩ := relAlts_proj d (k + 1) vs y w h ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    refine ⟨i, vals, e, ?_, fun z hz => hv z hz⟩
    rw [show k + (j + 1) = k + 1 + j by omega]
    exact hi

theorem relVs_length : {ts : List Ty} → (y : Ty.dens ts) → (vals : List Val) → RelVs L ts y vals →
    vals.length = ts.length
  | [], _, _, h => by simp only [RelVs] at h; simp [h]
  | _ :: _, (_, _), _, ⟨_, _, e, _, h⟩ => by subst e; simp [relVs_length _ _ h]

theorem relVs_field : {ts : List Ty} → {t : Ty} → (y : Ty.dens ts) → (vals : List Val) → RelVs L ts y vals →
    (k : Nat) → (h : ts[k]? = some t) → RelV L t (Dens.field y k h) (vals[k]?.getD default)
  | [], _, _, _, _, _, h => nomatch h
  | _ :: _, _, (_, _), _, ⟨v, _, e, h1, _⟩, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h e; exact h1
  | _ :: _, _, (_, _), _, ⟨_, _, e, _, h2⟩, k + 1, h => by
    subst e; exact relVs_field _ _ h2 k (by simpa using h)

theorem relVs_get : {ts : List Ty} → (y : Ty.dens ts) → (vals : List Val) → RelVs L ts y vals →
    (k : Fin ts.length) → RelV L (ts.get k) (Dens.get y k) (vals[k.val]?.getD default)
  | _ :: _, (_, _), _, ⟨_, _, e, h1, _⟩, ⟨0, _⟩ => by subst e; exact h1
  | _ :: _, (_, _), _, ⟨_, _, e, _, h2⟩, ⟨k + 1, hk⟩ => by
    subst e; exact relVs_get _ _ h2 ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem denotes_sels (M : Model) (d k : Nat) (x : Term) (vals : List Val) (hx : x.denote M = .ctor d k vals) :
    Term.denotes M ((List.range vals.length).map fun j => .sel d k j x) = vals := by
  have : ∀ (ts : List Term), Term.denotes M ts = ts.map (Term.denote M) := by
    intro ts; induction ts with
    | nil => rfl
    | cons t ts ih => simp [Term.denotes, ih]
  rw [this, List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [Term.denote, hx, h2]

theorem fieldT_denote (d j : Nat) (x : Term) (i : Nat) (vals : List Val) (hx : x.denote M = .ctor d i vals) :
    (k n : Nat) → k ≤ i → i ≤ k + n → (fieldT d j x k n).denote M = vals[j]?.getD default
  | k, 0, h1, h2 => by
    have : i = k := by omega
    subst this; simp [fieldT, Term.denote, hx]
  | k, n + 1, h1, h2 => by
    simp only [fieldT, Term.denote, hx, Val.toBool]
    by_cases hk : i = k
    · subst hk; simp
    · have : (i == k) = false := by simpa using hk
      simp only [BEq.rfl, Bool.true_and, this, Bool.false_eq_true, ite_false]
      exact fieldT_denote d j x i vals hx (k + 1) n (by omega) (by omega)

/-- A constructor's code denotes the value it builds. -/
theorem adtCtor_rel {i : Nat} {args : List Ty} {vs : List (List Ty)} (v : Fin vs.length) (fs : List Term) (t : Term)
    (h : adtCtor L i args vs v.val fs = .ok t) (y : Ty.dens (vs.get v)) (hy : RelVs L (vs.get v) y (Term.denotes M fs)) :
    RelV L (.adt i args vs) (Alts.inj v y) (t.denote M) := by
  cases i with
  | zero =>
    simp only [adtCtor] at h
    split at h
    · rename_i hb
      cases h
      obtain ⟨rfl⟩ := (by revert hb; unfold boolVs?; split <;> simp : vs = [[], []])
      refine ⟨rfl, ?_⟩
      match v with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    · cases h
  | succ i =>
    simp only [adtCtor] at h
    split at h
    · rename_i d n hf
      cases h
      refine ⟨d, n, hf, ?_⟩
      simp only [Term.denote]
      simpa using relAlts_inj (L := L) d 0 v y _ hy
    · cases h

/-- A constructor test and its fields' terms denote whether the value is that variant, and its fields. -/
theorem adtView_rel {i : Nat} {args : List Ty} {vs : List (List Ty)} (v : Fin vs.length) (s : Term)
    (x : Ty.alts vs) (hx : RelV L (.adt i args vs) x (s.denote M)) (m : Term) (fts : List Term)
    (h : adtView L i args vs v.val s = .ok (m, fts)) :
    m.denote M = .bool (Alts.proj x v).isSome ∧
      ∀ y, Alts.proj x v = some y → RelVs L (vs.get v) y (Term.denotes M fts) := by
  cases i with
  | zero =>
    obtain ⟨rfl, hs⟩ := hx
    simp only [adtView, boolVs?, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, fun y _ => by match v with | ⟨0, _⟩ | ⟨1, _⟩ => simp [RelVs, Term.denotes]⟩
    match v, x with
    | ⟨0, _⟩, .inl () => simp only [↓reduceIte, hs]; rfl
    | ⟨0, _⟩, .inr (.inl ()) => simp only [↓reduceIte, hs]; rfl
    | ⟨1, _⟩, .inl () => show Term.denote M (Term.not s) = _; simp only [Term.denote, hs]; rfl
    | ⟨1, _⟩, .inr (.inl ()) => show Term.denote M (Term.not s) = _; simp only [Term.denote, hs]; rfl
  | succ i =>
    obtain ⟨d, n, hf, hr⟩ := hx
    simp only [adtView, hf, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨j, vals, e, hiff, hv⟩ := relAlts_proj d 0 vs x _ hr v
    refine ⟨?_, fun y hy => ?_⟩
    · simp only [Term.denote, e]
      congr 1
      rw [Nat.zero_add] at hiff
      cases hp : (Alts.proj x v).isSome
      · have : j ≠ v.val := fun hj => by rw [hiff.1 hj] at hp; cases hp
        simpa using this
      · simpa using hiff.2 hp
    · have hj : j = v.val := by
        have := hiff.2 (by simp [hy]); omega
      subst hj
      have hl := relVs_length _ _ (hv y hy)
      have : (vs[v.val]?.getD []).length = vals.length := by
        rw [hl]; simp
      rw [this, denotes_sels M d v.val s vals e]
      exact hv y hy

theorem denote_andT_false (a b : Term) (ha : a.denote M = .bool false) : (andT a b).denote M = .bool false := by
  unfold andT
  split
  · simp [Term.denote] at ha
  · exact ha
  · simp [Term.denote, ha, Val.toBool]


mutual
/-- A pattern's condition denotes whether it matches, and its bindings' codes the values it binds. -/
theorem encodePat_agrees {t : Ty} {Δ : List Ty} : (p : Pat t Δ) → (x : t.den) → (s : Code t) → Rel M L t x s →
    (m : Term) → (δs : Codes Δ) → encodePat L p s = .ok (m, δs) →
    m.denote M = .bool (p.match x).isSome ∧ ∀ δ, p.match x = some δ → Rels M L Δ δ δs
  | .wild, _, _, _, m, δs, h => by
    cases h; exact ⟨rfl, fun _ _ => trivial⟩
  | .bind, x, s, hx, m, δs, h => by
    cases h; exact ⟨rfl, fun δ hδ => by cases hδ; exact ⟨hx, trivial⟩⟩
  | .int n, x, s, hx, m, δs, h => by
    cases h
    simp only [Rel, RelV] at hx
    refine ⟨?_, fun _ _ => trivial⟩
    simp only [Term.denote, hx, Pat.match]
    show Val.bool (Val.beq (.int x) (.int n)) = _
    cases hb : (@BEq.beq Int _ x n)
    · simp [Val.beq, hb]
    · simp [Val.beq, hb]; rfl
  | .str lit, x, s, hx, m, δs, h => by
    simp only [encodePat] at h
    split at h
    · cases h
      simp only [Rel, RelV] at hx
      refine ⟨?_, fun _ _ => trivial⟩
      simp only [Term.denote, hx, Pat.match]
      show Val.bool (Val.beq (.str x) (.str lit)) = _
      cases hb : (@BEq.beq String _ x lit)
      · simp [Val.beq, hb]
      · simp [Val.beq, hb]; rfl
    · cases h
  | @Pat.tuple ts _ ps, x, s, hx, m, δs, h => by
    obtain ⟨d, n, vals, hf, e, hv⟩ := hx
    simp only [encodePat, tupleD, hf, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i fs hfs
      simp only [need] at hfs
      split at hfs
      · rename_i fs' hof
        cases hfs
        have hl := relVs_length _ _ hv
        rw [← hl] at hof
        refine encodePats_agrees ps x fs (rels_ofTerms hof x ?_) m δs h
        rw [denotes_sels M d 0 s vals e]; exact hv
      · cases hfs
  | @Pat.ctor i args vs _ v ps, x, s, hx, m, δs, h => by
    simp only [encodePat, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i mv hmv
      obtain ⟨m0, fts⟩ := mv
      obtain ⟨hm0, hfields⟩ := adtView_rel v s x hx m0 fts hmv
      split at h
      · cases h
      · rename_i fs hfs
        simp only [need] at hfs
        split at hfs
        · rename_i fs' hof
          cases hfs
          split at h
          · cases h
          · rename_i r hr
            obtain ⟨m', δ'⟩ := r
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Pat.match]
            cases hp : Alts.proj x v with
            | none =>
              rw [hp] at hm0
              exact ⟨denote_andT_false _ _ hm0, fun _ hδ => by simp at hδ⟩
            | some y =>
              rw [hp] at hm0
              have hy := rels_ofTerms hof y (hfields y hp)
              obtain ⟨h1, h2⟩ := encodePats_agrees ps y _ hy m' δ' hr
              refine ⟨?_, fun δ hδ => h2 δ (by simpa using hδ)⟩
              rw [denote_andT _ _ _ _ hm0 h1]
              simp
        · cases hfs
  | .as p, x, s, hx, m, δs, h => by
    simp only [encodePat, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      obtain ⟨m', δ'⟩ := r
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := encodePat_agrees p x s hx _ δ' hr
      refine ⟨by simpa [Pat.match] using h1, fun δ hδ => ?_⟩
      simp only [Pat.match, Option.map_eq_some_iff] at hδ
      obtain ⟨a, ha, rfl⟩ := hδ
      exact rels_append _ _ _ _ (h2 a ha) ⟨hx, trivial⟩
theorem encodePats_agrees {ts : List Ty} {Δ : List Ty} : (ps : Pats ts Δ) → (xs : Ty.dens ts) → (ss : Codes ts) →
    Rels M L ts xs ss → (m : Term) → (δs : Codes Δ) → encodePats L ps ss = .ok (m, δs) →
    m.denote M = .bool (ps.match xs).isSome ∧ ∀ δ, ps.match xs = some δ → Rels M L Δ δ δs
  | .nil, (), (), _, m, δs, h => by
    cases h; exact ⟨rfl, fun _ _ => trivial⟩
  | .cons p ps, (x, xs), (s, ss), ⟨hx, hxs⟩, m, δs, h => by
    simp only [encodePats, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r1 hr1
      obtain ⟨m1, δ1⟩ := r1
      split at h
      · cases h
      · rename_i r2 hr2
        obtain ⟨m2, δ2⟩ := r2
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨a1, b1⟩ := encodePat_agrees p x s hx m1 δ1 hr1
        obtain ⟨a2, b2⟩ := encodePats_agrees ps xs ss hxs m2 δ2 hr2
        refine ⟨?_, fun δ hδ => ?_⟩
        · rw [denote_andT _ _ _ _ a1 a2]
          simp only [Pats.match]
          cases p.match x <;> cases ps.match xs <;> rfl
        · simp only [Pats.match, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hδ
          obtain ⟨a, ha, b, hb, rfl⟩ := hδ
          exact rels_append _ _ _ _ (b1 a ha) (b2 b hb)
end

theorem find_det {t : Ty} {d n d' n' : Nat} (h : L.find? t = some (d, n)) (h' : L.find? t = some (d', n')) :
    d = d' := by rw [h] at h'; cases h'; rfl

theorem relAlts_index (d : Nat) (k : Nat) (vs : List (List Ty)) (x : Ty.alts vs) (w : Val)
    (h : RelAlts L d k vs x w) : ∃ j vals, w = .ctor d j vals ∧ k ≤ j := by
  obtain ⟨vals, e, _⟩ := relAlts_view d k vs x w h
  exact ⟨_, vals, e, by omega⟩

mutual
/-- SMT-LIB's `=` on the codes of values of an `eqable` type is Gleam's `==`. -/
theorem relV_beq : (t : Ty) → t.eqable = true → (x y : t.den) → (vx vy : Val) → RelV L t x vx → RelV L t y vy →
    Val.beq vx vy = t.deq x y
  | .int, _, x, y, _, _, hx, hy => by
    simp only [RelV] at hx hy; subst hx hy; rfl
  | .str, _, x, y, _, _, hx, hy => by
    simp only [RelV] at hx hy; subst hx hy; rfl
  | .date, _, x, y, _, _, hx, hy => by
    simp only [RelV] at hx hy; subst hx hy; rfl
  | .id, _, x, y, _, _, ⟨d, n, hf, ex⟩, ⟨d', n', hf', ey⟩ => by
    obtain rfl := find_det hf hf'
    subst ex ey
    cases x <;> cases y <;> simp [idVal, Val.beq, Val.beqs, Ty.deq, Ty.sem, Ty.semWith] <;>
      (rename_i a b; by_cases hab : a = b <;> simp [hab] <;> omega)
  | .adt 0 _ vs, _, x, y, _, _, ⟨h, ex⟩, ⟨_, ey⟩ => by
    subst h ex ey
    rcases x with _ | _ | e <;> rcases y with _ | _ | e' <;> first | rfl | exact nomatch e | exact nomatch e'
  | .adt (i + 1) _ vs, he, x, y, _, _, ⟨d, n, hf, hx⟩, ⟨d', n', hf', hy⟩ => by
    obtain rfl := find_det hf hf'
    exact relAlts_beq d 0 vs (by simpa [Ty.eqable] using he) x y _ _ hx hy
  | .tuple ts, he, x, y, _, _, ⟨d, n, vals, hf, ex, hx⟩, ⟨d', n', vals', hf', ey, hy⟩ => by
    obtain rfl := find_det hf hf'
    subst ex ey
    simp only [Val.beq, BEq.rfl, Bool.true_and]
    exact relVs_beq ts (by simpa [Ty.eqable] using he) x y _ _ hx hy
theorem relVs_beq : (ts : List Ty) → Ty.eqables ts = true → (x y : Ty.dens ts) → (vx vy : List Val) →
    RelVs L ts x vx → RelVs L ts y vy → Val.beqs vx vy = (Ty.semsWith Dsl.val ts).2 x y
  | [], _, _, _, _, _, hx, hy => by
    simp only [RelVs] at hx hy; subst hx hy; rfl
  | t :: ts, he, (x, xs), (y, ys), _, _, ⟨v, vs, ex, hx, hxs⟩, ⟨w, ws, ey, hy, hys⟩ => by
    subst ex ey
    simp only [Ty.eqables, Bool.and_eq_true] at he
    simp only [Val.beqs, Ty.semsWith, Sem.pair]
    rw [relV_beq t he.1 x y v w hx hy, relVs_beq ts he.2 xs ys vs ws hxs hys]
theorem relAlts_beq (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.eqabless vs = true → (x y : Ty.alts vs) →
    (vx vy : Val) → RelAlts L d k vs x vx → RelAlts L d k vs y vy → Val.beq vx vy = (Ty.semAltsWith Dsl.val vs).2 x y
  | k, fs :: _, he, .inl x, .inl y, _, _, ⟨a, ex, hx⟩, ⟨b, ey, hy⟩ => by
    subst ex ey
    simp only [Ty.eqabless, Bool.and_eq_true] at he
    simp only [Val.beq, BEq.rfl, Bool.true_and, Ty.semAltsWith, Sem.sum]
    exact relVs_beq fs he.1 x y a b hx hy
  | k, _ :: vs, he, .inr x, .inr y, vx, vy, hx, hy => by
    simp only [Ty.eqabless, Bool.and_eq_true] at he
    simp only [Ty.semAltsWith, Sem.sum]
    exact relAlts_beq d (k + 1) vs he.2 x y vx vy hx hy
  | k, _ :: vs, _, .inl _, .inr y, _, vy, ⟨a, ex, _⟩, hy => by
    obtain ⟨j, b, ey, hj⟩ := relAlts_index d (k + 1) vs y vy hy
    subst ex ey
    have : (k == j) = false := by simp; omega
    simp [Val.beq, this, Ty.semAltsWith, Sem.sum]
  | k, _ :: vs, _, .inr x, .inl _, vx, _, hx, ⟨b, ey, _⟩ => by
    obtain ⟨j, a, ex, hj⟩ := relAlts_index d (k + 1) vs x vx hx
    subst ex ey
    have : (j == k) = false := by simp; omega
    simp [Val.beq, this, Ty.semAltsWith, Sem.sum]
end

theorem rel_bool (x : Ty.bool.den) (s : Code Ty.bool) : Rel M L Ty.bool x s ↔ Term.denote M s = .bool (Ty.toBool x) := by
  constructor
  · intro ⟨_, h⟩; rw [h]; rcases x with _ | _ | e <;> rfl
  · intro h; refine ⟨rfl, ?_⟩; rw [h]; rcases x with _ | _ | e <;> rfl

theorem toBool_ofBool (b : Bool) : Ty.toBool (Ty.ofBool b) = b := by cases b <;> rfl

theorem absT_denote (t : Term) (n : Nat) (h : t.denote M = .int n ∨ t.denote M = .int (-(n : Int))) :
    (absT t).denote M = .int n := by
  rcases h with h | h <;> simp only [absT, Term.denote, h, Val.toInt, Val.toBool] <;> split <;> simp_all; omega

theorem tdivT_agrees (tx ty : Term) (x y : Int) (hx : tx.denote M = .int x)
    (hy : ty.denote M = .int y) : (tdivT tx ty).denote M = .int (Gleam.div x y) := by
  obtain ⟨m, hm⟩ := Int.eq_nat_or_neg x
  obtain ⟨n, hn⟩ := Int.eq_nat_or_neg y
  have ax := absT_denote (M := M) tx m (by rcases hm with rfl | rfl <;> simp [hx])
  have ay := absT_denote (M := M) ty n (by rcases hn with rfl | rfl <;> simp [hy])
  simp only [tdivT, Term.denote, hx, hy, ax, ay, Val.toInt, Val.toBool, Gleam.div]
  by_cases hy0 : y = 0
  · subst hy0; simp [BEq.beq, Val.beq]
  · have hn0 : (n : Int) ≠ 0 := by rcases hn with rfl | rfl <;> omega
    simp only [BEq.beq, Val.beq, hy0, decide_false, Bool.false_eq_true, ite_false, hn0]
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
      simp [Int.neg_tdiv, Int.tdiv_neg] <;>
      rcases Nat.eq_zero_or_pos m with rfl | hm <;> simp_all <;> omega

theorem tmodT_agrees (tx ty : Term) (x y : Int) (hx : tx.denote M = .int x)
    (hy : ty.denote M = .int y) : (tmodT tx ty).denote M = .int (Gleam.mod x y) := by
  obtain ⟨m, hm⟩ := Int.eq_nat_or_neg x
  obtain ⟨n, hn⟩ := Int.eq_nat_or_neg y
  have ax := absT_denote (M := M) tx m (by rcases hm with rfl | rfl <;> simp [hx])
  have ay := absT_denote (M := M) ty n (by rcases hn with rfl | rfl <;> simp [hy])
  simp only [tmodT, Term.denote, hx, hy, ax, ay, Val.toInt, Val.toBool, Gleam.mod]
  by_cases hy0 : y = 0
  · subst hy0; simp [BEq.beq, Val.beq]
  · have hn0 : (n : Int) ≠ 0 := by rcases hn with rfl | rfl <;> omega
    simp only [BEq.beq, Val.beq, hy0, decide_false, Bool.false_eq_true, ite_false, hn0]
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
      simp [Int.neg_tmod, Int.tmod_neg, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)] <;>
      rcases Nat.eq_zero_or_pos m with rfl | hm <;> simp_all <;> omega

theorem encodeBin_agrees {a b c : Ty} (op : BinOp a b c) (sx : Code a) (sy : Code b) (x : a.den) (y : b.den)
    (hx : Rel M L a x sx) (hy : Rel M L b y sy) (r : Code c) (h : encodeBin op sx sy = .ok r) :
    Rel M L c (op.eval x y) r := by
  cases op with
  | add => cases h; simp only [Rel, RelV] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toInt, BinOp.eval]
  | sub => cases h; simp only [Rel, RelV] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toInt, BinOp.eval]
  | mul => cases h; simp only [Rel, RelV] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toInt, BinOp.eval]
  | div => cases h; simp only [Rel, RelV] at hx hy ⊢; exact tdivT_agrees sx sy x y hx hy
  | mod => cases h; simp only [Rel, RelV] at hx hy ⊢; exact tmodT_agrees sx sy x y hx hy
  | lt =>
    cases h; simp only [Rel, RelV] at hx hy; refine (rel_bool _ _).2 ?_
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLt, toBool_ofBool]; congr 2
  | le =>
    cases h; simp only [Rel, RelV] at hx hy; refine (rel_bool _ _).2 ?_
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLe, toBool_ofBool]; congr 2
  | gt =>
    cases h; simp only [Rel, RelV] at hx hy; refine (rel_bool _ _).2 ?_
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLt, toBool_ofBool]; congr 2
  | ge =>
    cases h; simp only [Rel, RelV] at hx hy; refine (rel_bool _ _).2 ?_
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLe, toBool_ofBool]; congr 2
  | and =>
    cases h; replace hx := (rel_bool _ _).1 hx; replace hy := (rel_bool _ _).1 hy; refine (rel_bool _ _).2 ?_
    simp only [Term.denote, hx, hy, Val.toBool, BinOp.eval, toBool_ofBool]
  | or =>
    cases h; replace hx := (rel_bool _ _).1 hx; replace hy := (rel_bool _ _).1 hy; refine (rel_bool _ _).2 ?_
    simp only [Term.denote, hx, hy, Val.toBool, BinOp.eval, toBool_ofBool]
  | concat => cases h; simp only [Rel, RelV] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toStr, BinOp.eval]
  | eq hc =>
    simp only [encodeBin] at h
    split at h
    · rename_i he
      cases h1 : Code.term? _ sx with
      | none => simp [h1, need, bind, Except.bind] at h
      | some tx =>
        cases h2 : Code.term? _ sy with
        | none => simp [h1, h2, need, bind, Except.bind] at h
        | some ty =>
          simp only [h1, h2, need, bind, Except.bind] at h
          cases h
          refine (rel_bool _ _).2 ?_
          simp only [Term.denote, BinOp.eval, toBool_ofBool]
          exact congrArg Val.bool (relV_beq _ he x y _ _ ((rel_term h1 x).1 hx) ((rel_term h2 y).1 hy))
    · cases h
  | ne hc =>
    simp only [encodeBin] at h
    split at h
    · rename_i he
      cases h1 : Code.term? _ sx with
      | none => simp [h1, need, bind, Except.bind] at h
      | some tx =>
        cases h2 : Code.term? _ sy with
        | none => simp [h1, h2, need, bind, Except.bind] at h
        | some ty =>
          simp only [h1, h2, need, bind, Except.bind] at h
          cases h
          refine (rel_bool _ _).2 ?_
          simp only [Term.denote, BinOp.eval, toBool_ofBool, Val.toBool]
          exact congrArg (fun b => Val.bool !b)
            (relV_beq _ he x y _ _ ((rel_term h1 x).1 hx) ((rel_term h2 y).1 hy))
    · cases h

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem pure_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem need_ok {α : Type} {w : String} {o : Option α} {a : α} : need w o = .ok a ↔ o = some a := by
  cases o <;> simp [need]

theorem tupleD_ok {ts : List Ty} {d : Nat} (h : tupleD L ts = .ok d) : ∃ n, L.find? (.tuple ts) = some (d, n) := by
  unfold tupleD at h
  split at h
  · cases h; exact ⟨_, by assumption⟩
  · cases h

theorem denotes_map (ts : List Term) : Term.denotes M ts = ts.map (Term.denote M) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Term.denotes, ih]

end

section
variable {M : Model} {L : Layout}

/-- A bag's item and its slot's item values. -/
def EBag (L : Layout) (t : Ty) : t.den → List Val → Prop := fun y vs => ∃ z, vs = [z] ∧ RelV L t y z
/-- A table's entry and its slot's key and value. -/
def ETab (L : Layout) (k w : Ty) : k.den × w.den → List Val → Prop :=
  fun e vs => ∃ zk zv, vs = [zk, zv] ∧ RelV L k e.1 zk ∧ RelV L w e.2 zv

theorem collD_ok {c : Ty} {item : List Ty} {d n dt : Nat} (h : collD L c item = .ok (d, n, dt)) :
    L.find? c = some (d, n) ∧ ∃ m, L.find? (.tuple (Ty.bool :: item)) = some (dt, m) := by
  unfold collD at h
  split at h
  · cases h; exact ⟨by assumption, _, by assumption⟩
  · cases h

theorem bag_view {t : Ty} {xs : (Ty.bag t).den} {b : Term} (hb : Rel M L (.bag t) xs b) {d n dt : Nat}
    (hc : collD L (.bag t) [t] = .ok (d, n, dt)) :
    ∃ sv ys, SlotsDen M (slotsOf d dt n 1 b) sv ∧ sv.length = n ∧ (∀ p ∈ sv, p.2.length = 1) ∧ ys.Perm xs ∧
      Holds2 (EBag L t) ys sv := by
  obtain ⟨hf, m, hft⟩ := collD_ok hc
  obtain ⟨d', n', dt', m', sv, hf', hft', hl, hv, hw, ys, hp, hh⟩ := hb
  rw [hf] at hf'; cases hf'
  rw [hft] at hft'; cases hft'
  refine ⟨sv, ys, ?_, hl, hw, hp, hh⟩
  rw [← hl]; exact slotsOf_den d dt 1 b sv hv hw

theorem bag_mk {t : Ty} {xs : (Ty.bag t).den} {d n dt : Nat} (hc : collD L (.bag t) [t] = .ok (d, n, dt))
    {S : List Slot} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hl : sv.length = n)
    (hw : ∀ p ∈ sv, p.2.length = 1) {ys : List t.den} (hp : ys.Perm xs) (hh : Holds2 (EBag L t) ys sv) :
    Rel M L (.bag t) xs (slotsTerm d dt S) := by
  obtain ⟨hf, m, hft⟩ := collD_ok hc
  exact ⟨d, n, dt, m, sv, hf, hft, hl, slotsTerm_den d dt hS, hw, ys, hp, hh⟩

theorem table_view {k w : Ty} {x : (Ty.table k w).den} {b : Term} (hb : Rel M L (.table k w) x b) {d n dt : Nat}
    (hc : collD L (.table k w) [k, w] = .ok (d, n, dt)) :
    ∃ sv ys, SlotsDen M (slotsOf d dt n 2 b) sv ∧ sv.length = n ∧ (∀ p ∈ sv, p.2.length = 2) ∧ ys.Perm x.1 ∧
      Holds2 (ETab L k w) ys sv := by
  obtain ⟨hf, m, hft⟩ := collD_ok hc
  obtain ⟨d', n', dt', m', sv, hf', hft', hl, hv, hw, ys, hp, hh⟩ := hb
  rw [hf] at hf'; cases hf'
  rw [hft] at hft'; cases hft'
  refine ⟨sv, ys, ?_, hl, hw, hp, hh⟩
  rw [← hl]; exact slotsOf_den d dt 2 b sv hv hw

theorem table_mk {k w : Ty} {x : (Ty.table k w).den} {d n dt : Nat} (hc : collD L (.table k w) [k, w] = .ok (d, n, dt))
    {S : List Slot} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hl : sv.length = n)
    (hw : ∀ p ∈ sv, p.2.length = 2) {ys : List (k.den × w.den)} (hp : ys.Perm x.1) (hh : Holds2 (ETab L k w) ys sv) :
    Rel M L (.table k w) x (slotsTerm d dt S) := by
  obtain ⟨hf, m, hft⟩ := collD_ok hc
  exact ⟨d, n, dt, m, sv, hf, hft, hl, slotsTerm_den d dt hS, hw, ys, hp, hh⟩

/-- A predicate's code applied slot by slot denotes the predicate on each occupied slot's item. -/
theorem slotPreds_aligned {ps : List Ty} {f : (Ty.fn ps Ty.bool).den} {sf : Code (.fn ps Ty.bool)}
    (hf : Rel M L (.fn ps Ty.bool) f sf) {α : Type} {E : α → List Val → Prop} (toD : α → Ty.dens ps)
    (hE : ∀ y vs, E y vs → RelVs L ps (toD y) vs) {S : List Slot} {sv : List (Bool × List Val)} {ys : List α}
    {R : List (Term × Term)} (hS : SlotsDen M S sv) (hy : Holds2 E ys sv) (hR : slotPreds sf S = .ok R)
    (hg : Holds M (guardsT S (R.map (·.2)))) :
    Aligned M E (fun y => Ty.toBool (f (toD y))) S (R.map (·.1)) sv ys := by
  refine aligned_of (fun sl r => slotApply sf sl.2 = .ok r) ?_ hS hy (mapM_ok _ S R hR) hg
  intro sl r y hr he hc
  simp only [slotApply] at hr
  obtain ⟨cs, h1, hr⟩ := bind_ok.1 hr
  have hcs := rels_ofTerms (need_ok.1 h1) (toD y) (hE y _ he)
  exact (rel_bool _ _).1 (hf (toD y) cs hcs r.1 r.2 hr hc)

/-- Inserting an item related by `E` into the first free slot, when one was free. -/
theorem insert_rel {α : Type} {E : α → List Val → Prop} {S : List Slot} {sv : List (Bool × List Val)} {ys : List α}
    {w : Nat} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = w) (hy : Holds2 E ys sv) (x : List Term)
    (hx : x.length = w) (y : α) (hey : E y (Term.denotes M x)) (hc : Holds M (.not (insertSlots x tt S).2)) :
    ∃ sv' ys', SlotsDen M (insertSlots x tt S).1 sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = w) ∧
      ys'.Perm (y :: ys) ∧ Holds2 E ys' sv' := by
  have hxl : (Term.denotes M x).length = w := by rw [denotes_eq_map]; simpa using hx
  obtain ⟨h1, h2⟩ := insertSlots_den x (Term.denotes M x) rfl tt true rfl hS (fun q hq => by rw [hw q hq, hx])
  obtain ⟨hocc, -⟩ := insertVals_occupied (Term.denotes M x) true sv
  obtain ⟨hl, hw'⟩ := insertVals_length (Term.denotes M x) w hxl true sv hw
  have hp : (insertVals (Term.denotes M x) true sv).2 = false := by
    simp only [Holds, Term.denote, h2, Val.toBool] at hc; simpa using hc
  rw [hp] at hocc
  simp only [and_self, ite_true, List.singleton_append] at hocc
  obtain ⟨ys', hperm, hh⟩ := forall2_perm hocc.symm (as := y :: ys) ⟨hey, hy⟩
  exact ⟨_, ys', h1, hl, hw', hperm, hh⟩

theorem need'_ok {α : Type} {w : String} {b : Bool} {a a' : α} (h : need' w b a = .ok a') : b = true ∧ a' = a := by
  unfold need' at h; split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

/-- The keys that `table_remove` keeps: the slot terms denote `!sameKey`. -/
theorem keep_aligned {k w : Ty} (hk : k.eqable = true) (key : k.den) (kt : Term) (hkt : RelV L k key (kt.denote M))
    {S : List Slot} {sv : List (Bool × List Val)} {ys : List (k.den × w.den)} (hS : SlotsDen M S sv)
    (hy : Holds2 (ETab L k w) ys sv) :
    Aligned M (ETab L k w) (fun e => !(k.deq key e.1 || k.deq e.1 key)) S (keepQs kt S) sv ys := by
  refine aligned_map (fun xs => .not (.or (.eq kt (xs.headD kt)) (.eq (xs.headD kt) kt))) ?_ hS hy
  intro e xs he
  obtain ⟨zk, zv, hxs, hzk, _⟩ := he
  cases xs with
  | nil => simp [Term.denotes] at hxs
  | cons tk rest =>
    simp only [Term.denotes, List.cons.injEq] at hxs
    simp only [List.headD_cons, Term.denote, hxs.1, Val.toBool]
    show Val.bool (!(Val.beq (kt.denote M) zk || Val.beq zk (kt.denote M))) = _
    rw [relV_beq k hk key e.1 _ _ hkt hzk, relV_beq k hk e.1 key _ _ hzk hkt]

/-- `table_insert` on slots: the key's slot freed, then the entry in the first free slot. -/
theorem put_den {k w : Ty} (hk : k.eqable = true) {t0 : (Ty.table k w).den} {S : List Slot}
    {sv : List (Bool × List Val)} {ys : List (k.den × w.den)} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = 2)
    (hperm : ys.Perm t0.1) (hh : Holds2 (ETab L k w) ys sv) (key : k.den) (val : w.den) (kt vt : Term)
    (hkt : RelV L k key (kt.denote M)) (hvt : RelV L w val (vt.denote M)) (hc : Holds M (putSlots S kt vt).2) :
    ∃ sv' ys', SlotsDen M (putSlots S kt vt).1 sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 2) ∧
      ys'.Perm (Builtin.tableInsert key val t0).1 ∧ Holds2 (ETab L k w) ys' sv' := by
  have ha := keep_aligned hk key kt hkt hS hh
  obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
  have hl' : sv'.length = sv.length := by simpa using congrArg List.length hsnd
  have hw' : ∀ p ∈ sv', p.2.length = 2 := fun p hp' => by
    have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
    obtain ⟨q, hq, e⟩ := List.mem_map.1 this
    rw [← e]; exact hw q hq
  obtain ⟨sv'', ys'', hS'', hl'', hw'', hperm'', hh''⟩ :=
    insert_rel hS' hw' hh' [kt, vt] rfl (key, val) ⟨_, _, by simp [Term.denotes], hkt, hvt⟩ hc
  refine ⟨sv'', ys'', hS'', hl''.trans hl', hw'', hperm''.trans ?_, hh''⟩
  exact ((hperm.filter _).cons _).trans (List.perm_append_singleton _ _).symm

theorem insertAll_rel {α : Type} {E : α → List Val → Prop} : {zs : List α} → {ts : List Term} →
    Forall2 (fun y t => E y [Term.denote M t]) zs ts → {S : List Slot} → {sv : List (Bool × List Val)} →
    SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 1) → {ys : List α} → Holds2 E ys sv → Holds M (insertAll S ts).2 →
    ∃ sv' ys', SlotsDen M (insertAll S ts).1 sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 1) ∧
      ys'.Perm (zs ++ ys) ∧ Holds2 E ys' sv'
  | [], [], _, S, sv, hS, hw, ys, hy, _ => ⟨sv, ys, hS, rfl, hw, List.Perm.refl _, hy⟩
  | z :: zs, t :: ts, ⟨hz, hzs⟩, S, sv, hS, hw, ys, hy, hc => by
    simp only [insertAll] at hc ⊢
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨sv1, ys1, hS1, hl1, hw1, hp1, hh1⟩ :=
      insert_rel hS hw hy [t] rfl z (by simpa [Term.denotes] using hz) hc1
    obtain ⟨sv2, ys2, hS2, hl2, hw2, hp2, hh2⟩ := insertAll_rel hzs hS1 hw1 hh1 hc2
    refine ⟨sv2, ys2, hS2, hl2.trans hl1, hw2, hp2.trans ?_, hh2⟩
    exact (List.Perm.append_left zs hp1).trans List.perm_middle
  | [], _ :: _, h, _, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _, _ => nomatch h

theorem items_ebag {t : Ty} {w : String} : {xs : List t.den} → {items : List (Code t)} → {ts : List Term} →
    Forall2 (Rel M L t) xs items → Forall2 (fun x y => need w (Code.term? t x) = .ok y) items ts →
    Forall2 (fun y tm => EBag L t y [Term.denote M tm]) xs ts
  | [], [], [], _, _ => trivial
  | y :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ =>
    ⟨⟨_, rfl, (rel_term (need_ok.1 h3) y).1 h1⟩, items_ebag h2 h4⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _, [], _ :: _, _, h | _, _ :: _, [], _, h => nomatch h

theorem putAll_rel {k w : Ty} (hk : k.eqable = true) (dp : Nat) (hdp : ∃ m, L.find? (.tuple [k, w]) = some (dp, m)) :
    {pairs : List (Ty.tuple [k, w]).den} → {ps : List Term} →
    Forall2 (fun e p => RelV L (.tuple [k, w]) e (Term.denote M p)) pairs ps →
    {t0 : (Ty.table k w).den} → {S : List Slot} → {sv : List (Bool × List Val)} → {ys : List (k.den × w.den)} →
    SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 2) → ys.Perm t0.1 → Holds2 (ETab L k w) ys sv →
    Holds M (putAll S (ps.map fun p => (.sel dp 0 0 p, .sel dp 0 1 p))).2 →
    ∃ sv' ys', SlotsDen M (putAll S (ps.map fun p => (.sel dp 0 0 p, .sel dp 0 1 p))).1 sv' ∧
      sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 2) ∧
      ys'.Perm (pairs.foldl (fun t (k, v, ()) => Builtin.tableInsert k v t) t0).1 ∧ Holds2 (ETab L k w) ys' sv'
  | [], [], _, t0, S, sv, ys, hS, hw, hp, hh, _ => ⟨sv, ys, hS, rfl, hw, hp, hh⟩
  | (key, val, ()) :: pairs, p :: ps, ⟨he, hrest⟩, t0, S, sv, ys, hS, hw, hp, hh, hc => by
    simp only [List.map_cons, putAll] at hc ⊢
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨m, hf⟩ := hdp
    obtain ⟨d', n', vals, hf', ev, zk, rest, e1, hzk, zv, rest', e2, hzv, e3⟩ := he
    obtain rfl := find_det hf hf'
    subst e1 e2
    simp only [RelVs] at e3; subst e3
    have hk' : RelV L k key (Term.denote M (.sel dp 0 0 p)) := by rw [sel_ctor 0 ev]; exact hzk
    have hv' : RelV L w val (Term.denote M (.sel dp 0 1 p)) := by rw [sel_ctor 1 ev]; exact hzv
    obtain ⟨sv1, ys1, hS1, hl1, hw1, hp1, hh1⟩ := put_den hk hS hw hp hh key val _ _ hk' hv' hc1
    obtain ⟨sv2, ys2, hS2, hl2, hw2, hp2, hh2⟩ := putAll_rel hk dp ⟨m, hf⟩ hrest hS1 hw1 hp1 hh1 hc2
    exact ⟨sv2, ys2, hS2, hl2.trans hl1, hw2, hp2, hh2⟩
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _, _, _, _ => nomatch h

theorem eBag_rels {t : Ty} (y : t.den) (vs : List Val) (h : EBag L t y vs) : RelVs L [t] (y, ()) vs := by
  obtain ⟨z, rfl, hz⟩ := h; exact ⟨z, [], rfl, hz, rfl⟩

theorem eTab_rels {k w : Ty} (e : k.den × w.den) (vs : List Val) (h : ETab L k w e vs) :
    RelVs L [k, w] (e.1, e.2, ()) vs := by
  obtain ⟨zk, zv, rfl, hk, hv⟩ := h; exact ⟨zk, [zv], rfl, hk, zv, [], rfl, hv, rfl⟩

end

section
variable {M : Model} {L : Layout}

/-- Each built-in's code relates to its meaning. -/
theorem primCode_agrees (p : Prim) (args : List Ty) (hp : p.ok args = true) (s : Code (p.ty.inst args))
    (h : primCode L p args hp = .ok s) : Rel M L (p.ty.inst args) (p.den args hp) s := by
  cases p
  case length =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨sx, ()⟩ ⟨hx, _⟩ r c hr _
    cases hr
    change Rel M L .str x sx at hx
    show Rel M L .int _ (Term.len sx)
    simp only [Rel, RelV] at hx ⊢
    simp [Term.denote, hx, Val.toStr]; rfl
  case dateAddDays =>
    simp only [primCode] at h; cases h
    intro ⟨x, y, ()⟩ ⟨sx, sy, ()⟩ ⟨hx, hy, _⟩ r c hr _
    cases hr
    change Rel M L .date x sx at hx
    change Rel M L .int y sy at hy
    show Rel M L .date _ (Term.add sx sy)
    simp only [Rel, RelV] at hx hy ⊢
    simp [Term.denote, hx, hy, Val.toInt]; rfl
  case dateDaysBetween =>
    simp only [primCode] at h; cases h
    intro ⟨x, y, ()⟩ ⟨sx, sy, ()⟩ ⟨hx, hy, _⟩ r c hr _
    cases hr
    change Rel M L .date x sx at hx
    change Rel M L .date y sy at hy
    show Rel M L .int _ (Term.sub sy sx)
    simp only [Rel, RelV] at hx hy ⊢
    simp [Term.denote, hx, hy, Val.toInt]; rfl
  case require =>
    simp only [primCode] at h; cases h
    intro ⟨b, rej, next, ()⟩ ⟨sb, srej, snext, ()⟩ ⟨hb, hrej, hnext, _⟩ r c hr hc
    obtain ⟨⟨v, c1⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨t, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨err, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    have hb' := (rel_bool _ _).1 hb
    have hv := hnext () () trivial v c1 h1
    have he := adtCtor_rel (M := M) (vs := [[_], [_]]) ⟨1, by simp⟩ [t] err h3 (rej, ())
      ⟨_, _, rfl, (rel_term (need_ok.1 h2) _).1 hrej, rfl⟩
    show RelV L (.adt 2 [_, _] [[_], [_]]) (if Ty.toBool b then next () else Ty.error rej)
      (Term.denote M (Term.ite sb v err))
    simp only [Holds, Term.denote, hb', Val.toBool] at hc ⊢
    by_cases hbt : Ty.toBool b = true
    · simp only [hbt, ite_true] at hc ⊢
      exact hv hc
    · simp only [hbt, Bool.false_eq_true, ite_false] at hc ⊢
      exact he
  case bagSize =>
    simp only [primCode] at h; cases h
    intro ⟨xs, ()⟩ ⟨b, ()⟩ ⟨hb, _⟩ r c hr _
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    show Rel M L .int (xs.length : Int) (sizeT (slotsOf d dt n 1 b))
    simp only [Rel, RelV, sizeT_den hS, ← holds2_length hh, hperm.length_eq]
  case bagFilter =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := bag_view hb h1
    have ha := slotPreds_aligned hf (fun y => (y, ())) eBag_rels hS hh h2 hc
    obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
    have hl' : sv'.length = n := by rw [← hl]; simpa using congrArg List.length hsnd
    have hw' : ∀ p ∈ sv', p.2.length = 1 := fun p hp' => by
      have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
      obtain ⟨q, hq, e⟩ := List.mem_map.1 this
      rw [← e]; exact hw q hq
    exact bag_mk h1 hS' hl' hw' (hperm.filter _) hh'
  case bagCount =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have ha := slotPreds_aligned hf (fun y => (y, ())) eBag_rels hS hh h2 hc
    show RelV L .int _ _
    simp only [RelV, countT_den ha, (hperm.filter _).length_eq]
    rfl
  case bagAny =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have ha := slotPreds_aligned hf (fun y => (y, ())) eBag_rels hS hh h2 hc
    refine (rel_bool _ _).2 ?_
    rw [anySlotT_den ha, hperm.any_eq]
    simp only [Prim.den, toBool_ofBool]
  case bagAll =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have ha := slotPreds_aligned hf (fun y => (y, ())) eBag_rels hS hh h2 hc
    refine (rel_bool _ _).2 ?_
    rw [allSlotT_den ha, hperm.all_eq]
    simp only [Prim.den, toBool_ofBool]
  case tableSize =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨b, ()⟩ ⟨hb, _⟩ r c hr _
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    show Rel M L .int (x.1.length : Int) (sizeT (slotsOf d dt n 2 b))
    simp only [Rel, RelV, sizeT_den hS, ← holds2_length hh, hperm.length_eq]
  case tableFilter =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view hb h1
    have ha := slotPreds_aligned hf (fun e => (e.1, e.2, ())) eTab_rels hS hh h2 hc
    obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
    have hl' : sv'.length = n := by rw [← hl]; simpa using congrArg List.length hsnd
    have hw' : ∀ p ∈ sv', p.2.length = 2 := fun p hp' => by
      have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
      obtain ⟨q, hq, e⟩ := List.mem_map.1 this
      rw [← e]; exact hw q hq
    exact table_mk h1 hS' hl' hw' (hperm.filter _) hh'
  case tableCount =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha := slotPreds_aligned hf (fun e => (e.1, e.2, ())) eTab_rels hS hh h2 hc
    show RelV L .int _ _
    simp only [RelV, countT_den ha, (hperm.filter _).length_eq]
    rfl
  case tableAny =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha := slotPreds_aligned hf (fun e => (e.1, e.2, ())) eTab_rels hS hh h2 hc
    refine (rel_bool _ _).2 ?_
    rw [anySlotT_den ha, hperm.any_eq]
    simp only [Prim.den, toBool_ofBool]
  case tableAll =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha := slotPreds_aligned hf (fun e => (e.1, e.2, ())) eTab_rels hS hh h2 hc
    refine (rel_bool _ _).2 ?_
    rw [allSlotT_den ha, hperm.all_eq]
    simp only [Prim.den, toBool_ofBool]
  case bagInsert =>
    simp only [primCode] at h; cases h
    intro ⟨xs, x, ()⟩ ⟨b, sx, ()⟩ ⟨hb, hx, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨xt, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := bag_view hb h1
    have hxt := (rel_term (need_ok.1 h2) x).1 hx
    obtain ⟨sv', ys', hS', hl', hw', hperm', hh'⟩ :=
      insert_rel hS hw hh [xt] rfl x ⟨_, by simp [Term.denotes], hxt⟩ hc
    exact bag_mk h1 hS' (hl'.trans hl) hw' (hperm'.trans (hperm.cons x)) hh'
  case tableNew =>
    simp only [primCode] at h; cases h
    intro ⟨⟩ ⟨⟩ _ r c hr _
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨S, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    simp only [emptySlots] at h2
    obtain ⟨xs, h3, h2⟩ := bind_ok.1 h2
    cases pure_ok.1 h2
    have hxl : xs.length = 2 := by
      have := need_ok.1 h3
      simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind, pure] at this
      split at this <;> try cases this
      split at this <;> try cases this
      all_goals rfl
    refine table_mk h1 (empty_den xs n) (by simp) (fun p hp => ?_) (ys := []) (List.Perm.refl _)
      (by simp [Holds2, occupied_empty, Forall2])
    simp only [List.mem_replicate] at hp
    rw [hp.2, denotes_eq_map]; simpa using hxl
  case tableRemove =>
    simp only [primCode] at h; cases h
    intro ⟨x, key, ()⟩ ⟨b, sk, ()⟩ ⟨hb, hk, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨kt0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨kt, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view hb h1
    have ha := keep_aligned heq key kt ((rel_term (need_ok.1 h2) key).1 hk) hS hh
    obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
    have hl' : sv'.length = n := by rw [← hl]; simpa using congrArg List.length hsnd
    have hw' : ∀ p ∈ sv', p.2.length = 2 := fun p hp' => by
      have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
      obtain ⟨q, hq, e⟩ := List.mem_map.1 this
      rw [← e]; exact hw q hq
    exact table_mk h1 hS' hl' hw' (hperm.filter _) hh'
  case tableInsert =>
    simp only [primCode] at h; cases h
    intro ⟨x, key, val, ()⟩ ⟨b, sk, sv0, ()⟩ ⟨hb, hk, hv, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨kt0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨kt, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨vt, h4, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view hb h1
    obtain ⟨sv', ys', hS', hl', hw', hperm', hh'⟩ := put_den heq hS hw hperm hh key val kt vt
      ((rel_term (need_ok.1 h2) key).1 hk) ((rel_term (need_ok.1 h4) val).1 hv) hc
    exact table_mk h1 hS' (hl'.trans hl) hw' hperm' hh'
  case bagFromList =>
    simp only [primCode] at h; cases h
    intro ⟨xs, ()⟩ ⟨items, ()⟩ ⟨hxs, _⟩ r c hr hc
    change Forall2 (Rel M L ((Ty.param 0).inst args)) xs items at hxs
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨ts, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨S0, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    simp only [emptySlots] at h3
    obtain ⟨dx, h4, h3⟩ := bind_ok.1 h3
    cases pure_ok.1 h3
    have hdl : dx.length = 1 := by
      have := need_ok.1 h4
      simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind, pure] at this
      split at this <;> try cases this
      all_goals rfl
    have hts := mapM_ok _ items ts h2
    have hz := items_ebag (M := M) hxs hts
    obtain ⟨sv', ys', hS', hl', hw', hperm', hh'⟩ := insertAll_rel hz (empty_den dx n)
      (fun p hp => by simp only [List.mem_replicate] at hp; rw [hp.2, denotes_eq_map]; simpa using hdl)
      (ys := []) (by simp [Holds2, occupied_empty, Forall2]) hc
    exact bag_mk h1 hS' (by simpa using hl') hw' (hperm'.trans (List.Perm.of_eq (List.append_nil xs))) hh'
  case tableFromList =>
    simp only [primCode] at h; cases h
    intro ⟨pairs, ()⟩ ⟨ps, ()⟩ ⟨hps, _⟩ r c hr hc
    change Forall2 (Rel M L (.tuple [(Ty.param 0).inst args, (Ty.param 1).inst args])) pairs ps at hps
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨dp0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨dp, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨S0, h4, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    obtain ⟨m, hdp⟩ := tupleD_ok h2
    simp only [emptySlots] at h4
    obtain ⟨dx, h5, h4⟩ := bind_ok.1 h4
    cases pure_ok.1 h4
    have hdl : dx.length = 2 := by
      have := need_ok.1 h5
      simp only [List.mapM_cons, List.mapM_nil, bind, Option.bind, pure] at this
      split at this <;> try cases this
      split at this <;> try cases this
      all_goals rfl
    obtain ⟨sv', ys', hS', hl', hw', hperm', hh'⟩ := putAll_rel heq dp ⟨m, hdp⟩ (t0 := Builtin.tableEmpty) hps
      (empty_den dx n) (fun p hp => by simp only [List.mem_replicate] at hp; rw [hp.2, denotes_eq_map]; simpa using hdl)
      (ys := []) (List.Perm.refl _) (by simp [Holds2, occupied_empty, Forall2]) hc
    exact table_mk h1 hS' (by simpa using hl') hw' hperm' hh'
  case bagContains =>
    simp only [primCode] at h; cases h
    intro ⟨xs, x, ()⟩ ⟨b, sx, ()⟩ ⟨hb, hx, _⟩ r c hr _
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨xt0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨xt, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    have hxt := (rel_term (need_ok.1 h2) x).1 hx
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have ha := aligned_map (P := fun y => Ty.deq _ x y) (fun xs => .eq xt (xs.headD xt)) (fun y xs he => by
      obtain ⟨z, hz, hyz⟩ := he
      cases xs with
      | nil => simp [Term.denotes] at hz
      | cons t rest =>
        simp only [Term.denotes, List.cons.injEq] at hz
        simp only [List.headD_cons, Term.denote, hz.1]
        exact congrArg Val.bool (relV_beq _ heq x y _ _ hxt hyz)) hS hh
    refine (rel_bool _ _).2 ?_
    rw [anySlotT_den ha, hperm.any_eq]
    simp only [Prim.den, toBool_ofBool]
    rfl
  all_goals simp [primCode] at h

end

theorem encodeClauses_none {L : Layout} {G : List Ty} {gs : Encs G} {Γ : List Ty} {t r : Ty} {sh : List Shape} :
    (cs : Clauses G Γ t r sh) → (σ : Codes Γ) → (s : Code t) → encodeClauses L gs cs σ s = .ok none → sh = []
  | .nil, _, _, _ => rfl
  | .cons p body rest, σ, s, h => by
    unfold encodeClauses at h
    obtain ⟨_, _, h⟩ := bind_ok.1 h
    obtain ⟨_, _, h⟩ := bind_ok.1 h
    obtain ⟨o, _, h⟩ := bind_ok.1 h
    cases o with
    | none => cases h
    | some vc => obtain ⟨_, _, h⟩ := bind_ok.1 h; cases h
  | .guarded p g body rest, σ, s, h => by
    unfold encodeClauses at h
    obtain ⟨_, _, h⟩ := bind_ok.1 h
    obtain ⟨_, _, h⟩ := bind_ok.1 h
    obtain ⟨_, _, h⟩ := bind_ok.1 h
    obtain ⟨o, _, h⟩ := bind_ok.1 h
    cases o with
    | none => cases h
    | some vc => obtain ⟨_, _, h⟩ := bind_ok.1 h; cases h

/-- The globals' codes relate to their values. -/
def GRel (M : Model) (L : Layout) {G : List Ty} (g : Ty.dens G) (gs : Encs G) : Prop :=
  ∀ (t : Ty) (v : Var G t) s c, v.enc gs = .ok (s, c) → Holds M c → Rel M L t (v.get g) s

section
variable {M : Model} {L : Layout} {G : List Ty} (g : Ty.dens G) (gs : Encs G) (hg : GRel M L g gs)
include hg

set_option linter.unusedSectionVars false

mutual
/-- T1: wherever its condition holds, an expression's code denotes the value `eval` computes, in every model whose
variables denote the values of the expression's variables. -/
theorem encode_agrees {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    Rels M L Γ ρ σ → (s : Code t) → (c : Term) → encode L gs e σ = .ok (s, c) → Holds M c →
    Rel M L t (e.eval g ρ) s
  | .int n, _, _, _, s, c, h, _ => by cases h; simp [Rel, RelV, Expr.eval, Term.denote]
  | .str lit, _, _, _, s, c, h, _ => by
    simp only [encode] at h; split at h
    · cases h; simp [Rel, RelV, Expr.eval, Term.denote]
    · cases h
  | .var v, σ, ρ, hσ, s, c, h, _ => by cases h; exact var_rel v ρ σ hσ
  | .global v, _, _, _, s, c, h, hc => hg _ v s c h hc
  | @Expr.ctor _ _ i args vs v es, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨fs, h2, h⟩ := bind_ok.1 h
    obtain ⟨t', h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have hr := encodes_agrees es σ ρ hσ ss _ h1 hc
    exact adtCtor_rel v fs _ h3 _ (rels_terms (need_ok.1 h2) _ hr)
  | @Expr.field _ _ i args vs ft _ k hk e, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    have hx := encode_agrees e σ ρ hσ x c1 h1
    cases i with
    | zero => cases h
    | succ i =>
      simp only at h
      split at h
      · rename_i d n hf
        obtain ⟨r, h2, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        obtain ⟨d', n', hf', hr⟩ := hx hc
        obtain rfl := find_det hf hf'
        refine (rel_ofTerm (need_ok.1 h2) _).2 ?_
        obtain ⟨vals, ev, hv⟩ := relAlts_view d 0 vs _ _ hr
        have hlt := (Alts.view (e.eval g ρ)).1.isLt
        rw [fieldT_denote d k x _ vals (by simpa using ev) 0 (vs.length - 1) (by omega) (by omega)]
        exact relVs_field _ _ hv k _
      · cases h
  | @Expr.index _ _ ts e k, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨d, h2, h⟩ := bind_ok.1 h
    obtain ⟨r, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨n, hf⟩ := tupleD_ok h2
    obtain ⟨d', n', vals, hf', ev, hv⟩ := encode_agrees e σ ρ hσ x c1 h1 hc
    obtain rfl := find_det hf hf'
    refine (rel_ofTerm (need_ok.1 h3) _).2 ?_
    simp only [Term.denote, ev, and_self, ite_true]
    exact relVs_get _ _ hv k
  | @Expr.update _ _ i args fs e p, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    have hx := encode_agrees e σ ρ hσ x c1 h1
    have hpa := encodePatch_agrees p σ ρ hσ
    cases i with
    | zero => cases h
    | succ i =>
      simp only at h
      split at h
      · rename_i d n hf
        obtain ⟨⟨ys, c2⟩, h2, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
        obtain ⟨d', n', hf', hr⟩ := hx hc1
        obtain rfl := find_det hf hf'
        refine ⟨d, n, hf, ?_⟩
        simp only [Expr.eval]
        generalize e.eval g ρ = y at hr
        rcases y with y | e'
        · obtain ⟨vals, ev, hv⟩ := hr
          have hl := relVs_length _ _ hv
          have hp := hpa (fun j => .sel d 0 j x) 0 ys c2 h2 hc2 y (by
            have := denotes_sels M d 0 x vals ev
            rw [hl] at this; simpa using this ▸ hv)
          simp only [Term.denote]
          exact relAlts_inj d 0 (vs := [fs]) ⟨0, by simp⟩ _ _ hp
        · exact nomatch e'
      · cases h
  | .call f args, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨sf, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨ss, c2⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨r, c3⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc'⟩ := (holds_andT _ _).1 hc
    obtain ⟨hc2, hc3⟩ := (holds_andT _ _).1 hc'
    exact encode_agrees f σ ρ hσ sf c1 h1 hc1 _ ss (encodes_agrees args σ ρ hσ ss c2 h2 hc2) _ c3 h3 hc3
  | .lam body, σ, ρ, hσ, s, c, h, _ => by
    cases h
    intro xs ss hxs r c' hr hc'
    exact encode_agrees body (Codes.append ss σ) (Dens.append xs ρ) (rels_append _ _ _ _ hxs hσ) r c' hr hc'
  | .let_ e body, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨r, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    exact encode_agrees body (x, σ) (e.eval g ρ, ρ) ⟨encode_agrees e σ ρ hσ x c1 h1 hc1, hσ⟩ _ c2 h2 hc2
  | .case e cs hx, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨o, h2, h⟩ := bind_ok.1 h
    cases o with
    | none => cases h
    | some rc =>
      obtain ⟨r, c2⟩ := rc
      cases pure_ok.1 h
      obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
      exact encodeClauses_agrees cs σ ρ hσ x _ (encode_agrees e σ ρ hσ x c1 h1 hc1) _ _ c2 h2 hc2
  | .list items, σ, ρ, hσ, s, c, h, hc => encodeItems_agrees items σ ρ hσ s c h hc
  | @Expr.tuple _ _ ts es, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨fs, h2, h⟩ := bind_ok.1 h
    obtain ⟨d, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨n, hf⟩ := tupleD_ok h3
    exact ⟨d, n, _, hf, rfl, rels_terms (need_ok.1 h2) _ (encodes_agrees es σ ρ hσ ss _ h1 hc)⟩
  | .bin op l r, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨y, c2⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨z, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    exact encodeBin_agrees op x y _ _ (encode_agrees l σ ρ hσ x c1 h1 hc1) (encode_agrees r σ ρ hσ y c2 h2 hc2) _ h3
  | .not e, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have := (rel_bool _ _).1 (encode_agrees e σ ρ hσ x _ h1 hc)
    refine (rel_bool _ _).2 ?_
    simp only [Expr.eval, Term.denote, this, Val.toBool, toBool_ofBool]
  | .neg e, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have := encode_agrees e σ ρ hσ x _ h1 hc
    simp only [Rel, RelV] at this ⊢
    simp [Expr.eval, Term.denote, this, Val.toInt]; omega
  | .prim p args hp, _, _, _, s, c, h, _ => by
    simp only [encode] at h
    obtain ⟨r, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact primCode_agrees p args hp _ h1
theorem encodes_agrees {Γ : List Ty} {ts : List Ty} : (es : Exprs G Γ ts) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    Rels M L Γ ρ σ → (ss : Codes ts) → (c : Term) → encodes L gs es σ = .ok (ss, c) → Holds M c →
    Rels M L ts (Exprs.eval g es ρ) ss
  | .nil, _, _, _, _, _, _, _ => trivial
  | .cons e es, σ, ρ, hσ, ss, c, h, hc => by
    simp only [encodes] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨xs, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    exact ⟨encode_agrees e σ ρ hσ x c1 h1 hc1, encodes_agrees es σ ρ hσ xs c2 h2 hc2⟩
theorem encodeItems_agrees {Γ : List Ty} {t : Ty} : (items : Items G Γ t) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    Rels M L Γ ρ σ → (ss : List (Code t)) → (c : Term) → encodeItems L gs items σ = .ok (ss, c) → Holds M c →
    Forall2 (Rel M L t) (Items.eval g items ρ) ss
  | .nil, _, _, _, ss, c, h, _ => by cases h; trivial
  | .cons e es, σ, ρ, hσ, ss, c, h, hc => by
    simp only [encodeItems] at h
    obtain ⟨⟨x, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨xs, c2⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    exact ⟨encode_agrees e σ ρ hσ x c1 h1 hc1, encodeItems_agrees es σ ρ hσ xs c2 h2 hc2⟩
theorem encodePatch_agrees {Γ : List Ty} {ts : List Ty} : (p : Patch G Γ ts) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    Rels M L Γ ρ σ → (keep : Nat → Term) → (j : Nat) → (ys : List Term) → (c : Term) →
    encodePatch L gs p σ keep j = .ok (ys, c) → Holds M c → (xs : Ty.dens ts) →
    RelVs L ts xs (Term.denotes M ((List.range ts.length).map fun i => keep (j + i))) →
    RelVs L ts (Patch.eval g p ρ xs) (Term.denotes M ys)
  | .nil, _, _, _, _, _, ys, c, h, _, (), _ => by cases h; rfl
  | .keep rest, σ, ρ, hσ, keep, j, ys, c, h, hc, (x, xs), hk => by
    simp only [encodePatch] at h
    obtain ⟨⟨zs, c1⟩, h1, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨v, vs, e, hv, hvs⟩ := hk
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, Term.denotes,
      List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨_, _, rfl, by simpa using hv, encodePatch_agrees rest σ ρ hσ keep (j + 1) zs _ h1 hc xs ?_⟩
    have : (fun i => keep (j + 1 + i)) = ((fun i => keep (j + i)) ∘ Nat.succ) := by
      funext i; simp only [Function.comp]; congr 1; omega
    rw [this]; exact hvs
  | .set e rest, σ, ρ, hσ, keep, j, ys, c, h, hc, (x, xs), hk => by
    simp only [encodePatch] at h
    obtain ⟨⟨s, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨y, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨zs, c2⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    obtain ⟨v, vs, e', hv, hvs⟩ := hk
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, Term.denotes,
      List.cons.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    refine ⟨_, _, rfl, (rel_term (need_ok.1 h2) _).1 (encode_agrees e σ ρ hσ s c1 h1 hc1),
      encodePatch_agrees rest σ ρ hσ keep (j + 1) zs c2 h3 hc2 xs ?_⟩
    have : (fun i => keep (j + 1 + i)) = ((fun i => keep (j + i)) ∘ Nat.succ) := by
      funext i; simp only [Function.comp]; congr 1; omega
    rw [this]; exact hvs
theorem encodeClauses_agrees {Γ : List Ty} {t r : Ty} {sh : List Shape} : (cs : Clauses G Γ t r sh) →
    (σ : Codes Γ) → (ρ : Ty.dens Γ) → Rels M L Γ ρ σ → (s : Code t) → (x : t.den) → Rel M L t x s →
    (hx : ∃ s ∈ sh, Shape.Matches t s x) → (v : Code r) → (c : Term) →
    encodeClauses L gs cs σ s = .ok (some (v, c)) → Holds M c → Rel M L r (Clauses.eval g cs ρ x hx) v
  | .nil, _, _, _, _, _, _, _, _, _, h, _ => by cases h
  | .cons p body rest, σ, ρ, hσ, s, x, hs, hx, v, c, h, hc => by
    simp only [encodeClauses] at h
    obtain ⟨⟨m, δs⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨vb, cb⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨o, h3, h⟩ := bind_ok.1 h
    obtain ⟨hm, hδ⟩ := encodePat_agrees p x s hs m δs h1
    simp only [Clauses.eval]
    split
    · rename_i δ hpm
      have hb := encode_agrees body (Codes.append δs σ) (Dens.append δ ρ) (rels_append _ _ _ _ (hδ δ hpm) hσ) vb cb h2
      rw [hpm] at hm
      cases o with
      | none => cases pure_ok.1 h; exact hb hc
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h4, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        have hcb : Holds M cb := by simpa [holds_ite, hm, Val.toBool] using hc
        refine rel_ite? (need_ok.1 h4) _ ?_
        simp only [hm, Val.toBool, Option.isSome_some, ite_true]
        exact hb hcb
    · rename_i hpm
      rw [hpm] at hm
      cases o with
      | none => exact absurd (Clauses.skip hpm hx) (by rw [encodeClauses_none rest σ s h3]; simp)
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h4, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        refine rel_ite? (need_ok.1 h4) _ ?_
        have hcr : Holds M cr := by simpa [holds_ite, hm, Val.toBool] using hc
        simpa [hm, Val.toBool] using encodeClauses_agrees rest σ ρ hσ s x hs _ vr cr h3 hcr
  | .guarded p guard body rest, σ, ρ, hσ, s, x, hs, hx, v, c, h, hc => by
    simp only [encodeClauses] at h
    obtain ⟨⟨m, δs⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨vg, cg⟩, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨vb, cb⟩, h3, h⟩ := bind_ok.1 h
    obtain ⟨o, h4, h⟩ := bind_ok.1 h
    obtain ⟨hm, hδ⟩ := encodePat_agrees p x s hs m δs h1
    simp only [Clauses.eval]
    split
    · rename_i δ hpm
      have hr := rels_append _ _ _ _ (hδ δ hpm) hσ
      have hgd := encode_agrees guard (Codes.append δs σ) (Dens.append δ ρ) hr vg cg h2
      have hb := encode_agrees body (Codes.append δs σ) (Dens.append δ ρ) hr vb cb h3
      rw [hpm] at hm
      cases o with
      | none =>
        cases pure_ok.1 h
        obtain ⟨hcg, hcb⟩ := (holds_andT _ _).1 hc
        split
        · exact hb hcb
        · exact absurd hx (by rw [encodeClauses_none rest σ s h4]; simp)
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h5, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        have hc' : Holds M (andT cg (.ite vg cb cr)) := by simpa [holds_ite, hm, Val.toBool] using hc
        obtain ⟨hcg, hci⟩ := (holds_andT _ _).1 hc'
        have hvg := (rel_bool _ _).1 (hgd hcg)
        refine rel_ite? (need_ok.1 h5) _ ?_
        simp only [Term.denote, hm, hvg, Val.toBool, Option.isSome_some, Bool.true_and]
        split
        · rename_i hgt
          have := (holds_ite _ _ _).1 hci
          rw [hvg] at this
          exact hb (by simpa [Val.toBool, hgt] using this)
        · rename_i hgt
          have := (holds_ite _ _ _).1 hci
          rw [hvg] at this
          exact encodeClauses_agrees rest σ ρ hσ s x hs hx vr cr h4 (by simpa [Val.toBool, hgt] using this)
    · rename_i hpm
      rw [hpm] at hm
      cases o with
      | none => exact absurd hx (by rw [encodeClauses_none rest σ s h4]; simp)
      | some vc =>
        obtain ⟨vr, cr⟩ := vc
        obtain ⟨w, h5, h⟩ := bind_ok.1 h
        cases pure_ok.1 h
        refine rel_ite? (need_ok.1 h5) _ ?_
        have hcr : Holds M cr := by simpa [holds_ite, hm, Val.toBool] using hc
        simpa [Term.denote, hm, Val.toBool] using encodeClauses_agrees rest σ ρ hσ s x hs hx vr cr h4 hcr
end

end

/-- Every global's code relates to its value, so `encode_agrees` holds for every program's expressions. -/
theorem Defs.encode_agrees (M : Model) (L : Layout) : {G : List Ty} → (defs : Defs G) →
    GRel M L defs.eval (defs.encode L)
  | [], .nil => fun _ v => nomatch v
  | _ :: _, .snoc defs _ body => by
    intro t v s c h hc
    cases v with
    | here => exact Smt.encode_agrees _ _ (Defs.encode_agrees M L defs) body () () trivial s c h hc
    | there v => exact Defs.encode_agrees M L defs t v s c h hc

end Tazuna.Smt
