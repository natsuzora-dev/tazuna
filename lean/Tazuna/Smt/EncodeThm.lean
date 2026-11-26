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

def altsBool0 : (Ty.semAltsWith Dsl.base [[], []]).1 → Bool
  | .inl _ => true
  | .inr _ => false

/-- An id as a value of its datatype `d`: a fresh one by its step's counter and index, an outside one by its name. -/
def idVal (d : Nat) : IdV → Val
  | .fresh s i => .ctor d 0 [.int s, .int i]
  | .named s => .ctor d 1 [.str s.1]

mutual
/-- A data value as the step holds it (`Ty.den0`) and the SMT value that codes it: `RelV` for the data a structure
value holds, such as an effect's input and the values its kept functions captured. -/
def RelD : (t : Ty) → t.den0 → Val → Prop
  | .int, x, v => v = .int x
  | .str, x, v => v = .str (x : Str).1
  | .date, x, v => v = .int x
  | .id, x, v => ∃ d n, L.find? .id = some (d, n) ∧ v = idVal d x
  | .adt 0 _ vs, x, v => ∃ h : vs = [[], []], v = .bool (altsBool0 (h ▸ x))
  | .adt (i + 1) a vs, x, v => ∃ d n, L.find? (.adt (i + 1) a vs) = some (d, n) ∧ RelDAlts d 0 vs x v
  | .tuple ts, x, v => ∃ d n vals, L.find? (.tuple ts) = some (d, n) ∧ v = .ctor d 0 vals ∧ RelDs ts x vals
  /- The slots hold the bag's items in some order. -/
  | .bag t, xs, v => ∃ d n dt m sv, L.find? (.bag t) = some (d, n) ∧ L.find? (.tuple [Ty.bool, t]) = some (dt, m) ∧
      sv.length = n ∧ v = slotsVal d dt sv ∧ (∀ p ∈ sv, p.2.length = 1) ∧
      ∃ ys : List t.den0, ys.Perm xs ∧ Holds2 (fun y vs => ∃ z, vs = [z] ∧ RelD t y z) ys sv
  | .table k w, x, v => ∃ d n dt m sv, L.find? (.table k w) = some (d, n) ∧
      L.find? (.tuple [Ty.bool, k, w]) = some (dt, m) ∧ sv.length = n ∧ v = slotsVal d dt sv ∧
      (∀ p ∈ sv, p.2.length = 2) ∧ ∃ ys : List (k.den0 × w.den0), ys.Perm x.1 ∧
        Holds2 (fun e vs => ∃ zk zv, vs = [zk, zv] ∧ RelD k e.1 zk ∧ RelD w e.2 zv) ys sv
  /- The occupied slots hold the list's items in order. -/
  | .list t, xs, v => ∃ d n dt m sv, L.find? (.list t) = some (d, n) ∧ L.find? (.tuple [Ty.bool, t]) = some (dt, m) ∧
      sv.length = n ∧ v = slotsVal d dt sv ∧ (∀ p ∈ sv, p.2.length = 1) ∧
      Holds2 (fun y vs => ∃ z, vs = [z] ∧ RelD t y z) xs sv
  /- A fresh-id source is the step's counter. -/
  | .dsl .fresh _, x, v => v = .int (Int.ofNat x)
  | .fn .., _, _ | .param _, _, _ | .dsl .., _, _ => False
def RelDs : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Val → Prop
  | [], _, vals => vals = []
  | t :: ts, (x, xs), vals => ∃ v vs, vals = v :: vs ∧ RelD t x v ∧ RelDs ts xs vs
/-- The value is constructor `k + j` of datatype `d` when it is the `j`-th variant of `vs`. -/
def RelDAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Val → Prop
  | k, fs :: _, .inl x, v => ∃ vals, v = .ctor d k vals ∧ RelDs fs x vals
  | k, _ :: vs, .inr y, v => RelDAlts d (k + 1) vs y v
end

/-- The captured values of a kept function: a tuple of their codes. -/
def CapRel {t : Ty} (f : Fun t) (v : Val) : Prop :=
  ∃ d n vals, L.find? (.tuple f.Γ) = some (d, n) ∧ v = .ctor d 0 vals ∧ RelDs L f.Γ f.env vals

/-- An effect of the kind `key` and its variant's fields: the same request, with its input and each kept function's
captured values coded by the fields, and its kept functions written at the kind's sites. -/
def EffectKey.Holds {e : Ty} (key : EffectKey) : EffectV e → List Val → Prop
  | .request r, vals => r.name = key.name ∧ r.input = key.input ∧ r.output = key.output ∧
      r.rejection = key.rejection ∧ r.onAnswer.site = key.answer.site ∧ r.onAnswer.Γ = key.answer.Γ ∧
      ∃ vi ve va, vals = [vi, ve, va] ∧ RelD L r.input r.value vi ∧ CapRel L r.onAnswer va ∧
      match r.ensures, key.ensures with
      | none, none => ∃ d n, L.find? (.tuple []) = some (d, n) ∧ ve = .ctor d 0 []
      | some f, some sk => f.site = sk.site ∧ f.Γ = sk.Γ ∧ CapRel L f ve
      | _, _ => False
  | _, _ => False

/-- An effect of the own kind `key` and its variant's fields: the same command or query, with its caller, its input
and its `on_answer`'s captured values coded by the fields, and its `on_answer` written at the kind's site. -/
def OwnKey.Holds {e : Ty} : OwnKey → EffectV e → List Val → Prop
  | .command _ name c i j a, .command name' c' i' j' caller value onAnswer, vals =>
      name' = name ∧ c' = c ∧ i' = i ∧ j' = j ∧ onAnswer.site = a.site ∧ onAnswer.Γ = a.Γ ∧
      ∃ vc vi va, vals = [vc, vi, va] ∧ RelD L c' caller vc ∧ RelD L i' value vi ∧ CapRel L onAnswer va
  | .query _ name c i o a, .query name' c' i' o' caller value onAnswer, vals =>
      name' = name ∧ c' = c ∧ i' = i ∧ o' = o ∧ onAnswer.site = a.site ∧ onAnswer.Γ = a.Γ ∧
      ∃ vc vi va, vals = [vc, vi, va] ∧ RelD L c' caller vc ∧ RelD L i' value vi ∧ CapRel L onAnswer va
  | _, _, _ => False

/-- An effect and the SMT value that codes it: the variant of its kind in the effect datatype of its event type,
request kinds first, then own kinds. -/
def EffRel {e : Ty} (eff : EffectV e) (v : Val) : Prop :=
  ∃ d n, L.find? (.dsl .effect [e]) = some (d, n) ∧
    ((∃ k key vals, (L.effectsOf e)[k]? = some key ∧ v = .ctor d k vals ∧ key.Holds L eff vals) ∨
      ∃ k key vals, (L.ownsOf e)[k]? = some key ∧ v = .ctor d ((L.effectsOf e).length + k) vals ∧
        key.Holds L eff vals)

mutual
/-- A value of a first-order type and the SMT value that codes it. -/
def RelV : (t : Ty) → t.den → Val → Prop
  | .int, x, v => v = .int x
  | .str, x, v => v = .str (x : Str).1
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
  /- The occupied slots hold the list's items in order. -/
  | .list t, xs, v => ∃ d n dt m sv, L.find? (.list t) = some (d, n) ∧ L.find? (.tuple [Ty.bool, t]) = some (dt, m) ∧
      sv.length = n ∧ v = slotsVal d dt sv ∧ (∀ p ∈ sv, p.2.length = 1) ∧
      Holds2 (fun y vs => ∃ z, vs = [z] ∧ RelV t y z) xs sv
  /- A fresh-id source is the step's counter. -/
  | .dsl .fresh _, x, v => v = .int (Int.ofNat x)
  /- An effect is its kind's variant. -/
  | .dsl .effect [_], x, v => EffRel L x v
  | .fn .., _, _ | .param _, _, _ | .dsl .., _, _ => False
def RelVs : (ts : List Ty) → Ty.dens ts → List Val → Prop
  | [], _, vals => vals = []
  | t :: ts, (x, xs), vals => ∃ v vs, vals = v :: vs ∧ RelV t x v ∧ RelVs ts xs vs
/-- The value is constructor `k + j` of datatype `d` when it is the `j`-th variant of `vs`. -/
def RelAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.alts vs → Val → Prop
  | k, fs :: _, .inl x, v => ∃ vals, v = .ctor d k vals ∧ RelVs fs x vals
  | k, _ :: vs, .inr y, v => RelAlts d (k + 1) vs y v
end

/-- A kept function and its closure code: written at the code's site, with the captured values the code's terms
denote. -/
def ClosureRel {t : Ty} (f : Fun t) (c : ClosureCode) : Prop :=
  f.site = c.key.site ∧ f.Γ = c.key.Γ ∧ RelDs L f.Γ f.env (Term.denotes M c.env)

/-- A structure value and its code: a kept function by its closure code, a handle by its name (and a query's
`ensures`), anything else by the term that denotes it. -/
def DslRel : (k : Dsl) → (a : List Ty) → (Ty.dsl k a).den → DslCode k a → Prop
  | .closure, [_], f, c => ClosureRel M L f c
  | .externalCommand, [_, _, _], n, c => n = c
  | .externalQuery, [_, _], (n, f), (c, cc) => n = c ∧ ClosureRel M L f cc
  | .command, [_, _, _, _, _], x, c => x.1.name = c
  | .query, [_, _, _, _], x, c => x.1.name = c
  | .spec, a, x, s => RelV L (.dsl .spec a) x (Term.denote M s)
  | .service, a, x, s => RelV L (.dsl .service a) x (Term.denote M s)
  | .machine, a, x, s => RelV L (.dsl .machine a) x (Term.denote M s)
  | .reaction, a, x, s => RelV L (.dsl .reaction a) x (Term.denote M s)
  | .external, a, x, s => RelV L (.dsl .external a) x (Term.denote M s)
  | .source, a, x, s => RelV L (.dsl .source a) x (Term.denote M s)
  | .declared, a, x, s => RelV L (.dsl .declared a) x (Term.denote M s)
  | .effect, a, x, s => RelV L (.dsl .effect a) x (Term.denote M s)
  | .subscription, a, x, s => RelV L (.dsl .subscription a) x (Term.denote M s)
  | .bounds, a, x, s => RelV L (.dsl .bounds a) x (Term.denote M s)
  | .create, a, x, s => RelV L (.dsl .create a) x (Term.denote M s)
  | .response, a, x, s => RelV L (.dsl .response a) x (Term.denote M s)
  | .scenario, a, x, s => RelV L (.dsl .scenario a) x (Term.denote M s)
  | .step, a, x, s => RelV L (.dsl .step a) x (Term.denote M s)
  | .sender, a, x, s => RelV L (.dsl .sender a) x (Term.denote M s)
  | .fresh, a, x, s => RelV L (.dsl .fresh a) x (Term.denote M s)
  | .effectClosure, a, x, s => RelV L (.dsl .effectClosure a) x (Term.denote M s)
  | _, _, _, _ => False

mutual
/-- A value and its code: a term denoting the value, or a function that maps related arguments to a related result
wherever its condition holds. -/
def Rel : (t : Ty) → t.den → Code t → Prop
  | .fn ps r, f, sf => ∀ xs ss, Rels ps xs ss → ∀ s c, sf ss = .ok (s, c) → Holds M c → Rel r (f xs) s
  | .list t, x, s => RelV L (.list t) x (Term.denote M s)
  | .int, x, s => RelV L .int x (Term.denote M s)
  | .str, x, s => RelV L .str x (Term.denote M s)
  | .tuple ts, x, s => RelV L (.tuple ts) x (Term.denote M s)
  | .adt i a vs, x, s => RelV L (.adt i a vs) x (Term.denote M s)
  | .param k, x, s => RelV L (.param k) x (Term.denote M s)
  | .bag t, x, s => RelV L (.bag t) x (Term.denote M s)
  | .table k v, x, s => RelV L (.table k v) x (Term.denote M s)
  | .date, x, s => RelV L .date x (Term.denote M s)
  | .id, x, s => RelV L .id x (Term.denote M s)
  | .dsl k a, x, s => DslRel M L k a x s
def Rels : (ts : List Ty) → Ty.dens ts → Codes ts → Prop
  | [], _, _ => True
  | t :: ts, (x, xs), (s, ss) => Rel t x s ∧ Rels ts xs ss
end

end

section
variable {M : Model} {L : Layout}

theorem map_down_up (t : Ty) (ht : t.isData = true) (xs : List t.den0) :
    (xs.map (Ty.up t ht)).map (Ty.down t ht) = xs := by
  simp [List.map_map, Function.comp_def, Ty.down_up]

mutual
/-- On data, `RelV` at a value read at the structure level is `RelD` at the value. -/
theorem relV_up : (t : Ty) → (h : t.isData = true) → (y : t.den0) → (v : Val) → RelV L t (Ty.up t h y) v →
    RelD L t y v
  | .int, _, _, _, hv | .str, _, _, _, hv | .date, _, _, _, hv | .id, _, _, _, hv | .dsl .fresh _, _, _, _, hv => hv
  | .adt 0 a vs, h, y, v, hv => by
    obtain ⟨e, hv⟩ := hv
    subst e
    refine ⟨rfl, ?_⟩
    rw [hv]
    rcases y with u | u | u
    · erw [Ty.up_inl 0 a [] [[]] h rfl u]; rfl
    · erw [Ty.up_inr 0 a [] [[]] h rfl (.inl u), Ty.up_inl 0 a [] [] rfl rfl u]; rfl
    · exact u.elim
  | .adt (i + 1) a vs, h, y, v, ⟨d, n, hf, hr⟩ => ⟨d, n, hf, relAlts_up d (i + 1) a 0 vs h y v hr⟩
  | .tuple ts, h, y, v, ⟨d, n, vals, hf, hv, hr⟩ => ⟨d, n, vals, hf, hv, relVs_up ts h y vals hr⟩
  | .bag t, h, xs, v, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys, hp, hh⟩ => by
    have ht : t.isData = true := by simpa [Ty.isData] using h
    rw [Ty.up_bag t h ht] at hp
    refine ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys.map (Ty.down t ht), ?_, ?_⟩
    · have := hp.map (Ty.down t ht)
      erw [map_down_up t ht] at this
      exact this
    · exact forall2_map _ (fun y vs ⟨z, hz, hyz⟩ => ⟨z, hz, relV_up t ht _ z (by rw [Ty.up_down]; exact hyz)⟩) hh
  | .list t, h, xs, v, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, hh⟩ => by
    have ht : t.isData = true := by simpa [Ty.isData] using h
    rw [Ty.up_list t h ht] at hh
    refine ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ?_⟩
    have := forall2_map (R := fun y vs => ∃ z, vs = [z] ∧ RelV L t y z)
      (R' := fun y vs => ∃ z, vs = [z] ∧ RelD L t y z) (Ty.down t ht)
      (fun y vs ⟨z, hz, hyz⟩ => ⟨z, hz, relV_up t ht _ z (by rw [Ty.up_down]; exact hyz)⟩) hh
    erw [map_down_up t ht] at this
    exact this
  | .table k w, h, x, v, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys, hp, hh⟩ => by
    have h' := h
    simp only [Ty.isData, Bool.and_eq_true] at h'
    have hk : k.isData = true := h'.1
    have hw : w.isData = true := h'.2
    rw [Ty.up_table k w h hk hw] at hp
    let dn : k.den × w.den → k.den0 × w.den0 := fun p => (Ty.down k hk p.1, Ty.down w hw p.2)
    refine ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, ys.map dn, ?_, ?_⟩
    · have := hp.map dn
      rwa [List.map_map, show dn ∘ (fun p : k.den0 × w.den0 => (Ty.up k hk p.1, Ty.up w hw p.2)) = id from
        funext fun p => by simp [dn, Ty.down_up], List.map_id] at this
    · exact forall2_map dn (fun e vs ⟨zk, zv, hz, h1, h2⟩ => ⟨zk, zv, hz,
        relV_up k hk _ zk (by show RelV L k (Ty.up k hk (Ty.down k hk e.1)) zk; rw [Ty.up_down]; exact h1),
        relV_up w hw _ zv (by show RelV L w (Ty.up w hw (Ty.down w hw e.2)) zv; rw [Ty.up_down]; exact h2)⟩) hh
  | .fn .., _, _, _, hv | .param _, _, _, _, hv => hv.elim
  | .dsl .effect _, h, _, _, _ => by simp [Ty.isData] at h
  | .dsl .spec _, _, _, _, hv | .dsl .service _, _, _, _, hv | .dsl .command _, _, _, _, hv
  | .dsl .query _, _, _, _, hv | .dsl .machine _, _, _, _, hv | .dsl .reaction _, _, _, _, hv
  | .dsl .external _, _, _, _, hv | .dsl .externalCommand _, _, _, _, hv | .dsl .externalQuery _, _, _, _, hv
  | .dsl .source _, _, _, _, hv | .dsl .declared _, _, _, _, hv | .dsl .subscription _, _, _, _, hv
  | .dsl .bounds _, _, _, _, hv | .dsl .create _, _, _, _, hv | .dsl .response _, _, _, _, hv
  | .dsl .scenario _, _, _, _, hv | .dsl .step _, _, _, _, hv | .dsl .sender _, _, _, _, hv
  | .dsl .closure _, _, _, _, hv => by simp [RelV] at hv
theorem relVs_up : (ts : List Ty) → (h : (Ty.tuple ts).isData = true) → (y : (Ty.semsWith Dsl.base ts).1) →
    (vals : List Val) → RelVs L ts (Ty.up (.tuple ts) h y) vals → RelDs L ts y vals
  | [], _, _, _, hv => hv
  | t :: ts, h, y, vals, hv => by
    have h' := h
    simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h'
    have ht : t.isData = true := h'.1
    have hts : (Ty.tuple ts).isData = true := by simpa [Ty.isData] using h'.2
    erw [Ty.up_tuple t ts h ht hts] at hv
    obtain ⟨v, vs, e, h1, h2⟩ := hv
    exact ⟨v, vs, e, relV_up t ht y.1 v h1, relVs_up ts hts y.2 vs h2⟩
theorem relAlts_up (d i : Nat) (a : List Ty) : (k : Nat) → (vs : List (List Ty)) → (h : (Ty.adt i a vs).isData = true) →
    (y : (Ty.semAltsWith Dsl.base vs).1) → (v : Val) → RelAlts L d k vs (Ty.up (.adt i a vs) h y) v →
    RelDAlts L d k vs y v
  | _, [], _, y, _, _ => nomatch y
  | k, fs :: vs, h, .inl x, v, hv => by
    have h' := h
    simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at h'
    have hfs : (Ty.tuple fs).isData = true := by simpa [Ty.isData] using h'.1
    erw [Ty.up_inl i a fs vs h hfs x] at hv
    obtain ⟨vals, e, hr⟩ := hv
    exact ⟨vals, e, relVs_up fs hfs x vals hr⟩
  | k, fs :: vs, h, .inr y, v, hv => by
    have h' := h
    simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at h'
    have hvs : (Ty.adt i a vs).isData = true := by simpa [Ty.isData] using h'.2
    erw [Ty.up_inr i a fs vs h hvs y] at hv
    exact relAlts_up d i a (k + 1) vs hvs y v hv
end

theorem rel_term : {t : Ty} → {s : Code t} → {x : Term} → Code.term? t s = some x → (v : t.den) →
    (Rel M L t v s ↔ RelV L t v (x.denote M))
  | .fn .., _, _, h, _ => nomatch h
  | .dsl k _, _, _, h, _ => by
    cases k <;> simp only [Code.term?, DslCode.term?, reduceCtorEq] at h <;> cases h <;> exact Iff.rfl
  | .list _, _, _, h, _ | .int, _, _, h, _ | .str, _, _, h, _ | .tuple _, _, _, h, _ | .adt .., _, _, h, _ | .param _, _, _, h, _
  | .bag _, _, _, h, _ | .table .., _, _, h, _ | .date, _, _, h, _ | .id, _, _, h, _ => by
    cases h; exact Iff.rfl

theorem rel_ofTerm : {t : Ty} → {x : Term} → {s : Code t} → Code.ofTerm? t x = some s → (v : t.den) →
    (Rel M L t v s ↔ RelV L t v (x.denote M))
  | .fn .., _, _, h, _ => nomatch h
  | .dsl k _, _, _, h, _ => by
    cases k <;> simp only [Code.ofTerm?, DslCode.ofTerm?, reduceCtorEq] at h <;> cases h <;>
      exact Iff.rfl
  | .list _, _, _, h, _ | .int, _, _, h, _ | .str, _, _, h, _ | .tuple _, _, _, h, _ | .adt .., _, _, h, _ | .param _, _, _, h, _
  | .bag _, _, _, h, _ | .table .., _, _, h, _ | .date, _, _, h, _ | .id, _, _, h, _ => by
    cases h; exact Iff.rfl

theorem rel_share : {t : Ty} → {v : t.den} → {s : Code t} → Rel M L t v s → Rel M L t v (Code.share t s)
  | .fn .., _, _, h => h
  | .list _, _, s, h | .int, _, s, h | .str, _, s, h | .tuple _, _, s, h | .adt .., _, s, h | .param _, _, s, h | .bag _, _, s, h
  | .table .., _, s, h | .date, _, s, h | .id, _, s, h => by
    simp only [Code.share, Rel] at h ⊢; rw [Term.denote_share M s]; exact h
  | .dsl k _, _, s, h => by
    cases k <;> first
      | exact h
      | (simp only [Code.share, DslCode.share, Rel, DslRel] at h ⊢; rw [Term.denote_share M s]; exact h)

theorem rels_share : {ts : List Ty} → {vs : Ty.dens ts} → {ss : Codes ts} → Rels M L ts vs ss →
    Rels M L ts vs (Codes.share ts ss)
  | [], _, _, _ => trivial
  | _ :: _, _, _, ⟨h, hs⟩ => ⟨rel_share h, rels_share hs⟩

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

-- SMT-LIB leaves a selector on a field its constructor lacks to the model, and the default stands for that value.
set_option linter.tazuna.silentDefault false in
theorem relVs_field : {ts : List Ty} → {t : Ty} → (y : Ty.dens ts) → (vals : List Val) → RelVs L ts y vals →
    (k : Nat) → (h : ts[k]? = some t) → RelV L t (Dens.field y k h) (vals[k]?.getD default)
  | [], _, _, _, _, _, h => nomatch h
  | _ :: _, _, (_, _), _, ⟨v, _, e, h1, _⟩, 0, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h e; exact h1
  | _ :: _, _, (_, _), _, ⟨_, _, e, _, h2⟩, k + 1, h => by
    subst e; exact relVs_field _ _ h2 k (by simpa using h)

-- SMT-LIB leaves a selector on a field its constructor lacks to the model, and the default stands for that value.
set_option linter.tazuna.silentDefault false in
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

-- SMT-LIB leaves a selector on a field its constructor lacks to the model, and the default stands for that value.
set_option linter.tazuna.silentDefault false in
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
    (h : adtView L i args vs v s = .ok (m, fts)) :
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
      have : (vs.get v).length = vals.length := hl.symm
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
    cases h
    obtain ⟨x, hxd⟩ := x
    obtain ⟨lit, hl⟩ := lit
    simp only [Rel, RelV] at hx
    refine ⟨?_, fun _ _ => trivial⟩
    simp only [Term.denote, hx, Pat.match]
    show Val.bool (Val.beq (.str x) (.str lit)) = _
    by_cases hb : x = lit
    · subst hb; simp [Val.beq]; rfl
    · have : (@BEq.beq Str _ ⟨x, hxd⟩ ⟨lit, hl⟩) = false := by simp [hb]
      simp [Val.beq, hb, this]
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

theorem ofNat_beq (x y : Nat) : (Int.ofNat x == Int.ofNat y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨Int.ofNat.inj, congrArg _⟩

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
  | .dsl .fresh a, _, x, y, _, _, hx, hy => by
    change _ = Val.int (Int.ofNat x) at hx
    change _ = Val.int (Int.ofNat y) at hy
    subst hx hy
    change (Int.ofNat x == Int.ofNat y) = (Dsl.base .fresh a).2 x y
    exact ofNat_beq x y
  | .id, _, x, y, _, _, ⟨d, n, hf, ex⟩, ⟨d', n', hf', ey⟩ => by
    obtain rfl := find_det hf hf'
    subst ex ey
    cases x <;> cases y <;> simp [idVal, Val.beq, Val.beqs, Ty.deq, Ty.sem, Ty.semWith]
    · rename_i a i b j
      by_cases hab : a = b <;> by_cases hij : i = j <;> simp [hab, hij, Int.natCast_inj]
    · rename_i a b
      by_cases hab : a = b <;> simp [hab]
      exact fun h => hab (Subtype.ext h)
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

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem map_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β} :
    f <$> x = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Functor.map, Except.map]

theorem pure_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem need_ok {α : Type} {w : Refusal} {o : Option α} {a : α} : need w o = .ok a ↔ o = some a := by
  cases o <;> simp [need]

theorem tupleD_ok {ts : List Ty} {d : Nat} (h : tupleD L ts = .ok d) : ∃ n, L.find? (.tuple ts) = some (d, n) := by
  unfold tupleD at h
  split at h
  · cases h; exact ⟨_, by assumption⟩
  · cases h

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
    {S : List (Slot 1)} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hl : sv.length = n)
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
    {S : List (Slot 2)} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv) (hl : sv.length = n)
    (hw : ∀ p ∈ sv, p.2.length = 2) {ys : List (k.den × w.den)} (hp : ys.Perm x.1) (hh : Holds2 (ETab L k w) ys sv) :
    Rel M L (.table k w) x (slotsTerm d dt S) := by
  obtain ⟨hf, m, hft⟩ := collD_ok hc
  exact ⟨d, n, dt, m, sv, hf, hft, hl, slotsTerm_den d dt hS, hw, ys, hp, hh⟩

theorem foldl_add (acc : Int) (l : List Int) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.sum_cons]; omega

theorem sum_perm {l l' : List Int} (h : l.Perm l') : l.sum = l'.sum := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [ih]
  | swap a b l => simp only [List.sum_cons]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- A function's code applied slot by slot denotes the function at each occupied slot's item. -/
theorem slotTerms_aligned {ps : List Ty} {r : Ty} {f : (Ty.fn ps r).den} {sf : Code (.fn ps r)}
    (hf : Rel M L (.fn ps r) f sf) {α : Type} {E : α → List Val → Prop} (toD : α → Ty.dens ps)
    (hE : ∀ y vs, E y vs → RelVs L ps (toD y) vs) {w : Nat} {S : List (Slot w)} {sv : List (Bool × List Val)} {ys : List α}
    {R : List (Term × Term)} (hS : SlotsDen M S sv) (hy : Holds2 E ys sv) (hR : slotTerms sf S = .ok R)
    (hg : Holds M (guardsT S (R.map (·.2)))) :
    AlignedV M E (fun y v => RelV L r (f (toD y)) v) S (R.map (·.1)) sv ys := by
  refine aligned_of _ ?_ hS hy (mapM_ok _ S R hR) hg
  intro sl r' y hr he hc
  obtain ⟨⟨v, c⟩, h1, hr⟩ := bind_ok.1 hr
  obtain ⟨t, h2, hr⟩ := bind_ok.1 hr
  cases pure_ok.1 hr
  simp only [slotApply] at h1
  obtain ⟨cs, h3, h1⟩ := bind_ok.1 h1
  have hcs := rels_ofTerms (need_ok.1 h3) (toD y) (hE y _ he)
  exact (rel_term (need_ok.1 h2) _).1 (hf (toD y) cs hcs v c h1 hc)

theorem relV_bool (x : Ty.bool.den) (v : Val) : RelV L Ty.bool x v ↔ v = .bool (Ty.toBool x) := by
  constructor
  · intro ⟨_, h⟩; rw [h]; rcases x with _ | _ | e <;> rfl
  · intro h; refine ⟨rfl, ?_⟩; rw [h]; rcases x with _ | _ | e <;> rfl

/-- A predicate's code applied slot by slot denotes the predicate on each occupied slot's item. -/
theorem slotPreds_aligned {ps : List Ty} {f : (Ty.fn ps Ty.bool).den} {sf : Code (.fn ps Ty.bool)}
    (hf : Rel M L (.fn ps Ty.bool) f sf) {α : Type} {E : α → List Val → Prop} (toD : α → Ty.dens ps)
    (hE : ∀ y vs, E y vs → RelVs L ps (toD y) vs) {w : Nat} {S : List (Slot w)} {sv : List (Bool × List Val)} {ys : List α}
    {R : List (Term × Term)} (hS : SlotsDen M S sv) (hy : Holds2 E ys sv) (hR : slotTerms sf S = .ok R)
    (hg : Holds M (guardsT S (R.map (·.2)))) :
    Aligned M E (fun y => Ty.toBool (f (toD y))) S (R.map (·.1)) sv ys :=
  alignedV_mono (fun _ v h => (relV_bool _ v).1 h) (slotTerms_aligned hf toD hE hS hy hR hg)

/-- Inserting an item related by `E` into the first free slot, pending by `p`, which holds, when one was free. -/
theorem insert_rel {α : Type} {E : α → List Val → Prop} {w : Nat} {S : List (Slot w)} {sv : List (Bool × List Val)}
    {ys : List α} (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = w) (hy : Holds2 E ys sv) (x : SlotItems w)
    (y : α) (hey : E y (Term.denotes M x.1)) {p : Term} (hp : p.denote M = .bool true)
    (hc : Holds M (.not (insertSlots x p S).2)) :
    ∃ sv' ys', SlotsDen M (insertSlots x p S).1 sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = w) ∧
      ys'.Perm (y :: ys) ∧ Holds2 E ys' sv' := by
  have hxl : (Term.denotes M x.1).length = w := by rw [denotes_eq_map, List.length_map, x.2]
  obtain ⟨h1, h2⟩ := insertSlots_den x (Term.denotes M x.1) rfl p true hp hS
  obtain ⟨hocc, -⟩ := insertVals_occupied (Term.denotes M x.1) true sv
  obtain ⟨hl, hw'⟩ := insertVals_length (Term.denotes M x.1) w hxl true sv hw
  have hp : (insertVals (Term.denotes M x.1) true sv).2 = false := by
    simp only [Holds, Term.denote, h2, Val.toBool] at hc; simpa using hc
  rw [hp] at hocc
  simp only [and_self, ite_true, List.singleton_append] at hocc
  obtain ⟨ys', hperm, hh⟩ := forall2_perm hocc.symm (as := y :: ys) ⟨hey, hy⟩
  exact ⟨_, ys', h1, hl, hw', hperm, hh⟩

/-- Moving the occupied slots of `S` into the slots `T` one by one, when each found a free slot. -/
theorem moveAll_rel {α : Type} {E : α → List Val → Prop} (d dt : Nat) {w : Nat} :
    {S : List (Slot w)} → {sv : List (Bool × List Val)} → {ys : List α} → SlotsDen M S sv →
    (∀ p ∈ sv, p.2.length = w) → Holds2 E ys sv → {T : List (Slot w)} → {tv : List (Bool × List Val)} →
    {zs : List α} → SlotsDen M T tv → (∀ p ∈ tv, p.2.length = w) → Holds2 E zs tv →
    Holds M (moveAll d dt T S).2 →
    ∃ tv' zs', SlotsDen M (moveAll d dt T S).1 tv' ∧ tv'.length = tv.length ∧ (∀ p ∈ tv', p.2.length = w) ∧
      zs'.Perm (ys ++ zs) ∧ Holds2 E zs' tv'
  | [], [], ys, _, _, hy, T, tv, zs, hT, htw, hz, _ => by
    have : ys = [] := by cases ys <;> simp_all [Holds2, occupied, Forall2]
    subst this; exact ⟨tv, zs, hT, rfl, htw, List.Perm.refl _, hz⟩
  | (f, xs) :: S, (b, vs) :: sv, ys, ⟨hf, hx, hS⟩, hw, hy, T, tv, zs, hT, htw, hz, hc => by
    simp only [moveAll] at hc ⊢
    obtain ⟨hc1, hc2⟩ := (holds_and _ _).1 hc
    have hvs : vs.length = w := hw (b, vs) (by simp)
    have hw' : ∀ p ∈ sv, p.2.length = w := fun q hq => hw q (by simp [hq])
    obtain ⟨h1, h2⟩ := insertSlots_den xs vs hx f b hf hT
    obtain ⟨hl1, hw1⟩ := insertVals_length vs w hvs b tv htw
    have hT1 := slotsOf_den d dt w _ _ (slotsTerm_den d dt h1) hw1
    rw [← slotsDen_length h1] at hT1
    have hp : (insertVals vs b tv).2 = false := by
      simp only [Holds, Term.denote, h2, Val.toBool] at hc1; simpa using hc1
    cases b with
    | false =>
      simp only [insertVals_false] at hT1 hw1 hl1
      obtain ⟨tv2, zs2, h3, h4, h5, h6, h7⟩ :=
        moveAll_rel d dt hS hw' (by simpa [Holds2, occupied] using hy) hT1 hw1 hz hc2
      exact ⟨tv2, zs2, h3, h4, h5, h6, h7⟩
    | true =>
      obtain ⟨y, ys', hey, hy'⟩ : ∃ y ys', ys = y :: ys' ∧ E y vs ∧ Holds2 E ys' sv := by
        cases ys with
        | nil => simp [Holds2, occupied, Forall2] at hy
        | cons y ys' => simp only [Holds2, occupied, ite_true, List.filterMap_cons, Forall2] at hy; exact ⟨y, ys', rfl, hy⟩
      obtain ⟨rfl, hey, hy'⟩ := hey
      obtain ⟨hocc, -⟩ := insertVals_occupied vs true tv
      rw [hp] at hocc
      simp only [and_self, ite_true, List.singleton_append] at hocc
      obtain ⟨zs1, hp1, hh1⟩ := forall2_perm hocc.symm (as := y :: zs) ⟨hy'.1, hz⟩
      obtain ⟨tv2, zs2, h3, h4, h5, h6, h7⟩ := moveAll_rel d dt hS hw' hy'.2 hT1 hw1 hh1 hc2
      refine ⟨tv2, zs2, h3, h4.trans hl1, h5, h6.trans ?_, h7⟩
      exact (List.Perm.append_left ys' hp1).trans List.perm_middle

/-- Carrying slots into a collection of another slot count, when they fit. -/
theorem resize_rel {α : Type} {E : α → List Val → Prop} (d dt n : Nat) {w : Nat} (dflt : SlotItems w)
    {S : List (Slot w)} {sv : List (Bool × List Val)} {ys : List α} (hS : SlotsDen M S sv)
    (hw : ∀ p ∈ sv, p.2.length = w) (hy : Holds2 E ys sv) (hc : Holds M (resizeSlots d dt dflt n S).2) :
    ∃ sv' ys', SlotsDen M (resizeSlots d dt dflt n S).1 sv' ∧ sv'.length = n ∧
      (∀ p ∈ sv', p.2.length = w) ∧ ys'.Perm ys ∧ Holds2 E ys' sv' := by
  have hfree : ∀ m, ∀ p ∈ List.replicate m (false, Term.denotes M dflt.1), p.2.length = w := by
    intro m p hp
    simp only [List.mem_replicate] at hp
    rw [hp.2, denotes_eq_map, List.length_map, dflt.2]
  by_cases hle : S.length ≤ n
  · simp only [resizeSlots, hle, ↓reduceIte]
    refine ⟨sv ++ List.replicate (n - S.length) (false, Term.denotes M dflt.1), ys,
      slotsDen_append hS (empty_den dflt _), ?_, ?_, List.Perm.refl _, ?_⟩
    · rw [List.length_append, List.length_replicate, ← slotsDen_length hS]; omega
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hw p hp
      · exact hfree _ p hp
    · simpa [Holds2, occupied_append, occupied_empty] using hy
  · simp only [resizeSlots, hle, ↓reduceIte] at hc ⊢
    obtain ⟨tv, zs, h1, h2, h3, h4, h5⟩ := moveAll_rel d dt hS hw hy (empty_den dflt n) (hfree n)
      (zs := []) (by simp [Holds2, occupied_empty, Forall2]) hc
    exact ⟨tv, zs, h1, by simpa using h2, h3, by simpa using h4, h5⟩

/-- A collection built from slots holding its items. -/
theorem collOf_rel {α : Type} {E : α → List Val → Prop} {c : Ty} {item : List Ty} {S : List (Slot item.length)}
    {sv : List (Bool × List Val)} {ys : List α} {r cond : Term} (h : collOf L c item S = .ok (r, cond))
    (hS : SlotsDen M S sv) (hw : ∀ p ∈ sv, p.2.length = item.length) (hy : Holds2 E ys sv) (hc : Holds M cond) :
    ∃ d n dt, ∃ S' : List (Slot item.length), ∃ sv' ys', collD L c item = .ok (d, n, dt) ∧ r = slotsTerm d dt S' ∧ SlotsDen M S' sv' ∧
      sv'.length = n ∧ (∀ p ∈ sv', p.2.length = item.length) ∧ ys'.Perm ys ∧ Holds2 E ys' sv' := by
  simp only [collOf] at h
  obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨dflt, -, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  obtain ⟨sv', ys', h3, h4, h5, h6, h7⟩ := resize_rel d dt n dflt hS hw hy hc
  exact ⟨d, n, dt, _, sv', ys', h1, rfl, h3, h4, h5, h6, h7⟩

theorem need'_ok {α : Type} {w : Refusal} {b : Bool} {a a' : α} (h : need' w b a = .ok a') : b = true ∧ a' = a := by
  unfold need' at h; split at h
  · cases h; exact ⟨by assumption, rfl⟩
  · cases h

/-- The keys that `table.remove` keeps: the slot terms denote `!sameKey`. -/
theorem keep_aligned {k w : Ty} (hk : k.eqable = true) (key : k.den) (kt : Term) (hkt : RelV L k key (kt.denote M))
    {S : List (Slot 2)} {sv : List (Bool × List Val)} {ys : List (k.den × w.den)} (hS : SlotsDen M S sv)
    (hy : Holds2 (ETab L k w) ys sv) :
    Aligned M (ETab L k w) (fun e => !(k.deq key e.1 || k.deq e.1 key)) S (keepQs kt S) sv ys := by
  refine aligned_map (fun xs => .not (.or (.eq kt xs[0]) (.eq xs[0] kt))) ?_ hS hy
  intro e xs he
  obtain ⟨zk, zv, hxs, hzk, _⟩ := he
  obtain ⟨tk, tv, rfl⟩ := xs.two
  simp only [Term.denotes, List.cons.injEq] at hxs
  simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, hxs.1, Val.toBool]
  show Val.bool (!(Val.beq (kt.denote M) zk || Val.beq zk (kt.denote M))) = _
  rw [relV_beq k hk key e.1 _ _ hkt hzk, relV_beq k hk e.1 key _ _ hzk hkt]

/-- `table.insert` on slots: the key's slot freed, then the entry in the first free slot. -/
theorem put_den {k w : Ty} (hk : k.eqable = true) {t0 : (Ty.table k w).den} {S : List (Slot 2)}
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
    insert_rel hS' hw' hh' ⟨[kt, vt], rfl⟩ (key, val) ⟨_, _, by simp [Term.denotes], hkt, hvt⟩ rfl hc
  refine ⟨sv'', ys'', hS'', hl''.trans hl', hw'', hperm''.trans ?_, hh''⟩
  exact ((hperm.filter _).cons _).trans (List.perm_append_singleton _ _).symm

theorem iteSlots_den {f : Term} {b : Bool} (hf : f.denote M = .bool b) {w : Nat} : {T S : List (Slot w)} →
    {tv sv : List (Bool × List Val)} → SlotsDen M T tv → SlotsDen M S sv → tv.length = sv.length →
    SlotsDen M (iteSlots f T S) (if b then tv else sv)
  | [], [], [], [], _, _, _ => by cases b <;> trivial
  | (g, xs) :: T, (g', xs') :: S, (c, vs) :: tv, (c', vs') :: sv, ⟨hg, hx, hT⟩, ⟨hg', hx', hS⟩, hl => by
    have ih := iteSlots_den hf hT hS (by simpa using hl)
    have hz := zip_ite f b hf xs.1 xs'.1 (by rw [xs.2, xs'.2])
    simp only [iteSlots, List.zipWith_cons_cons] at ih ⊢
    cases b with
    | true =>
      simp only [ite_true] at ih hz ⊢
      exact ⟨by simp [Term.denote, hf, hg, Val.toBool], by rw [hz, hx], ih⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false] at ih hz ⊢
      exact ⟨by simp [Term.denote, hf, hg', Val.toBool], by rw [hz, hx'], ih⟩
  | [], [], _ :: _, _, hT, _, _ | [], [], [], _ :: _, _, hS, _ | [], _ :: _, [], [], _, hS, _
  | [], _ :: _, _ :: _, _, hT, _, _ | _ :: _, [], [], _, hT, _, _
  | _ :: _, [], _ :: _, _ :: _, _, hS, _ | _ :: _, _ :: _, [], _, hT, _, _
  | _ :: _, _ :: _, _ :: _, [], _, hS, _ => by first | exact hT.elim | exact hS.elim
  | [], _ :: _, [], _ :: _, _, _, hl | _ :: _, [], _ :: _, [], _, _, hl => by simp at hl

theorem filterSlots_any {w : Nat} : {S : List (Slot w)} → {sv : List (Bool × List Val)} → (qs : List Term) → SlotsDen M S sv →
    qs.length = S.length → ∃ sv', SlotsDen M (filterSlots S qs) sv' ∧ sv'.map (·.2) = sv.map (·.2)
  | [], [], [], _, _ => ⟨[], trivial, rfl⟩
  | (f, xs) :: S, (b, vs) :: sv, q :: qs, ⟨hf, hx, h⟩, hl => by
    obtain ⟨sv', h1, h2⟩ := filterSlots_any qs h (by simpa using hl)
    exact ⟨(b && (q.denote M).toBool, vs) :: sv', ⟨by simp [Term.denote, hf, Val.toBool], hx, h1⟩, by simp [h2]⟩
  | [], [], _ :: _, _, hl | _ :: _, _ :: _, [], _, hl => by simp at hl
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => h.elim

/-- The slots after `table.insert` denote some slots of the same shape, whatever the key and value. -/
theorem putSlots_any {S : List (Slot 2)} {sv : List (Bool × List Val)} (hS : SlotsDen M S sv)
    (hw : ∀ p ∈ sv, p.2.length = 2) (k v : Term) :
    ∃ sv', SlotsDen M (putSlots S k v).1 sv' ∧ sv'.length = sv.length ∧ ∀ p ∈ sv', p.2.length = 2 := by
  obtain ⟨sv1, h1, h2⟩ := filterSlots_any (keepQs k S) hS (by simp [keepQs])
  have hl1 : sv1.length = sv.length := by simpa using congrArg List.length h2
  have hw1 : ∀ p ∈ sv1, p.2.length = 2 := fun p hp => by
    have : p.2 ∈ sv.map (·.2) := h2 ▸ List.mem_map_of_mem hp
    obtain ⟨q, hq, e⟩ := List.mem_map.1 this
    rw [← e]; exact hw q hq
  obtain ⟨hS', -⟩ := insertSlots_den ⟨[k, v], rfl⟩ _ rfl tt true rfl h1
  obtain ⟨hl', hw'⟩ := insertVals_length (Term.denotes M [k, v]) 2 rfl true sv1 hw1
  exact ⟨_, hS', hl'.trans hl1, hw'⟩

/-- `table.from_list` on a list's slots: each occupied slot's pair inserted in turn. -/
theorem putFrom_rel {k w : Ty} (hk : k.eqable = true) (d dt dp : Nat) (hdp : ∃ m, L.find? (.tuple [k, w]) = some (dp, m)) :
    {P : List (Slot 1)} → {lv : List (Bool × List Val)} → SlotsDen M P lv →
    {pairs : List (Ty.tuple [k, w]).den} → Holds2 (EBag L (.tuple [k, w])) pairs lv →
    {t0 : (Ty.table k w).den} → {S : List (Slot 2)} → {sv : List (Bool × List Val)} → {ys : List (k.den × w.den)} →
    SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 2) → ys.Perm t0.1 → Holds2 (ETab L k w) ys sv →
    Holds M (putFrom d dt dp S P).2 →
    ∃ sv' ys', SlotsDen M (putFrom d dt dp S P).1 sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 2) ∧
      ys'.Perm (pairs.foldl (fun t (k, v, ()) => Builtin.tableInsert k v t) t0).1 ∧ Holds2 (ETab L k w) ys' sv'
  | [], [], _, pairs, hpr, t0, S, sv, ys, hS, hw, hp, hh, _ => by
    have : pairs = [] := by cases pairs <;> simp_all [Holds2, occupied, Forall2]
    subst this
    exact ⟨sv, ys, hS, rfl, hw, hp, hh⟩
  | (f, xs) :: P, (b, vs) :: lv, ⟨hf, hxs, hP⟩, pairs, hpr, t0, S, sv, ys, hS, hw, hp, hh, hc => by
    obtain ⟨x0, rfl⟩ := xs.one
    simp only [putFrom, SlotItems.getElem_mk, List.getElem_cons_zero] at hc ⊢
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    have hT : ∀ {sv1 : List (Bool × List Val)} {ys1 : List (k.den × w.den)} {t1 : (Ty.table k w).den},
        SlotsDen M (iteSlots f (putSlots S (.sel dp 0 0 x0) (.sel dp 0 1 x0)).1 S) sv1 →
        sv1.length = sv.length → (∀ p ∈ sv1, p.2.length = 2) → ys1.Perm t1.1 → Holds2 (ETab L k w) ys1 sv1 →
        {pairs' : List (Ty.tuple [k, w]).den} → Holds2 (EBag L (.tuple [k, w])) pairs' lv →
        ∃ sv' ys', SlotsDen M (putFrom d dt dp (slotsOf d dt (iteSlots f (putSlots S (.sel dp 0 0 x0)
            (.sel dp 0 1 x0)).1 S).length 2 (slotsTerm d dt (iteSlots f (putSlots S (.sel dp 0 0 x0)
            (.sel dp 0 1 x0)).1 S))) P).1 sv' ∧ sv'.length = sv.length ∧ (∀ p ∈ sv', p.2.length = 2) ∧
          ys'.Perm (pairs'.foldl (fun t (k, v, ()) => Builtin.tableInsert k v t) t1).1 ∧ Holds2 (ETab L k w) ys' sv' := by
      intro sv1 ys1 t1 hS1 hl1 hw1 hp1 hh1 pairs' hpr'
      have hlen := slotsDen_length hS1
      have hS1' := slotsOf_den d dt 2 _ sv1 (slotsTerm_den d dt hS1) hw1
      rw [← hlen] at hS1'
      obtain ⟨sv2, ys2, hS2, hl2, hw2, hp2, hh2⟩ := putFrom_rel hk d dt dp hdp hP hpr' hS1' hw1 hp1 hh1 hc2
      exact ⟨sv2, ys2, hS2, hl2.trans hl1, hw2, hp2, hh2⟩
    cases b with
    | true =>
      have hc1' : Holds M (putSlots S (.sel dp 0 0 x0) (.sel dp 0 1 x0)).2 := by
        simpa [Holds, Term.denote, hf, Val.toBool] using hc1
      match pairs, hpr with
      | (key, val, ()) :: pairs', ⟨⟨z, hz, he⟩, hrest⟩ =>
        subst hz
        obtain ⟨m, hfd⟩ := hdp
        obtain ⟨d', n', vals, hf', ev, zk, rest, e1, hzk, zv, rest', e2, hzv, e3⟩ := he
        obtain rfl := find_det hfd hf'
        subst e1 e2
        simp only [RelVs] at e3; subst e3
        have hx0 : x0.denote M = z := by simpa [Term.denotes] using hxs
        have hk' : RelV L k key (Term.denote M (.sel dp 0 0 x0)) := by rw [sel_ctor 0 (hx0.trans ev)]; exact hzk
        have hv' : RelV L w val (Term.denote M (.sel dp 0 1 x0)) := by rw [sel_ctor 1 (hx0.trans ev)]; exact hzv
        obtain ⟨sv1, ys1, hS1, hl1, hw1, hp1, hh1⟩ := put_den hk hS hw hp hh key val _ _ hk' hv' hc1'
        have hI := iteSlots_den hf hS1 hS hl1
        simp only [ite_true] at hI
        exact hT hI hl1 hw1 hp1 hh1 hrest
    | false =>
      obtain ⟨svp, hSp, hlp, hwp⟩ := putSlots_any hS hw (.sel dp 0 0 x0) (.sel dp 0 1 x0)
      have hI := iteSlots_den hf hSp hS hlp
      simp only [Bool.false_eq_true, ite_false] at hI
      exact hT hI rfl hw hp hh (by simpa [Holds2, occupied] using hpr)
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _, _, _, _, _, _ => h.elim

theorem list_view {t : Ty} {xs : (Ty.list t).den} {b : Term} (hb : Rel M L (.list t) xs b) {d n dt : Nat}
    (hc : collD L (.list t) [t] = .ok (d, n, dt)) :
    ∃ sv, SlotsDen M (slotsOf d dt n 1 b) sv ∧ sv.length = n ∧ (∀ p ∈ sv, p.2.length = 1) ∧ Holds2 (EBag L t) xs sv := by
  obtain ⟨hf, m, hft⟩ := collD_ok hc
  obtain ⟨d', n', dt', m', sv, hf', hft', hl, hv, hw, hh⟩ := hb
  rw [hf] at hf'; cases hf'
  rw [hft] at hft'; cases hft'
  refine ⟨sv, ?_, hl, hw, hh⟩
  rw [← hl]; exact slotsOf_den d dt 1 b sv hv hw

theorem items_terms {t : Ty} {w : Refusal} : {xs : List t.den} → {items : List (Code t)} → {ts : List Term} →
    Forall2 (Rel M L t) xs items → Forall2 (fun x y => need w (Code.term? t x) = .ok y) items ts →
    Forall2 (fun x tm => RelV L t x (Term.denote M tm)) xs ts
  | [], [], [], _, _ => trivial
  | y :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨(rel_term (need_ok.1 h3) y).1 h1, items_terms h2 h4⟩
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ | _, [], _ :: _, _, h | _, _ :: _, [], _, h => nomatch h

theorem items_den : (ts : List Term) →
    SlotsDen M (ts.map ((tt, ⟨[·], rfl⟩) : Term → Slot 1)) (ts.map fun tm => (true, [tm.denote M]))
  | [] => trivial
  | _ :: ts => ⟨rfl, rfl, items_den ts⟩

theorem items_ebag {t : Ty} : {xs : List t.den} → {ts : List Term} →
    Forall2 (fun x tm => RelV L t x (Term.denote M tm)) xs ts → Forall2 (EBag L t) xs (ts.map fun tm => [tm.denote M])
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩ => ⟨⟨_, rfl, h⟩, items_ebag hs⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- A list literal's slots hold its items in order. -/
theorem listOf_rel {t : Ty} : {xs : List t.den} → {ts : List Term} →
    Forall2 (fun x tm => RelV L t x (Term.denote M tm)) xs ts → {r c : Term} → listOf L t ts = .ok (r, c) →
    Holds M c → RelV L (.list t) xs (r.denote M) := by
  intro xs ts hx r c h hc
  obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨dflt, h2, h⟩ := bind_ok.1 h
  obtain ⟨hf, m, hft⟩ := collD_ok h1
  split at h
  · rename_i hle
    cases pure_ok.1 h
    let sv := ts.map (fun tm => (true, [tm.denote M])) ++ List.replicate (n - ts.length) (false, [dflt.denote M])
    have hS : SlotsDen M (ts.map ((tt, ⟨[·], rfl⟩) : Term → Slot 1) ++
        List.replicate (n - ts.length) (.bool false, ⟨[dflt], rfl⟩)) sv :=
      slotsDen_append (items_den ts) (empty_den ⟨[dflt], rfl⟩ _)
    refine ⟨d, n, dt, m, sv, hf, hft, by simp [sv]; omega, slotsTerm_den d dt hS, ?_, ?_⟩
    · intro p hp
      simp only [sv, List.mem_append, List.mem_map, List.mem_replicate] at hp
      rcases hp with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    · show Forall2 _ xs (occupied sv)
      rw [show occupied sv = ts.map fun tm => [tm.denote M] by
        simp [sv, occupied, List.filterMap_append, List.filterMap_map, Function.comp_def]]
      exact items_ebag hx
  · cases pure_ok.1 h
    simp [Holds, Term.denote, Val.toBool] at hc

theorem eBag_rels {t : Ty} (y : t.den) (vs : List Val) (h : EBag L t y vs) : RelVs L [t] (y, ()) vs := by
  obtain ⟨z, rfl, hz⟩ := h; exact ⟨z, [], rfl, hz, rfl⟩

theorem eTab_rels {k w : Ty} (e : k.den × w.den) (vs : List Val) (h : ETab L k w e vs) :
    RelVs L [k, w] (e.1, e.2, ()) vs := by
  obtain ⟨zk, zv, rfl, hk, hv⟩ := h; exact ⟨zk, [zv], rfl, hk, zv, [], rfl, hv, rfl⟩

end

section
variable {M : Model} {L : Layout}

mutual
theorem Val.eq_of_beq : (a b : Val) → Val.beq a b = true → a = b
  | .int _, .int _, h | .bool _, .bool _, h | .str _, .str _, h => by simp [Val.beq] at h; rw [h]
  | .ctor d k as, .ctor d' k' bs, h => by
    simp only [Val.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1.1, h.1.2, Val.eq_of_beqs as bs h.2]
  | .int _, .bool _, h | .int _, .str _, h | .int _, .ctor .., h | .bool _, .int _, h | .bool _, .str _, h
  | .bool _, .ctor .., h | .str _, .int _, h | .str _, .bool _, h | .str _, .ctor .., h | .ctor .., .int _, h
  | .ctor .., .bool _, h | .ctor .., .str _, h => by simp [Val.beq] at h
theorem Val.eq_of_beqs : (as bs : List Val) → Val.beqs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Val.beqs, Bool.and_eq_true] at h; rw [Val.eq_of_beq a b h.1, Val.eq_of_beqs as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Val.beqs] at h
end

theorem lookupBy_find {κ ν : Type} (f : κ → κ → Bool) (k : κ) : (xs : List (κ × ν)) →
    lookupBy f k xs = (xs.find? fun e => f k e.1).map (·.2)
  | [] => rfl
  | (k', v) :: rest => by
    cases h : f k k' <;> simp [lookupBy, h, lookupBy_find f k rest]

/-- When no two items both satisfy `P`, an item that does is the one `find?` returns. -/
theorem find_unique {α : Type} {P : α → Bool} : {xs : List α} → xs.Pairwise (fun a b => ¬(P a = true ∧ P b = true)) →
    {a : α} → a ∈ xs → P a = true → xs.find? P = some a
  | b :: rest, hu, a, ha, hp => by
    rw [List.pairwise_cons] at hu
    rw [List.find?_cons]
    rcases List.mem_cons.1 ha with rfl | ha'
    · simp [hp]
    · by_cases hb : P b = true
      · exact absurd ⟨hb, hp⟩ (hu.1 a ha')
      · simp only [hb]; exact find_unique hu.2 ha' hp

theorem find_perm {α : Type} {P : α → Bool} {xs ys : List α} (hp : xs.Perm ys)
    (hu : xs.Pairwise (fun a b => ¬(P a = true ∧ P b = true))) : xs.find? P = ys.find? P := by
  have hu' := hp.pairwise hu (fun h e => h ⟨e.2, e.1⟩)
  by_cases h : ∃ a ∈ xs, P a = true
  · obtain ⟨a, ha, hpa⟩ := h
    rw [find_unique hu ha hpa, find_unique hu' (hp.mem_iff.1 ha) hpa]
  · have h1 : xs.find? P = none := List.find?_eq_none.2 fun a ha hpa => h ⟨a, ha, hpa⟩
    have h2 : ys.find? P = none := List.find?_eq_none.2 fun a ha hpa => h ⟨a, hp.mem_iff.2 ha, hpa⟩
    rw [h1, h2]

/-- The value term of the first occupied slot whose hit holds relates to the first item satisfying `P`. -/
theorem pick_aligned {α : Type} {E : α → List Val → Prop} {P : α → Bool} {w : Nat} (R : SlotItems w → Term)
    (V : α → Val → Prop) (hR : ∀ y (xs : SlotItems w), E y (Term.denotes M xs.1) → V y ((R xs).denote M))
    (none : Term) : {S : List (Slot w)} → {qs : List Term} → {sv : List (Bool × List Val)} → {ys : List α} →
    Aligned M E P S qs sv ys → ∀ y, ys.find? P = some y →
      V y ((pickT none (List.zipWith (fun sl q => (sl.1, q, R sl.2)) S qs)).denote M)
  | [], [], [], [], _, y, hy => by simp at hy
  | (f, xs) :: S, q :: qs, (false, vs) :: sv, ys, ⟨hf, _, h⟩, y, hy => by
    simp only [List.zipWith_cons_cons, pickT, Term.denote, hf, Val.toBool, Bool.false_and]
    exact pick_aligned R V hR none h y hy
  | (f, xs) :: S, q :: qs, (true, vs) :: sv, y' :: ys, ⟨hf, hx, he, hq, h⟩, y, hy => by
    simp only [List.zipWith_cons_cons, pickT, Term.denote, hf, hq, Val.toBool, Bool.true_and]
    rw [List.find?_cons] at hy
    cases hp : P y' with
    | true => simp only [hp] at hy ⊢; cases hy; exact hR y' xs (hx ▸ he)
    | false => simp only [hp] at hy ⊢; exact pick_aligned R V hR none h y hy

/-- A lookup in a table's slots: whether the key is there, and its value when it is. -/
theorem lookupT_rel {k w : Ty} {x : (Ty.table k w).den} {t : Term} (hb : Rel M L (.table k w) x t)
    (hk : k.eqable = true) {d n dt : Nat} (h1 : collD L (.table k w) [k, w] = .ok (d, n, dt)) (key : k.den)
    (kt' : Term) (hkt' : RelV L k key (kt'.denote M)) (dv : Term) :
    (lookupT kt' dv (slotsOf d dt n 2 t)).1.denote M = .bool (lookupBy (Ty.deq k) key x.1).isSome ∧
      ∀ val, lookupBy (Ty.deq k) key x.1 = some val →
        RelV L w val ((lookupT kt' dv (slotsOf d dt n 2 t)).2.denote M) := by
  obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
  let P : k.den × w.den → Bool := fun e => k.deq key e.1
  have ha : Aligned M (ETab L k w) P (slotsOf d dt n 2 t) (hitQs kt' (slotsOf d dt n 2 t)) sv ys := by
    refine aligned_map (fun xs => .eq kt' xs[0]) ?_ hS hh
    intro e xs he
    obtain ⟨zk, zv, hxs, hzk, _⟩ := he
    obtain ⟨tk, tv, rfl⟩ := xs.two
    simp only [Term.denotes, List.cons.injEq] at hxs
    simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, hxs.1]
    show Val.bool (Val.beq (kt'.denote M) zk) = _
    rw [relV_beq k hk key e.1 _ _ hkt' hzk]
  have hu : ys.Pairwise (fun a b => ¬(P a = true ∧ P b = true)) := by
    refine (hperm.symm.pairwise x.2 fun h => ⟨h.2, h.1⟩).imp_of_mem ?_
    intro a b ha hb' hab hp
    obtain ⟨va, -, zka, zva, rfl, hza, -⟩ := forall2_mem_left hh _ ha
    obtain ⟨vb, -, zkb, zvb, rfl, hzb, -⟩ := forall2_mem_left hh _ hb'
    have e1 := Val.eq_of_beq _ _ ((relV_beq k hk key a.1 _ _ hkt' hza).trans hp.1)
    have e2 := Val.eq_of_beq _ _ ((relV_beq k hk key b.1 _ _ hkt' hzb).trans hp.2)
    have := relV_beq k hk a.1 b.1 _ _ hza hzb
    rw [← e1, ← e2] at this
    have hr : Val.beq (kt'.denote M) (kt'.denote M) = true := by
      have h0 := (relV_beq k hk key a.1 _ _ hkt' hza).trans hp.1
      rwa [← e1] at h0
    rw [hr] at this
    exact absurd this.symm (by simp [hab.1])
  have hfind : lookupBy (Ty.deq k) key x.1 = (ys.find? P).map (·.2) := by
    rw [lookupBy_find]; exact congrArg _ (find_perm hperm.symm (hperm.pairwise hu fun h e => h ⟨e.2, e.1⟩))
  refine ⟨?_, fun val hv => ?_⟩
  · simp only [lookupT, anySlotT_den ha, hfind, Option.isSome_map]
    congr 1
    cases hf : ys.find? P with
    | none =>
      simp only [Option.isSome_none, Bool.eq_false_iff]
      intro hany
      obtain ⟨a, ha, hpa⟩ := List.any_eq_true.1 hany
      exact List.find?_eq_none.1 hf a ha hpa
    | some y => simp only [Option.isSome_some, List.any_eq_true]; exact ⟨y, List.mem_of_find?_eq_some hf,
        List.find?_some hf⟩
  · rw [hfind] at hv
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hv
    refine pick_aligned (fun xs => xs[1]) (fun y v => RelV L w y.2 v) ?_ dv ha y hy
    intro e xs he
    obtain ⟨zk, zv, hxs, -, hzv⟩ := he
    obtain ⟨_, tv, rfl⟩ := xs.two
    simp only [Term.denotes, List.cons.injEq] at hxs
    simpa [hxs.2.1] using hzv

theorem lookup_rel {k w : Ty} {x : (Ty.table k w).den} {t : Term} (hb : Rel M L (.table k w) x t) (key : k.den)
    (kt : Term) (hkt : RelV L k key (kt.denote M)) {hit found : Term}
    (h : lookupCode L k w t kt = .ok (hit, found)) :
    hit.denote M = .bool (lookupBy (Ty.deq k) key x.1).isSome ∧
      ∀ val, lookupBy (Ty.deq k) key x.1 = some val → RelV L w val (found.denote M) := by
  simp only [lookupCode] at h
  obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨kt', h2, h⟩ := bind_ok.1 h
  obtain ⟨hk, hkk⟩ := need'_ok h2
  obtain ⟨dv, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  exact lookupT_rel hb hk h1 key kt' (hkk ▸ hkt) dv

theorem natCast_beq (m n : Nat) : ((m : Int) == (n : Int)) = (m == n) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; omega

/-- A builder of `==` terms that is Gleam's `==` on any two terms denoting values of `t`. -/
def EqOk (M : Model) (L : Layout) (t : Ty) (eq : Term → Term → Term) : Prop :=
  ∀ (x y : t.den) (a b : Term), RelV L t x (a.denote M) → RelV L t y (b.denote M) →
    (eq a b).denote M = .bool (Ty.deq t x y)

/-- One `EqOk` builder per type, in order. -/
def EqsOk (M : Model) (L : Layout) : List Ty → List (Term → Term → Term) → Prop
  | [], fs => fs = []
  | t :: ts, fs => ∃ f fs', fs = f :: fs' ∧ EqOk M L t f ∧ EqsOk M L ts fs'

/-- One `EqsOk` list per variant, in order. -/
def EqssOk (M : Model) (L : Layout) : List (List Ty) → List (List (Term → Term → Term)) → Prop
  | [], fss => fss = []
  | ts :: vs, fss => ∃ fs fss', fss = fs :: fss' ∧ EqsOk M L ts fs ∧ EqssOk M L vs fss'

theorem eqOk_eq {t : Ty} (he : t.eqable = true) : EqOk M L t .eq := fun x y _ _ hx hy => by
  simp only [Term.denote]; exact congrArg Val.bool (relV_beq t he x y _ _ hx hy)

/-- How often an item occurs among a bag's slots. -/
theorem countEqT_den {a : Ty} {eq : Term → Term → Term} (heq : EqOk M L a eq) {z : a.den} {x : Term}
    (hz : RelV L a z (x.denote M)) {S : List (Slot 1)} {sv : List (Bool × List Val)} {ys : List a.den}
    (hS : SlotsDen M S sv) (hh : Holds2 (EBag L a) ys sv) :
    (countEqT eq x S).denote M = .int (ys.filter (Ty.deq a z)).length := by
  have ha : Aligned M (EBag L a) (fun y => Ty.deq a z y) S (S.map fun sl => eq x sl.2[0]) sv ys :=
    aligned_map (fun xs => eq x xs[0]) (fun y xs he => by
      obtain ⟨w, hw, hyw⟩ := he
      obtain ⟨t, rfl⟩ := xs.one
      simp only [Term.denotes, List.cons.injEq] at hw
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero]
      exact heq z y x t hz (hw.1 ▸ hyw)) hS hh
  exact countT_den ha

theorem fieldsEqT_den (d k : Nat) : (ts : List Ty) → {fs : List (Term → Term → Term)} → EqsOk M L ts fs →
    (j : Nat) → (x y : Ty.dens ts) → (a b : Term) → (pa pb va vb : List Val) → a.denote M = .ctor d k (pa ++ va) →
    b.denote M = .ctor d k (pb ++ vb) → pa.length = j → pb.length = j → RelVs L ts x va → RelVs L ts y vb →
    (fieldsEqT d k j fs a b).denote M = .bool ((Ty.semsWith Dsl.val ts).2 x y)
  | [], _, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by cases h; rfl
  | t :: ts, _, ⟨f, fs, rfl, hf, hfs⟩, j, (x, xs), (y, ys), a, b, pa, pb, _, _, ha, hb, hpa, hpb, hx, hy => by
    obtain ⟨v, va, rfl, hx, hxs⟩ := hx
    obtain ⟨w, vb, rfl, hy, hys⟩ := hy
    have sa : (Term.sel d k j a).denote M = v := by simp [Term.denote, ha, ← hpa]
    have sb : (Term.sel d k j b).denote M = w := by simp [Term.denote, hb, ← hpb]
    have e := fieldsEqT_den d k ts hfs (j + 1) xs ys a b (pa ++ [v]) (pb ++ [w]) va vb (by simpa using ha)
      (by simpa using hb) (by simp [hpa]) (by simp [hpb]) hxs hys
    simp only [fieldsEqT, Term.denote, e, hf x y _ _ (sa ▸ hx) (sb ▸ hy), Val.toBool, Ty.semsWith, Sem.pair]

/-- No variant from `k` on matches a value built by an earlier constructor. -/
theorem altsEqT_early (d : Nat) : (k : Nat) → (fss : List (List (Term → Term → Term))) → (a b : Term) →
    ((∃ j vs, a.denote M = .ctor d j vs ∧ j < k) ∨ (∃ j vs, b.denote M = .ctor d j vs ∧ j < k)) →
    (altsEqT d k fss a b).denote M = .bool false
  | _, [], _, _, _ => rfl
  | k, _ :: fss, a, b, h => by
    have e := altsEqT_early d (k + 1) fss a b (by
      rcases h with ⟨j, vs, h, hj⟩ | ⟨j, vs, h, hj⟩
      · exact .inl ⟨j, vs, h, by omega⟩
      · exact .inr ⟨j, vs, h, by omega⟩)
    rcases h with ⟨j, vs, h, hj⟩ | ⟨j, vs, h, hj⟩ <;>
      simp [altsEqT, Term.denote, e, h, Val.toBool, Nat.ne_of_lt hj]

theorem altsEqT_den (d : Nat) : (k : Nat) → (vs : List (List Ty)) → {fss : List (List (Term → Term → Term))} →
    EqssOk M L vs fss → (x y : Ty.alts vs) → (a b : Term) → RelAlts L d k vs x (a.denote M) →
    RelAlts L d k vs y (b.denote M) → (altsEqT d k fss a b).denote M = .bool ((Ty.semAltsWith Dsl.val vs).2 x y)
  | k, fs :: _, _, ⟨_, fss, rfl, hfs, _⟩, .inl x, .inl y, a, b, ⟨va, ea, hx⟩, ⟨vb, eb, hy⟩ => by
    have e1 := fieldsEqT_den d k fs hfs 0 x y a b [] [] va vb ea eb rfl rfl hx hy
    have e2 := altsEqT_early d (k + 1) fss a b (.inl ⟨k, va, ea, by omega⟩)
    simp [altsEqT, Term.denote, ea, eb, e1, e2, Val.toBool, Ty.semAltsWith, Sem.sum]
  | k, _ :: vs, _, ⟨_, fss, rfl, _, hfss⟩, .inr x, .inr y, a, b, hx, hy => by
    obtain ⟨j, va, ea, hj⟩ := relAlts_index d (k + 1) vs x _ hx
    have e := altsEqT_den d (k + 1) vs hfss x y a b hx hy
    simp [altsEqT, Term.denote, ea, e, Val.toBool, Ty.semAltsWith, Sem.sum, show j ≠ k by omega]
  | k, _ :: vs, _, ⟨_, fss, rfl, _, _⟩, .inl _, .inr y, a, b, ⟨va, ea, _⟩, hy => by
    obtain ⟨j, vb, eb, hj⟩ := relAlts_index d (k + 1) vs y _ hy
    have e := altsEqT_early d (k + 1) fss a b (.inl ⟨k, va, ea, by omega⟩)
    simp [altsEqT, Term.denote, ea, eb, e, Val.toBool, Ty.semAltsWith, Sem.sum, show j ≠ k by omega]
  | k, _ :: vs, _, ⟨_, fss, rfl, _, _⟩, .inr x, .inl _, a, b, hx, ⟨vb, eb, _⟩ => by
    obtain ⟨j, va, ea, hj⟩ := relAlts_index d (k + 1) vs x _ hx
    have e := altsEqT_early d (k + 1) fss a b (.inr ⟨k, vb, eb, by omega⟩)
    simp [altsEqT, Term.denote, ea, eb, e, Val.toBool, Ty.semAltsWith, Sem.sum, show j ≠ k by omega]

theorem bagEqT_den {a : Ty} {eq : Term → Term → Term} (heq : EqOk M L a eq) {d n dt : Nat}
    (h1 : collD L (.bag a) [a] = .ok (d, n, dt)) : EqOk M L (.bag a) fun x y =>
      bagEqT eq (slotsOf d dt n 1 x) (slotsOf d dt n 1 y) := by
  intro x y sa sb hx hy
  obtain ⟨svA, ysA, hSA, -, -, hpA, hhA⟩ := bag_view (M := M) (b := sa) hx h1
  obtain ⟨svB, ysB, hSB, -, -, hpB, hhB⟩ := bag_view (M := M) (b := sb) hy h1
  show _ = Val.bool (bagBeq (Ty.deq a) x y)
  rw [← bagBeq_perm _ hpA hpB]
  have hq : Aligned M (EBag L a) (fun z => countBy (Ty.deq a) z ysA == countBy (Ty.deq a) z ysB) _ _ svA ysA :=
    aligned_map (fun xs => .eq (countEqT eq xs[0] (slotsOf d dt n 1 sa))
      (countEqT eq xs[0] (slotsOf d dt n 1 sb))) (fun z xs he => by
      obtain ⟨w, hw, hzw⟩ := he
      obtain ⟨t, rfl⟩ := xs.one
      simp only [Term.denotes, List.cons.injEq] at hw
      have hz : RelV L a z (t.denote M) := hw.1 ▸ hzw
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, countEqT_den heq hz hSA hhA,
        countEqT_den heq hz hSB hhB]
      show Val.bool (Val.beq _ _) = _
      simp only [Val.beq, countBy, natCast_beq]) hSA hhA
  simp only [bagEqT, Term.denote, sizeT_den hSA, sizeT_den hSB, allSlotT_den hq, ← holds2_length hhA,
    ← holds2_length hhB, bagBeq]
  show Val.bool (Val.beq _ _ && _) = _
  simp only [Val.beq, Val.toBool, natCast_beq]

theorem tableEqT_den {k v : Ty} {eq : Term → Term → Term} (heq : EqOk M L v eq) (hk : k.eqable = true)
    {d n dt : Nat} (h1 : collD L (.table k v) [k, v] = .ok (d, n, dt)) (dv : Term) : EqOk M L (.table k v) fun x y =>
      tableEqT eq dv (slotsOf d dt n 2 x) (slotsOf d dt n 2 y) := by
  intro x y sa sb hx hy
  obtain ⟨svA, ysA, hSA, -, -, hpA, hhA⟩ := table_view (M := M) (b := sa) hx h1
  obtain ⟨svB, ysB, hSB, -, -, hpB, hhB⟩ := table_view (M := M) (b := sb) hy h1
  show _ = Val.bool (tableBeq (Ty.deq k) (Ty.deq v) x.1 y.1)
  have hq : Aligned M (ETab L k v) (fun (a, b) => match lookupBy (Ty.deq k) a y.1 with
      | some w => Ty.deq v b w
      | none => false) _ _ svA ysA :=
    aligned_map (fun xs => .and (lookupT xs[0] dv (slotsOf d dt n 2 sb)).1
      (eq xs[1] (lookupT xs[0] dv (slotsOf d dt n 2 sb)).2)) (fun e xs he => by
      obtain ⟨ek, ev⟩ := e
      obtain ⟨zk, zv, hxs, hzk, hzv⟩ := he
      obtain ⟨tk, tv, rfl⟩ := xs.two
      simp only [Term.denotes, List.cons.injEq] at hxs
      obtain ⟨hh1, hh2⟩ := lookupT_rel (M := M) (t := sb) hy hk h1 ek tk (hxs.1 ▸ hzk) dv
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero, List.getElem_cons_succ, Term.denote, hh1]
      cases hl : lookupBy (Ty.deq k) ek y.1 with
      | none => simp [Val.toBool]
      | some w =>
        have := heq ev w tv _ (hxs.2.1 ▸ hzv) (hh2 w hl)
        simp only [Option.isSome_some, Val.toBool, Bool.true_and, this]) hSA hhA
  simp only [tableEqT, Term.denote, sizeT_den hSA, sizeT_den hSB, allSlotT_den hq, ← holds2_length hhA,
    ← holds2_length hhB, tableBeq, hpA.length_eq, hpB.length_eq, hpA.all_eq]
  show Val.bool (Val.beq _ _ && _) = _
  simp only [Val.beq, Val.toBool, natCast_beq]
  congr 2
  refine congrArg _ (funext fun e => ?_)
  split <;> split <;> simp_all

mutual
theorem eqFn_ok : (t : Ty) → {f : Term → Term → Term} → eqFn L t = .ok f → EqOk M L t f
  | .int, _, h | .str, _, h | .date, _, h | .id, _, h => by cases h; exact eqOk_eq rfl
  | .dsl k a, _, h => by
    simp only [eqFn] at h
    split at h
    · rename_i hk; simp only [beq_iff_eq] at hk; subst hk; cases h; exact eqOk_eq rfl
    · cases h
  | .adt 0 a vs, _, h => by
    simp only [eqFn] at h
    split at h
    · rename_i hb; cases h; exact eqOk_eq (by simpa [Ty.eqable] using hb)
    · cases h
  | .tuple ts, _, h => by
    simp only [eqFn] at h
    split at h
    · rename_i he; cases h; exact eqOk_eq (by simpa [Ty.eqable] using he)
    · obtain ⟨d, h1, h⟩ := bind_ok.1 h
      obtain ⟨fs, h2, h⟩ := bind_ok.1 h
      cases pure_ok.1 h
      obtain ⟨n, hf⟩ := tupleD_ok h1
      intro x y a b ⟨d1, n1, va, hf1, ea, hx⟩ ⟨d2, n2, vb, hf2, eb, hy⟩
      obtain rfl := find_det hf hf1
      obtain rfl := find_det hf hf2
      exact fieldsEqT_den d 0 ts (eqFns_ok ts h2) 0 x y _ _ [] [] va vb (by simpa using ea) (by simpa using eb)
        rfl rfl hx hy
  | .adt (i + 1) a vs, _, h => by
    simp only [eqFn] at h
    split at h
    · rename_i he; cases h; exact eqOk_eq (by simpa [Ty.eqable] using he)
    · obtain ⟨⟨d, n⟩, h1, h⟩ := bind_ok.1 h
      obtain ⟨fss, h2, h⟩ := bind_ok.1 h
      cases pure_ok.1 h
      have hf := need_ok.1 h1
      intro x y a b ⟨d1, n1, hf1, hx⟩ ⟨d2, n2, hf2, hy⟩
      obtain rfl := find_det hf hf1
      obtain rfl := find_det hf hf2
      exact altsEqT_den d 0 vs (eqFnss_ok vs h2) x y _ _ (by simpa using hx) (by simpa using hy)
  | .bag a, _, h => by
    simp only [eqFn] at h
    obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨f, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact bagEqT_den (eqFn_ok a h2) h1
  | .table k v, _, h => by
    simp only [eqFn] at h
    obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨dv, -, h⟩ := bind_ok.1 h
    obtain ⟨f, h2, h⟩ := bind_ok.1 h
    obtain ⟨hk, rfl⟩ := need'_ok h
    exact tableEqT_den (eqFn_ok v h2) hk h1 dv
  | .list _, _, h | .fn .., _, h | .param _, _, h => by cases h
theorem eqFns_ok : (ts : List Ty) → {fs : List (Term → Term → Term)} → eqFns L ts = .ok fs → EqsOk M L ts fs
  | [], _, h => by cases h; rfl
  | t :: ts, _, h => by
    simp only [eqFns] at h
    obtain ⟨f, h1, h⟩ := bind_ok.1 h
    obtain ⟨fs, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨f, fs, rfl, eqFn_ok t h1, eqFns_ok ts h2⟩
theorem eqFnss_ok : (vs : List (List Ty)) → {fss : List (List (Term → Term → Term))} → eqFnss L vs = .ok fss →
    EqssOk M L vs fss
  | [], _, h => by cases h; rfl
  | ts :: vs, _, h => by
    simp only [eqFnss] at h
    obtain ⟨fs, h1, h⟩ := bind_ok.1 h
    obtain ⟨fss, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact ⟨fs, fss, rfl, eqFns_ok ts h1, eqFnss_ok vs h2⟩
end

/-- `==` on codes is Gleam's `==`. -/
theorem eqCode_rel {t : Ty} {x y : t.den} {sx sy : Code t} (hx : Rel M L t x sx) (hy : Rel M L t y sy) {r : Term}
    (h : eqCode L t sx sy = .ok r) : r.denote M = .bool (Ty.deq t x y) := by
  simp only [eqCode] at h
  obtain ⟨f, h1, h⟩ := bind_ok.1 h
  obtain ⟨tx, h2, h⟩ := bind_ok.1 h
  obtain ⟨ty, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  exact eqFn_ok t h1 x y tx ty ((rel_term (need_ok.1 h2) x).1 hx) ((rel_term (need_ok.1 h3) y).1 hy)

theorem encodeBin_agrees {a b c : Ty} (op : BinOp a b c) (sx : Code a) (sy : Code b) (x : a.den) (y : b.den)
    (hx : Rel M L a x sx) (hy : Rel M L b y sy) (r : Code c) (h : encodeBin L op sx sy = .ok r) :
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
  | concat => cases h; simp only [Rel, RelV] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toStr, BinOp.eval, Str.append]
  | eq hc =>
    simp only [encodeBin] at h
    refine (rel_bool _ _).2 ?_
    simp only [BinOp.eval, toBool_ofBool]
    exact eqCode_rel hx hy h
  | ne hc =>
    simp only [encodeBin] at h
    obtain ⟨e, h1, h⟩ := bind_ok.1 h
    cases h
    refine (rel_bool _ _).2 ?_
    simp only [Term.denote, BinOp.eval, toBool_ofBool, eqCode_rel hx hy h1, Val.toBool]

/-! `bag.min_by` and `bag.max_by`. `pick` finds the winning key by a fold in list order; the encoding asks each slot
whether it beats all others. `pick_eq` shows the two agree, and that no order is involved. -/

theorem two_le_length {β : Type} {l : List β} {a b : β} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) : 2 ≤ l.length := by
  match l with
  | [] => simp at ha
  | [c] => simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | _ :: _ :: _ => simp

section Pick
variable {α : Type} (wins : Int → Int → Bool) (key : α → Int)

/-- Whether `y` beats every other item of `l`: it is the only item that does not lose to it. -/
def winsAll (l : List α) (y : α) : Bool := (l.filter fun z => !wins (key y) (key z)).length == 1

variable (hirr : ∀ a, wins a a = false) (htrans : ∀ a b c, wins a b = true → wins b c = true → wins a c = true)
include hirr htrans

omit htrans in
include htrans in
/-- The fold's key is one of the keys, and no key beats it. -/
theorem pick_best (htot : ∀ a b, a ≠ b → wins a b = true ∨ wins b a = true) : (rest : List α) → (m : Int) →
    let r := rest.foldl (fun m y => if wins (key y) m then key y else m) m
    (r = m ∨ ∃ z ∈ rest, key z = r) ∧ wins m r = false ∧ ∀ z ∈ rest, wins (key z) r = false
  | [], m => ⟨.inl rfl, hirr m, by simp⟩
  | y :: rest, m => by
    obtain ⟨h1, h2, h3⟩ := pick_best htot rest (if wins (key y) m then key y else m)
    simp only [List.foldl_cons]
    generalize List.foldl _ _ rest = r at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with h | ⟨z, hz, e⟩
      · by_cases hw : wins (key y) m = true
        · simp only [hw, ite_true] at h; exact .inr ⟨y, by simp, h.symm⟩
        · simp only [hw, Bool.false_eq_true, ite_false] at h; exact .inl h
      · exact .inr ⟨z, by simp [hz], e⟩
    · by_cases hw : wins (key y) m = true
      · simp only [hw, ite_true] at h2
        cases e : wins m r
        · rfl
        · exact absurd (htrans _ _ _ hw e) (by simp [h2])
      · simp only [hw, Bool.false_eq_true, ite_false] at h2; exact h2
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · by_cases hw : wins (key z) m = true
        · simp only [hw, ite_true] at h2; exact h2
        · simp only [hw, Bool.false_eq_true, ite_false] at h2
          cases e : wins (key z) r
          · rfl
          · exfalso
            by_cases hrm : r = m
            · rw [hrm] at e; exact hw e
            · rcases htot r m hrm with h | h
              · exact hw (htrans _ _ _ e h)
              · rw [h2] at h; cases h
      · exact h3 z hz

/-- `pick` is the first item that beats all others, an error saying whether the bag had items when none does. -/
theorem pick_eq (htot : ∀ a b, a ≠ b → wins a b = true ∨ wins b a = true) (l : List α) :
    Builtin.pick wins key l = match l.find? (winsAll wins key l) with
      | some w => .ok w
      | none => .error (!l.isEmpty) := by
  match l with
  | [] => rfl
  | x :: rest =>
    obtain ⟨h1, h2, h3⟩ := pick_best wins key hirr htrans htot rest (key x)
    generalize hb : rest.foldl (fun m y => if wins (key y) m then key y else m) (key x) = best at h1 h2 h3
    have B1 : ∃ z ∈ x :: rest, key z = best := by
      rcases h1 with h | ⟨z, hz, e⟩
      · exact ⟨x, by simp, h.symm⟩
      · exact ⟨z, by simp [hz], e⟩
    have B2 : ∀ z ∈ x :: rest, wins (key z) best = false := by
      intro z hz; rcases List.mem_cons.1 hz with rfl | hz
      · exact h2
      · exact h3 z hz
    let F := (x :: rest).filter (key · == best)
    have hA : ∀ y ∈ x :: rest, winsAll wins key (x :: rest) y = true → key y = best := by
      intro y hy hw
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨z, hz, ez⟩ := B1
      have : 2 ≤ ((x :: rest).filter fun z => !wins (key y) (key z)).length :=
        two_le_length (List.mem_filter.2 ⟨hy, by simp [hirr]⟩) (List.mem_filter.2 ⟨hz, by simp [ez, B2 y hy]⟩)
          (fun e => hne (e ▸ ez))
      simp only [winsAll, beq_iff_eq] at hw; omega
    have hB : ∀ y, key y = best → ((x :: rest).filter fun z => !wins (key y) (key z)) = F := by
      intro y ey
      refine List.filter_congr fun z hz => ?_
      rw [ey]
      by_cases e : key z = best
      · simp [e, hirr]
      · have := B2 z hz
        rcases htot best (key z) (Ne.symm e) with h | h
        · simp [h, e]
        · rw [this] at h; cases h
    have hW : ∀ y ∈ x :: rest, winsAll wins key (x :: rest) y = true ↔ key y = best ∧ F.length = 1 := by
      intro y hy
      constructor
      · intro hw
        have ey := hA y hy hw
        refine ⟨ey, ?_⟩
        simp only [winsAll, beq_iff_eq, hB y ey] at hw; exact hw
      · intro ⟨ey, hl⟩
        simp only [winsAll, beq_iff_eq, hB y ey]; exact hl
    simp only [Builtin.pick]
    rw [hb]
    split
    · rename_i w hF
      have hw : w ∈ F := by show w ∈ List.filter _ _; rw [hF]; simp
      obtain ⟨hwl, ew⟩ := List.mem_filter.1 hw
      simp only [beq_iff_eq] at ew
      cases hf : (x :: rest).find? (winsAll wins key (x :: rest)) with
      | none =>
        exact absurd ((hW w hwl).2 ⟨ew, by simp [F, hF]⟩) (by simp [List.find?_eq_none.1 hf w hwl])
      | some y =>
        have hyl := List.mem_of_find?_eq_some hf
        have ey := ((hW y hyl).1 (List.find?_some hf)).1
        have : y ∈ List.filter (key · == best) (x :: rest) := List.mem_filter.2 ⟨hyl, by simp [ey]⟩
        rw [hF] at this
        simp at this; subst this; rfl
    · rename_i hF
      have hl : F.length ≠ 1 := by
        intro h1
        match hF' : F, h1 with
        | [w], _ => exact hF w hF'
      have hf : (x :: rest).find? (winsAll wins key (x :: rest)) = none :=
        List.find?_eq_none.2 fun y hy hw => hl ((hW y hy).1 hw).2
      rw [hf]; rfl

/-- No two items of a list both beat all others. -/
theorem winners_unique (l : List α) : l.Pairwise fun a b => ¬(winsAll wins key l a = true ∧ winsAll wins key l b = true) := by
  refine List.pairwise_iff_forall_sublist.2 fun {a b} hs ⟨ha, hb⟩ => ?_
  have beat : ∀ u v, [u, v].Sublist l → winsAll wins key l u = true → wins (key u) (key v) = true := by
    intro u v huv hu
    cases e : wins (key u) (key v)
    · have := (huv.filter fun z => !wins (key u) (key z)).length_le
      simp only [List.filter_cons, hirr, e, Bool.not_false, ite_true, List.filter_nil, List.length_cons,
        List.length_nil] at this
      simp only [winsAll, beq_iff_eq] at hu; omega
    · rfl
  have hab := beat a b hs ha
  have hba : wins (key b) (key a) = true := by
    cases e : wins (key b) (key a)
    · have := (hs.filter fun z => !wins (key b) (key z)).length_le
      simp only [List.filter_cons, hirr, e, Bool.not_false, ite_true, List.filter_nil, List.length_cons,
        List.length_nil] at this
      simp only [winsAll, beq_iff_eq] at hb; omega
    · rfl
  have := htrans _ _ _ hab hba
  rw [hirr] at this; cases this

end Pick

/-- `bag.min_by` and `bag.max_by` on slots: the winning slot's item, or `Tie` or `Empty`, as `pick` gives. -/
theorem pickCode_rel (lt : Term → Term → Term) (wins : Int → Int → Bool)
    (hlt : ∀ (ta tb : Term) (a b : Int), ta.denote M = .int a → tb.denote M = .int b →
      (lt ta tb).denote M = .bool (wins a b))
    (hirr : ∀ a, wins a a = false) (htrans : ∀ a b c, wins a b = true → wins b c = true → wins a c = true)
    (htot : ∀ a b, a ≠ b → wins a b = true ∨ wins b a = true)
    {a : Ty} {xs : (Ty.bag a).den} {b : Term} (hb : Rel M L (.bag a) xs b) {f : (Ty.fn [a] .int).den}
    {sf : Code (.fn [a] .int)} (hf : Rel M L _ f sf) {r c : Term} (h : pickCode L lt a b sf = .ok (r, c))
    (hc : Holds M c) :
    RelV L (Ty.result a Ty.pickError) (Ty.ofPick (Builtin.pick wins (fun x => f (x, ())) xs)) (r.denote M) := by
  simp only [pickCode] at h
  obtain ⟨⟨d, n, dt⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨R, h2, h⟩ := bind_ok.1 h
  obtain ⟨dv, h3, h⟩ := bind_ok.1 h
  obtain ⟨foundT, h4, h⟩ := bind_ok.1 h
  obtain ⟨tieI, h5, h⟩ := bind_ok.1 h
  obtain ⟨tieT, h6, h⟩ := bind_ok.1 h
  obtain ⟨emI, h7, h⟩ := bind_ok.1 h
  obtain ⟨emT, h8, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  dsimp only at h4 ⊢
  let key : a.den → Int := fun x => f (x, ())
  obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
  have hk : AlignedV M (EBag L a) (fun y v => v = .int (key y)) _ _ sv ys :=
    slotTerms_aligned (r := .int) hf (fun y => (y, ())) eBag_rels hS hh h2 hc
  have hks : AlignedV M (EBag L a) (fun y v => v = .int (key y)) (slotsOf d dt n 1 b) (R.map fun r => Term.share r.1)
      sv ys := by
    have := alignedV_mapq (V' := fun y v => v = .int (key y)) Term.share
      (fun y q hq => by rw [Term.denote_share]; exact hq) hk
    rwa [List.map_map] at this
  generalize slotsOf d dt n 1 b = S at hS hks h4 ⊢
  generalize R.map (fun r => Term.share r.1) = ks at hks h4 ⊢
  have hws : Aligned M (EBag L a) (winsAll wins key ys) S
      (ks.map fun k => Term.share (.eq (countT S (ks.map fun k' => .not (lt k k'))) (.int 1))) sv ys := by
    refine alignedV_mapq _ (fun y k hy => ?_) hks
    have hin : Aligned M (EBag L a) (fun z => !wins (key y) (key z)) S (ks.map fun k' => .not (lt k k')) sv ys :=
      alignedV_mapq _ (fun z k' hz => by
        show Val.bool (!(Term.denote M (lt k k')).toBool) = _
        rw [hlt k k' _ _ hy hz]; rfl) hks
    simp only [Term.denote_share, Term.denote, countT_den hin]
    show Val.bool (Val.beq _ _) = _
    simp only [Val.beq, winsAll]
    congr 1
    cases e : (List.filter (fun z => !wins (key y) (key z)) ys).length == 1 <;> simp_all; omega
  have hany := anySlotT_den hws
  have hne : (anySlotT S (S.map fun _ => tt)).denote M = .bool (ys.any fun _ => true) :=
    anySlotT_den (aligned_map (V := fun _ v => v = .bool true) (fun _ => tt) (fun _ _ _ => rfl) hS hh)
  have hW : winsAll wins key xs = winsAll wins key ys := funext fun y => by
    simp only [winsAll, (hperm.filter _).length_eq]
  have hfind : xs.find? (winsAll wins key ys) = ys.find? (winsAll wins key ys) := by
    refine find_perm hperm.symm ?_
    have := winners_unique wins key hirr htrans xs
    rwa [hW] at this
  show RelV L _ (Ty.ofPick (Builtin.pick wins key xs)) _
  rw [pick_eq wins key hirr htrans htot xs, hW, hfind]
  simp only [Term.denote, hany, Val.toBool]
  cases hy : ys.find? (winsAll wins key ys) with
  | some y =>
    have : ys.any (winsAll wins key ys) = true := List.any_eq_true.2 ⟨y, List.mem_of_find?_eq_some hy, List.find?_some hy⟩
    simp only [this, ite_true]
    have hitem := pick_aligned (fun xs => xs[0]) (fun y v => RelV L a y v) (fun y xs he => by
      obtain ⟨z, hz, hyz⟩ := he
      obtain ⟨t, rfl⟩ := xs.one
      simp only [Term.denotes, List.cons.injEq] at hz; simpa [hz.1] using hyz) dv hws y hy
    exact adtCtor_rel (vs := [[a], [Ty.pickError]]) ⟨0, by simp⟩ _ foundT h4 (y, ()) ⟨_, _, rfl, hitem, rfl⟩
  | none =>
    have : ys.any (winsAll wins key ys) = false := by
      cases e : ys.any (winsAll wins key ys)
      · rfl
      · obtain ⟨y, hy', hw⟩ := List.any_eq_true.1 e
        exact absurd hw (by simp [List.find?_eq_none.1 hy y hy'])
    simp only [this, Bool.false_eq_true, ite_false, hne]
    have hemp : xs.isEmpty = ys.isEmpty := by
      have := hperm.length_eq
      cases xs <;> cases ys <;> simp_all
    rw [hemp]
    cases ys with
    | nil =>
      simp only [List.any_nil, Bool.false_eq_true, ite_false, List.isEmpty_nil]
      exact adtCtor_rel (vs := [[a], [Ty.pickError]]) ⟨1, by simp⟩ _ emT h8 (Alts.inj ⟨0, by simp⟩ (), ())
        ⟨_, _, rfl, adtCtor_rel (vs := [[], []]) ⟨0, by simp⟩ [] emI h7 () rfl, rfl⟩
    | cons y ys =>
      simp only [List.any_cons, Bool.true_or, ite_true, List.isEmpty_cons, Bool.not_false]
      exact adtCtor_rel (vs := [[a], [Ty.pickError]]) ⟨1, by simp⟩ _ tieT h6 (Alts.inj ⟨1, by simp⟩ (), ())
        ⟨_, _, rfl, adtCtor_rel (vs := [[], []]) ⟨1, by simp⟩ [] tieI h5 () rfl, rfl⟩

/-- Each built-in's code relates to its meaning. -/
theorem Ty.eq_of_same {a b : Ty} (h : (Ty.same a b).isSome = true) : a = b := by
  obtain ⟨⟨e⟩, _⟩ := Option.isSome_iff_exists.1 h; exact e

theorem Ty.eq_of_sames {a b : List Ty} (h : (Ty.sames a b).isSome = true) : a = b := by
  obtain ⟨⟨e⟩, _⟩ := Option.isSome_iff_exists.1 h; exact e

theorem SiteKey.eq_of_same {a b : SiteKey} (h : a.same b = true) : a = b := by
  obtain ⟨s, Γ⟩ := a; obtain ⟨s', Γ'⟩ := b
  simp only [SiteKey.same, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, Ty.eq_of_sames h.2]

theorem optSame_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    {a b : Option α} → optSame f a b = true → a = b
  | none, none, _ => rfl
  | some _, some _, h => by rw [hf _ _ h]
  | none, some _, h | some _, none, h => by simp [optSame] at h

theorem EffectKey.eq_of_same {a b : EffectKey} (h : a.same b = true) : a = b := by
  obtain ⟨e, n, i, o, j, en, an⟩ := a; obtain ⟨e', n', i', o', j', en', an'⟩ := b
  simp only [EffectKey.same, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨he, hn⟩, hi⟩, ho⟩, hj⟩, hen⟩, han⟩ := h
  rw [Ty.eq_of_same he, hn, Ty.eq_of_same hi, Ty.eq_of_same ho, optSame_eq (fun _ _ => Ty.eq_of_same) hj,
    optSame_eq (fun _ _ => SiteKey.eq_of_same) hen, SiteKey.eq_of_same han]

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- An effect's code is its kind's variant, with the input and the captured values' tuples as its fields. -/
theorem effectT_ok {key : EffectKey} {it : Term} {ens ans : List Term} {t : Term}
    (h : effectT L key it ens ans = .ok t) :
    ∃ d n k de da, L.find? (.dsl .effect [key.event]) = some (d, n) ∧ (L.effectsOf key.event)[k]? = some key ∧
      (∃ m, L.find? (.tuple ((key.ensures.map (·.Γ)).getD [])) = some (de, m)) ∧
      (∃ m, L.find? (.tuple key.answer.Γ) = some (da, m)) ∧ t = .ctor d k [it, .ctor de 0 ens, .ctor da 0 ans] := by
  simp only [effectT] at h
  obtain ⟨⟨d, n⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨k, h2, h⟩ := bind_ok.1 h
  obtain ⟨de, h3, h⟩ := bind_ok.1 h
  obtain ⟨da, h4, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  obtain ⟨hk, hsame, -⟩ := List.findIdx?_eq_some_iff_getElem.1 (need_ok.1 h2)
  refine ⟨d, n, k, de, da, need_ok.1 h1, ?_, tupleD_ok h3, tupleD_ok h4, rfl⟩
  rw [List.getElem?_eq_getElem hk, EffectKey.eq_of_same hsame]

theorem OwnKey.eq_of_same : {a b : OwnKey} → a.same b = true → a = b
  | .command .., .command .., h | .query .., .query .., h => by
    simp only [OwnKey.same, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨he, hn⟩, hc⟩, hi⟩, hj⟩, ha⟩ := h
    rw [Ty.eq_of_same he, hn, Ty.eq_of_same hc, Ty.eq_of_same hi, Ty.eq_of_same hj, SiteKey.eq_of_same ha]
  | .command .., .query .., h | .query .., .command .., h => by simp [OwnKey.same] at h

/-- An own effect's code is its kind's variant after the request kinds', with the caller, the input and the captured
values' tuple as its fields. -/
theorem ownT_ok {key : OwnKey} {ct it : Term} {ans : List Term} {t : Term} (h : ownT L key ct it ans = .ok t) :
    ∃ d n k da, L.find? (.dsl .effect [key.event]) = some (d, n) ∧ (L.ownsOf key.event)[k]? = some key ∧
      (∃ m, L.find? (.tuple key.answer.Γ) = some (da, m)) ∧
      t = .ctor d ((L.effectsOf key.event).length + k) [ct, it, .ctor da 0 ans] := by
  simp only [ownT] at h
  obtain ⟨⟨d, n⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨k, h2, h⟩ := bind_ok.1 h
  obtain ⟨da, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  obtain ⟨hk, hsame, -⟩ := List.findIdx?_eq_some_iff_getElem.1 (need_ok.1 h2)
  refine ⟨d, n, k, da, need_ok.1 h1, ?_, tupleD_ok h3, rfl⟩
  rw [List.getElem?_eq_getElem hk, OwnKey.eq_of_same hsame]

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
  case tableGet =>
    simp only [primCode] at h; cases h
    intro ⟨tb, key, ()⟩ ⟨st, sk, ()⟩ ⟨ht, hk, _⟩ r c hr _
    obtain ⟨kt, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨hit, found⟩, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨tsome, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨tnone, h4, hr⟩ := map_ok.1 hr
    cases hr
    obtain ⟨hhit, hval⟩ := lookup_rel ht key kt ((rel_term (need_ok.1 h1) _).1 hk) h2
    change RelV L (.adt 3 [_] [[_], []]) (match lookupBy (Ty.deq _) key tb.1 with
      | some v => Ty.some v
      | none => Ty.none) ((Term.ite hit tsome tnone).denote M)
    cases hl : lookupBy (Ty.deq _) key tb.1 with
    | none =>
      simp only [hl, Option.isSome_none] at hhit
      simp only [Term.denote, hhit, Val.toBool, Bool.false_eq_true, ite_false]
      exact adtCtor_rel (M := M) (vs := [[_], []]) ⟨1, by simp⟩ [] tnone h4 () rfl
    | some val =>
      simp only [hl, Option.isSome_some] at hhit
      simp only [Term.denote, hhit, Val.toBool, ite_true]
      exact adtCtor_rel (M := M) (vs := [[_], []]) ⟨0, by simp⟩ [found] tsome h3 (val, ())
        ⟨_, _, rfl, hval val hl, rfl⟩
  case tableLookup =>
    simp only [primCode] at h; cases h
    intro ⟨tb, key, rej, next, ()⟩ ⟨st, sk, srej, snext, ()⟩ ⟨ht, hk, hrej, hnext, _⟩ r c hr hc
    obtain ⟨kt, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨hit, found⟩, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨fc, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨v, c1⟩, h4, hr⟩ := bind_ok.1 hr
    obtain ⟨rt, h5, hr⟩ := bind_ok.1 hr
    obtain ⟨err, h6, hr⟩ := map_ok.1 hr
    cases hr
    obtain ⟨hhit, hval⟩ := lookup_rel ht key kt ((rel_term (need_ok.1 h1) _).1 hk) h2
    change RelV L (.adt 2 [_, _] [[_], [_]]) (match lookupBy (Ty.deq _) key tb.1 with
      | some v => next (v, ())
      | none => Ty.error rej) ((Term.ite hit v err).denote M)
    cases hl : lookupBy (Ty.deq _) key tb.1 with
    | none =>
      simp only [hl, Option.isSome_none] at hhit
      simp only [Term.denote, hhit, Val.toBool, Bool.false_eq_true, ite_false]
      exact adtCtor_rel (M := M) (vs := [[_], [_]]) ⟨1, by simp⟩ [rt] err h6 (rej, ())
        ⟨_, _, rfl, (rel_term (need_ok.1 h5) _).1 hrej, rfl⟩
    | some val =>
      simp only [hl, Option.isSome_some] at hhit
      simp only [Holds, Term.denote, hhit, Val.toBool, ite_true] at hc ⊢
      exact hnext (val, ()) (fc, ()) ⟨(rel_ofTerm (need_ok.1 h3) _).2 (hval val hl), trivial⟩ v c1 h4 hc
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
  case bagSum =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have ha : AlignedV M (EBag L _) (fun y v => v = .int (f (y, ()))) _ _ sv ys :=
      slotTerms_aligned (r := .int) hf (fun y => (y, ())) eBag_rels hS hh h2 hc
    show RelV L .int _ _
    simp only [RelV, sumSlotT_den ha, Prim.den, Builtin.sumBy, foldl_add, Int.zero_add]
    exact congrArg Val.int (sum_perm (hperm.map (fun y => f (y, ()))))
  case bagMap =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨r', c'⟩, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨hg, hc'⟩ := (holds_andT _ _).1 hc
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := bag_view hb h1
    have ha := slotTerms_aligned hf (fun y => (y, ())) eBag_rels hS hh h2 hg
    obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := EBag L _) (fun y => f (y, ())) (fun _ q => ⟨[q], rfl⟩)
      (fun _ _ _ _ hq => ⟨_, rfl, hq⟩) ha
    obtain ⟨d', n', dt', S', sv', ys', h4, rfl, hS', hl', hw', hp', hh'⟩ := collOf_rel h3 hS1 hw1 hh1 hc'
    exact bag_mk h4 hS' hl' hw' (hp'.trans (hperm.map _)) hh'
  case tableMap =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨R, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨r', c'⟩, h3, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨hg, hc'⟩ := (holds_andT _ _).1 hc
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha := slotTerms_aligned hf (fun e => (e.1, e.2, ())) eTab_rels hS hh h2 hg
    obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := ETab L _ _) (fun e => (e.1, f (e.1, e.2, ())))
      (fun xs q => (⟨[xs[0], q], rfl⟩ : SlotItems 2)) (fun e xs q he hq => by
        obtain ⟨zk, zv, hxs, hzk, -⟩ := he
        obtain ⟨tk, tv, rfl⟩ := xs.two
        simp only [Term.denotes, List.cons.injEq] at hxs
        exact ⟨zk, _, by simp [Term.denotes, hxs.1], hzk, hq⟩) ha
    obtain ⟨d', n', dt', S', sv', ys', h4, rfl, hS', hl', hw', hp', hh'⟩ := collOf_rel h3 hS1 hw1 hh1 hc'
    exact table_mk h4 hS' hl' hw' (hp'.trans (hperm.map _)) hh'
  case tableKeys =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨b, ()⟩ ⟨hb, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha : AlignedV M (ETab L _ _) (fun _ _ => True) _ _ sv ys := aligned_map (fun _ => tt) (fun _ _ _ => trivial) hS hh
    obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := EBag L _) (fun e => e.1) (fun xs _ => ⟨[xs[0]], rfl⟩)
      (fun e xs q he _ => by
        obtain ⟨zk, zv, hxs, hzk, -⟩ := he
        obtain ⟨tk, tv, rfl⟩ := xs.two
        simp only [Term.denotes, List.cons.injEq] at hxs
        exact ⟨zk, by simp [Term.denotes, hxs.1], hzk⟩) ha
    obtain ⟨d', n', dt', S', sv', ys', h4, rfl, hS', hl', hw', hp', hh'⟩ := collOf_rel hr hS1 hw1 hh1 hc
    exact bag_mk h4 hS' hl' hw' (hp'.trans (hperm.map _)) hh'
  case tableValues =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨b, ()⟩ ⟨hb, _⟩ r c hr hc
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view hb h1
    have ha : AlignedV M (ETab L _ _) (fun _ _ => True) _ _ sv ys := aligned_map (fun _ => tt) (fun _ _ _ => trivial) hS hh
    obtain ⟨sv1, hS1, -, hw1, hh1⟩ := mapSlots_den (E' := EBag L _) (fun e => e.2) (fun xs _ => ⟨[xs[1]], rfl⟩)
      (fun e xs q he _ => by
        obtain ⟨zk, zv, hxs, -, hzv⟩ := he
        obtain ⟨tk, tv, rfl⟩ := xs.two
        simp only [Term.denotes, List.cons.injEq] at hxs
        exact ⟨zv, by simp [Term.denotes, hxs.2.1], hzv⟩) ha
    obtain ⟨d', n', dt', S', sv', ys', h4, rfl, hS', hl', hw', hp', hh'⟩ := collOf_rel hr hS1 hw1 hh1 hc
    exact bag_mk h4 hS' hl' hw' (hp'.trans (hperm.map _)) hh'
  case bagMinBy =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    exact pickCode_rel (fun k k' => .lt k k') (fun a b => decide (a < b))
      (fun ta tb a b ha hb => by simp [Term.denote, ha, hb, Val.toInt])
      (fun a => by simp) (fun a b c => by simp; omega) (fun a b h => by simp; omega) hb hf hr hc
  case bagMaxBy =>
    simp only [primCode] at h; cases h
    intro ⟨xs, f, ()⟩ ⟨b, sf, ()⟩ ⟨hb, hf, _⟩ r c hr hc
    exact pickCode_rel (fun k k' => .lt k' k) (fun a b => decide (a > b))
      (fun ta tb a b ha hb => by simp [Term.denote, ha, hb, Val.toInt])
      (fun a => by simp) (fun a b c => by simp; omega) (fun a b h => by simp; omega) hb hf hr hc
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
      insert_rel hS hw hh ⟨[xt], rfl⟩ x ⟨_, by simp [Term.denotes], hxt⟩ rfl hc
    exact bag_mk h1 hS' (hl'.trans hl) hw' (hperm'.trans (hperm.cons x)) hh'
  case tableNew =>
    simp only [primCode] at h; cases h
    intro ⟨⟩ ⟨⟩ _ r c hr _
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨S, h2, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    simp only [emptySlots] at h2
    obtain ⟨xs, -, h2⟩ := bind_ok.1 h2
    cases pure_ok.1 h2
    refine table_mk h1 (empty_den xs n) (by simp) (fun p hp => ?_) (ys := []) (List.Perm.refl _)
      (by simp [Holds2, occupied_empty, Forall2])
    simp only [List.mem_replicate] at hp
    rw [hp.2, denotes_eq_map, List.length_map, xs.2]; rfl
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
    change Rel M L (.list ((Ty.param 0).inst args)) xs items at hxs
    obtain ⟨⟨dl, nl, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨sv, hS, -, hw, hh⟩ := list_view hxs h1
    obtain ⟨d, n, dt', S', sv', ys', h2, rfl, hS', hl', hw', hperm', hh'⟩ := collOf_rel hr hS hw hh hc
    exact bag_mk h2 hS' hl' hw' hperm' hh'
  case tableFromList =>
    simp only [primCode] at h; cases h
    intro ⟨pairs, ()⟩ ⟨ps, ()⟩ ⟨hps, _⟩ r c hr hc
    change Rel M L (.list (.tuple [(Ty.param 0).inst args, (Ty.param 1).inst args])) pairs ps at hps
    obtain ⟨⟨d, n, dt⟩, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨⟨dl, nl, dtl⟩, h1', hr⟩ := bind_ok.1 hr
    obtain ⟨dp0, h2, hr⟩ := bind_ok.1 hr
    obtain ⟨dp, h3, hr⟩ := bind_ok.1 hr
    obtain ⟨S0, h4, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    obtain ⟨heq, rfl⟩ := need'_ok h3
    obtain ⟨m, hdp⟩ := tupleD_ok h2
    simp only [emptySlots] at h4
    obtain ⟨dx, -, h4⟩ := bind_ok.1 h4
    cases pure_ok.1 h4
    obtain ⟨lv, hP, -, -, hlh⟩ := list_view hps h1'
    obtain ⟨sv', ys', hS', hl', hw', hperm', hh'⟩ := putFrom_rel heq d dt dp ⟨m, hdp⟩ hP hlh
      (t0 := Builtin.tableEmpty) (empty_den dx n)
      (fun p hp => by simp only [List.mem_replicate] at hp; rw [hp.2, denotes_eq_map, List.length_map, dx.2]; rfl)
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
    have ha : Aligned M (EBag L _) (fun y => Ty.deq _ x y) _ _ sv ys := aligned_map (fun xs => .eq xt xs[0]) (fun y xs he => by
      obtain ⟨z, hz, hyz⟩ := he
      obtain ⟨t, rfl⟩ := xs.one
      simp only [Term.denotes, List.cons.injEq] at hz
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, hz.1]
      exact congrArg Val.bool (relV_beq _ heq x y _ _ hxt hyz)) hS hh
    refine (rel_bool _ _).2 ?_
    rw [anySlotT_den ha, hperm.any_eq]
    simp only [Prim.den, toBool_ofBool]
    rfl
  case fresh =>
    simp only [primCode] at h; cases h
    intro ⟨step, index, ()⟩ ⟨ss, si, ()⟩ ⟨hs, hi, _⟩ r c hr _
    obtain ⟨⟨d, n⟩, h1, hr⟩ := bind_ok.1 hr
    cases pure_ok.1 hr
    change RelV L (.dsl .fresh []) step (ss.denote M) at hs
    change RelV L .int index (si.denote M) at hi
    simp only [RelV] at hs hi
    refine ⟨d, n, need_ok.1 h1, ?_⟩
    show Val.ctor d 0 (Term.denotes M [ss, si]) = idVal d (.fresh step index)
    simp only [Term.denotes, hs, hi, idVal]
    rfl
  case externalCommand =>
    simp only [primCode] at h; cases h
    intro ⟨x, ()⟩ ⟨sx, ()⟩ ⟨hx, _⟩ r c hr _
    change RelV L .str x (Term.denote M sx) at hx
    dsimp only at hr
    split at hr
    · cases hr
      simp only [RelV, Term.denote] at hx
      exact (Val.str.inj hx).symm
    · cases hr
  case requestCommand =>
    simp only [primCode] at h; cases h
    intro ⟨nm, x, f, ()⟩ ⟨sn, sx, cf, ()⟩ ⟨hn, hx, hf, _⟩ r c hr _
    change nm = sn at hn
    change ClosureRel M L f cf at hf
    dsimp only at hr
    obtain ⟨it, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨t, h2, e⟩ := map_ok.1 hr
    cases e
    obtain ⟨d, n, k, de, da, hd, hk, ⟨m, hde⟩, ⟨m', hda⟩, rfl⟩ := effectT_ok h2
    have hd0 := Prim.dataOf hp rfl
    have hi := (rel_term (need_ok.1 h1) x).1 hx
    refine ⟨d, n, hd, .inl ⟨k, _, _, hk, rfl, hn, rfl, rfl, rfl, hf.1, hf.2.1, _, _, _, rfl, ?_, ?_, ?_⟩⟩
    · have hdi := Ty.isData_inst hd0 (.param 1) rfl
      exact relV_up _ hdi (Ty.down _ hdi x) _ (by rw [Ty.up_down]; exact hi)
    · exact ⟨da, m', _, hf.2.1 ▸ hda, rfl, hf.2.2⟩
    · exact ⟨de, m, hde, rfl⟩
  case requestQuery =>
    simp only [primCode] at h; cases h
    intro ⟨⟨nm, g⟩, x, f, ()⟩ ⟨⟨sn, cg⟩, sx, cf, ()⟩ ⟨⟨hn, hg⟩, hx, hf, _⟩ r c hr _
    change ClosureRel M L f cf at hf
    dsimp only at hr
    obtain ⟨it, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨t, h2, e⟩ := map_ok.1 hr
    cases e
    obtain ⟨d, n, k, de, da, hd, hk, ⟨m, hde⟩, ⟨m', hda⟩, rfl⟩ := effectT_ok h2
    have hd0 := Prim.dataOf hp rfl
    have hi := (rel_term (need_ok.1 h1) x).1 hx
    refine ⟨d, n, hd, .inl ⟨k, _, _, hk, rfl, hn, rfl, rfl, rfl, hf.1, hf.2.1, _, _, _, rfl, ?_, ?_, ?_⟩⟩
    · have hdi := Ty.isData_inst hd0 (.param 1) rfl
      exact relV_up _ hdi (Ty.down _ hdi x) _ (by rw [Ty.up_down]; exact hi)
    · exact ⟨da, m', _, hf.2.1 ▸ hda, rfl, hf.2.2⟩
    · exact ⟨hg.1, hg.2.1, de, m, _, hg.2.1 ▸ hde, rfl, hg.2.2⟩
  case externalQuery =>
    simp only [primCode] at h; cases h
    intro ⟨x, f, ()⟩ ⟨sx, cf, ()⟩ ⟨hx, hf, _⟩ r c hr _
    change RelV L .str x (Term.denote M sx) at hx
    dsimp only at hr
    split at hr
    · cases hr
      simp only [RelV, Term.denote] at hx
      exact ⟨(Val.str.inj hx).symm, hf⟩
    · cases hr
  case command =>
    simp only [primCode] at h; cases h
    intro ⟨x, _, _, _, _, ()⟩ ⟨sx, _, _, _, _, ()⟩ ⟨hx, _⟩ r c hr _
    change RelV L .str x (Term.denote M sx) at hx
    dsimp only at hr
    split at hr
    · cases hr
      simp only [RelV, Term.denote] at hx
      exact (Val.str.inj hx).symm
    · cases hr
  case query =>
    simp only [primCode] at h; cases h
    intro ⟨x, _, _, _, ()⟩ ⟨sx, _, _, _, ()⟩ ⟨hx, _⟩ r c hr _
    change RelV L .str x (Term.denote M sx) at hx
    dsimp only at hr
    split at hr
    · cases hr
      simp only [RelV, Term.denote] at hx
      exact (Val.str.inj hx).symm
    · cases hr
  case sendCommand =>
    simp only [primCode] at h; cases h
    intro ⟨cmd, cl, x, f, ()⟩ ⟨sn, scl, sx, cf, ()⟩ ⟨hn, hcl, hx, hf, _⟩ r c hr _
    change cmd.1.name = sn at hn
    change ClosureRel M L f cf at hf
    dsimp only at hr
    obtain ⟨ct, h0, hr⟩ := bind_ok.1 hr
    obtain ⟨it, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨t, h2, e⟩ := map_ok.1 hr
    cases e
    obtain ⟨d, n, k, da, hd, hk, ⟨m', hda⟩, rfl⟩ := ownT_ok h2
    have hd0 := Prim.dataOf hp rfl
    have hc := (rel_term (need_ok.1 h0) cl).1 hcl
    have hi := (rel_term (need_ok.1 h1) x).1 hx
    refine ⟨d, n, hd, .inr ⟨k, _, _, hk, rfl, hn, rfl, rfl, rfl, hf.1, hf.2.1, _, _, _, rfl, ?_, ?_, ?_⟩⟩
    · have hdc := Ty.isData_inst hd0 (.param 2) rfl
      exact relV_up _ hdc (Ty.down _ hdc cl) _ (by rw [Ty.up_down]; exact hc)
    · have hdi := Ty.isData_inst hd0 (.param 3) rfl
      exact relV_up _ hdi (Ty.down _ hdi x) _ (by rw [Ty.up_down]; exact hi)
    · exact ⟨da, m', _, hf.2.1 ▸ hda, rfl, hf.2.2⟩
  case sendQuery =>
    simp only [primCode] at h; cases h
    intro ⟨qry, cl, x, f, ()⟩ ⟨sn, scl, sx, cf, ()⟩ ⟨hn, hcl, hx, hf, _⟩ r c hr _
    change qry.1.name = sn at hn
    change ClosureRel M L f cf at hf
    dsimp only at hr
    obtain ⟨ct, h0, hr⟩ := bind_ok.1 hr
    obtain ⟨it, h1, hr⟩ := bind_ok.1 hr
    obtain ⟨t, h2, e⟩ := map_ok.1 hr
    cases e
    obtain ⟨d, n, k, da, hd, hk, ⟨m', hda⟩, rfl⟩ := ownT_ok h2
    have hd0 := Prim.dataOf hp rfl
    have hc := (rel_term (need_ok.1 h0) cl).1 hcl
    have hi := (rel_term (need_ok.1 h1) x).1 hx
    refine ⟨d, n, hd, .inr ⟨k, _, _, hk, rfl, hn, rfl, rfl, rfl, hf.1, hf.2.1, _, _, _, rfl, ?_, ?_, ?_⟩⟩
    · have hdc := Ty.isData_inst hd0 (.param 2) rfl
      exact relV_up _ hdc (Ty.down _ hdc cl) _ (by rw [Ty.up_down]; exact hc)
    · have hdi := Ty.isData_inst hd0 (.param 3) rfl
      exact relV_up _ hdi (Ty.down _ hdi x) _ (by rw [Ty.up_down]; exact hi)
    · exact ⟨da, m', _, hf.2.1 ▸ hda, rfl, hf.2.2⟩
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
variable {M : Model} {L : Layout} {G : List Ty} (D : Defs G) (g : Ty.dens G) (gs : Encs G) (hg : GRel M L g gs)
include hg

set_option linter.unusedSectionVars false

mutual
/-- T1: wherever its condition holds, an expression's code denotes the value `eval` computes, in every model whose
variables denote the values of the expression's variables. -/
theorem encode_agrees {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    Rels M L Γ ρ σ → (s : Code t) → (c : Term) → encode L gs e σ = .ok (s, c) → Holds M c →
    Rel M L t (e.eval D g ρ) s
  | .int n, _, _, _, s, c, h, _ => by cases h; simp [Rel, RelV, Expr.eval, Term.denote]
  | .str lit, _, _, _, s, c, h, _ => by
    simp only [encode] at h; cases h; simp [Rel, RelV, Expr.eval, Term.denote]
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
        have hlt := (Alts.view (e.eval D g ρ)).1.isLt
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
        generalize e.eval D g ρ = y at hr
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
    exact encode_agrees f σ ρ hσ sf c1 h1 hc1 _ _ (rels_share (encodes_agrees args σ ρ hσ ss c2 h2 hc2)) _ c3 h3 hc3
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
    exact encode_agrees body _ (e.eval D g ρ, ρ) ⟨rel_share (encode_agrees e σ ρ hσ x c1 h1 hc1), hσ⟩ _ c2 h2 hc2
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
      exact encodeClauses_agrees cs σ ρ hσ _ _ (rel_share (encode_agrees e σ ρ hσ x c1 h1 hc1)) _ _ c2 h2 hc2
  | @Expr.list _ _ t items, σ, ρ, hσ, s, c, h, hc => by
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨ts, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨r, c2⟩, h3, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    obtain ⟨hc1, hc2⟩ := (holds_andT _ _).1 hc
    exact listOf_rel (items_terms (encodeItems_agrees items σ ρ hσ ss c1 h1 hc1) (mapM_ok _ ss ts h2)) h3 hc2
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
  | @Expr.close _ _ Γ' _ _ env hΓ _ _, σ, ρ, hσ, s, c, h, hc => by
    simp only [encode] at h
    obtain ⟨⟨ss, c1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨ts, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    have hv := rels_terms (need_ok.1 h2) _ (encodes_agrees env σ ρ hσ ss c1 h1 hc)
    exact ⟨rfl, rfl, relVs_up Γ' hΓ _ _ (by erw [Ty.up_down]; exact hv)⟩
  | .closeEffect .., _, _, _, _, _, h, _ => by simp only [encode] at h; cases h
theorem encodes_agrees {Γ : List Ty} {ts : List Ty} : (es : Exprs G Γ ts) → (σ : Codes Γ) → (ρ : Ty.dens Γ) →
    Rels M L Γ ρ σ → (ss : Codes ts) → (c : Term) → encodes L gs es σ = .ok (ss, c) → Holds M c →
    Rels M L ts (Exprs.eval D g es ρ) ss
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
    Forall2 (Rel M L t) (Items.eval D g items ρ) ss
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
    RelVs L ts (Patch.eval D g p ρ xs) (Term.denotes M ys)
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
    encodeClauses L gs cs σ s = .ok (some (v, c)) → Holds M c → Rel M L r (Clauses.eval D g cs ρ x hx) v
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
    | here => exact Smt.encode_agrees defs _ _ (Defs.encode_agrees M L defs) body () () trivial s c h hc
    | there v => exact Defs.encode_agrees M L defs t v s c h hc

section
variable {M : Model}

theorem holds_ite_tt {c a : Term} {b : Bool} (h : (c.denote M).toBool = b) : Holds M (.ite c a tt) ↔ (b = true → Holds M a) := by
  rw [holds_ite, h]; cases b <;> simp [holds_tt]

theorem holds_ite_hit {c a : Term} : Holds M (.ite c a tt) ↔ (Holds M c → Holds M a) := by
  rw [holds_ite]; unfold Holds; cases (c.denote M).toBool <;> simp; rfl

end

end Tazuna.Smt
