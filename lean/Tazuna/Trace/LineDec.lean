import Tazuna.Trace.LineTree
import Tazuna.Trace.WireThm
import Tazuna.Semantics.StepSame

/-! What a trace line's value means: the value `dec` reads from it. Verify compares out lines as trees (`valTree`,
`wireTree`), so that it can name ids lazily; a wire form's tree is a value's tree once a binding names the value's ids
exactly when decoding the wire form with the binding's names gives the value, up to the order of bags and tables
(`tree_dec`, `dec_tree`). -/

namespace Tazuna.Ir

theorem PBij.refl_inv : PBij.refl.inv = PBij.refl := by
  simp only [PBij.inv, PBij.refl, PBij.mk.injEq]
  funext a b; exact propext eq_comm

theorem Ty.same_symm {t : Ty} {x y : t.den0} (h : Ty.Same t x y) : Ty.Same t y x := by
  have := Ty.rel0_inv.1 h; rwa [PBij.refl_inv] at this

end Tazuna.Ir

namespace Tazuna.Trace

open Tazuna.Ir

section Lists
variable {α β γ δ : Type}

theorem mapM_perm {f : α → Option β} : {xs ys : List α} → xs.Perm ys → {bs : List β} → xs.mapM f = some bs →
    ∃ cs, ys.mapM f = some cs ∧ bs.Perm cs
  | _, _, .nil, bs, h => by simp at h; subst h; exact ⟨[], rfl, .nil⟩
  | _, _, .cons x hp, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    obtain ⟨cs, hcs, hp'⟩ := mapM_perm hp hbs
    exact ⟨b :: cs, by simp [List.mapM_cons, hb, hcs], hp'.cons b⟩
  | _, _, .swap x y l, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, _, ⟨c, hc, cs, hcs, rfl⟩, rfl⟩ := h
    exact ⟨c :: b :: cs, by simp [List.mapM_cons, hb, hc, hcs], .swap c b cs⟩
  | _, _, .trans h1 h2, bs, h => by
    obtain ⟨cs, hcs, hp1⟩ := mapM_perm h1 h
    obtain ⟨ds, hds, hp2⟩ := mapM_perm h2 hcs
    exact ⟨ds, hds, hp1.trans hp2⟩

theorem mapM_rel2 {r : α → γ → Prop} {S : β → δ → Prop} {f : α → Option β} {g : γ → Option δ}
    (h : ∀ a c, r a c → ∀ b, f a = some b → ∃ d, g c = some d ∧ S b d) :
    {xs : List α} → {ys : List γ} → Forall2 r xs ys → {bs : List β} → xs.mapM f = some bs →
      ∃ ds, ys.mapM g = some ds ∧ Forall2 S bs ds
  | [], [], _, bs, hb => by simp at hb; subst hb; exact ⟨[], rfl, trivial⟩
  | x :: xs, y :: ys, ⟨hxy, hr⟩, bs, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hb
    obtain ⟨b, hb1, bs', hbs, rfl⟩ := hb
    obtain ⟨d, hd, hs⟩ := h x y hxy b hb1
    obtain ⟨ds, hds, hs'⟩ := mapM_rel2 h hr hbs
    exact ⟨d :: ds, by simp [List.mapM_cons, hd, hds], hs, hs'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem mapM_multi {r : α → γ → Prop} {S : β → δ → Prop} {f : α → Option β} {g : γ → Option δ}
    (h : ∀ a c, r a c → ∀ b, f a = some b → ∃ d, g c = some d ∧ S b d) {xs : List α} {ys : List γ}
    (hm : Multi r xs ys) {bs : List β} (hb : xs.mapM f = some bs) : ∃ ds, ys.mapM g = some ds ∧ Multi S bs ds := by
  obtain ⟨zs, hz, hp⟩ := hm
  obtain ⟨ds, hds, hs⟩ := mapM_rel2 h hz hb
  obtain ⟨es, hes, hp'⟩ := mapM_perm hp hds
  exact ⟨es, hes, ds, hs, hp'⟩

/-- Items each written by `f` and read back two ways, by `g` from the item and by `k` from what `f` wrote. -/
theorem mapM_two {f : α → Option β} {g : α → Option γ} {k : β → Option δ} {S : γ → δ → Prop}
    (h : ∀ a b, f a = some b → ∃ c d, g a = some c ∧ k b = some d ∧ S c d) :
    (xs : List α) → (bs : List β) → xs.mapM f = some bs →
      ∃ cs ds, xs.mapM g = some cs ∧ bs.mapM k = some ds ∧ Forall2 S cs ds
  | [], bs, hb => by simp at hb; subst hb; exact ⟨[], [], rfl, rfl, trivial⟩
  | x :: xs, bs, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hb
    obtain ⟨b, hb1, bs', hbs, rfl⟩ := hb
    obtain ⟨c, d, hc, hd, hs⟩ := h x b hb1
    obtain ⟨cs, ds, hcs, hds, hs'⟩ := mapM_two h xs bs' hbs
    exact ⟨c :: cs, d :: ds, by simp [List.mapM_cons, hc, hcs], by simp [List.mapM_cons, hd, hds], hs, hs'⟩


theorem mapM_of_forall2 {α γ : Type} {f : α → Option γ} : {xs : List α} → {ys : List γ} →
    Forall2 (fun x y => f x = some y) xs ys → xs.mapM f = some ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp [List.mapM_cons, h, mapM_of_forall2 hs]
  | [], _ :: _, h | _ :: _, [], h => h.elim

/-- Items read two ways, `f` from one list and `g` from another, whose readings relate item by item, read a third way
`d` from the second list. -/
theorem mapM_back {f : α → Option γ} {g : β → Option δ} {ε : Type} {d : β → Option ε} {R : γ → δ → Prop}
    {S : α → ε → Prop} (h : ∀ x w a c, f x = some a → g w = some c → R a c → ∃ y, d w = some y ∧ S x y) :
    {xs : List α} → {ws : List β} → {as : List γ} → {cs : List δ} → xs.mapM f = some as → ws.mapM g = some cs →
    Forall2 R as cs → ∃ ys, ws.mapM d = some ys ∧ Forall2 S xs ys
  | [], [], _, _, _, _, _ => ⟨[], rfl, trivial⟩
  | x :: xs, w :: ws, as, cs, hx, hw, hr => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx hw
    obtain ⟨a, ha, as', has, rfl⟩ := hx
    obtain ⟨c, hc, cs', hcs, rfl⟩ := hw
    obtain ⟨y, hy, hs⟩ := h x w a c ha hc hr.1
    obtain ⟨ys, hys, hss⟩ := mapM_back h has hcs hr.2
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys], hs, hss⟩
  | [], _ :: _, as, cs, hx, hw, hr => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at hx; subst hx
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hw
    obtain ⟨c, -, cs', -, rfl⟩ := hw
    exact hr.elim
  | _ :: _, [], as, cs, hx, hw, hr => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at hw; subst hw
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx
    obtain ⟨a, -, as', -, rfl⟩ := hx
    exact hr.elim

theorem forall2_and_mem {R : α → β → Prop} {P : α → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs →
    (∀ a ∈ as, P a) → Forall2 (fun a b => R a b ∧ P a) as bs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩, hp => ⟨⟨h, hp _ List.mem_cons_self⟩, forall2_and_mem hs fun a ha => hp a (.tail _ ha)⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

theorem keysUnique_forall2 {κ κ' ν ν' : Type} {f : κ → κ → Bool} {g : κ' → κ' → Bool} {r : κ × ν → κ' × ν' → Prop}
    (hfg : ∀ a b a' b', r a a' → r b b' → f a.1 b.1 = g a'.1 b'.1) :
    {l : List (κ × ν)} → {l' : List (κ' × ν')} → Forall2 r l l' → KeysUnique f l → KeysUnique g l'
  | [], [], _, _ => List.Pairwise.nil
  | a :: l, a' :: l', ⟨h, hs⟩, hu => by
    unfold KeysUnique at hu ⊢
    rw [List.pairwise_cons] at hu ⊢
    refine ⟨fun b' hb' => ?_, keysUnique_forall2 hfg hs hu.2⟩
    obtain ⟨b, hb, hbb⟩ := forall2_mem_right hs b' hb'
    have := hu.1 b hb
    rw [← hfg a b a' b' h hbb, ← hfg b a b' a' hbb h]; exact this
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

end Lists

section Trees
variable (T : List TypeDecl)

theorem encBool_bool {vs : List (List Ty)} {x : (Ty.semAltsWith Dsl.base vs).1} {w : Wire}
    (h : encBool vs x = some w) : ∃ b, w = .bool b := by
  match vs, x with
  | [], x => exact nomatch x
  | [] :: _, .inl () => have h : some (Wire.bool true) = some w := h; cases h; exact ⟨_, rfl⟩
  | (_ :: _) :: _, .inl _ => have h : none = some w := h; cases h
  | f :: vs, .inr y =>
    match vs, y with
    | [], y => exact nomatch y
    | [] :: _, .inl () => cases f <;> (have h : some (Wire.bool false) = some w := h; cases h; exact ⟨_, rfl⟩)
    | (_ :: _) :: _, .inl _ => cases f <;> (have h : none = some w := h; cases h)
    | g :: _, .inr _ => cases f <;> cases g <;> (have h : none = some w := h; cases h)

theorem encNil_null {vs : List (List Ty)} {x : (Ty.semAltsWith Dsl.base vs).1} {w : Wire}
    (h : encNil vs x = some w) : w = .null := by
  match vs, x with
  | [], x => exact nomatch x
  | [] :: _, .inl () => have h : some Wire.null = some w := h; cases h; rfl
  | (_ :: _) :: _, .inl _ => have h : none = some w := h; cases h
  | f :: _, .inr _ => cases f <;> (have h : none = some w := h; cases h)

theorem encBool_rel {RD : (k : Dsl) → (a : List Ty) → (Dsl.base k a).1 → (Dsl.base k a).1 → Prop} {R : PBij}
    {vs : List (List Ty)} {x y : (Ty.semAltsWith Dsl.base vs).1} (h : Ty.relAltsWith Dsl.base RD R vs x y) :
    encBool vs x = encBool vs y := by
  match vs, x, y, h with
  | [], x, _, _ => exact nomatch x
  | [] :: _, .inl (), .inl (), _ => rfl
  | (_ :: _) :: _, .inl _, .inl _, _ => rfl
  | f :: vs, .inr x, .inr y, h =>
    match vs, x, y, h with
    | [], x, _, _ => exact nomatch x
    | [] :: _, .inl (), .inl (), _ => cases f <;> rfl
    | (_ :: _) :: _, .inl _, .inl _, _ => cases f <;> rfl
    | g :: _, .inr _, .inr _, _ => cases f <;> cases g <;> rfl
    | _ :: _, .inl _, .inr _, h | _ :: _, .inr _, .inl _, h => exact h.elim
  | _ :: _, .inl _, .inr _, h | _ :: _, .inr _, .inl _, h => exact h.elim

theorem encNil_rel {RD : (k : Dsl) → (a : List Ty) → (Dsl.base k a).1 → (Dsl.base k a).1 → Prop} {R : PBij}
    {vs : List (List Ty)} {x y : (Ty.semAltsWith Dsl.base vs).1} (h : Ty.relAltsWith Dsl.base RD R vs x y) :
    encNil vs x = encNil vs y := by
  match vs, x, y, h with
  | [], x, _, _ => exact nomatch x
  | [] :: _, .inl (), .inl (), _ => rfl
  | (_ :: _) :: _, .inl _, .inl _, _ => rfl
  | f :: _, .inr _, .inr _, _ => cases f <;> rfl
  | _ :: _, .inl _, .inr _, h | _ :: _, .inr _, .inl _, h => exact h.elim

theorem wireFields_length (kvs : List (String × Wire)) : (fs : List Ty) → (keys : List String) →
    (tls : List (Tree Name)) → wireFields T kvs fs keys = some tls → tls.length = keys.length
  | [], [], tls, h => by simp only [wireFields, Option.some.injEq] at h; subst h; rfl
  | f :: fs, key :: keys, tls, h => by
    simp only [wireFields, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, _, _, _, tls', h', rfl⟩ := h
    simp [wireFields_length kvs fs keys tls' h']
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [wireFields] at h

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- Values the same up to the order of their bags and tables have the same trees up to that order. -/
theorem valTree_same : (t : Ty) → (x y : t.den0) → Ty.Same t x y → (te : Tree Key) → valTree T t x = some te →
    ∃ te', valTree T t y = some te' ∧ Tree.Same te te'
  | .int, x, y, h, te, hx | .str, x, y, h, te, hx | .point _, x, y, h, te, hx => by
    have h : x = y := h; subst h; exact ⟨te, hx, rfl⟩
  | .id, x, y, h, te, hx => by
    have h : IdV.Rel PBij.refl x y := h
    rcases h with ⟨s, rfl, rfl⟩ | ⟨c, c', i, hc, rfl, rfl⟩
    · exact ⟨te, hx, rfl⟩
    · have hc : c = c' := hc
      subst hc; exact ⟨te, hx, rfl⟩
  | .list t, xs, ys, h, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    obtain ⟨tes', h1, h2⟩ := mapM_rel2 (S := Tree.Same) (fun a c hac b hb => valTree_same t a c hac b hb)
      (show Forall2 (Ty.Same t) xs ys from h) htes
    exact ⟨.seq tes', by simp [valTree, h1], Tree.same_seq.2 h2⟩
  | .bag t, xs, ys, h, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    obtain ⟨tes', h1, h2⟩ := mapM_multi (S := Tree.Same) (fun a c hac b hb => valTree_same t a c hac b hb)
      (show Multi (Ty.Same t) xs ys from h) htes
    exact ⟨.bag tes', by simp [valTree, h1], Tree.same_bag.2 h2⟩
  | .tuple ts, x, y, h, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    obtain ⟨tes', h1, h2⟩ := valTrees_same ts x y h tes htes
    exact ⟨.seq tes', by simp [valTree, h1], Tree.same_seq.2 h2⟩
  | .adt 0 _ vs, x, y, h, te, hx => by
    have e : valTree T (.adt 0 _ vs) x = (encBool vs x).bind litTree := rfl
    have e' : valTree T (.adt 0 _ vs) y = (encBool vs y).bind litTree := rfl
    rw [e] at hx
    rw [e', ← encBool_rel h]
    exact ⟨te, hx, rfl⟩
  | .adt 1 _ vs, x, y, h, te, hx => by
    have e : valTree T (.adt 1 _ vs) x = (encNil vs x).bind litTree := rfl
    have e' : valTree T (.adt 1 _ vs) y = (encNil vs y).bind litTree := rfl
    rw [e] at hx
    rw [e', ← encNil_rel h]
    exact ⟨te, hx, rfl⟩
  | .adt (i + 2) _ vs, x, y, h, te, hx => valAlts_same _ 0 vs x y h te hx
  | .table k v, x, y, h, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    obtain ⟨tes', h1, h2⟩ := mapM_multi (S := Tree.Same)
      (g := fun (e : k.den0 × v.den0) => do pure (Tree.seq [← valTree T k e.1, ← valTree T v e.2]))
      (fun a c ⟨hk, hv⟩ b hb => by
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
        obtain ⟨ta, ha, tb, hb', rfl⟩ := hb
        obtain ⟨ta', ha', hsa⟩ := valTree_same k a.1 c.1 hk ta ha
        obtain ⟨tb', hb'', hsb⟩ := valTree_same v a.2 c.2 hv tb hb'
        exact ⟨.seq [ta', tb'], by simp [ha', hb''], Tree.same_seq.2 ⟨hsa, hsb, trivial⟩⟩)
      (show Multi (fun e e' => Ty.Same k e.1 e'.1 ∧ Ty.Same v e.2 e'.2) x.1 y.1 from h) htes
    exact ⟨.bag tes', by simp only [valTree]; erw [h1]; rfl, Tree.same_bag.2 h2⟩
  | .fn .., _, _, _, _, hx | .param _, _, _, _, _, hx | .dsl .., _, _, _, _, hx => by simp [valTree] at hx
theorem valTrees_same : (ts : List Ty) → (x y : (Ty.semsWith Dsl.base ts).1) →
    Ty.relsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl ts x y → (tes : List (Tree Key)) → valTrees T ts x = some tes →
    ∃ tes', valTrees T ts y = some tes' ∧ Forall2 Tree.Same tes tes'
  | [], (), (), _, tes, hx => by simp only [valTrees, Option.some.injEq] at hx; subst hx; exact ⟨[], rfl, trivial⟩
  | t :: ts, (x, xs), (y, ys), ⟨h, hs⟩, tes, hx => by
    simp only [valTrees, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hx
    obtain ⟨te, h1, tes0, h2, rfl⟩ := hx
    obtain ⟨te', h1', hs1⟩ := valTree_same t x y h te h1
    obtain ⟨tes', h2', hs2⟩ := valTrees_same ts xs ys hs tes0 h2
    exact ⟨te' :: tes', by simp [valTrees, h1', h2'], hs1, hs2⟩
theorem valAlts_same (decl : List Variant) : (k : Nat) → (vs : List (List Ty)) → (x y : (Ty.semAltsWith Dsl.base vs).1) →
    Ty.relAltsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl vs x y → (te : Tree Key) → valAlts T decl k vs x = some te →
    ∃ te', valAlts T decl k vs y = some te' ∧ Tree.Same te te'
  | _, [], x, _, _, _, _ => nomatch x
  | k, fs :: _, .inl x, .inl y, h, te, hx => by
    simp only [valAlts, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨var, hvar, ts, hts, hx⟩ := hx
    obtain ⟨ts', hts', hs⟩ := valTrees_same fs x y h ts hts
    have hl : ts.length = ts'.length := forall2_length hs
    split at hx
    case isFalse => simp at hx
    case isTrue hw =>
      simp only [Option.pure_def, Option.some.injEq] at hx
      subst hx
      refine ⟨.seq (.atom (.bin var.name) :: ts'), ?_, Tree.same_seq.2 ⟨rfl, hs⟩⟩
      simp only [valAlts, Option.bind_eq_bind, hvar, Option.bind_some, hts', ← hl]
      simp [hw]
  | k, _ :: vs, .inr x, .inr y, h, te, hx => by
    simp only [valAlts] at hx ⊢
    exact valAlts_same decl (k + 1) vs x y h te hx
  | _, _ :: _, .inl _, .inr _, h, _, _ | _, _ :: _, .inr _, .inl _, h, _, _ => h.elim
end

theorem encBool_decBool (vs : List (List Ty)) (w : Wire) (y : (Ty.semAltsWith Dsl.base vs).1)
    (h : decBool vs w = some y) : encBool vs y = some w := by
  match vs, w with
  | [] :: _, .bool true => simp only [decBool] at h; cases h; rfl
  | f :: [] :: _, .bool false =>
    cases f with
    | nil => simp only [decBool] at h; cases h; rfl
    | cons => simp only [decBool] at h; cases h; rfl
  | [], _ | (_ :: _) :: [], _ | (_ :: _) :: (_ :: _) :: _, _ | [] :: _, .null | [] :: _, .num _
  | [] :: _, .str _ | [] :: _, .arr _ | [] :: _, .obj _ | [] :: [], .bool false | [] :: (_ :: _) :: _, .bool false
  | (_ :: _) :: [] :: _, .bool true | (_ :: _) :: [] :: _, .null | (_ :: _) :: [] :: _, .num _
  | (_ :: _) :: [] :: _, .str _ | (_ :: _) :: [] :: _, .arr _ | (_ :: _) :: [] :: _, .obj _ => simp [decBool] at h

theorem encNil_decNil (vs : List (List Ty)) (w : Wire) (y : (Ty.semAltsWith Dsl.base vs).1)
    (h : decNil vs w = some y) : encNil vs y = some w := by
  match vs, w with
  | [] :: _, .null => simp only [decNil] at h; cases h; rfl
  | [], _ | (_ :: _) :: _, _ | [] :: _, .bool _ | [] :: _, .num _ | [] :: _, .str _ | [] :: _, .arr _
  | [] :: _, .obj _ => simp [decNil] at h

theorem decBool_bool {vs : List (List Ty)} {w : Wire} {y : (Ty.semAltsWith Dsl.base vs).1}
    (h : decBool vs w = some y) : ∃ b, w = .bool b := by
  obtain ⟨b, hb⟩ := encBool_bool (encBool_decBool vs w y h); exact ⟨b, hb⟩

/-- Atoms written for Bool and Nil read the same only when they are one wire form. -/
theorem litTree_same {α γ : Type} [Leaf γ] {f : α → γ} {w w' : Wire} {t : Tree α} {t' : Tree γ}
    (h : litTree w = some t) (h' : litTree w' = some t') (hs : Tree.Same (t.map f) t') : w = w' := by
  cases w <;> simp only [litTree, reduceCtorEq] at h <;> cases w' <;> simp only [litTree, reduceCtorEq] at h' <;>
    cases h <;> cases h' <;> simp only [Tree.map, Tree.same_atom, Erl.atom.injEq] at hs
  all_goals first
    | rfl
    | (rename_i b b'; cases b <;> cases b' <;> simp_all)

theorem findIdx_name {decl : List Variant} {tag : String} {k : Nat} {var : Variant}
    (hk : decl.findIdx? (·.name == tag) = some k) (hv : decl[k]? = some var) : var.name = tag := by
  obtain ⟨h, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hk
  rw [List.getElem?_eq_getElem h, Option.some.injEq] at hv
  subst hv; simpa using hp

theorem writable_idx {decl : List Variant} {k : Nat} {var : Variant} (h : writable decl k var = true) :
    decl.findIdx? (·.name == var.name) = some k := by
  simp only [writable, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1

theorem head_name {α γ : Type} [Leaf γ] {f : α → γ} {a b : String} {ts : List (Tree α)} {ts' : List (Tree γ)}
    (h : Tree.Same ((Tree.seq (.atom (.bin a) :: ts)).map f) (.seq (.atom (.bin b) :: ts'))) : a = b := by
  simp only [Tree.map, Tree.maps, Tree.same_seq] at h
  simpa [Tree.map, Tree.same_atom] using h.1

/-- A value of a custom type has the tree of the variant it is, from index `j` on, with its name first. -/
theorem valAlts_head (decl : List Variant) : (j : Nat) → (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) →
    (te : Tree Key) → valAlts T decl j vs x = some te →
    ∃ m var ts, j ≤ m ∧ decl[m]? = some var ∧ writable decl m var = true ∧ te = .seq (.atom (.bin var.name) :: ts)
  | _, [], x, _, _ => nomatch x
  | j, _ :: _, .inl x, te, h => by
    simp only [valAlts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨var, hvar, ts, -, h⟩ := h
    split at h
    · rename_i hw
      simp only [Option.pure_def, Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hw
      exact ⟨j, var, ts, Nat.le_refl j, hvar, hw.1, h.symm⟩
    · cases h
  | j, _ :: vs, .inr x, te, h => by
    simp only [valAlts] at h
    obtain ⟨m, var, ts, hm, h1, h2, h3⟩ := valAlts_head decl (j + 1) vs x te h
    exact ⟨m, var, ts, by omega, h1, h2, h3⟩

theorem wireAlts_head (decl : List Variant) (kvs : List (String × Wire)) (k : Nat) : (j : Nat) → (vs : List (List Ty)) →
    (tl : Tree Name) → wireAlts T decl kvs k j vs = some tl →
    ∃ var ts, decl[k]? = some var ∧ tl = .seq (.atom (.bin var.name) :: ts)
  | _, [], _, h => by simp [wireAlts] at h
  | j, _ :: vs, tl, h => by
    simp only [wireAlts] at h
    split at h
    · rename_i hkj
      subst hkj
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨var, hvar, h⟩ := h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨ts, -, h⟩ := h
        exact ⟨var, ts, hvar, h.symm⟩
      · cases h
    · exact wireAlts_head decl kvs k (j + 1) vs tl h

/-- `lookup` reads back each id among `ks` by the name `β` gives it. -/
def Undoes (lookup : String → Option IdV) (β : Key → Name) (ks : List Key) : Prop :=
  ∀ i s, Key.id i ∈ ks → β (.id i) = .id s → lookup s = some i

theorem Undoes.mono {lookup : String → Option IdV} {β : Key → Name} {ks ks' : List Key} (h : Undoes lookup β ks)
    (hs : ∀ k ∈ ks', k ∈ ks) : Undoes lookup β ks' := fun i s hi he => h i s (hs _ hi) he

section
variable (lookup : String → Option IdV) (β : Key → Name)

-- One mutual block proves the theorems together, so each sees the naming hypothesis only some of them use.
set_option linter.unusedSectionVars false

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- A wire form whose tree is a value's once `β` names the value's ids decodes, where `lookup` reads each id back by
its name, to that value up to the order of its bags and tables. -/
theorem tree_dec : (t : Ty) → t.comparable = true → (x : t.den0) → (w : Wire) → (te : Tree Key) → (tl : Tree Name) →
    valTree T t x = some te → wireTree T t w = some tl → Tree.Same (te.map β) tl → Undoes lookup β te.leaves →
    ∃ y, dec T lookup t w = some y ∧ Ty.Same t x y
  | .int, _, x, w, te, tl, hx, hw, hs, _ => by
    cases w <;> simp only [wireTree, reduceCtorEq] at hw
    simp only [valTree, Option.some.injEq] at hx hw; subst hx hw
    simp only [Tree.map, Tree.same_atom] at hs
    cases Erl.int.inj hs
    exact ⟨_, rfl, rfl⟩
  | .str, _, x, w, te, tl, hx, hw, hs, _ => by
    cases w <;> simp only [wireTree, reduceCtorEq] at hw
    simp only [valTree, Option.some.injEq] at hx hw; subst hx hw
    simp only [Tree.map, Tree.same_atom] at hs
    cases Erl.bin.inj hs
    exact ⟨_, Str.of?_val x, rfl⟩
  | .point .day, _, x, w, te, tl, hx, hw, hs, _ => by
    cases w <;> simp only [wireTree, reduceCtorEq] at hw
    simp only [valTree, Option.some.injEq] at hx hw; subst hx hw
    simp only [Tree.map, Tree.same_atom] at hs
    cases Erl.bin.inj hs
    exact ⟨_, DateThm.parse_render x, rfl⟩
  | .point .ms, _, x, w, te, tl, hx, hw, hs, _ => by
    cases w <;> simp only [wireTree, reduceCtorEq] at hw
    simp only [valTree, Option.some.injEq] at hx hw; subst hx hw
    simp only [Tree.map, Tree.same_atom] at hs
    cases Erl.int.inj hs
    exact ⟨_, rfl, rfl⟩
  | .id, _, x, w, te, tl, hx, hw, hs, hu => by
    cases w <;> simp only [wireTree, reduceCtorEq] at hw
    simp only [valTree, Option.some.injEq] at hx hw; subst hx hw
    rename_i s
    simp only [Tree.map] at hs
    exact ⟨x, hu x s (by simp [Tree.leaves]) (Tree.same_leaf.1 hs), Ty.rel0_refl .id rfl x⟩
  | .list t, hc, xs, w, te, tl, hx, hw, hs, hu => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    cases w <;> simp only [wireTree, reduceCtorEq, Option.map_eq_some_iff] at hw
    obtain ⟨tls, htls, rfl⟩ := hw
    simp only [Tree.map, Tree.maps_eq, Tree.same_seq, forall2_map_left_iff] at hs
    exact mapM_back (R := fun a c => Tree.Same (a.map β) c ∧ Undoes lookup β a.leaves)
      (fun x w a c ha hc' h => tree_dec t hc x w a c ha hc' h.1 h.2) htes htls
      (forall2_and_mem hs fun a ha => hu.mono fun _ hk => Tree.mem_leavess ha hk)
  | .bag t, hc, xs, w, te, tl, hx, hw, hs, hu => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    cases w <;> simp only [wireTree, reduceCtorEq, Option.map_eq_some_iff] at hw
    obtain ⟨tls, htls, rfl⟩ := hw
    simp only [Tree.map, Tree.maps_eq, Tree.same_bag, multi_map_left_iff] at hs
    obtain ⟨zs, hz, hp⟩ := hs
    obtain ⟨ws', hws', hf⟩ := forall2_perm hp.symm (mapM_forall2 htls)
    obtain ⟨ys', hys', hr⟩ := mapM_back (R := fun a c => Tree.Same (a.map β) c ∧ Undoes lookup β a.leaves)
      (fun x w a c ha hc' h => tree_dec t hc x w a c ha hc' h.1 h.2) htes (mapM_of_forall2 hf)
      (forall2_and_mem hz fun a ha => hu.mono fun _ hk => Tree.mem_leavess ha hk)
    obtain ⟨ys, hys, hp'⟩ := mapM_perm hws' hys'
    exact ⟨ys, hys, ys', hr, hp'⟩
  | .tuple ts, hc, x, w, te, tl, hx, hw, hs, hu => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    cases w <;> simp only [wireTree, reduceCtorEq, Option.map_eq_some_iff] at hw
    obtain ⟨tls, htls, rfl⟩ := hw
    simp only [Tree.map, Tree.maps_eq, Tree.same_seq, forall2_map_left_iff] at hs
    exact trees_decs ts hc x _ tes tls htes htls hs hu
  | .adt 0 a vs, hc, x, w, te, tl, hx, hw, hs, _ => by
    have e1 : valTree T (.adt 0 a vs) x = (encBool vs x).bind litTree := rfl
    have e2 : wireTree T (.adt 0 a vs) w = if (decBool vs w).isSome then litTree w else none := rfl
    rw [e1, Option.bind_eq_some_iff] at hx
    obtain ⟨w0, h0, hl0⟩ := hx
    rw [e2] at hw
    split at hw
    · rw [← litTree_same hl0 hw hs]
      exact ⟨x, decBool_encBool vs x w0 h0, Ty.rel0_refl _ hc x⟩
    · cases hw
  | .adt 1 a vs, hc, x, w, te, tl, hx, hw, hs, _ => by
    have e1 : valTree T (.adt 1 a vs) x = (encNil vs x).bind litTree := rfl
    have e2 : wireTree T (.adt 1 a vs) w = if (decNil vs w).isSome then litTree w else none := rfl
    rw [e1, Option.bind_eq_some_iff] at hx
    obtain ⟨w0, h0, hl0⟩ := hx
    rw [e2] at hw
    split at hw
    · rw [← litTree_same hl0 hw hs]
      exact ⟨x, decNil_encNil vs x w0 h0, Ty.rel0_refl _ hc x⟩
    · cases hw
  | .adt (i + 2) a vs, hc, x, w, te, tl, hx, hw, hs, hu => by
    cases w with
    | obj kvs =>
      have hw' : (do
          let decl := (T[i + 2]?.map (·.variants)).getD []
          let .str tag ← kvs.lookup "tag" | none
          let k ← decl.findIdx? (·.name == tag)
          wireAlts T decl kvs k 0 vs) = some tl := hw
      cases hl : kvs.lookup "tag" with
      | none => simp [hl] at hw'
      | some tw =>
        cases tw with
        | str tag =>
          simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at hw'
          obtain ⟨k, hk, hwa⟩ := hw'
          obtain ⟨y, hy, hr⟩ := alts_dec _ tag kvs k hk 0 vs hc x te tl hx hwa hs hu
          refine ⟨y, ?_, hr⟩
          show (do
            let decl := (T[i + 2]?.map (·.variants)).getD []
            let .str tag ← kvs.lookup "tag" | none
            let k ← decl.findIdx? (·.name == tag)
            decAlts T lookup decl kvs k 0 vs) = some y
          simp only [hl, Option.bind_eq_bind, Option.bind_some, hk, hy]
        | _ => simp [hl] at hw'
    | _ => simp [wireTree] at hw
  | .table k v, hc, x, w, te, tl, hx, hw, hs, hu => by
    simp only [Ty.comparable, Bool.and_eq_true] at hc
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    cases w <;> simp only [wireTree, reduceCtorEq, Option.map_eq_some_iff] at hw
    obtain ⟨tls, htls, rfl⟩ := hw
    rename_i ws
    simp only [Tree.map, Tree.maps_eq, Tree.same_bag, multi_map_left_iff] at hs
    obtain ⟨zs, hz, hp⟩ := hs
    obtain ⟨ws', hws', hf⟩ := forall2_perm hp.symm (mapM_forall2 htls)
    obtain ⟨ps', hps', hr⟩ := mapM_back (R := fun a c => Tree.Same (a.map β) c ∧ Undoes lookup β a.leaves)
      (S := fun (e e' : k.den0 × v.den0) => Ty.Same k e.1 e'.1 ∧ Ty.Same v e.2 e'.2)
      (d := fun (w : Wire) => match w with
        | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
        | _ => none)
      (fun p w a c ha hc' h => by
        obtain ⟨pa, pb⟩ := p
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at ha
        obtain ⟨ta, hta, tb, htb, rfl⟩ := ha
        match w, hc' with
        | .arr [wa, wb], hc' =>
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hc'
          obtain ⟨la, hla, lb, hlb, rfl⟩ := hc'
          obtain ⟨h1, h2⟩ := h
          simp only [Tree.map, Tree.maps, Tree.same_seq, Forall2] at h1
          have hl : Undoes lookup β ta.leaves ∧ Undoes lookup β tb.leaves :=
            ⟨h2.mono fun _ hk => by simp [Tree.leaves, Tree.leavess, hk],
              h2.mono fun _ hk => by simp [Tree.leaves, Tree.leavess, hk]⟩
          obtain ⟨a', ha', hsa⟩ := tree_dec k hc.1 pa wa ta la hta hla h1.1 hl.1
          obtain ⟨b', hb', hsb⟩ := tree_dec v hc.2 pb wb tb lb htb hlb h1.2.1 hl.2
          exact ⟨(a', b'), by simp [ha', hb'], hsa, hsb⟩) htes (mapM_of_forall2 hf)
      (forall2_and_mem hz fun a ha => hu.mono fun _ hk => Tree.mem_leavess ha hk)
    obtain ⟨ps, hps, hpp⟩ := mapM_perm hws' hps'
    have hu' : KeysUnique (Ty.semWith Dsl.base k).2 ps :=
      keysUnique_perm hpp (keysUnique_forall2 (fun _ _ _ _ ha hb => Ty.rel0_deq k hc.1 ha.1 hb.1) hr x.2)
    refine ⟨⟨ps, hu'⟩, ?_, ps', hr, hpp⟩
    show (do
      let pairs ← ws.mapM fun
        | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
        | _ => none
      if h : KeysUnique (Ty.semWith Dsl.base k).2 pairs then some ⟨pairs, h⟩ else none) =
      (some ⟨ps, hu'⟩ : Option (Ty.table k v).den0)
    rw [hps]
    simp [hu']
  | .fn .., _, _, _, _, _, hx, _, _, _ | .param _, _, _, _, _, _, hx, _, _, _ | .dsl .., _, _, _, _, _, hx, _, _, _ => by
    simp [valTree] at hx
theorem trees_decs : (ts : List Ty) → Ty.comparables ts = true → (x : (Ty.semsWith Dsl.base ts).1) → (ws : List Wire) →
    (tes : List (Tree Key)) → (tls : List (Tree Name)) → valTrees T ts x = some tes → wireTrees T ts ws = some tls →
    Forall2 (fun a c => Tree.Same (a.map β) c) tes tls → Undoes lookup β (Tree.leavess tes) →
    ∃ y, decs T lookup ts ws = some y ∧ Ty.relsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl ts x y
  | [], _, (), ws, tes, tls, hx, hw, hs, _ => by
    simp only [valTrees, Option.some.injEq] at hx; subst hx
    cases ws with
    | nil => exact ⟨(), rfl, trivial⟩
    | cons => simp [wireTrees] at hw
  | t :: ts, hc, (x, xs), ws, tes, tls, hx, hw, hs, hu => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    simp only [valTrees, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hx
    obtain ⟨te, h1, tes', h2, rfl⟩ := hx
    cases ws with
    | nil => simp [wireTrees] at hw
    | cons w ws =>
      simp only [wireTrees, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
      obtain ⟨tl, h3, tls', h4, rfl⟩ := hw
      obtain ⟨y, hy, hr⟩ := tree_dec t hc.1 x w te tl h1 h3 hs.1 (hu.mono fun _ hk => by simp [Tree.leavess, hk])
      obtain ⟨ys, hys, hrs⟩ := trees_decs ts hc.2 xs ws tes' tls' h2 h4 hs.2
        (hu.mono fun _ hk => by simp [Tree.leavess, hk])
      exact ⟨(y, ys), by simp [decs, hy, hys], hr, hrs⟩
theorem fields_dec (kvs : List (String × Wire)) : (fs : List Ty) → Ty.comparables fs = true →
    (keys : List String) → (x : (Ty.semsWith Dsl.base fs).1) → (tes : List (Tree Key)) → (tls : List (Tree Name)) →
    valTrees T fs x = some tes → wireFields T kvs fs keys = some tls →
    Forall2 (fun a c => Tree.Same (a.map β) c) tes tls → Undoes lookup β (Tree.leavess tes) →
    ∃ y, decFields T lookup kvs fs keys = some y ∧ Ty.relsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl fs x y
  | [], _, keys, (), tes, tls, hx, hw, _, _ => by
    simp only [valTrees, Option.some.injEq] at hx; subst hx
    cases keys with
    | nil => exact ⟨(), rfl, trivial⟩
    | cons => simp [wireFields] at hw
  | f :: fs, hc, keys, (x, xs), tes, tls, hx, hw, hs, hu => by
    simp only [Ty.comparables, Bool.and_eq_true] at hc
    simp only [valTrees, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hx
    obtain ⟨te, h1, tes', h2, rfl⟩ := hx
    cases keys with
    | nil => simp [wireFields] at hw
    | cons key keys =>
      simp only [wireFields, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
      obtain ⟨w, hkw, tl, h3, tls', h4, rfl⟩ := hw
      obtain ⟨y, hy, hr⟩ := tree_dec f hc.1 x w te tl h1 h3 hs.1 (hu.mono fun _ hk => by simp [Tree.leavess, hk])
      obtain ⟨ys, hys, hrs⟩ := fields_dec kvs fs hc.2 keys xs tes' tls' h2 h4 hs.2
        (hu.mono fun _ hk => by simp [Tree.leavess, hk])
      exact ⟨(y, ys), by simp [decFields, hkw, hy, hys], hr, hrs⟩
theorem alts_dec (decl : List Variant) (tag : String) (kvs : List (String × Wire)) (k : Nat)
    (hk : decl.findIdx? (·.name == tag) = some k) : (j : Nat) → (vs : List (List Ty)) → Ty.comparabless vs = true →
    (x : (Ty.semAltsWith Dsl.base vs).1) → (te : Tree Key) → (tl : Tree Name) → valAlts T decl j vs x = some te →
    wireAlts T decl kvs k j vs = some tl → Tree.Same (te.map β) tl → Undoes lookup β te.leaves →
    ∃ y, decAlts T lookup decl kvs k j vs = some y ∧ Ty.relAltsWith Dsl.base (Dsl.rel0 PBij.refl) PBij.refl vs x y
  | _, [], _, x, _, _, _, _, _, _ => nomatch x
  | j, fs :: vs, hc, .inl x, te, tl, hx, hw, hs, hu => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    have hx0 := hx
    simp only [valAlts, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨var, hvar, ts, hts, hx⟩ := hx
    split at hx
    · rename_i hwr
      simp only [Option.pure_def, Option.some.injEq] at hx
      subst hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hwr
      by_cases hkj : k = j
      · subst hkj
        simp only [wireAlts, ↓reduceIte, hvar, Option.bind_eq_bind, Option.bind_some] at hw
        split at hw
        · rename_i hlen
          simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
          obtain ⟨tls, htls, rfl⟩ := hw
          simp only [Tree.map, Tree.maps, Tree.same_seq, Forall2] at hs
          rw [Tree.maps_eq] at hs
          obtain ⟨y, hy, hr⟩ := fields_dec kvs fs hc.1 _ x ts tls hts htls (forall2_map_left_iff.1 hs.2)
            (hu.mono fun _ hk => by simp [Tree.leaves, Tree.leavess, hk])
          refine ⟨.inl y, ?_, hr⟩
          simp [decAlts, hvar, hwr.1, hlen, hy]
        · cases hw
      · simp only [wireAlts, hkj, ↓reduceIte] at hw
        obtain ⟨var', ts', hvar', rfl⟩ := wireAlts_head T decl kvs k (j + 1) vs tl hw
        have e := head_name hs
        have h1 := writable_idx hwr.1
        rw [e, findIdx_name hk hvar', hk] at h1
        exact absurd (Option.some.inj h1) hkj
    · cases hx
  | j, _ :: vs, hc, .inr x, te, tl, hx, hw, hs, hu => by
    simp only [Ty.comparabless, Bool.and_eq_true] at hc
    simp only [valAlts] at hx
    by_cases hkj : k = j
    · subst hkj
      obtain ⟨m, var, ts, hm, hvar, hwr, rfl⟩ := valAlts_head T decl (k + 1) vs x te hx
      obtain ⟨var', ts', hvar', rfl⟩ := wireAlts_head T decl kvs k k (_ :: vs) tl hw
      have e := head_name hs
      have h1 := writable_idx hwr
      rw [e, findIdx_name hk hvar', hk] at h1
      have := Option.some.inj h1
      omega
    · simp only [wireAlts, hkj, ↓reduceIte] at hw
      obtain ⟨y, hy, hr⟩ := alts_dec decl tag kvs k hk (j + 1) vs hc.2 x te tl hx hw hs hu
      exact ⟨.inr y, by simp only [decAlts, hkj, ↓reduceIte, hy]; rfl, hr⟩
end

end

section
variable (lookup : String → Option IdV) (β : Key → Name) (hβ : ∀ s i, lookup s = some i → β (.id i) = .id s)
include hβ

-- One mutual block proves the theorems together, so each sees the naming hypothesis only some of them use.
set_option linter.unusedSectionVars false

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- A wire form that decodes to a value, where `β` names each id by the name `lookup` read it from, has the value's
tree once `β` names its ids. -/
theorem dec_tree : (t : Ty) → (w : Wire) → (y : t.den0) → dec T lookup t w = some y →
    ∃ te tl, valTree T t y = some te ∧ wireTree T t w = some tl ∧ Tree.Same (te.map β) tl
  | .int, .num n, y, h => by
    cases Option.some.inj (show some n = some y from h); exact ⟨_, _, rfl, rfl, rfl⟩
  | .str, .str s, y, h => by
    obtain ⟨y, hy⟩ := y
    have h : Str.of? s = some ⟨y, hy⟩ := h
    simp only [Str.of?] at h
    split at h
    · cases h; exact ⟨_, _, rfl, rfl, rfl⟩
    · cases h
  | .point .day, .str s, y, h => by
    have h : parseDate? s = some y := h
    refine ⟨_, _, rfl, rfl, ?_⟩
    simp only [Tree.map, DateThm.render_parse s y h]; rfl
  | .point .ms, .num n, y, h => by
    cases Option.some.inj (show some n = some y from h); exact ⟨_, _, rfl, rfl, rfl⟩
  | .id, .str s, y, h => by
    have h : lookup s = some y := h
    refine ⟨_, _, rfl, rfl, ?_⟩
    simp only [Tree.map, hβ s y h]; rfl
  | .list t, .arr ws, ys, h => by
    have h : ws.mapM (dec T lookup t) = some ys := h
    obtain ⟨tls, tes, h1, h2, h3⟩ := mapM_two (S := fun (c : Tree Name) (d : Tree Key) => Tree.Same (d.map β) c)
      (fun w y hy => by
        obtain ⟨te, tl, h1, h2, h3⟩ := dec_tree t w y hy
        exact ⟨tl, te, h2, h1, h3⟩) _ ys h
    refine ⟨.seq tes, .seq tls, by simp [valTree, h2], by simp [wireTree, h1], ?_⟩
    simp only [Tree.map, Tree.maps_eq]
    exact Tree.same_seq.2 (forall2_map_left_iff.2 (forall2_flip h3))
  | .bag t, .arr ws, ys, h => by
    have h : ws.mapM (dec T lookup t) = some ys := h
    obtain ⟨tls, tes, h1, h2, h3⟩ := mapM_two (S := fun (c : Tree Name) (d : Tree Key) => Tree.Same (d.map β) c)
      (fun w y hy => by
        obtain ⟨te, tl, h1, h2, h3⟩ := dec_tree t w y hy
        exact ⟨tl, te, h2, h1, h3⟩) _ ys h
    refine ⟨.bag tes, .bag tls, by simp [valTree, h2], by simp [wireTree, h1], ?_⟩
    simp only [Tree.map, Tree.maps_eq]
    exact Tree.same_bag.2 (Multi.of_forall2 (forall2_map_left_iff.2 (forall2_flip h3)))
  | .tuple ts, .arr ws, y, h => by
    obtain ⟨tes, tls, h1, h2, h3⟩ := decs_trees ts ws y h
    refine ⟨.seq tes, .seq tls, by simp [valTree, h1], by simp [wireTree, h2], ?_⟩
    simp only [Tree.map, Tree.maps_eq]
    exact Tree.same_seq.2 (forall2_map_left_iff.2 h3)
  | .adt 0 a vs, w, y, h => by
    have h : decBool vs w = some y := h
    obtain ⟨b, rfl⟩ := decBool_bool h
    refine ⟨.atom (.atom (if b then "true" else "false")), .atom (.atom (if b then "true" else "false")), ?_, ?_, rfl⟩
    · show (encBool vs y).bind litTree = _
      rw [encBool_decBool vs _ y h]; rfl
    · show (if (decBool vs (.bool b)).isSome then litTree (.bool b) else none) = _
      rw [h]; rfl
  | .adt 1 a vs, w, y, h => by
    have h : decNil vs w = some y := h
    have hw := encNil_null (encNil_decNil vs w y h)
    subst hw
    refine ⟨.atom (.atom "nil"), .atom (.atom "nil"), ?_, ?_, rfl⟩
    · show (encNil vs y).bind litTree = _
      rw [encNil_decNil vs _ y h]; rfl
    · show (if (decNil vs .null).isSome then litTree .null else none) = _
      rw [h]; rfl
  | .adt (i + 2) a vs, .obj kvs, y, h => by
    have h' : (do
        let decl := (T[i + 2]?.map (·.variants)).getD []
        let .str tag ← kvs.lookup "tag" | none
        let k ← decl.findIdx? (·.name == tag)
        decAlts T lookup decl kvs k 0 vs) = some y := h
    cases hl : kvs.lookup "tag" with
    | none => simp [hl] at h'
    | some tw =>
      cases tw with
      | str tag =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some] at h'
        cases hk : ((T[i + 2]?.map (·.variants)).getD []).findIdx? (·.name == tag) with
        | none => simp [hk] at h'
        | some k =>
        simp only [hk] at h'
        obtain ⟨te, tl, h1, h2, h3⟩ := decAlts_trees _ kvs k 0 vs y h'
        refine ⟨te, tl, h1, ?_, h3⟩
        show (do
          let decl := (T[i + 2]?.map (·.variants)).getD []
          let .str tag ← kvs.lookup "tag" | none
          let k ← decl.findIdx? (·.name == tag)
          wireAlts T decl kvs k 0 vs) = some tl
        simp only [hl, Option.bind_eq_bind, Option.bind_some, hk, h2]
      | _ => simp [hl] at h'
  | .table k v, .arr ws, y, h => by
    have e : dec T lookup (.table k v) (.arr ws) = (do
        let pairs ← ws.mapM fun (w : Wire) => match w with
          | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
          | _ => none
        if h : KeysUnique (Ty.semWith Dsl.base k).2 pairs then some ⟨pairs, h⟩ else none) := rfl
    rw [e, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ps, hps, h⟩ := h
    split at h
    · cases h
      obtain ⟨tls, tes, h1, h2, h3⟩ := mapM_two (S := fun (c : Tree Name) (d : Tree Key) => Tree.Same (d.map β) c)
        (g := fun (w : Wire) => match w with
          | .arr [a, b] => do pure (Tree.seq [← wireTree T k a, ← wireTree T v b])
          | _ => none)
        (k := fun (e : k.den0 × v.den0) => do pure (Tree.seq [← valTree T k e.1, ← valTree T v e.2]))
        (fun w p hp => by
          match w, hp with
          | .arr [wa, wb], hp =>
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hp
            obtain ⟨a, ha, b, hb, rfl⟩ := hp
            obtain ⟨ta, la, ha1, ha2, ha3⟩ := dec_tree k wa a ha
            obtain ⟨tb, lb, hb1, hb2, hb3⟩ := dec_tree v wb b hb
            refine ⟨.seq [la, lb], .seq [ta, tb], by simp [ha2, hb2], by simp [ha1, hb1], ?_⟩
            simp only [Tree.map, Tree.maps_eq]
            exact Tree.same_seq.2 ⟨ha3, hb3, trivial⟩) ws ps hps
      refine ⟨.bag tes, .bag tls, ?_, by simp only [wireTree]; erw [h1]; rfl, ?_⟩
      · show (ps.mapM fun (a, b) => do pure (Tree.seq [← valTree T k a, ← valTree T v b])).map Tree.bag = _
        erw [h2]; rfl
      · simp only [Tree.map, Tree.maps_eq]
        exact Tree.same_bag.2 (Multi.of_forall2 (forall2_map_left_iff.2 (forall2_flip h3)))
    · cases h
  | .int, .null, _, h | .int, .bool _, _, h | .int, .str _, _, h | .int, .arr _, _, h | .int, .obj _, _, h
  | .str, .null, _, h | .str, .bool _, _, h | .str, .num _, _, h | .str, .arr _, _, h | .str, .obj _, _, h
  | .point .day, .null, _, h | .point .day, .bool _, _, h | .point .day, .num _, _, h | .point .day, .arr _, _, h
  | .point .day, .obj _, _, h
  | .point .ms, .null, _, h | .point .ms, .bool _, _, h | .point .ms, .str _, _, h | .point .ms, .arr _, _, h
  | .point .ms, .obj _, _, h
  | .id, .null, _, h | .id, .bool _, _, h | .id, .num _, _, h | .id, .arr _, _, h | .id, .obj _, _, h
  | .list _, .null, _, h | .list _, .bool _, _, h | .list _, .num _, _, h | .list _, .str _, _, h
  | .list _, .obj _, _, h | .bag _, .null, _, h | .bag _, .bool _, _, h | .bag _, .num _, _, h
  | .bag _, .str _, _, h | .bag _, .obj _, _, h | .tuple _, .null, _, h | .tuple _, .bool _, _, h
  | .tuple _, .num _, _, h | .tuple _, .str _, _, h | .tuple _, .obj _, _, h
  | .adt (_ + 2) _ _, .null, _, h | .adt (_ + 2) _ _, .bool _, _, h | .adt (_ + 2) _ _, .num _, _, h
  | .adt (_ + 2) _ _, .str _, _, h | .adt (_ + 2) _ _, .arr _, _, h
  | .table _ _, .null, _, h | .table _ _, .bool _, _, h | .table _ _, .num _, _, h | .table _ _, .str _, _, h
  | .table _ _, .obj _, _, h | .fn .., _, _, h | .param _, _, _, h | .dsl .., _, _, h => nomatch h
theorem decs_trees : (ts : List Ty) → (ws : List Wire) → (y : (Ty.semsWith Dsl.base ts).1) →
    decs T lookup ts ws = some y → ∃ tes tls, valTrees T ts y = some tes ∧ wireTrees T ts ws = some tls ∧
      Forall2 (fun a c => Tree.Same (a.map β) c) tes tls
  | [], [], (), _ => ⟨[], [], rfl, rfl, trivial⟩
  | t :: ts, w :: ws, y, h => by
    have h : (do pure (← dec T lookup t w, ← decs T lookup ts ws)) = some y := h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨y, hy, ys, hys, he⟩ := h
    obtain rfl := Option.some.inj he
    obtain ⟨te, tl, h1, h2, h3⟩ := dec_tree t w y hy
    obtain ⟨tes, tls, h4, h5, h6⟩ := decs_trees ts ws ys hys
    exact ⟨te :: tes, tl :: tls, by simp [valTrees, h1, h4], by simp [wireTrees, h2, h5], h3, h6⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => nomatch h
theorem decFields_trees (kvs : List (String × Wire)) : (fs : List Ty) → (keys : List String) →
    (y : (Ty.semsWith Dsl.base fs).1) → decFields T lookup kvs fs keys = some y →
    ∃ tes tls, valTrees T fs y = some tes ∧ wireFields T kvs fs keys = some tls ∧
      Forall2 (fun a c => Tree.Same (a.map β) c) tes tls
  | [], [], (), _ => ⟨[], [], rfl, rfl, trivial⟩
  | f :: fs, key :: keys, y, h => by
    have h : (do pure (← dec T lookup f (← kvs.lookup key), ← decFields T lookup kvs fs keys)) = some y := h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨w, hw, y, hy, ys, hys, he⟩ := h
    obtain rfl := Option.some.inj he
    obtain ⟨te, tl, h1, h2, h3⟩ := dec_tree f w y hy
    obtain ⟨tes, tls, h4, h5, h6⟩ := decFields_trees kvs fs keys ys hys
    exact ⟨te :: tes, tl :: tls, by simp [valTrees, h1, h4], by simp [wireFields, hw, h2, h5], h3, h6⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => nomatch h
theorem decAlts_trees (decl : List Variant) (kvs : List (String × Wire)) (k : Nat) : (j : Nat) →
    (vs : List (List Ty)) → (y : (Ty.semAltsWith Dsl.base vs).1) → decAlts T lookup decl kvs k j vs = some y →
    ∃ te tl, valAlts T decl j vs y = some te ∧ wireAlts T decl kvs k j vs = some tl ∧ Tree.Same (te.map β) tl
  | _, [], _, h => by simp [decAlts] at h
  | j, fs :: vs, y, h => by
    by_cases hkj : k = j
    · subst hkj
      simp only [decAlts, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨var, hvar, h⟩ := h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.bind_eq_some_iff, Option.pure_def] at h
        obtain ⟨ys, hys, he⟩ := h
        cases Option.some.inj he
        obtain ⟨tes, tls, h1, h2, h3⟩ := decFields_trees kvs fs _ ys hys
        have hlen : (fieldKeys var.fields).length = tes.length := by
          rw [forall2_length h3, wireFields_length T kvs fs _ tls h2]
        refine ⟨.seq (.atom (.bin var.name) :: tes), .seq (.atom (.bin var.name) :: tls), ?_, ?_, ?_⟩
        · simp [valAlts, hvar, h1, hc.1, hlen]
        · simp [wireAlts, hvar, hc.2, h2]
        · simp only [Tree.map, Tree.maps, Tree.same_seq]
          refine ⟨rfl, ?_⟩
          rw [Tree.maps_eq]; exact forall2_map_left_iff.2 h3
      · cases h
    · simp only [decAlts, hkj, ↓reduceIte] at h
      cases hy : decAlts T lookup decl kvs k (j + 1) vs with
      | none => rw [hy] at h; cases h
      | some y' =>
      rw [hy] at h
      obtain rfl := Option.some.inj h
      obtain ⟨te, tl, h1, h2, h3⟩ := decAlts_trees decl kvs k (j + 1) vs y' hy
      exact ⟨te, tl, by simpa [valAlts] using h1, by simpa [wireAlts, hkj] using h2, h3⟩
end

end

end Trees

end Tazuna.Trace
