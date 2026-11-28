import Std.Data.String.ToNat
import Tazuna.Trace.Verify
import Tazuna.Trace.WriteOk
import Tazuna.Semantics.StepSame

/-! A trace the writer writes for a run reads as the spec (`traceOf_reads`), so verify replays it as passed unless it
runs out of tries (`replay_iff`). Verify's states follow the writer's up to the order bags and tables are stored in
(`StateSame`): an in line reads back as the writer's input up to that order (`dec_enc`), so its step is the writer's up
to that order (`step_same`); the binding is the writer's names; and each out line, read as a tree, is the spec's value
up to that order once the names name its ids (`enc_tree`, `valTree_same`), so it decodes to that value
(`lineW_of_treeW`). -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

section Trees
variable (T : List TypeDecl)

variable (name : IdV → Option String) (β : Key → Name) (hβ : ∀ i s, name i = some s → β (.id i) = .id s)
include hβ

-- One mutual block proves the theorems together, so each sees the naming hypothesis only some of them use.
set_option linter.unusedSectionVars false

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- A written value read as a tree is the value's tree once `β` names its ids as the writer did, its bags and tables in
any order. -/
theorem enc_tree : (t : Ty) → (x : t.den0) → (w : Wire) → enc T name t x = some w →
    ∃ te tl, valTree T t x = some te ∧ wireTree T t w = some tl ∧ Tree.Same (te.map β) tl
  | .int, x, w, h => by
    simp only [enc, Option.some.injEq] at h; subst h; exact ⟨_, _, rfl, rfl, rfl⟩
  | .str, x, w, h => by
    simp only [enc, Option.some.injEq] at h; subst h; exact ⟨_, _, rfl, rfl, rfl⟩
  | .point .day, x, w, h | .point .ms, x, w, h => by
    simp only [enc, Option.some.injEq] at h; subst h; exact ⟨_, _, rfl, rfl, rfl⟩
  | .id, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    refine ⟨_, _, rfl, rfl, ?_⟩
    show Tree.Same (.leaf (β (.id x))) (.leaf (.id s))
    rw [hβ x s hs]; rfl
  | .list t, xs, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨tes, tls, h1, h2, h3⟩ := mapM_two (S := fun (a : Tree Key) (c : Tree Name) => Tree.Same (a.map β) c) (enc_tree t) xs ws hws
    refine ⟨.seq tes, .seq tls, by simp [valTree, h1], by simp [wireTree, h2], ?_⟩
    simp only [Tree.map, Tree.maps_eq]
    exact Tree.same_seq.2 (forall2_map_left_iff.2 h3)
  | .bag t, xs, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨tes, tls, h1, h2, h3⟩ := mapM_two (S := fun (a : Tree Key) (c : Tree Name) => Tree.Same (a.map β) c) (enc_tree t) _ ws hws
    obtain ⟨tes', h1', hp⟩ := mapM_perm (List.mergeSort_perm xs _) h1
    refine ⟨.bag tes', .bag tls, by simp [valTree, h1'], by simp [wireTree, h2], ?_⟩
    simp only [Tree.map, Tree.maps_eq]
    exact Tree.same_bag.2 ((Multi.of_forall2 (forall2_map_left_iff.2 h3)).perm_left (hp.map _))
  | .tuple ts, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨tes, tls, h1, h2, h3⟩ := encs_trees ts x ws hws
    refine ⟨.seq tes, .seq tls, by simp [valTree, h1], by simp [wireTree, h2], ?_⟩
    simp only [Tree.map, Tree.maps_eq]
    exact Tree.same_seq.2 (forall2_map_left_iff.2 h3)
  | .adt 0 _ vs, x, w, h => by
    have hw : enc T name (.adt 0 _ vs) x = encBool vs x := rfl
    rw [hw] at h
    obtain ⟨b, rfl⟩ := encBool_bool h
    refine ⟨.atom (.atom (if b then "true" else "false")), .atom (.atom (if b then "true" else "false")), by simp [valTree, h, litTree], by simp [wireTree, decBool_encBool vs x _ h, litTree], rfl⟩
  | .adt 1 _ vs, x, w, h => by
    have hw : enc T name (.adt 1 _ vs) x = encNil vs x := rfl
    rw [hw] at h
    obtain rfl := encNil_null h
    refine ⟨.atom (.atom "nil"), .atom (.atom "nil"), by simp [valTree, h, litTree], by simp [wireTree, decNil_encNil vs x _ h, litTree], rfl⟩
  | .adt (i + 2) _ vs, x, w, h => by
    obtain ⟨kvs, tag, k, rfl, htag, hk, _, te, tl, h1, h2, h3⟩ := encAlts_trees vs _ 0 x w h
    refine ⟨te, tl, h1, ?_, h3⟩
    show (do
      let decl := (T[i + 2]?.map (·.variants)).getD []
      let .str tag ← kvs.lookup "tag" | none
      let k ← decl.findIdx? (·.name == tag)
      wireAlts T decl kvs k 0 vs) = some tl
    rw [htag]
    show (List.findIdx? (fun (var : Variant) => var.name == tag) ((T[i + 2]?.map (·.variants)).getD []) >>= fun k =>
      wireAlts T ((T[i + 2]?.map (·.variants)).getD []) kvs k 0 vs) = some tl
    rw [hk]
    exact h2
  | .table k v, x, w, h => by
    rw [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨tes, tls, h1, h2, h3⟩ := mapM_two (S := fun (a : Tree Key) (c : Tree Name) => Tree.Same (a.map β) c)
      (g := fun (e : k.den0 × v.den0) => do pure (Tree.seq [← valTree T k e.1, ← valTree T v e.2]))
      (k := fun (w : Wire) => match w with
        | .arr [a, b] => do pure (Tree.seq [← wireTree T k a, ← wireTree T v b])
        | _ => none) (by
      intro ⟨a, b⟩ w hw
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
      obtain ⟨wa, ha, wb, hb, rfl⟩ := hw
      obtain ⟨ta, la, ha1, ha2, ha3⟩ := enc_tree k a wa ha
      obtain ⟨tb, lb, hb1, hb2, hb3⟩ := enc_tree v b wb hb
      refine ⟨.seq [ta, tb], .seq [la, lb], by simp [ha1, hb1], by simp [ha2, hb2], ?_⟩
      simp only [Tree.map, Tree.maps_eq]
      exact Tree.same_seq.2 ⟨ha3, hb3, trivial⟩) _ ws hws
    obtain ⟨tes', h1', hp⟩ := mapM_perm (List.mergeSort_perm x.1 _) h1
    refine ⟨.bag tes', .bag tls, ?_, by simp only [wireTree]; erw [h2]; rfl, ?_⟩
    · show (x.1.mapM fun (a, b) => do pure (Tree.seq [← valTree T k a, ← valTree T v b])).map Tree.bag = _
      rw [h1']; rfl
    · simp only [Tree.map, Tree.maps_eq]
      exact Tree.same_bag.2 ((Multi.of_forall2 (forall2_map_left_iff.2 h3)).perm_left (hp.map _))
  | .fn .., _, _, h | .param _, _, _, h | .dsl .., _, _, h => by simp [enc] at h
theorem encs_trees : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (ws : List Wire) →
    encs T name ts x = some ws → ∃ tes tls, valTrees T ts x = some tes ∧ wireTrees T ts ws = some tls ∧
      Forall2 (fun a c => Tree.Same (a.map β) c) tes tls
  | [], (), ws, h => by simp only [encs, Option.some.injEq] at h; subst h; exact ⟨[], [], rfl, rfl, trivial⟩
  | t :: ts, (x, xs), ws, h => by
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    obtain ⟨te, tl, h1, h2, h3⟩ := enc_tree t x w hw
    obtain ⟨tes, tls, h4, h5, h6⟩ := encs_trees ts xs ws' hws'
    exact ⟨te :: tes, tl :: tls, by simp [valTrees, h1, h4], by simp [wireTrees, h2, h5], h3, h6⟩
theorem fields_trees : (fs : List Ty) → (x : (Ty.semsWith Dsl.base fs).1) → (ws : List Wire) →
    encs T name fs x = some ws → ∀ (keys : List String) (kvs : List (String × Wire)),
    keys.length = ws.length → (∀ k w, (k, w) ∈ keys.zip ws → kvs.lookup k = some w) →
    ∃ tes tls, valTrees T fs x = some tes ∧ wireFields T kvs fs keys = some tls ∧
      Forall2 (fun a c => Tree.Same (a.map β) c) tes tls
  | [], (), ws, h, keys, kvs, hlen, _ => by
    simp only [encs, Option.some.injEq] at h; subst h
    cases keys with
    | nil => exact ⟨[], [], rfl, rfl, trivial⟩
    | cons _ _ => simp at hlen
  | f :: fs, (x, xs), ws, h, keys, kvs, hlen, hkv => by
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    cases keys with
    | nil => simp at hlen
    | cons key keys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hhead := hkv key w (by simp)
      have hrest : ∀ k w, (k, w) ∈ keys.zip ws' → kvs.lookup k = some w := fun k w hm => hkv k w (by simp [hm])
      obtain ⟨te, tl, h1, h2, h3⟩ := enc_tree f x w hw
      obtain ⟨tes, tls, h4, h5, h6⟩ := fields_trees fs xs ws' hws' keys kvs hlen hrest
      exact ⟨te :: tes, tl :: tls, by simp [valTrees, h1, h4], by simp [wireFields, hhead, h2, h5], h3, h6⟩
theorem encAlts_trees : (vs : List (List Ty)) → (decl : List Variant) → (j : Nat) →
    (x : (Ty.semAltsWith Dsl.base vs).1) → (w : Wire) → encAlts T name decl j vs x = some w →
    ∃ kvs tag k, w = .obj kvs ∧ kvs.lookup "tag" = some (.str tag) ∧ decl.findIdx? (·.name == tag) = some k ∧
      j ≤ k ∧ ∃ te tl, valAlts T decl j vs x = some te ∧ wireAlts T decl kvs k j vs = some tl ∧
        Tree.Same (te.map β) tl
  | [], _, _, x, _, _ => nomatch x
  | fs :: _, decl, j, .inl x, w, h => by
    simp only [encAlts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨var, hvar, ws, hws, h⟩ := h
    split at h
    case isFalse => simp at h
    case isTrue hw =>
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      have hw' := hw
      simp only [writable, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hw'
      obtain ⟨⟨⟨hidx, hnd⟩, htag⟩, hlen⟩ := hw'
      refine ⟨_, var.name, j, rfl, by simp, hidx, Nat.le_refl j, ?_⟩
      have hnotag : "tag" ∉ fieldKeys var.fields := by simpa using htag
      have hkv : ∀ k w, (k, w) ∈ (fieldKeys var.fields).zip ws →
          List.lookup k (("tag", Wire.str var.name) :: (fieldKeys var.fields).zip ws) = some w := by
        intro k w hm
        have hk' : k ≠ "tag" := fun e => hnotag (e ▸ (List.of_mem_zip hm).1)
        have hk : (k == "tag") = false := by simp [hk']
        simp only [List.lookup_cons, hk]; exact lookup_zip _ ws hnd k w hm
      obtain ⟨tes, tls, h1, h2, h3⟩ := fields_trees fs x ws hws _ _ hlen hkv
      have hl1 : tes.length = tls.length := forall2_length h3
      have hl2 := wireFields_length T _ fs _ tls h2
      have hwr : writable decl j var = true := by
        simp only [Bool.and_eq_true] at hw; exact hw.1
      refine ⟨.seq (.atom (.bin var.name) :: tes), .seq (.atom (.bin var.name) :: tls), ?_, ?_, ?_⟩
      · simp only [valAlts, Option.bind_eq_bind, hvar, Option.bind_some, h1, hwr, Bool.true_and]
        simp [hl1, hl2]
      · simp only [wireAlts, ↓reduceIte, Option.bind_eq_bind, hvar, Option.bind_some, List.length_cons,
          List.length_zip, hlen, Nat.min_self]
        simp [h2]
      · simp only [Tree.map, Tree.maps_eq, List.map_cons]
        exact Tree.same_seq.2 ⟨rfl, forall2_map_left_iff.2 h3⟩
  | _ :: vs, decl, j, .inr y, w, h => by
    simp only [encAlts] at h
    obtain ⟨kvs, tag, k, rfl, htag, hk, hle, te, tl, h1, h2, h3⟩ := encAlts_trees vs decl (j + 1) y w h
    refine ⟨kvs, tag, k, rfl, htag, hk, by omega, te, tl, h1, ?_, h3⟩
    have hne : k ≠ j := by omega
    simp only [wireAlts, hne, ↓reduceIte, h2]
end

end Trees

section Same
variable (T : List TypeDecl)


theorem encBool_ids {vs : List (List Ty)} {x : (Ty.semAltsWith Dsl.base vs).1} {w : Wire}
    (h : encBool vs x = some w) : idsOfAlts T vs x = [] := by
  match vs, x with
  | [], x => exact nomatch x
  | [] :: _, .inl () => rfl
  | (_ :: _) :: _, .inl _ => have h : none = some w := h; cases h
  | f :: vs, .inr y =>
    match vs, y with
    | [], y => exact nomatch y
    | [] :: _, .inl () => cases f <;> rfl
    | (_ :: _) :: _, .inl _ => cases f <;> (have h : none = some w := h; cases h)
    | g :: _, .inr _ => cases f <;> cases g <;> (have h : none = some w := h; cases h)

theorem encNil_ids {vs : List (List Ty)} {x : (Ty.semAltsWith Dsl.base vs).1} {w : Wire}
    (h : encNil vs x = some w) : idsOfAlts T vs x = [] := by
  match vs, x with
  | [], x => exact nomatch x
  | [] :: _, .inl () => rfl
  | (_ :: _) :: _, .inl _ => have h : none = some w := h; cases h
  | f :: _, .inr _ => cases f <;> (have h : none = some w := h; cases h)


theorem perm_flatMap_forall2 {α : Type} {f : α → List IdV} {r : α → Tree Key → Prop}
    (hr : ∀ a te, r a te → te.leaves.Perm ((f a).map Key.id)) :
    {xs : List α} → {tes : List (Tree Key)} → Forall2 r xs tes →
      (Tree.leavess tes).Perm ((xs.flatMap f).map Key.id)
  | [], [], _ => by simp [Tree.leavess]
  | x :: xs, te :: tes, ⟨h, hs⟩ => by
    simp only [Tree.leavess, List.flatMap_cons, List.map_append]
    exact (hr x te h).append (perm_flatMap_forall2 hr hs)
  | [], _ :: _, h | _ :: _, [], h => h.elim

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- A value's tree holds its ids at its leaves, as often as its wire form names them. -/
theorem valTree_leaves : (t : Ty) → (x : t.den0) → (te : Tree Key) → valTree T t x = some te →
    te.leaves.Perm ((idsOf T t x).map Key.id)
  | .int, _, te, hx | .str, _, te, hx | .point .day, _, te, hx | .point .ms, _, te, hx => by
    simp only [valTree, Option.some.injEq] at hx; subst hx; simp [Tree.leaves, idsOf]
  | .id, _, te, hx => by
    simp only [valTree, Option.some.injEq] at hx; subst hx; exact .refl _
  | .list t, xs, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    simp only [Tree.leaves, idsOf]
    exact perm_flatMap_forall2 (fun a te h => valTree_leaves t a te h) (mapM_forall2 htes)
  | .bag t, xs, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    simp only [Tree.leaves, idsOf]
    exact (perm_flatMap_forall2 (fun a te h => valTree_leaves t a te h) (mapM_forall2 htes)).trans
      (((List.mergeSort_perm xs _).symm.flatMap_right _).map _)
  | .tuple ts, x, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    simp only [Tree.leaves, idsOf]
    exact valTrees_leaves ts x tes htes
  | .adt 0 _ vs, x, te, hx => by
    have e : valTree T (.adt 0 _ vs) x = (encBool vs x).bind litTree := rfl
    rw [e, Option.bind_eq_some_iff] at hx
    obtain ⟨w, hw, hl⟩ := hx
    obtain ⟨b, rfl⟩ := encBool_bool hw
    simp only [litTree, Option.some.injEq] at hl
    subst hl
    simp [Tree.leaves, idsOf, encBool_ids T hw]
  | .adt 1 _ vs, x, te, hx => by
    have e : valTree T (.adt 1 _ vs) x = (encNil vs x).bind litTree := rfl
    rw [e, Option.bind_eq_some_iff] at hx
    obtain ⟨w, hw, hl⟩ := hx
    obtain rfl := encNil_null hw
    simp only [litTree, Option.some.injEq] at hl
    subst hl
    simp [Tree.leaves, idsOf, encNil_ids T hw]
  | .adt (i + 2) _ vs, x, te, hx => by
    simp only [idsOf]
    exact valAlts_leaves _ 0 vs x te hx
  | .table k v, x, te, hx => by
    simp only [valTree, Option.map_eq_some_iff] at hx
    obtain ⟨tes, htes, rfl⟩ := hx
    simp only [Tree.leaves, idsOf]
    refine (perm_flatMap_forall2 (f := fun (e : k.den0 × v.den0) => idsOf T k e.1 ++ idsOf T v e.2)
      (fun e te h => ?_) (mapM_forall2 htes)).trans (((List.mergeSort_perm x.1 _).symm.flatMap_right _).map _)
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨ta, ha, tb, hb, rfl⟩ := h
    simp only [Tree.leaves, Tree.leavess, List.append_nil, List.map_append]
    exact (valTree_leaves k e.1 ta ha).append (valTree_leaves v e.2 tb hb)
  | .fn .., _, _, hx | .param _, _, _, hx | .dsl .., _, _, hx => by simp [valTree] at hx
theorem valTrees_leaves : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (tes : List (Tree Key)) →
    valTrees T ts x = some tes → (Tree.leavess tes).Perm ((idsOfs T ts x).map Key.id)
  | [], (), tes, hx => by simp only [valTrees, Option.some.injEq] at hx; subst hx; simp [Tree.leavess, idsOfs]
  | t :: ts, (x, xs), tes, hx => by
    simp only [valTrees, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hx
    obtain ⟨te, h1, tes0, h2, rfl⟩ := hx
    simp only [Tree.leavess, idsOfs, List.map_append]
    exact (valTree_leaves t x te h1).append (valTrees_leaves ts xs tes0 h2)
theorem valAlts_leaves (decl : List Variant) : (k : Nat) → (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) →
    (te : Tree Key) → valAlts T decl k vs x = some te → te.leaves.Perm ((idsOfAlts T vs x).map Key.id)
  | _, [], x, _, _ => nomatch x
  | k, fs :: _, .inl x, te, hx => by
    simp only [valAlts, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
    obtain ⟨var, -, ts, hts, hx⟩ := hx
    split at hx
    case isFalse => simp at hx
    case isTrue =>
      simp only [Option.pure_def, Option.some.injEq] at hx
      subst hx
      simp only [Tree.leaves, Tree.leavess, List.nil_append, idsOfAlts]
      exact valTrees_leaves fs x ts hts
  | k, _ :: vs, .inr y, te, hx => by
    simp only [valAlts, idsOfAlts] at hx ⊢
    exact valAlts_leaves decl (k + 1) vs y te hx
end

end Same

section Names

theorem wireName_inj {a b : Nat} (h : s!"r{a}" = s!"r{b}") : a = b := by
  have h2 : ("r" ++ toString a).toList = ("r" ++ toString b).toList := by
    have := congrArg String.toList h
    simpa using this
  simp only [String.toList_append] at h2
  exact Nat.repr_injective (String.toList_injective (List.append_cancel_left h2))

theorem eq_of_nodup_map {α β γ : Type} {f : α → γ} {g : α → β} : {l : List α} → (l.map f).Nodup → ∀ {a c},
    a ∈ l → c ∈ l → f a = f c → g a = g c
  | x :: xs, h, a, c, ha, hc, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hc with hc' | hc'
    · rw [ha', hc']
    · subst ha'; exact absurd (he ▸ List.mem_map_of_mem hc') h.1
    · subst hc'; exact absurd (he.symm ▸ List.mem_map_of_mem ha') h.1
    · exact eq_of_nodup_map h.2 ha' hc' he

/-- The binding verify reads a trace with where the writer named its ids and wire ids: the writer's names. -/
def Names.bindOf (ns : Names) : Bind := ⟨ns.ids, ns.wires⟩

/-- The wire names `r1`, `r2`, ... the writer gives the first `n` requests it names. -/
def wireNames (n : Nat) : List String := (List.range n).map fun j => s!"r{j + 1}"

theorem wireNames_nodup (n : Nat) : (wireNames n).Nodup :=
  List.Pairwise.map _ (fun a b hab he => hab (by have := wireName_inj he; omega)) List.nodup_range

/-- What the writer's names keep beside `Names.Ok`: an id or wire id has one name, and wire names are `r1`, `r2`, ...
in order, so no two wire ids share one. -/
structure Names.Good (ns : Names) : Prop where
  ok : ns.Ok
  keys : (ns.ids.map (·.1)).Nodup
  wkeys : (ns.wires.map (·.1)).Nodup
  wnames : ns.wires.map (·.2) = wireNames ns.wires.length

/-- `ns'` names every id and wire id `ns` names as `ns` does, and avoids the same names. -/
structure Names.Sub (ns ns' : Names) : Prop where
  ids : ∀ p ∈ ns.ids, p ∈ ns'.ids
  wires : ∀ p ∈ ns.wires, p ∈ ns'.wires
  avoid : ns'.avoid = ns.avoid

theorem Names.Sub.refl (ns : Names) : ns.Sub ns := ⟨fun _ h => h, fun _ h => h, rfl⟩

theorem Names.Sub.trans {a b c : Names} (h : a.Sub b) (h' : b.Sub c) : a.Sub c :=
  ⟨fun p hp => h'.ids p (h.ids p hp), fun p hp => h'.wires p (h.wires p hp), h'.avoid.trans h.avoid⟩

theorem Names.Good.one {ns : Names} (h : ns.Good) : ns.bindOf.OneToOne where
  ids _ _ _ hs hs' := eq_of_nodup_map (g := Prod.snd) h.keys hs hs' rfl
  idNames _ _ _ hs hs' := eq_of_nodup_map (g := Prod.fst) h.ok.nodup hs hs' rfl
  wires _ _ _ hs hs' := eq_of_nodup_map (g := Prod.snd) h.wkeys hs hs' rfl
  wireNames _ _ _ hs hs' := eq_of_nodup_map (g := Prod.fst) (h.wnames ▸ wireNames_nodup _) hs hs' rfl

theorem Names.Good.id? {ns : Names} (h : ns.Good) {x : IdV} {s : String} (hx : (x, s) ∈ ns.ids) :
    ns.bindOf.id? s = some x := by
  simp only [Bind.id?, Bind.idOf, Names.bindOf]
  rw [find_pair hx fun y hy => h.one.idNames y x s hy hx]; rfl

theorem Names.Good.wire? {ns : Names} (h : ns.Good) {n : Nat} {s : String} (hn : (n, s) ∈ ns.wires) :
    ns.bindOf.wire? s = some n := by
  simp only [Bind.wire?, Names.bindOf]
  exact find_pair hn fun y hy => h.one.wireNames y n s hy hn

theorem Names.bindOne_ids (ns : Names) (x : IdV) : (ns.bindOne x).wires = ns.wires ∧ (ns.bindOne x).avoid = ns.avoid ∧
    ((ns.bindOne x).ids = ns.ids ∨ ns.ids.any (·.1 == x) = false ∧ ∃ n, (ns.bindOne x).ids = ns.ids ++ [(x, n)]) := by
  unfold Names.bindOne
  split
  · exact ⟨rfl, rfl, .inl rfl⟩
  · rename_i hx
    simp only [Bool.not_eq_true] at hx
    cases x with
    | named s =>
      dsimp only
      split
      · exact ⟨rfl, rfl, .inl rfl⟩
      · exact ⟨rfl, rfl, .inr ⟨hx, s, rfl⟩⟩
    | fresh => exact ⟨rfl, rfl, .inr ⟨hx, _, rfl⟩⟩

theorem Names.bindOne_good {ns : Names} (h : ns.Good) (x : IdV) :
    (ns.bindOne x).Good ∧ ns.Sub (ns.bindOne x) ∧ (ns.bindOne x).wires = ns.wires := by
  obtain ⟨hok, -, -⟩ := Names.bindOne_ok h.ok x
  obtain ⟨hw, hav, hi⟩ := Names.bindOne_ids ns x
  refine ⟨⟨hok, ?_, hw ▸ h.wkeys, hw ▸ h.wnames⟩, ⟨?_, fun _ hp => hw ▸ hp, hav⟩, hw⟩
  · rcases hi with hi | ⟨hx, n, hi⟩
    · rw [hi]; exact h.keys
    · rw [hi]
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨h.keys, List.nodup_cons.2 ⟨List.not_mem_nil, .nil⟩, fun a ha b hb => ?_⟩
      simp at hb; subst hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      intro he
      have : ns.ids.any (·.1 == b) = true := List.any_eq_true.2 ⟨p, hp, by simp [he]⟩
      rw [hx] at this; cases this
  · rcases hi with hi | ⟨-, n, hi⟩
    · rw [hi]; exact fun _ hp => hp
    · rw [hi]; exact fun _ hp => List.mem_append_left _ hp

theorem Names.bind_good : (xs : List IdV) → {ns : Names} → ns.Good →
    (ns.bind xs).Good ∧ ns.Sub (ns.bind xs) ∧ (ns.bind xs).wires = ns.wires
  | [], ns, h => ⟨h, .refl ns, rfl⟩
  | x :: xs, ns, h => by
    obtain ⟨h1, s1, w1⟩ := Names.bindOne_good h x
    obtain ⟨h2, s2, w2⟩ := Names.bind_good xs h1
    exact ⟨h2, s1.trans s2, w2.trans w1⟩

theorem Names.bind_append (ns : Names) (xs ys : List IdV) : ns.bind (xs ++ ys) = (ns.bind xs).bind ys := by
  simp [Names.bind, List.foldl_append]

/-- What binding adds: ids among `xs` that had no name, an outside id by its own name, which no id had. -/
theorem Names.bind_mem : (xs : List IdV) → (ns : Names) → ∀ p ∈ (ns.bind xs).ids, p ∈ ns.ids ∨
    (p.1 ∈ xs ∧ ns.ids.any (·.1 == p.1) = false ∧ ∀ s, p.1 = .named s → p.2 = s ∧ ns.taken s = false)
  | [], ns, p, hp => .inl hp
  | x :: xs, ns, p, hp => by
    have ih := Names.bind_mem xs (ns.bindOne x) p hp
    have grow : ∀ q ∈ ns.ids, q ∈ (ns.bindOne x).ids := fun q hq => by
      rcases (Names.bindOne_ids ns x).2.2 with hi | ⟨-, n, hi⟩
      · rw [hi]; exact hq
      · rw [hi]; exact List.mem_append_left _ hq
    have anyF : ∀ y, (ns.bindOne x).ids.any (·.1 == y) = false → ns.ids.any (·.1 == y) = false := fun y hy => by
      simp only [List.any_eq_false, beq_iff_eq] at hy ⊢; exact fun q hq => hy q (grow q hq)
    have takenF : ∀ s, (ns.bindOne x).taken s = false → ns.taken s = false := fun s hs => by
      simp only [Names.taken, List.any_eq_false, beq_iff_eq] at hs ⊢; exact fun q hq => hs q (grow q hq)
    rcases ih with ih | ⟨h1, h2, h3⟩
    · unfold Names.bindOne at ih
      split at ih
      · exact .inl ih
      · rename_i hx
        simp only [Bool.not_eq_true] at hx
        cases x with
        | named s =>
          dsimp only at ih
          split at ih
          · exact .inl ih
          · rename_i ht
            rcases List.mem_append.1 ih with ih | ih
            · exact .inl ih
            · simp only [List.mem_singleton] at ih; subst ih
              refine .inr ⟨List.mem_cons_self, hx, fun s' he => ?_⟩
              cases he; exact ⟨rfl, by simpa using ht⟩
        | fresh a b =>
          dsimp only at ih
          rcases List.mem_append.1 ih with ih | ih
          · exact .inl ih
          · simp only [List.mem_singleton] at ih; subst ih
            exact .inr ⟨List.mem_cons_self, hx, nofun⟩
    · exact .inr ⟨List.mem_cons_of_mem _ h1, anyF _ h2, fun s he => ⟨(h3 s he).1, takenF s (h3 s he).2⟩⟩

theorem Names.bind_names {ns : Names} (h : ns.Ok) {xs : List IdV} (hc : Covers ns.avoid xs) :
    ∀ x ∈ xs, ∃ n, (x, n) ∈ (ns.bind xs).ids := fun x hx => by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 ((Names.bind_ok h xs hc).2.2.2 x hx)
  exact ⟨n, lookup_mem hn⟩

theorem Names.wire_good {ns : Names} (h : ns.Good) (n : Nat) :
    (ns.wire n).1.Good ∧ ns.Sub (ns.wire n).1 ∧ (ns.wire n).1.ids = ns.ids ∧ (n, (ns.wire n).2) ∈ (ns.wire n).1.wires ∧
      ∀ p ∈ (ns.wire n).1.wires, p ∈ ns.wires ∨ p.1 = n := by
  unfold Names.wire
  split
  · rename_i w hw
    exact ⟨h, .refl _, rfl, lookup_mem hw, fun p hp => .inl hp⟩
  · rename_i hw
    dsimp only
    have hnot : n ∉ ns.wires.map (·.1) := fun hm => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      obtain ⟨c, hc⟩ := lookup_isSome hp
      rw [hc] at hw; cases hw
    refine ⟨⟨⟨h.ok.avoided, h.ok.named, h.ok.nodup⟩, h.keys, ?_, ?_⟩,
      ⟨fun _ hp => hp, fun _ hp => List.mem_append_left _ hp, rfl⟩, rfl,
      List.mem_append_right _ List.mem_cons_self, fun p hp => ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.2 ⟨h.wkeys, List.nodup_cons.2 ⟨List.not_mem_nil, .nil⟩,
        fun a ha b hb => by simp at hb; subst hb; exact fun he => hnot (he ▸ ha)⟩
    · simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_cons,
        List.length_nil, h.wnames, wireNames, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    · rcases List.mem_append.1 hp with hp | hp
      · exact .inl hp
      · simp at hp; exact .inr (by rw [hp])

/-- What `Bind.outside` adds: each outside id among `xs` by its own name. -/
theorem outside_mem : (xs : List IdV) → (b : Bind) → ∀ p ∈ (b.outside xs).ids,
    p ∈ b.ids ∨ ∃ s : Str, p = (.named s, s.1) ∧ IdV.named s ∈ xs
  | [], b, p, hp => .inl hp
  | x :: xs, b, p, hp => by
    simp only [Bind.outside, List.foldl_cons] at hp
    rcases outside_mem xs _ p hp with h | ⟨s, rfl, hs⟩
    · cases x with
      | named s =>
        dsimp only at h
        split at h
        · exact .inl h
        · rcases List.mem_append.1 h with h | h
          · exact .inl h
          · simp only [List.mem_singleton] at h; subst h; exact .inr ⟨s, rfl, List.mem_cons_self⟩
      | fresh => exact .inl h
    · exact .inr ⟨s, rfl, List.mem_cons_of_mem _ hs⟩

/-- `Bind.outside` names each outside id among `xs` by its own name, unless the id or the name is bound. -/
theorem outside_has : (xs : List IdV) → (b : Bind) → ∀ s : Str, IdV.named s ∈ xs →
    (IdV.named s, s.1) ∈ (b.outside xs).ids ∨ b.ids.any (·.1 == .named s) = true ∨ b.ids.any (·.2 == s.1) = true
  | x :: xs, b, s, hs => by
    simp only [Bind.outside, List.foldl_cons]
    have keep := fun (b' : Bind) => (Bind.outside_sub b' xs).1
    by_cases hx : x = .named s
    · subst hx
      dsimp only
      split
      · rename_i hb
        simp only [Bool.or_eq_true] at hb
        exact .inr hb
      · exact .inl (keep _ _ (List.mem_append_right _ List.mem_cons_self))
    · have hs' : IdV.named s ∈ xs := by
        rcases List.mem_cons.1 hs with h | h
        · exact absurd h.symm hx
        · exact h
      cases x with
      | fresh => exact outside_has xs b s hs'
      | named t =>
        have ht : t ≠ s := fun e => hx (by rw [e])
        dsimp only
        split
        · exact outside_has xs b s hs'
        · rcases outside_has xs { b with ids := b.ids ++ [(.named t, t.1)] } s hs' with ih | ih | ih
          · exact .inl ih
          · simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq,
              IdV.named.injEq] at ih
            exact .inr (.inl (by simpa using ih.resolve_right ht))
          · simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at ih
            exact .inr (.inr (by simpa using ih.resolve_right fun e => ht (Subtype.ext e)))

end Names

section Out
variable {T : List TypeDecl} {v : ServiceV}

/-- What writing out lines took the names from `ns` to `ns'`, where `K` are the keys the spec's expected lines show:
`ns'` grows `ns` one to one by names for keys among `K`, and names every key of `K`. -/
structure OutNames (ns ns' : Names) (K : List Key) : Prop where
  sub : ns.Sub ns'
  good : ns'.Good
  newIds : ∀ p ∈ ns'.ids, p ∈ ns.ids ∨ Key.id p.1 ∈ K
  newWires : ∀ p ∈ ns'.wires, p ∈ ns.wires ∨ Key.wire p.1 ∈ K
  covers : ∀ k ∈ K, ns'.bindOf.Binds k

theorem OutNames.refl {ns : Names} (h : ns.Good) : OutNames ns ns [] :=
  ⟨.refl ns, h, fun _ hp => .inl hp, fun _ hp => .inl hp, nofun⟩

theorem binds_mono {a b : Names} (h : a.Sub b) {k : Key} (hk : a.bindOf.Binds k) : b.bindOf.Binds k := by
  cases k with
  | id x => obtain ⟨s, hs⟩ := hk; exact ⟨s, h.ids _ hs⟩
  | wire n => obtain ⟨s, hs⟩ := hk; exact ⟨s, h.wires _ hs⟩

theorem OutNames.trans {a b c : Names} {K K' : List Key} (h : OutNames a b K) (h' : OutNames b c K') :
    OutNames a c (K ++ K') where
  sub := h.sub.trans h'.sub
  good := h'.good
  newIds p hp := by
    rcases h'.newIds p hp with hp | hp
    · rcases h.newIds p hp with hp | hp
      · exact .inl hp
      · exact .inr (List.mem_append_left _ hp)
    · exact .inr (List.mem_append_right _ hp)
  newWires p hp := by
    rcases h'.newWires p hp with hp | hp
    · rcases h.newWires p hp with hp | hp
      · exact .inl hp
      · exact .inr (List.mem_append_left _ hp)
    · exact .inr (List.mem_append_right _ hp)
  covers k hk := by
    rcases List.mem_append.1 hk with hk | hk
    · exact binds_mono h'.sub (h.covers k hk)
    · exact h'.covers k hk

theorem OutNames.congr {a b : Names} {K K' : List Key} (h : OutNames a b K) (hk : ∀ k, k ∈ K ↔ k ∈ K') :
    OutNames a b K' :=
  ⟨h.sub, h.good, fun p hp => (h.newIds p hp).imp_right (hk _).1, fun p hp => (h.newWires p hp).imp_right (hk _).1,
    fun k hm => h.covers k ((hk k).2 hm)⟩

/-- `β` names every id and wire id as `ns` does. -/
def Names.Fits (ns : Names) (β : Key → Name) : Prop :=
  (∀ p ∈ ns.ids, β (.id p.1) = .id p.2) ∧ ∀ p ∈ ns.wires, β (.wire p.1) = .wire p.2

theorem Names.Fits.of_sub {a b : Names} {β : Key → Name} (h : a.Sub b) (hb : b.Fits β) : a.Fits β :=
  ⟨fun p hp => hb.1 p (h.ids p hp), fun p hp => hb.2 p (h.wires p hp)⟩

theorem Names.Good.fits {ns : Names} (h : ns.Good) : ns.Fits ns.bindOf.name :=
  ⟨fun _ hp => Bind.name_id h.one hp, fun _ hp => Bind.name_wire h.one hp⟩

/-- A value written with names that grow `ns`, read back as the tree of a value the same up to order. -/
theorem enc_value {ns : Names} (hg : ns.Good) {t : Ty} {x x' : t.den0} (hs : Ty.Same t x x')
    (hc : Covers ns.avoid (idsOf T t x)) {w : Wire} (hw : (ns.enc T t x).2 = some w) :
    ∃ te' tl, valTree T t x' = some te' ∧ wireTree T t w = some tl ∧
      (∀ β, (ns.enc T t x).1.Fits β → Tree.Same (te'.map β) tl) ∧ OutNames ns (ns.enc T t x).1 te'.leaves ∧
      ∀ i ∈ idsOf T t x, Key.id i ∈ te'.leaves := by
  obtain ⟨g1, s1, w1⟩ := Names.bind_good (idsOf T t x) hg
  have fit : ∀ β, (ns.bind (idsOf T t x)).Fits β → ∀ i s, (ns.bind (idsOf T t x)).name i = some s →
      β (.id i) = .id s := fun β hβ i s h => hβ.1 (i, s) (lookup_mem h)
  obtain ⟨te, tl, h1, h2, -⟩ := enc_tree T _ _ (fit _ g1.fits) t x w hw
  obtain ⟨te', h1', hte⟩ := valTree_same T t x x' hs te h1
  have hperm : te'.leaves.Perm ((idsOf T t x).map Key.id) := (Tree.Same.leaves hte).symm.trans (valTree_leaves T t x te h1)
  refine ⟨te', tl, h1', h2, fun β hβ => ?_, ⟨s1, g1, fun p hp => ?_, fun p hp => .inl (w1 ▸ hp), fun k hk => ?_⟩,
    fun i hi => hperm.symm.mem_iff.1 (List.mem_map_of_mem hi)⟩
  · obtain ⟨te2, tl2, h3, h4, h5⟩ := enc_tree T _ _ (fit β hβ) t x w hw
    rw [h1] at h3; cases h3
    rw [h2] at h4; cases h4
    exact (Tree.Same.map β hte).symm.trans h5
  · rcases Names.bind_mem _ ns p hp with hp | ⟨hm, -, -⟩
    · exact .inl hp
    · exact .inr (hperm.symm.mem_iff.1 (List.mem_map_of_mem hm))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (hperm.mem_iff.1 hk)
    obtain ⟨n, hn⟩ := Names.bind_names hg.ok hc i hi
    exact ⟨n, hn⟩

end Out

section OutLines
variable {T : List TypeDecl} {v : ServiceV}

theorem enc_parts {ns ns1 : Names} {t : Ty} {x : t.den0} {f : Wire → Line} {l : Line}
    (h : ((ns.enc T t x).1, (ns.enc T t x).2.map f) = (ns1, some l)) :
    ns1 = (ns.enc T t x).1 ∧ ∃ w, (ns.enc T t x).2 = some w ∧ l = f w := by
  simp only [Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨rfl, w, hw, rfl⟩ := h
  exact ⟨rfl, w, hw, rfl⟩

theorem wireVal_rel_inv {R : PBij} {t : Ty} {x : t.den0} {w : WireVal} (h : WireVal.Rel R ⟨t, x⟩ w) :
    ∃ y, w = ⟨t, y⟩ ∧ Ty.rel0 R t x y := by
  cases h with
  | mk h => exact ⟨_, rfl, h⟩

theorem eventLine_reads {ns : Names} (hg : ns.Good) {t : Int} {ev ev' : v.event.den0} (hs : Ty.Same v.event ev ev')
    (hc : Covers ns.avoid (idsOf T v.event ev)) {ns1 : Names} {l : Line} (hw : eventLine T v t ns ev = (ns1, some l)) :
    OutNames ns ns1 (Expect.keys T v t (.applied ev')) ∧ (∀ β, ns1.Fits β → TreeW T v β t (.applied ev') l) ∧
      l.isIn = false ∧ ∀ k ∈ (idsOf T v.event ev).map Key.id, k ∈ Expect.keys T v t (.applied ev') := by
  simp only [eventLine] at hw
  obtain ⟨rfl, w, hw', rfl⟩ := enc_parts hw
  obtain ⟨te', tl, h1, h2, h3, h4, h5⟩ := enc_value hg hs hc hw'
  have hb : Expect.body T v (.applied ev') = some [te'] := by simp [Expect.body, h1]
  refine ⟨h4.congr fun k => by simp [keys_of hb, Tree.leavess], fun β hβ => treeW_of (bl := [tl]) hb rfl ?_ ⟨h3 β hβ, trivial⟩, rfl,
    fun k hk => ?_⟩
  · simp [Line.body, Expect.ty, h2]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
    simpa [keys_of hb, Tree.leavess] using h5 i hi

theorem sentLine_reads {ns : Names} (hg : ns.Good) {t : Int} {o o' : OutLine} (ho : OutLine.Rel Ren.refl o o')
    (hc : Covers ns.avoid (idsOf T o.input.1 o.input.2)) {ns1 : Names} {l : Line}
    (hw : sentLine T t ns o = (ns1, some l)) :
    OutNames ns ns1 (Expect.keys T v t (.sent o'.id o'.external o'.name o'.input)) ∧
      (∀ β, ns1.Fits β → TreeW T v β t (.sent o'.id o'.external o'.name o'.input) l) ∧ l.isIn = false ∧
      ∀ k ∈ Key.wire o.id :: (idsOf T o.input.1 o.input.2).map Key.id,
        k ∈ Expect.keys T v t (.sent o'.id o'.external o'.name o'.input) := by
  obtain ⟨oid, oext, oname, ⟨ty, x⟩⟩ := o
  obtain ⟨oid', oext', oname', w'⟩ := o'
  obtain ⟨hid, hext, hname, hin⟩ := ho
  have hid : oid = oid' := hid
  simp only at hid hext hname hin hc
  subst hid hext hname
  obtain ⟨x', rfl, hs⟩ := wireVal_rel_inv hin
  have hwg := Names.wire_good hg oid
  rcases hq : ns.wire oid with ⟨nsw, wn⟩
  rw [hq] at hwg
  obtain ⟨g1, s1, i1, hm1, n1⟩ := hwg
  simp only [sentLine, hq] at hw
  obtain ⟨rfl, w, hw', rfl⟩ := enc_parts hw
  obtain ⟨te', tl, h1, h2, h3, h4, h5⟩ := enc_value g1 hs (s1.avoid ▸ hc) hw'
  have hb : Expect.body T v (.sent oid oext oname ⟨ty, x'⟩) = some [.leaf (.wire oid), te'] := by
    simp [Expect.body, h1]
  have hwire : OutNames ns nsw [.wire oid] :=
    ⟨s1, g1, fun p hp => .inl (i1 ▸ hp), fun p hp => (n1 p hp).imp_right fun e => by simp [e],
      fun k hk => by simp at hk; subst hk; exact ⟨wn, hm1⟩⟩
  have hk5 : ∀ k ∈ Key.wire oid :: (idsOf T ty x).map Key.id,
      k ∈ Expect.keys T v t (.sent oid oext oname ⟨ty, x'⟩) := fun k hk => by
    rcases List.mem_cons.1 hk with rfl | hk
    · simp [keys_of hb, Tree.leavess, Tree.leaves]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
      simp [keys_of hb, Tree.leavess, Tree.leaves, h5 i hi]
  refine ⟨(hwire.trans h4).congr fun k => by simp [keys_of hb, Tree.leavess, Tree.leaves], fun β hβ => ?_, rfl, hk5⟩
  refine treeW_of (bl := [.leaf (.wire wn), tl]) hb rfl (by simp [Line.body, Expect.ty, h2]) ⟨?_, h3 β hβ, trivial⟩
  show Tree.Same (.leaf (β (.wire oid))) (.leaf (.wire wn))
  rw [hβ.2 (oid, wn) (h4.sub.wires _ hm1)]
  rfl

/-- The ids an answer's outcome shows. -/
def outcomeIds (T : List TypeDecl) : Outcome → List IdV
  | .answered ⟨t, x⟩ | .rejected ⟨t, x⟩ => idsOf T t x
  | _ => []

theorem answerLine_reads {ns : Names} (hg : ns.Good) {t : Int} {to : String} {o o' : Outcome}
    (hc : Covers ns.avoid (outcomeIds T o)) (ho : Outcome.Same o o') {ns1 : Names} {l : Line}
    (hw : answerLine T ns t to o = (ns1, some l)) :
    OutNames ns ns1 (Expect.keys T v t (.answered to o')) ∧
      (∀ β, ns1.Fits β → TreeW T v β t (.answered to o') l) ∧ l.isIn = false ∧
      ∀ k ∈ (outcomeIds T o).map Key.id, k ∈ Expect.keys T v t (.answered to o') := by
  match o, o', ho with
  | .accepted, .accepted, _ =>
    simp only [answerLine, Prod.mk.injEq, Option.some.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hb : Expect.body T v (.answered to .accepted) = some [] := rfl
    exact ⟨(OutNames.refl hg).congr fun k => by simp [keys_of hb, Tree.leavess],
      fun β _ => treeW_of hb rfl rfl trivial, rfl, by simp [outcomeIds]⟩
  | .invalid rs, .invalid rs', ho =>
    have ho : rs = rs' := ho
    subst ho
    simp only [answerLine, Prod.mk.injEq, Option.some.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hb : Expect.body T v (.answered to (.invalid rs)) = some [.bag (rs.map (.atom ∘ .bin))] := rfl
    have hm : rs.map (Tree.atom (α := Key) ∘ Erl.bin) = (rs.map Erl.bin).map Tree.atom := by simp
    refine ⟨(OutNames.refl hg).congr fun k => ?_, fun β _ => treeW_of hb rfl rfl ⟨?_, trivial⟩, rfl,
      by simp [outcomeIds]⟩
    · rw [keys_of hb]
      simp only [Tree.leavess, Tree.leaves, hm, leavess_atoms]
      simp
    · have e : (Tree.bag (rs.map (Tree.atom (α := Key) ∘ Erl.bin))).map β = .bag (rs.map (Tree.atom ∘ Erl.bin)) := by
        rw [hm]
        simp only [Tree.map, Tree.maps_eq, List.map_map]
        rfl
      rw [e]
      rfl
  | .answered ⟨ty, x⟩, .answered w', ho =>
    obtain ⟨x', rfl, hs⟩ := wireVal_rel_inv ho
    simp only [answerLine] at hw
    obtain ⟨rfl, w, hw', rfl⟩ := enc_parts hw
    obtain ⟨te', tl, h1, h2, h3, h4, h5⟩ := enc_value hg hs hc hw'
    have hb : Expect.body T v (.answered to (.answered ⟨ty, x'⟩)) = some [te'] := by simp [Expect.body, h1]
    refine ⟨h4.congr fun k => by simp [keys_of hb, Tree.leavess],
      fun β hβ => treeW_of (bl := [tl]) hb rfl (by simp [Line.body, Expect.ty, h2]) ⟨h3 β hβ, trivial⟩, rfl,
      fun k hk => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
    simpa [keys_of hb, Tree.leavess] using h5 i hi
  | .rejected ⟨ty, x⟩, .rejected w', ho =>
    obtain ⟨x', rfl, hs⟩ := wireVal_rel_inv ho
    simp only [answerLine] at hw
    obtain ⟨rfl, w, hw', rfl⟩ := enc_parts hw
    obtain ⟨te', tl, h1, h2, h3, h4, h5⟩ := enc_value hg hs hc hw'
    have hb : Expect.body T v (.answered to (.rejected ⟨ty, x'⟩)) = some [te'] := by simp [Expect.body, h1]
    refine ⟨h4.congr fun k => by simp [keys_of hb, Tree.leavess],
      fun β hβ => treeW_of (bl := [tl]) hb rfl (by simp [Line.body, Expect.ty, h2]) ⟨h3 β hβ, trivial⟩, rfl,
      fun k hk => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
    simpa [keys_of hb, Tree.leavess] using h5 i hi
  | .fault _, .fault _, _ => simp [answerLine] at hw

/-- Items written in order, each read as the spec's expected line it relates to, each item's keys `G` among the
expected lines'. -/
theorem writeAll_reads {α γ : Type} {f : Names → α → Names × Option Line} {E : γ → Expect v} {R : α → γ → Prop}
    {now : Int} {A : List String} {Cov : α → Prop} {G : α → List Key}
    (hf : ∀ ns a c ns1 l, ns.Good → ns.avoid = A → R a c → Cov a → f ns a = (ns1, some l) →
      OutNames ns ns1 (Expect.keys T v now (E c)) ∧ (∀ β, ns1.Fits β → TreeW T v β now (E c) l) ∧ l.isIn = false ∧
        ∀ k ∈ G a, k ∈ Expect.keys T v now (E c)) :
    {as : List α} → {cs : List γ} → Forall2 R as cs → (∀ a ∈ as, Cov a) → {ns ns' : Names} → ns.Good → ns.avoid = A →
      {ls : List Line} → writeAll f ns as = (ns', some ls) →
      OutNames ns ns' ((cs.map E).flatMap (Expect.keys T v now)) ∧
        (∀ β, ns'.Fits β → Forall2 (TreeW T v β now) (cs.map E) ls) ∧ (∀ l ∈ ls, l.isIn = false) ∧
        ∀ a ∈ as, ∀ k ∈ G a, k ∈ (cs.map E).flatMap (Expect.keys T v now)
  | [], [], _, _, ns, ns', hg, _, ls, hw => by
    simp only [writeAll, Prod.mk.injEq, Option.some.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨OutNames.refl hg, fun _ _ => trivial, nofun, nofun⟩
  | a :: as, c :: cs, ⟨hr, hrs⟩, hcov, ns, ns', hg, ha, ls, hw => by
    simp only [writeAll] at hw
    revert hw
    generalize hq : f ns a = q
    obtain ⟨ns1, l1⟩ := q
    cases l1 with
    | none => intro hw; simp at hw
    | some l =>
      intro hw
      obtain ⟨o1, lw1, in1, g1⟩ := hf ns a c ns1 l hg ha hr (hcov a List.mem_cons_self) hq
      dsimp only at hw
      rcases hq2 : writeAll f ns1 as with ⟨ns2, ls2⟩
      rw [hq2] at hw
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, ls2', rfl, rfl⟩ := hw
      obtain ⟨o2, lw2, in2, g2⟩ := writeAll_reads hf hrs (fun b hb => hcov b (List.mem_cons_of_mem _ hb)) o1.good
        (o1.sub.avoid.trans ha) hq2
      refine ⟨by simpa using o1.trans o2, fun β hβ => ⟨lw1 β (hβ.of_sub o2.sub), lw2 β hβ⟩, fun l' hl' => ?_,
        fun b hb k hk => ?_⟩
      · rcases List.mem_cons.1 hl' with rfl | hl'
        · exact in1
        · exact in2 l' hl'
      · simp only [List.map_cons, List.flatMap_cons, List.mem_append]
        rcases List.mem_cons.1 hb with rfl | hb
        · exact .inl (g1 k hk)
        · exact .inr (g2 b hb k hk)
  | [], _ :: _, h, _, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _, _ => h.elim

end OutLines

section Finish
variable {T : List TypeDecl} {v : ServiceV}

/-- The out lines written for a step's result read as the spec's expected lines for a result the same up to order,
and name every id and wire id the result shows. -/
theorem outLines_reads {ns : Names} (hg : ns.Good) {answerTo : Option String} {r r' : Result v} (hrs : ResultSame r r')
    (hans : answerTo = none → (∀ w, r.outcome ≠ .answered w) ∧ ∀ w, r.outcome ≠ .rejected w)
    (hcov : Covers ns.avoid (r.shownIds T)) {ns' : Names} {outs : List Line}
    (hw : outLines T v ns answerTo r = (ns', some outs)) :
    OutNames ns ns' ((expects v answerTo r').flatMap (Expect.keys T v r'.state.now)) ∧
      (∀ β, ns'.Fits β → Forall2 (TreeW T v β r'.state.now) (expects v answerTo r') outs) ∧
      (∀ l ∈ outs, l.isIn = false) ∧
      (∀ i ∈ r.shownIds T, Key.id i ∈ (expects v answerTo r').flatMap (Expect.keys T v r'.state.now)) ∧
      ∀ o ∈ r.out, Key.wire o.id ∈ (expects v answerTo r').flatMap (Expect.keys T v r'.state.now) := by
  obtain ⟨hst, hout, hev, hos⟩ := hrs
  have hnow : r.state.now = r'.state.now := hst.2.2.2.1
  have hcov' := hcov
  simp only [Result.shownIds] at hcov
  obtain ⟨hcov, hco⟩ := covers_append hcov
  obtain ⟨hca, hce⟩ := covers_append hcov
  have hsh : ∀ i ∈ r.shownIds T, i ∈ outcomeIds T r.outcome ∨ i ∈ r.events.flatMap (idsOf T v.event) ∨
      i ∈ r.out.flatMap fun o => idsOf T o.input.1 o.input.2 := fun i hi => by
    simp only [Result.shownIds, List.mem_append] at hi
    rcases hi with (hi | hi) | hi
    · exact .inl (by revert hi; cases r.outcome <;> simp [outcomeIds])
    · exact .inr (.inl hi)
    · exact .inr (.inr hi)
  -- The events' and the sent requests' lines, after the answer's.
  have rest : ∀ (ns1 : Names) (a : List Line) (Ea : List (Expect v)), ns1.Good → ns1.avoid = ns.avoid →
      OutNames ns ns1 (Ea.flatMap (Expect.keys T v r'.state.now)) →
      (∀ β, ns1.Fits β → Forall2 (TreeW T v β r'.state.now) Ea a) → (∀ l ∈ a, l.isIn = false) →
      (∀ i ∈ outcomeIds T r.outcome, Key.id i ∈ Ea.flatMap (Expect.keys T v r'.state.now)) →
      (match writeAll (eventLine T v r.state.now) ns1 r.events with
        | (ns, none) => (ns, none)
        | (ns, some evs) => let o := writeAll (sentLine T r.state.now) ns r.out; (o.1, o.2.map (a ++ evs ++ ·))) =
        (ns', some outs) →
      OutNames ns ns' ((Ea ++ r'.events.map Expect.applied ++
          r'.out.map fun (o : OutLine) => Expect.sent o.id o.external o.name o.input).flatMap (Expect.keys T v r'.state.now)) ∧
        (∀ β, ns'.Fits β → Forall2 (TreeW T v β r'.state.now) (Ea ++ r'.events.map Expect.applied ++
          r'.out.map fun (o : OutLine) => Expect.sent o.id o.external o.name o.input) outs) ∧ (∀ l ∈ outs, l.isIn = false) ∧
        (∀ i ∈ r.shownIds T, Key.id i ∈ (Ea ++ r'.events.map Expect.applied ++
          r'.out.map fun (o : OutLine) => Expect.sent o.id o.external o.name o.input).flatMap (Expect.keys T v r'.state.now)) ∧
        ∀ o ∈ r.out, Key.wire o.id ∈ (Ea ++ r'.events.map Expect.applied ++
          r'.out.map fun (o : OutLine) => Expect.sent o.id o.external o.name o.input).flatMap (Expect.keys T v r'.state.now) := by
    intro ns1 a Ea g1 av1 o1 lw1 in1 ga hw
    rcases he : writeAll (eventLine T v r.state.now) ns1 r.events with ⟨ns2, evs⟩
    rw [he] at hw
    cases evs with
    | none => simp at hw
    | some evs =>
      dsimp only at hw
      rcases hs : writeAll (sentLine T r.state.now) ns2 r.out with ⟨ns3, os⟩
      rw [hs] at hw
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, os, rfl, rfl⟩ := hw
      obtain ⟨o2, lw2, in2, g2⟩ := writeAll_reads (R := Ty.Same v.event) (E := Expect.applied) (now := r'.state.now)
        (Cov := fun ev => Covers ns.avoid (idsOf T v.event ev)) (G := fun ev => (idsOf T v.event ev).map Key.id)
        (fun ns a c ns1 l hg ha hr hc hw => by
          rw [hnow] at hw; exact eventLine_reads hg hr (ha ▸ hc) hw)
        hev (fun ev hev' => covers_flatMap hce ev hev') g1 av1 he
      obtain ⟨o3, lw3, in3, g3⟩ := writeAll_reads (v := v) (R := OutLine.Rel Ren.refl)
        (E := fun (o : OutLine) => Expect.sent o.id o.external o.name o.input) (now := r'.state.now)
        (Cov := fun (o : OutLine) => Covers ns.avoid (idsOf T o.input.1 o.input.2))
        (G := fun (o : OutLine) => Key.wire o.id :: (idsOf T o.input.1 o.input.2).map Key.id)
        (fun ns a c ns1 l hg ha hr hc hw => by
          rw [hnow] at hw; exact sentLine_reads (v := v) hg hr (ha ▸ hc) hw)
        hos (fun o ho => covers_flatMap hco o ho) o2.good (o2.sub.avoid.trans av1) hs
      have hK : ∀ k, (k ∈ Ea.flatMap (Expect.keys T v r'.state.now) ∨
          k ∈ (r'.events.map Expect.applied).flatMap (Expect.keys T v r'.state.now) ∨
          k ∈ (r'.out.map fun (o : OutLine) => Expect.sent o.id o.external o.name o.input).flatMap
            (Expect.keys T v r'.state.now)) →
          k ∈ (Ea ++ r'.events.map Expect.applied ++ r'.out.map fun (o : OutLine) =>
            Expect.sent o.id o.external o.name o.input).flatMap (Expect.keys T v r'.state.now) := fun k hk => by
        simp only [List.flatMap_append, List.mem_append]
        rcases hk with hk | hk | hk
        · exact .inl (.inl hk)
        · exact .inl (.inr hk)
        · exact .inr hk
      refine ⟨((o1.trans o2).trans o3).congr fun k => by simp [List.flatMap_append], fun β hβ => ?_, fun l hl => ?_,
        fun i hi => ?_, fun o ho => hK _ (.inr (.inr (g3 o ho _ List.mem_cons_self)))⟩
      · have h3 := lw3 β hβ
        have h2 := lw2 β (hβ.of_sub o3.sub)
        have h1 := lw1 β (hβ.of_sub (o2.sub.trans o3.sub))
        exact forall2_append (forall2_append h1 h2) h3
      · simp only [List.mem_append] at hl
        rcases hl with (hl | hl) | hl
        · exact in1 l hl
        · exact in2 l hl
        · exact in3 l hl
      · rcases hsh i hi with hi | hi | hi
        · exact hK _ (.inl (ga i hi))
        · obtain ⟨ev, hev', hi⟩ := List.mem_flatMap.1 hi
          exact hK _ (.inr (.inl (g2 ev hev' _ (List.mem_map_of_mem hi))))
        · obtain ⟨o, ho, hi⟩ := List.mem_flatMap.1 hi
          exact hK _ (.inr (.inr (g3 o ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hi)))))
  unfold outLines at hw
  unfold expects
  cases answerTo with
  | none =>
    have hno : outcomeIds T r.outcome = [] := by
      obtain ⟨h1, h2⟩ := hans rfl
      revert h1 h2; cases r.outcome <;> simp [outcomeIds]
    exact rest ns [] [] hg rfl (OutNames.refl hg) (fun _ _ => trivial) nofun (by simp [hno]) hw
  | some to =>
    dsimp only at hw
    rcases ha : answerLine T ns r.state.now to r.outcome with ⟨ns1, l⟩
    rw [ha] at hw
    cases l with
    | none => simp at hw
    | some l =>
      dsimp only at hw
      rw [hnow] at ha
      have hca' : Covers ns.avoid (outcomeIds T r.outcome) := fun s hs => hca s (by
        revert hs; cases r.outcome <;> simp [outcomeIds])
      obtain ⟨o1, lw1, in1, ga⟩ := answerLine_reads hg hca' hout ha
      exact rest ns1 [l] [.answered to r'.outcome] o1.good o1.sub.avoid (o1.congr fun k => by simp)
        (fun β hβ => ⟨lw1 β hβ, trivial⟩) (fun l' hl' => by simp at hl'; subst hl'; exact in1)
        (fun i hi => by simpa using ga _ (List.mem_map_of_mem hi)) hw

end Finish

section InLine
variable {T : List TypeDecl} {v : ServiceV}

theorem finish'_reads {run : Run v} (hg : run.names.Good) {input : Input v} {inLines : List Line}
    {answerTo : Option String} {k : Nat} {w' : Run v} (hw : run.finish' T v input inLines answerTo k = .ok w')
    {r' : Result v} (hrs : ResultSame (step T v run.state input) r')
    (hans : answerTo = none → (∀ w, (step T v run.state input).outcome ≠ .answered w) ∧
      ∀ w, (step T v run.state input).outcome ≠ .rejected w)
    (hcov : Covers run.names.avoid ((step T v run.state input).shownIds T)) :
    ∃ outs, w'.lines = run.lines ++ inLines ++ outs ∧ w'.state = (step T v run.state input).state ∧
      w'.requests = run.requests ∧
      OutNames run.names w'.names ((expects v answerTo r').flatMap (Expect.keys T v r'.state.now)) ∧
      (∀ β, w'.names.Fits β → Forall2 (TreeW T v β r'.state.now) (expects v answerTo r') outs) ∧
      (∀ l ∈ outs, l.isIn = false) ∧
      (∀ i ∈ (step T v run.state input).shownIds T,
        Key.id i ∈ (expects v answerTo r').flatMap (Expect.keys T v r'.state.now)) ∧
      ∀ o ∈ (step T v run.state input).out,
        Key.wire o.id ∈ (expects v answerTo r').flatMap (Expect.keys T v r'.state.now) := by
  unfold Run.finish' at hw
  revert hw hrs hans hcov
  generalize step T v run.state input = r
  intro hw hrs hans hcov
  rcases hq : outLines T v run.names answerTo r with ⟨ns, outs⟩
  cases ho : r.outcome with
  | fault f => simp only [ho] at hw; cases hw
  | _ =>
    all_goals
      simp only [ho, hq] at hw
      cases outs with
      | none => simp at hw
      | some outs =>
        simp only [pure, Except.pure, Except.ok.injEq] at hw
        subst hw
        obtain ⟨o1, lw1, in1, g1, g2⟩ := outLines_reads hg hrs hans hcov hq
        exact ⟨outs, rfl, rfl, rfl, o1, lw1, in1, g1, g2⟩

theorem dec_same {t : Ty} (ho : t.ordered T = true) (hc : t.comparable = true) {name : IdV → Option String}
    {lookup : String → Option IdV} (hid : ∀ n s, name n = some s → lookup s = some n) {x : t.den0} {w : Wire}
    (h : enc T name t x = some w) : ∃ y, dec T lookup t w = some y ∧ Ty.Same t x y := by
  obtain ⟨y, hy, he⟩ := dec_enc T name lookup hid t ho x w h
  exact ⟨y, hy, Ty.same_of_deq hc ((Ty.erl_iff T t ho x y).2 he.symm)⟩

-- Any naming fits here: which ids a value holds does not depend on their names.
set_option linter.tazuna.silentDefault false in
/-- A value and one the same up to order hold the same ids, where the value has a wire form. -/
theorem ids_iff {t : Ty} {name : IdV → Option String} {x x' : t.den0} {w : Wire} (h : enc T name t x = some w)
    (hs : Ty.Same t x x') (i : IdV) : i ∈ idsOf T t x ↔ i ∈ idsOf T t x' := by
  obtain ⟨te, -, h1, -, -⟩ := enc_tree T name (fun k => match k with
    | .id i => .id ((name i).getD "")
    | .wire _ => .wire "") (fun i s hs => by simp [hs]) t x w h
  obtain ⟨te', h1', hte⟩ := valTree_same T t x x' hs te h1
  have hp := ((valTree_leaves T t x te h1).symm.trans (Tree.Same.leaves hte)).trans (valTree_leaves T t x' te' h1')
  have := hp.mem_iff (a := Key.id i)
  simpa using this

theorem id?_of_bind {ns : Names} (hg : ns.Good) {xs : List IdV}
    (hk : ∀ i ∈ xs, (∀ s, i ≠ .named s) → ∃ n, (i, n) ∈ ns.ids) :
    ∀ n s, (n, s) ∈ (ns.bind xs).ids → ns.bindOf.id? s = some n := by
  intro n s hm
  rcases Names.bind_mem xs ns _ hm with hm | ⟨hx, hb, hnamed⟩
  · exact hg.id? hm
  · cases n with
    | named s' =>
      obtain ⟨hs, ht⟩ := hnamed s' rfl
      simp only at hs
      subst hs
      simp only [Bind.id?, Bind.idOf, Names.bindOf]
      rw [find_none fun y hy => by
        have : ns.taken s'.1 = true := List.any_eq_true.2 ⟨_, hy, by simp⟩
        rw [ht] at this; cases this]
      simp [Str.of?_val]
    | fresh a b =>
      obtain ⟨m, hm'⟩ := hk _ hx nofun
      have : ns.ids.any (·.1 == IdV.fresh a b) = true := List.any_eq_true.2 ⟨_, hm', by simp⟩
      simp only at hb
      rw [hb] at this; cases this

theorem finIdx_eq {α : Type} {xs : List α} {p : α → Bool} {i : Fin xs.length} (hi : p (xs.get i) = true)
    (hu : ∀ j, p (xs.get j) = true → j = i) : finIdx xs p = some i := by
  unfold finIdx
  cases h : (List.finRange xs.length).find? fun i => p (xs.get i) with
  | none =>
    have := List.find?_eq_none.1 h i (List.mem_finRange i)
    exact absurd hi this
  | some j => exact congrArg some (hu j (by simpa using List.find?_some h))

theorem finIdx_none {α : Type} {xs : List α} {p : α → Bool} (h : ∀ j, p (xs.get j) = false) : finIdx xs p = none := by
  unfold finIdx
  exact List.find?_eq_none.2 fun j _ => by rw [h j]; simp

theorem wire_of_mem {ns : Names} (hg : ns.Good) {n : Nat} {s : String} (h : (n, s) ∈ ns.wires) : ns.wire n = (ns, s) := by
  obtain ⟨c, hc⟩ := lookup_isSome h
  have : c = s := hg.one.wires n c s (lookup_mem hc) h
  subst this
  simp [Names.wire, hc]

theorem nodup_get_inj {α β : Type} {f : α → β} {xs : List α} (h : (xs.map f).Nodup) {i j : Fin xs.length}
    (he : f (xs.get j) = f (xs.get i)) : j = i := by
  have := (List.Nodup.getElem_inj h (hi := by simp; exact j.2) (hj := by simp; exact i.2)).1 (by simpa using he)
  exact Fin.ext this

end InLine

section Answer
variable {T : List TypeDecl} {v : ServiceV}

theorem wire_ordered {P : List AnySite} {E : List AnyEffectSite} (chk : Smt.Checked P E T v) {t : Ty}
    (ht : t ∈ v.wireTys) : t.ordered T = true ∧ t.comparable = true := by
  have h := chk.wire
  simp only [ServiceV.wireOk, List.all_eq_true, Bool.and_eq_true] at h
  exact ⟨(h t ht).1.2, (h t ht).2⟩

/-- A step from a state of the invariant keeps it, and its out lines carry values of wire types, which are
comparable. -/
theorem inv_out {P : List AnySite} {E : List AnyEffectSite} (chk : Smt.Checked P E T v) {s : State v} (hs : Inv P s) (x : Input v) :
    Inv P (step T v s x).state ∧ OutComparable v (step T v s x) := by
  have hc : ∀ t ∈ v.wireTys, t.comparable = true := fun t ht => (wire_ordered chk ht).2
  refine ⟨step_inv T chk.reach s hs x, hc _ (List.mem_cons_of_mem _ List.mem_cons_self),
    fun w hw => hc _ ((step_outcome_tys T s x).1 w hw), fun w hw => hc _ ((step_outcome_tys T s x).2 w hw),
    fun o ho => ?_⟩
  obtain ⟨p, hp, rfl⟩ := step_outsWait T s x o ho
  exact hc _ (atShapes_tys ((step_inv T chk.reach s hs x).shaped p hp)).1

theorem answerWire_names (ns : Names) (o : Ty) : (rj : Option Ty) → (x : (answerTy o rj).den0) →
    (ns.answerWire T o rj x).1 = ns.bind (idsOf T (answerTy o rj) x)
  | some _, .inl (x, ()) => by simp [Names.answerWire, Names.enc, answerTy, Ty.result, idsOf, idsOfAlts, idsOfs]
  | some _, .inr (.inl (x, ())) => by simp [Names.answerWire, Names.enc, answerTy, Ty.result, idsOf, idsOfAlts, idsOfs]
  | none, x => by simp [Names.answerWire, Names.enc, answerTy]

/-- An answer written reads back, with `decAnswer`, as an answer the same up to order. -/
theorem answerWire_dec {ns : Names} {lookup : String → Option IdV} {o : Ty} (ho : o.ordered T = true)
    (hoc : o.comparable = true) : (rj : Option Ty) → (∀ j, rj = some j → j.ordered T = true ∧ j.comparable = true) →
    (x : (answerTy o rj).den0) → {a : Except Wire Wire} → (ns.answerWire T o rj x).2 = some a →
    (∀ n s, (ns.answerWire T o rj x).1.name n = some s → lookup s = some n) →
    ∃ x', (∀ b : Bind, b.id? = lookup → decAnswer T b o rj a = some x') ∧ Ty.Same (answerTy o rj) x x' ∧
      ∀ i, i ∈ idsOf T (answerTy o rj) x ↔ i ∈ idsOf T (answerTy o rj) x'
  | some j, hj, .inl (x, ()), a, ha, hid => by
    simp only [Names.answerWire, Option.map_eq_some_iff] at ha hid
    obtain ⟨w, hw, rfl⟩ := ha
    obtain ⟨y, hy, hs⟩ := dec_same ho hoc hid hw
    refine ⟨.inl (y, ()), fun b hb => by simp only [decAnswer, hb, hy]; rfl, ⟨hs, trivial⟩, fun i => ?_⟩
    simp only [answerTy, Ty.result, idsOf, idsOfAlts, idsOfs, List.append_nil]
    exact ids_iff hw hs i
  | some j, hj, .inr (.inl (x, ())), a, ha, hid => by
    simp only [Names.answerWire, Option.map_eq_some_iff] at ha hid
    obtain ⟨w, hw, rfl⟩ := ha
    obtain ⟨y, hy, hs⟩ := dec_same (hj j rfl).1 (hj j rfl).2 hid hw
    refine ⟨.inr (.inl (y, ())), fun b hb => by simp only [decAnswer, hb, hy]; rfl, ⟨hs, trivial⟩, fun i => ?_⟩
    simp only [answerTy, Ty.result, idsOf, idsOfAlts, idsOfs, List.append_nil]
    exact ids_iff hw hs i
  | none, _, x, a, ha, hid => by
    simp only [Names.answerWire, Option.map_eq_some_iff] at ha hid
    obtain ⟨w, hw, rfl⟩ := ha
    obtain ⟨y, hy, hs⟩ := dec_same ho hoc hid hw
    exact ⟨y, fun b hb => by simp only [decAnswer, hb, hy]; rfl, hs, ids_iff hw hs⟩

theorem request_types {R : PBij} {e : Ty} {a b : RequestV e} (h : RequestV.Rel R a b) :
    b.output = a.output ∧ b.rejection = a.rejection := by
  cases h; exact ⟨rfl, rfl⟩

/-- A step on an input that is no request answers nothing. -/
theorem noAnswer (s : State v) (x : Input v) (hc : ∀ i c y, x ≠ .command i c y) (hq : ∀ i c y, x ≠ .query i c y) :
    (∀ w, (step T v s x).outcome ≠ .answered w) ∧ ∀ w, (step T v s x).outcome ≠ .rejected w := by
  cases x with
  | command i c y => exact absurd rfl (hc i c y)
  | query i c y => exact absurd rfl (hq i c y)
  | answer to w =>
    obtain ⟨t, value⟩ := w
    simp only [step]
    split
    · exact ⟨nofun, nofun⟩
    · split
      · exact ⟨nofun, nofun⟩
      · split
        · exact ⟨nofun, nofun⟩
        · exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩
  | event i value => exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩
  | clock t =>
    simp only [step]
    split
    · exact ⟨nofun, nofun⟩
    · split
      · exact ⟨nofun, nofun⟩
      · exact ⟨fun w h => absurd h (finish_answers T).1, fun w h => absurd h (finish_answers T).2⟩

end Answer

section InLineReads
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

theorem enc_eq {ns ns1 : Names} {t : Ty} {x : t.den0} {c : Option Wire} (h : ns.enc T t x = (ns1, c)) :
    ns1 = ns.bind (idsOf T t x) ∧ c = enc T ns1.name t x := by
  simp only [Names.enc, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- An in line the writer writes for an input reads back, under the writer's names before it, as an input the same up
to order: verify's step on it is the writer's step up to order. -/
theorem inLine_reads (chk : Smt.Checked P E T v) {w : Run v} {s : State v} (hg : w.names.Good)
    (hsame : StateSame w.state s) (hinv : Inv P w.state) (hpend : ∀ p ∈ w.state.pending, ∃ n, (p.id, n) ∈ w.names.wires)
    (x : Input v) (hk : ∀ i ∈ x.ids T, (∀ s, i ≠ .named s) → ∃ n, (i, n) ∈ w.names.ids)
    {k : Nat} {w' : Run v} (hw : w.input T v k x = .ok w') :
    ∃ inLine x' answerTo, ∃ run1 : Run v, run1.state = w.state ∧ run1.lines = w.lines ∧
      run1.names = w.names.bind (x.ids T) ∧ run1.finish' T v x [inLine] answerTo k = .ok w' ∧ inLine.isIn = true ∧
      readIn T v s w.names.bindOf inLine = .ok (x', answerTo, x'.ids T) ∧ Input.Same x x' ∧
      (answerTo = none → (∀ w', (step T v w.state x).outcome ≠ .answered w') ∧
        ∀ w', (step T v w.state x).outcome ≠ .rejected w') ∧
      ∀ i, i ∈ x.ids T ↔ i ∈ x'.ids T := by
  have hid := id?_of_bind hg hk
  have hnow : w.state.now = s.now := hsame.2.2.2.1
  have hreq := chk.requests
  rw [List.nodup_append] at hreq
  -- What the in line holds is written with names that grow to the names after it, which verify's binding reads.
  have named : ∀ {ns : Names}, w.names.bind (x.ids T) = ns → ∀ {ns' : Names}, ns'.Sub ns →
      ∀ n s, ns'.name n = some s → w.names.bindOf.id? s = some n := fun hn _ hs n s h =>
    hid n s (hn ▸ hs.ids _ (lookup_mem h))
  cases x with
  | command i caller input =>
    unfold Run.input Run.input.request at hw
    rcases h1 : w.names.enc T v.caller caller with ⟨ns1, c⟩
    rcases h2 : ns1.enc T (v.commands.get i).input input with ⟨ns2, iw⟩
    simp only [h1, h2] at hw
    obtain ⟨e1, rfl⟩ := enc_eq h1
    obtain ⟨e2, rfl⟩ := enc_eq h2
    have hn2 : w.names.bind (Input.ids T (.command i caller input)) = ns2 := by
      simp only [Input.ids, Names.bind_append, ← e1, e2]
    have hs12 : ns1.Sub ns2 := e2 ▸ (Names.bind_good (idsOf T _ input) (e1 ▸ (Names.bind_good _ hg).1)).2.1
    rcases hc : enc T ns1.name v.caller caller with _ | c
    · simp only [hc] at hw; cases hw
    rcases hi : enc T ns2.name (v.commands.get i).input input with _ | iw
    · simp only [hc, hi] at hw; cases hw
    simp only [hc, hi] at hw
    obtain ⟨caller', hdc, hsc⟩ := dec_same (wire_ordered chk caller_wire).1 (wire_ordered chk caller_wire).2
      (named hn2 hs12) hc
    obtain ⟨input', hdi, hsi⟩ := dec_same (wire_ordered chk (command_wire i)).1
      (wire_ordered chk (command_wire i)).2 (named hn2 (.refl _)) hi
    have hfin : finIdx v.commands (·.name == (v.commands.get i).name) = some i :=
      finIdx_eq (by simp) fun j hj => nodup_get_inj hreq.1 (by simpa using hj)
    refine ⟨.request w.state.now (toString (w.requests + 1)) (v.commands.get i).name c iw, .command i caller' input',
      some (toString (w.requests + 1)), { w with names := ns2, requests := w.requests + 1 }, rfl, rfl, hn2.symm, hw,
      rfl, ?_, .command i hsc hsi, nofun, fun j => ?_⟩
    · simp only [List.get_eq_getElem] at hfin hdi
      simp [readIn, hnow, hdc, hfin, hdi, Input.ids]; rfl
    · simp only [Input.ids, List.mem_append]
      rw [ids_iff hc hsc, ids_iff hi hsi]
  | query i caller input =>
    unfold Run.input Run.input.request at hw
    rcases h1 : w.names.enc T v.caller caller with ⟨ns1, c⟩
    rcases h2 : ns1.enc T (v.queries.get i).input input with ⟨ns2, iw⟩
    simp only [h1, h2] at hw
    obtain ⟨e1, rfl⟩ := enc_eq h1
    obtain ⟨e2, rfl⟩ := enc_eq h2
    have hn2 : w.names.bind (Input.ids T (.query i caller input)) = ns2 := by
      simp only [Input.ids, Names.bind_append, ← e1, e2]
    have hs12 : ns1.Sub ns2 := e2 ▸ (Names.bind_good (idsOf T _ input) (e1 ▸ (Names.bind_good _ hg).1)).2.1
    rcases hc : enc T ns1.name v.caller caller with _ | c
    · simp only [hc] at hw; cases hw
    rcases hi : enc T ns2.name (v.queries.get i).input input with _ | iw
    · simp only [hc, hi] at hw; cases hw
    simp only [hc, hi] at hw
    obtain ⟨caller', hdc, hsc⟩ := dec_same (wire_ordered chk caller_wire).1 (wire_ordered chk caller_wire).2
      (named hn2 hs12) hc
    obtain ⟨input', hdi, hsi⟩ := dec_same (wire_ordered chk (query_wire i)).1
      (wire_ordered chk (query_wire i)).2 (named hn2 (.refl _)) hi
    have hfin : finIdx v.queries (·.name == (v.queries.get i).name) = some i :=
      finIdx_eq (by simp) fun j hj => nodup_get_inj hreq.2.1 (by simpa using hj)
    have hnc : finIdx v.commands (·.name == (v.queries.get i).name) = none := finIdx_none fun j => by
      have := hreq.2.2 _ (List.mem_map_of_mem (List.get_mem v.commands j)) _
        (List.mem_map_of_mem (List.get_mem v.queries i))
      simpa using this
    refine ⟨.request w.state.now (toString (w.requests + 1)) (v.queries.get i).name c iw, .query i caller' input',
      some (toString (w.requests + 1)), { w with names := ns2, requests := w.requests + 1 }, rfl, rfl, hn2.symm, hw,
      rfl, ?_, .query i hsc hsi, nofun, fun j => ?_⟩
    · simp only [List.get_eq_getElem] at hfin hdi hnc
      simp [readIn, hnow, hdc, hfin, hnc, hdi, Input.ids]; rfl
    · simp only [Input.ids, List.mem_append]
      rw [ids_iff hc hsc, ids_iff hi hsi]
  | answer to wv =>
    obtain ⟨ty, value⟩ := wv
    unfold Run.input at hw
    rcases hp : w.state.pending.find? (·.id == to) with _ | p
    · simp only [hp] at hw; cases hw
    simp only [hp] at hw
    rcases hty : Ty.same ty (answerTy p.request.output p.request.rejection) with _ | hpl
    · simp only [hty] at hw; cases hw
    simp only [hty] at hw
    obtain ⟨h⟩ := hpl
    subst h
    have hpm := List.mem_of_find?_eq_some hp
    have hpid : p.id = to := by simpa using List.find?_some hp
    obtain ⟨wn, hwn⟩ := hpend p hpm
    rw [wire_of_mem hg hwn] at hw
    simp only at hw
    rcases ha : w.names.answerWire T p.request.output p.request.rejection value with ⟨ns1, a⟩
    simp only [ha] at hw
    rcases a with _ | a
    · cases hw
    simp only at hw
    have hn1 : w.names.bind (Input.ids T (Input.answer (v := v) to ⟨_, value⟩)) = ns1 := by
      have := answerWire_names (T := T) w.names p.request.output p.request.rejection value
      rw [ha] at this
      simp only [Input.ids]
      exact this.symm
    obtain ⟨-, hso, hsj⟩ := atShapes_tys (hinv.shaped p hpm)
    obtain ⟨x', hdec, hsx, hids⟩ := answerWire_dec (ns := w.names) (lookup := w.names.bindOf.id?)
      (wire_ordered chk hso).1 (wire_ordered chk hso).2 p.request.rejection
      (fun j hj => wire_ordered chk (hsj j hj)) value (by rw [ha]) (by rw [ha]; exact named hn1 (.refl _))
    have hf := forall2_find? (p := (·.id == to)) (q := (·.id == to)) (fun a b h => by
      have : a.id = b.id := h.1
      rw [this]) hsame.2.2.1
    rw [hp] at hf
    revert hf
    generalize hq : s.pending.find? (·.id == to) = q
    intro hf
    cases hf with
    | some hr =>
      rename_i p'
      obtain ⟨hout, hrej⟩ := request_types hr.2.2.2
      obtain ⟨pid', psnd', pext', ⟨n', i', o', rj', val', hold', onA'⟩⟩ := p'
      simp only at hout hrej
      subst hout hrej
      refine ⟨.answer w.state.now wn a, .answer to ⟨_, x'⟩, none, { w with names := ns1 }, rfl, rfl, hn1.symm, hw, rfl,
        ?_, .answer to (.mk hsx), fun _ => noAnswer w.state _ (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h),
        fun i => hids i⟩
      have hwire : w.names.bindOf.wire? wn = some to := hpid ▸ hg.wire? hwn
      simp [readIn, hnow, hwire, hq, hdec _ rfl, Input.ids]
  | event i value =>
    unfold Run.input at hw
    rcases h1 : w.names.enc T (v.subscribes.get i).event value with ⟨ns1, ew⟩
    simp only [h1] at hw
    obtain ⟨e1, rfl⟩ := enc_eq h1
    have hn1 : w.names.bind (Input.ids T (.event i value)) = ns1 := by simp only [Input.ids, e1]
    rcases he : enc T ns1.name (v.subscribes.get i).event value with _ | ew
    · simp only [he] at hw; cases hw
    simp only [he] at hw
    obtain ⟨value', hde, hse⟩ := dec_same (wire_ordered chk (subscribe_wire i)).1
      (wire_ordered chk (subscribe_wire i)).2 (named hn1 (.refl _)) he
    have hfin : finIdx v.subscribes (fun sub => sub.source == (v.subscribes.get i).source &&
        sub.name == (v.subscribes.get i).name) = some i :=
      finIdx_eq (by simp) fun j hj => nodup_get_inj (f := fun sub => (sub.source, sub.name)) chk.subscriptions
        (by simp only [Bool.and_eq_true, beq_iff_eq] at hj; simpa using hj)
    refine ⟨.event w.state.now (v.subscribes.get i).source (v.subscribes.get i).name ew, .event i value', none,
      { w with names := ns1 }, rfl, rfl, hn1.symm, hw, rfl, ?_, .event i hse,
      fun _ => noAnswer w.state _ (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h), fun j => ?_⟩
    · simp only [List.get_eq_getElem] at hfin hde
      simp [readIn, hnow, hfin, hde, Input.ids]
    · simp only [Input.ids]
      exact ids_iff he hse j
  | clock t =>
    simp only [Run.input] at hw
    exact ⟨.clock t, .clock t, none, w, rfl, rfl, by simp [Input.ids, Names.bind], hw, rfl, rfl, .clock (t := t) rfl,
      fun _ => noAnswer w.state _ (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h), fun i => Iff.rfl⟩

end InLineReads

section Sim
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

/-- What the writer's run and verify's replay keep between inputs: verify's state is the writer's up to the order bags
and tables are stored in, verify's binding is the writer's names, every request that waits has a wire name, and every
id an out line showed has a name. -/
structure Sim (P : List AnySite) (A : List String) (w : Run v) (s : State v) (seen : List IdV) : Prop where
  good : w.names.Good
  avoid : w.names.avoid = A
  same : StateSame w.state s
  inv : Inv P w.state
  pend : ∀ p ∈ w.state.pending, ∃ n, (p.id, n) ∈ w.names.wires
  seen : ∀ i ∈ seen, ∃ n, (i, n) ∈ w.names.ids
  vinv : Inv P s

/-- One input the writer writes reads as the spec under its names: its in line reads as the writer's input up to
order, the binding grows to the writer's names after its out lines, which write the spec's expected lines. -/
theorem input_reads (chk : Smt.Checked P E T v) (ho : Ordered T v) {A : List String} {w : Run v} {s : State v}
    {seen : List IdV} (hsim : Sim P A w s seen) (x : Input v) (hnf : ∀ f, (step T v w.state x).outcome ≠ .fault f)
    (hknown : ∀ i ∈ x.ids T, i.Known seen) (hcov : Covers A (x.ids T ++ (step T v w.state x).shownIds T)) {k : Nat}
    {w' : Run v} (hw : w.input T v k x = .ok w') :
    ∃ inLine outs r' ids es, w'.lines = w.lines ++ inLine :: outs ∧ inLine.isIn = true ∧
      (∀ l ∈ outs, l.isIn = false) ∧ (∀ n, stepIn T v s w.names.bindOf n inLine = .ok (r', ids, es)) ∧
      Grows (w.names.bindOf.outside ids) (es.flatMap (Expect.keys T v r'.state.now)) w'.names.bindOf ∧
      Forall2 (TreeW T v w'.names.bindOf.name r'.state.now) es outs ∧ w'.state = (step T v w.state x).state ∧
      Sim P A w' r'.state (seen ++ (step T v w.state x).shownIds T) := by
  obtain ⟨hcx, hcs⟩ := covers_append hcov
  have hk : ∀ i ∈ x.ids T, (∀ s, i ≠ .named s) → ∃ n, (i, n) ∈ w.names.ids := fun i hi hn => by
    have := hknown i hi
    cases i with
    | named s => exact absurd rfl (hn s)
    | fresh a b => exact hsim.seen _ this
  obtain ⟨inLine, x', answerTo, run1, hst, hli, hna, hfin, hin, hread, hsame, hans, hids⟩ :=
    inLine_reads chk hsim.good hsim.same hsim.inv hsim.pend x hk hw
  have hrs := step_same ho hsim.same hsame
  obtain ⟨g1, s1, ww1⟩ := Names.bind_good (x.ids T) hsim.good
  have hcx' : Covers w.names.avoid (x.ids T) := hsim.avoid ▸ hcx
  rw [← hna] at g1 s1 ww1
  obtain ⟨outs, hlines, hstate, -, on, lw, hout, hshown, hwires⟩ := finish'_reads g1 hfin (hst ▸ hrs) (hst ▸ hans)
    (by rw [hst, s1.avoid, hsim.avoid]; exact hcs)
  have hnf' : ∀ f, (step T v s x').outcome ≠ .fault f := fun f hf => by
    have h := hrs.2.1
    rw [hf] at h
    cases hc : (step T v w.state x).outcome <;> rw [hc] at h
    case fault g => exact hnf g hc
    all_goals exact h.elim
  have hstep : ∀ n, stepIn T v s w.names.bindOf n inLine = .ok (step T v s x', x'.ids T, expects v answerTo (step T v s x')) :=
    fun n => by
      unfold stepIn
      rw [hread]
      dsimp only
      split
      · rename_i f hf; exact absurd hf (hnf' f)
      · rfl
  have hst' : (step T v run1.state x) = step T v w.state x := by rw [hst]
  refine ⟨inLine, outs, step T v s x', x'.ids T, expects v answerTo (step T v s x'), by simp [hlines, hli], hin, hout,
    hstep, ⟨?_, ?_, ?_, ?_, on.covers, on.good.one⟩, lw _ on.good.fits, by rw [hstate, hst'], ⟨on.good, ?_, ?_, ?_, ?_, ?_, step_inv T chk.reach s hsim.vinv x'⟩⟩
  · intro p hp
    rcases outside_mem _ _ p hp with hp | ⟨s', rfl, hs'⟩
    · exact on.sub.ids _ (s1.ids _ hp)
    · obtain ⟨n, hn⟩ := Names.bind_names hsim.good.ok hcx' _ ((hids _).2 hs')
      rw [← hna] at hn
      have : n = s'.1 := g1.ok.named s' n hn
      subst this
      exact on.sub.ids _ hn
  · intro p hp
    rw [(Bind.outside_sub _ _).2] at hp
    exact on.sub.wires _ (s1.wires _ hp)
  · intro p hp
    rcases on.newIds p hp with hp | hp
    · rw [hna] at hp
      rcases Names.bind_mem _ _ p hp with hp | ⟨hx, hb, hnamed⟩
      · exact .inl ((Bind.outside_sub _ _).1 _ hp)
      · obtain ⟨i, n⟩ := p
        cases i with
        | fresh a b =>
          obtain ⟨m, hm⟩ := hk _ hx nofun
          have : w.names.ids.any (·.1 == IdV.fresh a b) = true := List.any_eq_true.2 ⟨_, hm, by simp⟩
          simp only at hb
          rw [hb] at this; cases this
        | named s' =>
          obtain ⟨hn, ht⟩ := hnamed s' rfl
          simp only at hn
          subst n
          rcases outside_has _ w.names.bindOf s' ((hids _).1 hx) with h | h | h
          · exact .inl h
          · simp only at hb; simp only [Names.bindOf] at h; rw [hb] at h; cases h
          · simp only [Names.taken] at ht; simp only [Names.bindOf] at h; rw [ht] at h; cases h
    · exact .inr hp
  · intro p hp
    rcases on.newWires p hp with hp | hp
    · rw [(Bind.outside_sub _ _).2]; exact .inl (show p ∈ w.names.wires by rw [← ww1]; exact hp)
    · exact .inr hp
  · rw [on.sub.avoid, s1.avoid, hsim.avoid]
  · rw [hstate, hst']; exact hrs.1
  · rw [hstate, hst']; exact step_inv T chk.reach w.state hsim.inv x
  · intro p hp
    rw [hstate, hst'] at hp
    obtain ⟨base, ps, hsub, hpend, hout'⟩ := step_sent T w.state x
    rw [hpend] at hp
    rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨n, hn⟩ := hsim.pend p (hsub.subset hp)
      exact ⟨n, on.sub.wires _ (s1.wires _ hn)⟩
    · have hl : p.line ∈ (step T v run1.state x).out := by rw [hst', hout']; exact List.mem_map_of_mem hp
      exact on.covers _ (hwires _ hl)
  · intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · obtain ⟨n, hn⟩ := hsim.seen i hi
      exact ⟨n, on.sub.ids _ (s1.ids _ hn)⟩
    · exact on.covers _ (hshown i (hst' ▸ hi))

end Sim

section Run
variable {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}

variable (T) in
/-- Whether each input carries only ids from outside and ids an earlier step's out lines showed, after `seen`: what
`Step.ShownRun` says of a model's run, checked. -/
def knownRun : List IdV → State v → List (Input v) → Bool
  | _, _, [] => true
  | seen, s, x :: xs => (x.ids T).all (fun
      | .named _ => true
      | i => seen.contains i) && knownRun (seen ++ (step T v s x).shownIds T) (step T v s x).state xs

/-- Lines numbered from line `m + 2` on, as verify numbers a trace's lines after its header. -/
def numberFrom (m : Nat) (L : List Line) : List (Nat × Line) := (L.zipIdx m).map fun (l, j) => (j + 2, l)

theorem numberFrom_append (m : Nat) (A B : List Line) :
    numberFrom m (A ++ B) = numberFrom m A ++ numberFrom (m + A.length) B := by
  simp [numberFrom, List.zipIdx_append]

theorem window_of {outs : List Line} (hout : ∀ l ∈ outs, l.isIn = false) {rest : List (Nat × Line)}
    (hr : ∀ p ∈ rest.head?, p.2.isIn = true) (m : Nat) :
    window (numberFrom m outs ++ rest) = outs ∧ afterWindow (numberFrom m outs ++ rest) = rest := by
  have hA : ∀ p ∈ numberFrom m outs, (!p.2.isIn) = true := fun p hp => by
    simp only [numberFrom, List.mem_map] at hp
    obtain ⟨⟨l, j⟩, hl, rfl⟩ := hp
    have : l ∈ outs := by
      rw [← List.zipIdx_map_fst m outs]; exact List.mem_map_of_mem (f := Prod.fst) hl
    simp [hout l this]
  have hB : ∀ p ∈ rest.head?, (!p.2.isIn) = false := fun p hp => by simp [hr p hp]
  have tw : (numberFrom m outs ++ rest).takeWhile (!·.2.isIn) = numberFrom m outs := by
    rw [List.takeWhile_append_of_pos hA]
    cases rest with
    | nil => simp
    | cons q qs => simp [hB q rfl]
  have dw : (numberFrom m outs ++ rest).dropWhile (!·.2.isIn) = rest := by
    rw [List.dropWhile_append_of_pos hA]
    cases rest with
    | nil => simp
    | cons q qs => simp [hB q rfl]
  refine ⟨?_, dw⟩
  unfold window
  rw [tw]
  simp only [numberFrom, List.map_map]
  conv => rhs; rw [← List.zipIdx_map_fst m outs]
  rfl

theorem known_of {seen : List IdV} {s : State v} {x : Input v} {xs : List (Input v)}
    (h : knownRun T seen s (x :: xs) = true) :
    (∀ i ∈ x.ids T, i.Known seen) ∧ knownRun T (seen ++ (step T v s x).shownIds T) (step T v s x).state xs = true := by
  simp only [knownRun, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i hi => ?_, h.2⟩
  have := h.1 i hi
  cases i with
  | named _ => trivial
  | fresh a b => simpa [IdV.Known] using this

/-- The lines the writer adds for the inputs from `w` read as the spec from verify's state `s` under the writer's
names. -/
theorem run_reads (chk : Smt.Checked P E T v) (ho : Ordered T v) {A : List String} :
    (xs : List (Input v)) → (w : Run v) → (k : Nat) → (s : State v) → (seen : List IdV) → Sim P A w s seen →
    Covers A (xs.flatMap (·.ids T) ++ (Tazuna.Ir.run T v w.state xs).2.flatMap (·.shownIds T)) →
    knownRun T seen w.state xs = true → NoFaultRun T w.state xs →
    ∀ r, xs.foldlM (fun (run, k) x => do pure (← run.input T v (k + 1) x, k + 1)) (w, k) = .ok r →
    ∃ L, r.1.lines = w.lines ++ L ∧ (∀ l ∈ L.head?, l.isIn = true) ∧
      ∀ m, Reads T v s w.names.bindOf (numberFrom m L)
  | [], w, k, s, seen, _, _, _, _, r, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, nofun, fun m => .nil _ _⟩
  | x :: xs, w, k, s, seen, hsim, hcov, hkn, ⟨hnf, hrest⟩, r, h => by
    rw [List.foldlM_cons] at h
    rcases hw : w.input T v (k + 1) x with e | w'
    · simp [hw, bind, Except.bind] at h
    simp only [hw, bind, Except.bind, pure, Except.pure] at h
    obtain ⟨hknown, hkn'⟩ := known_of hkn
    have hc1 : Covers A (x.ids T ++ (step T v w.state x).shownIds T) := fun s hs => hcov s (by
      simp only [List.flatMap_cons, Tazuna.Ir.run, List.mem_append] at hs ⊢
      rcases hs with hs | hs
      · exact .inl (.inl hs)
      · exact .inr (.inl hs))
    obtain ⟨inLine, outs, r', ids, es, hl, hin, hout, hstep, hgrow, hlw, hstate, hsim'⟩ :=
      input_reads chk ho hsim x hnf hknown hc1 hw
    have hc2 : Covers A (xs.flatMap (·.ids T) ++ (Tazuna.Ir.run T v w'.state xs).2.flatMap (·.shownIds T)) :=
      fun s hs => hcov s (by
        rw [hstate] at hs
        simp only [List.flatMap_cons, Tazuna.Ir.run, List.mem_append] at hs ⊢
        rcases hs with hs | hs
        · exact .inl (.inr hs)
        · exact .inr (.inr hs))
    obtain ⟨L, hL, hhead, hreads⟩ := run_reads chk ho xs w' (k + 1) r'.state _ hsim' hc2 (hstate ▸ hkn')
      (hstate ▸ hrest) r h
    refine ⟨inLine :: outs ++ L, by simp [hL, hl], by simp [hin], fun m => ?_⟩
    have e : numberFrom m (inLine :: outs ++ L) =
        (m + 2, inLine) :: (numberFrom (m + 1) outs ++ numberFrom (m + 1 + outs.length) L) := by
      rw [List.cons_append, ← numberFrom_append]
      simp [numberFrom, List.zipIdx_cons]
    rw [e]
    have hr : ∀ p ∈ (numberFrom (m + 1 + outs.length) L).head?, p.2.isIn = true := fun p hp => by
      cases L with
      | nil => simp [numberFrom] at hp
      | cons l L => simp [numberFrom, List.zipIdx_cons] at hp; subst hp; exact hhead l rfl
    obtain ⟨hwin, haft⟩ := window_of hout hr (m + 1)
    obtain ⟨x0, a0, hr0, hes0⟩ := stepIn_ok T v (hstep 0)
    have hoc := (inv_out chk hsim.vinv x0).2
    rw [← hr0] at hoc
    refine .cons (hstep (m + 2)) hgrow ?_ (by rw [haft]; exact hreads _)
    rw [hwin]
    exact Multi.imp_mem (fun e he l _ h => lineW_of_treeW hgrow.one
      (fun k hk => hgrow.covers k (List.mem_flatMap.2 ⟨e, he, hk⟩)) (expects_comparable v hoc a0 e (hes0 ▸ he)) h)
      (Multi.of_forall2 hlw)

theorem init_same (hc : v.records.comparable = true) : StateSame (State.init v) (State.init v) := by
  refine ⟨Ty.rel0_refl _ hc _, ?_, trivial, rfl, rfl, rfl⟩
  show Machines.Same (PerMachine.ofFn (fun _ => []) v.machines) (PerMachine.ofFn (fun _ => []) v.machines)
  generalize v.machines = ms
  induction ms with
  | nil => trivial
  | cons m ms ih => exact ⟨trivial, ih⟩

/-- A trace generate writes for a run from the initial state reads as the spec, so verify replays it as passed unless
it runs out of tries (`replay_iff`): where no step of the run faults and each input carries only ids from outside and
ids an earlier out line showed. -/
theorem traceOf_reads (chk : Smt.Checked P E T v) (ho : Ordered T v) {xs : List (Input v)}
    (hnf : NoFaultRun T (State.init v) xs) (hkn : knownRun T [] (State.init v) xs = true) {tr : TraceFile}
    (h : traceOf T v xs = .ok tr) : Reads T v (State.init v) {} tr.numbered := by
  unfold traceOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i r hf
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hsim : Sim P (outsideNames T (State.init v) xs)
      ({ state := State.init v, names := { avoid := outsideNames T (State.init v) xs } } : Run v) (State.init v) [] :=
    ⟨⟨Names.ok_avoid _, .nil, .nil, rfl⟩, rfl, init_same chk.recordsComparable, init_inv, by simp [State.init], nofun, init_inv⟩
  obtain ⟨L, hL, -, hreads⟩ := run_reads chk ho xs _ 0 _ [] hsim (fun s hs => contains_outside hs) hkn hnf r hf
  simp only [List.nil_append] at hL
  have := hreads 0
  rw [← hL] at this
  exact this

end Run

/-- Verify's oracle comparison: unless it runs out of tries (`tryCap`), it reads a trace as passed exactly when some
binding reads it: one bijection of the spec's ids and wire ids with the trace's names, grown window by window, under
which every in line reads as the spec's input and every window's out lines decode, in some order, to the spec's out
lines. -/
theorem replay_iff {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (chk : Smt.Checked P E T v) (lines : List (Nat × Line)) (h : ∀ k, replay T v lines ≠ .limit k) :
    replay T v lines = .passed ↔ Reads T v (State.init v) {} lines :=
  replay_iff_of T v (I := Inv P) (fun _ x hs => inv_out chk hs x) init_inv lines h

end Tazuna.Trace
