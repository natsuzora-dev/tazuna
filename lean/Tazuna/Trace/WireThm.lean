import Tazuna.Trace.DateThm
import Tazuna.Trace.Wire

/-! Reading back what was written gives the value written, up to `==` (`dec_enc`): for every ordered type, every value
with a wire form, and every binding of ids whose reading undoes its writing. A bag or table reads back in the canonical
order it was written in, so the value read is the one written as Gleam's `==` sees it: the same Erlang term. -/

namespace Tazuna.Trace

open Tazuna.Ir

-- One mutual block proves the theorems together, so each sees the binding hypothesis only one of them uses.
set_option linter.unusedSectionVars false

theorem mapM_rel {α β γ : Type} {f : α → Option β} {g : β → Option α} {e : α → γ}
    (h : ∀ x w, f x = some w → ∃ y, g w = some y ∧ e y = e x) :
    ∀ (xs : List α) (ws : List β), xs.mapM f = some ws → ∃ ys, ws.mapM g = some ys ∧ ys.map e = xs.map e
  | [], ws, hx => by simp at hx; subst hx; exact ⟨[], rfl, rfl⟩
  | x :: xs, ws, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx
    obtain ⟨w, hw, ws', hws', rfl⟩ := hx
    obtain ⟨y, hy, he⟩ := h x w hw
    obtain ⟨ys, hys, hes⟩ := mapM_rel h xs ws' hws'
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys], by simp [he, hes]⟩

theorem lookup_zip : (keys : List String) → (ws : List Wire) → keys.Nodup →
    ∀ k w, (k, w) ∈ keys.zip ws → (keys.zip ws).lookup k = some w
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | key :: keys, w0 :: ws, hnd, k, w, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    simp only [List.nodup_cons] at hnd
    simp only [List.zip_cons_cons, List.lookup_cons]
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · have hk' : k ≠ key := fun e => hnd.1 (e ▸ (List.of_mem_zip h).1)
      have hk : (k == key) = false := by simp [hk']
      simp only [hk]; exact lookup_zip keys ws hnd.2 k w h

-- `encBool` and `encNil` have overlapping patterns, so each case unfolds them by definition.
theorem decBool_encBool (vs : List (List Ty)) (x : (Ty.semAltsWith Dsl.base vs).1) (w : Wire)
    (h : encBool vs x = some w) : decBool vs w = some x := by
  match vs, x with
  | [], x => exact nomatch x
  | [] :: _, .inl () => have h : some (Wire.bool true) = some w := h; cases h; rfl
  | (_ :: _) :: _, .inl _ => have h : none = some w := h; cases h
  | f :: vs, .inr y =>
    match vs, y with
    | [], y => exact nomatch y
    | [] :: _, .inl () => cases f <;> (have h : some (Wire.bool false) = some w := h; cases h; rfl)
    | (_ :: _) :: _, .inl _ => cases f <;> (have h : none = some w := h; cases h)
    | g :: _, .inr _ => cases f <;> cases g <;> (have h : none = some w := h; cases h)

theorem decNil_encNil (vs : List (List Ty)) (x : (Ty.semAltsWith Dsl.base vs).1) (w : Wire)
    (h : encNil vs x = some w) : decNil vs w = some x := by
  match vs, x with
  | [], x => exact nomatch x
  | [] :: _, .inl () => have h : some Wire.null = some w := h; cases h; rfl
  | (_ :: _) :: _, .inl _ => have h : none = some w := h; cases h
  | f :: _, .inr _ => cases f <;> (have h : none = some w := h; cases h)

section
variable (T : List TypeDecl) (name : IdV → Option String) (lookup : String → Option IdV)
  (hid : ∀ n s, name n = some s → lookup s = some n)
include hid

attribute [local instance] lexOrd

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
theorem dec_enc : (t : Ty) → t.ordered T = true → (x : t.den0) → (w : Wire) → enc T name t x = some w →
    ∃ y, dec T lookup t w = some y ∧ Ty.erl T t y = Ty.erl T t x
  | .int, _, x, w, h => by simp only [enc, Option.some.injEq] at h; subst h; exact ⟨x, rfl, rfl⟩
  | .str, _, x, w, h => by simp only [enc, Option.some.injEq] at h; subst h; exact ⟨x, Str.of?_val x, rfl⟩
  | .list t, ho, xs, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨ys, hys, he⟩ := mapM_rel (dec_enc t ho) xs ws hws
    exact ⟨ys, hys, by simp only [Ty.erl]; rw [he]⟩
  | .bag t, ho, xs, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨ys, hys, he⟩ := mapM_rel (dec_enc t ho) _ ws hws
    refine ⟨ys, hys, ?_⟩
    simp only [Ty.erl]
    rw [he, Erl.list.injEq, Erl.sort_eq_iff]
    exact (List.mergeSort_perm xs _).map _
  | .tuple ts, ho, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    obtain ⟨y, hy, he⟩ := decs_encs ts ho x ws hws
    exact ⟨y, hy, by simp only [Ty.erl]; rw [he]⟩
  | .adt 0 _ vs, _, x, w, h => ⟨x, decBool_encBool vs x w h, rfl⟩
  | .adt 1 _ vs, _, x, w, h => ⟨x, decNil_encNil vs x w h, rfl⟩
  | .adt (i + 2) _ vs, ho, x, w, h => by
    simp only [Ty.ordered, Bool.and_eq_true] at ho
    obtain ⟨kvs, tag, k, rfl, htag, hk, _, y, hdec, he⟩ := decAlts_encAlts vs _ 0 ho.2 x w h
    refine ⟨y, ?_, he⟩
    show (do
      let decl := (T[i + 2]?.map (·.variants)).getD []
      let .str tag ← kvs.lookup "tag" | none
      let k ← decl.findIdx? (·.name == tag)
      decAlts T lookup decl kvs k 0 vs) = some y
    rw [htag]
    show (List.findIdx? (fun (var : Variant) => var.name == tag) ((T[i + 2]?.map (·.variants)).getD []) >>= fun k => decAlts T lookup ((T[i + 2]?.map (·.variants)).getD []) kvs k 0 vs) = some y
    rw [hk]
    exact hdec
  | .table k v, ho, x, w, h => by
    simp only [Ty.ordered, Bool.and_eq_true] at ho
    rw [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    let P : k.den0 × v.den0 → Erl × Erl := fun e => (Ty.erl T k e.1, Ty.erl T v e.2)
    obtain ⟨ps, hps, he⟩ := mapM_rel (e := P) (g := fun
        | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
        | _ => none) (by
      intro ⟨a, b⟩ w hw
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
      obtain ⟨wa, ha, wb, hb, rfl⟩ := hw
      obtain ⟨a', ha', ea⟩ := dec_enc k ho.1 a wa ha
      obtain ⟨b', hb', eb⟩ := dec_enc v ho.2 b wb hb
      exact ⟨(a', b'), by simp [ha', hb'], by simp [P, ea, eb]⟩) _ ws hws
    have hperm : (ps.map P).Perm (x.1.map P) := he ▸ (List.mergeSort_perm x.1 _).map P
    have hu : KeysUnique (Ty.semWith Dsl.base k).2 ps := by
      rw [keysUnique_iff (Ty.erl_iff T k ho.1)]
      have hx := (keysUnique_iff (Ty.erl_iff T k ho.1) x.1).1 x.2
      have e2 : (ps.map fun e => Ty.erl T k e.1) = (ps.map P).map (·.1) := by simp [P]
      have e3 : (x.1.map fun e => Ty.erl T k e.1) = (x.1.map P).map (·.1) := by simp [P]
      rw [e2]; rw [e3] at hx
      exact hx.perm (hperm.map _).symm
    refine ⟨⟨ps, hu⟩, ?_, ?_⟩
    · show (do
        let pairs ← ws.mapM fun
          | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
          | _ => none
        if h : KeysUnique (Ty.semWith Dsl.base k).2 pairs then some ⟨pairs, h⟩ else none) =
        (some ⟨ps, hu⟩ : Option (Ty.table k v).den0)
      rw [hps]
      simp [hu]
    · have hs : Erl.sort (ps.map P) = Erl.sort (x.1.map P) := (Erl.sort_eq_iff _ _).2 hperm
      simp only [Ty.erl]
      simp only [P] at hs
      rw [hs]
  | .date, _, x, w, h => by
    simp only [enc, Option.some.injEq] at h
    subst h
    exact ⟨x, DateThm.parse_render x, rfl⟩
  | .id, _, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨x, hid x s hs, rfl⟩
  | .fn .., _, _, _, h => by simp [enc] at h
  | .param _, _, _, _, h => by simp [enc] at h
  | .dsl .., _, _, _, h => by simp [enc] at h
theorem decs_encs : (ts : List Ty) → Ty.ordereds T ts = true → (x : (Ty.semsWith Dsl.base ts).1) → (ws : List Wire) →
    encs T name ts x = some ws → ∃ y, decs T lookup ts ws = some y ∧ Ty.erls T ts y = Ty.erls T ts x
  | [], _, (), ws, h => by simp only [encs, Option.some.injEq] at h; subst h; exact ⟨(), rfl, rfl⟩
  | t :: ts, ho, (x, xs), ws, h => by
    simp only [Ty.ordereds, Bool.and_eq_true] at ho
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    obtain ⟨y, hy, e⟩ := dec_enc t ho.1 x w hw
    obtain ⟨ys, hys, es⟩ := decs_encs ts ho.2 xs ws' hws'
    exact ⟨(y, ys), by simp [decs, hy, hys], by simp [Ty.erls, e, es]⟩
theorem decFields_encs : (fs : List Ty) → Ty.ordereds T fs = true → (x : (Ty.semsWith Dsl.base fs).1) →
    (ws : List Wire) → encs T name fs x = some ws → ∀ (keys : List String) (kvs : List (String × Wire)),
    keys.length = ws.length → (∀ k w, (k, w) ∈ keys.zip ws → kvs.lookup k = some w) →
    ∃ y, decFields T lookup kvs fs keys = some y ∧ Ty.erls T fs y = Ty.erls T fs x
  | [], _, (), ws, h, keys, kvs, hlen, _ => by
    simp only [encs, Option.some.injEq] at h; subst h
    cases keys with
    | nil => exact ⟨(), rfl, rfl⟩
    | cons _ _ => simp at hlen
  | f :: fs, ho, (x, xs), ws, h, keys, kvs, hlen, hkv => by
    simp only [Ty.ordereds, Bool.and_eq_true] at ho
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    cases keys with
    | nil => simp at hlen
    | cons key keys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hhead := hkv key w (by simp)
      have hrest : ∀ k w, (k, w) ∈ keys.zip ws' → kvs.lookup k = some w := fun k w hm =>
        hkv k w (by simp [hm])
      obtain ⟨y, hy, e⟩ := dec_enc f ho.1 x w hw
      obtain ⟨ys, hys, es⟩ := decFields_encs fs ho.2 xs ws' hws' keys kvs hlen hrest
      exact ⟨(y, ys), by simp [decFields, hhead, hy, hys], by simp [Ty.erls, e, es]⟩
theorem decAlts_encAlts : (vs : List (List Ty)) → (decl : List Variant) → (j : Nat) → Ty.orderedss T vs = true →
    (x : (Ty.semAltsWith Dsl.base vs).1) → (w : Wire) → encAlts T name decl j vs x = some w →
    ∃ kvs tag k, w = .obj kvs ∧ kvs.lookup "tag" = some (.str tag) ∧ decl.findIdx? (·.name == tag) = some k ∧
      j ≤ k ∧ ∃ y, decAlts T lookup decl kvs k j vs = some y ∧ Ty.erlAlts T decl j vs y = Ty.erlAlts T decl j vs x
  | [], _, _, _, x, _, _ => nomatch x
  | fs :: _, decl, j, ho, .inl x, w, h => by
    simp only [Ty.orderedss, Bool.and_eq_true] at ho
    simp only [encAlts, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨var, hvar, ws, hws, h⟩ := h
    split at h
    case isFalse => simp at h
    case isTrue hw =>
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp only [writable, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hw
      obtain ⟨⟨⟨hidx, hnd⟩, htag⟩, hlen⟩ := hw
      refine ⟨_, var.name, j, rfl, by simp, hidx, Nat.le_refl j, ?_⟩
      have hnotag : "tag" ∉ fieldKeys var.fields := by simpa using htag
      have hkv : ∀ k w, (k, w) ∈ (fieldKeys var.fields).zip ws →
          List.lookup k (("tag", Wire.str var.name) :: (fieldKeys var.fields).zip ws) = some w := by
        intro k w hm
        have hk' : k ≠ "tag" := fun e => hnotag (e ▸ (List.of_mem_zip hm).1)
        have hk : (k == "tag") = false := by simp [hk']
        simp only [List.lookup_cons, hk]; exact lookup_zip _ ws hnd k w hm
      obtain ⟨y, hy, e⟩ := decFields_encs fs ho.1 x ws hws _ _ hlen hkv
      have hw : writable decl j var = true := by simp [writable, hidx, hnd, hnotag]
      refine ⟨.inl y, by simp [decAlts, hvar, hy, hw, hlen], ?_⟩
      cases fs with
      | nil => rfl
      | cons => simp only [Ty.erlAlts, e]
  | _ :: vs, decl, j, ho, .inr y, w, h => by
    simp only [Ty.orderedss, Bool.and_eq_true] at ho
    simp only [encAlts] at h
    obtain ⟨kvs, tag, k, rfl, htag, hk, hle, y', hdec, e⟩ := decAlts_encAlts vs decl (j + 1) ho.2 y w h
    refine ⟨kvs, tag, k, rfl, htag, hk, by omega, .inr y', ?_, by simp only [Ty.erlAlts, e]⟩
    have hne : k ≠ j := by omega
    simp only [decAlts, hne, ↓reduceIte, hdec]; rfl
end

end

end Tazuna.Trace
