import Tazuna.Trace.DateThm
import Tazuna.Trace.Wire

/-! Reading back what was written gives the value written (`dec_enc`): for every type, every value with a wire form,
and every binding of ids whose reading undoes its writing. -/

namespace Tazuna.Trace

open Tazuna.Ir

-- One mutual block proves the theorems together, so each sees the binding hypothesis only one of them uses.
set_option linter.unusedSectionVars false

theorem mapM_inv {α β : Type} {f : α → Option β} {g : β → Option α} (h : ∀ x w, f x = some w → g w = some x) :
    ∀ (xs : List α) (ws : List β), xs.mapM f = some ws → ws.mapM g = some xs
  | [], ws, hx => by simp at hx; subst hx; rfl
  | x :: xs, ws, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hx
    obtain ⟨w, hw, ws', hws', rfl⟩ := hx
    simp [List.mapM_cons, h x w hw, mapM_inv h xs ws' hws']

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

section
variable (T : List TypeDecl) (name : Nat → Option String) (lookup : String → Option Nat)
  (hid : ∀ n s, name n = some s → lookup s = some n)
include hid

mutual
theorem dec_enc : (t : Ty) → (x : t.den0) → (w : Wire) → enc T name t x = some w → dec T lookup t w = some x
  | .int, x, w, h => by simp only [enc, Option.some.injEq] at h; subst h; rfl
  | .str, x, w, h => by simp only [enc, Option.some.injEq] at h; subst h; rfl
  | .list t, xs, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    exact mapM_inv (dec_enc t) xs ws hws
  | .bag t, xs, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    exact mapM_inv (dec_enc t) xs ws hws
  | .tuple ts, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    exact decs_encs ts x ws hws
  | .adt i _ vs, x, w, h => by
    rw [enc] at h
    obtain ⟨kvs, tag, k, rfl, htag, hk, _, hdec⟩ := decAlts_encAlts vs _ 0 x w h
    show (do
      let decl := (T[i]?.map (·.variants)).getD []
      let .str tag ← kvs.lookup "tag" | none
      let k ← decl.findIdx? (·.name == tag)
      decAlts T lookup decl kvs k 0 vs) = some x
    rw [htag]
    show (List.findIdx? (fun (var : Variant) => var.name == tag) ((T[i]?.map (·.variants)).getD []) >>= fun k => decAlts T lookup ((T[i]?.map (·.variants)).getD []) kvs k 0 vs) = some x
    rw [hk]
    exact hdec
  | .table k v, x, w, h => by
    rw [enc, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    have hpairs := mapM_inv (g := fun
        | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
        | _ => none) (by
      intro ⟨a, b⟩ w hw
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hw
      obtain ⟨wa, ha, wb, hb, rfl⟩ := hw
      simp [dec_enc k a wa ha, dec_enc v b wb hb]) x.1 ws hws
    show (do
      let pairs ← ws.mapM fun
        | .arr [a, b] => do pure (← dec T lookup k a, ← dec T lookup v b)
        | _ => none
      if h : KeysUnique (Ty.semWith Dsl.base k).2 pairs then some ⟨pairs, h⟩ else none) = some x
    rw [hpairs]
    show (if h : KeysUnique (Ty.semWith Dsl.base k).2 x.1 then some ⟨x.1, h⟩ else none) = some x
    rw [dite_eq_left_of_eq_true (eq_true x.2)]
    exact rfl
  | .date, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact DateThm.parse_render x s hs
  | .id, x, w, h => by
    simp only [enc, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact hid x s hs
  | .fn .., _, _, h => by simp [enc] at h
  | .param _, _, _, h => by simp [enc] at h
  | .dsl .., _, _, h => by simp [enc] at h
theorem decs_encs : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (ws : List Wire) →
    encs T name ts x = some ws → decs T lookup ts ws = some x
  | [], (), ws, h => by simp only [encs, Option.some.injEq] at h; subst h; rfl
  | t :: ts, (x, xs), ws, h => by
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    simp [decs, dec_enc t x w hw, decs_encs ts xs ws' hws']
theorem decFields_encs : (fs : List Ty) → (x : (Ty.semsWith Dsl.base fs).1) → (ws : List Wire) →
    encs T name fs x = some ws → ∀ (keys : List String) (kvs : List (String × Wire)), keys.length = ws.length →
    (∀ k w, (k, w) ∈ keys.zip ws → kvs.lookup k = some w) → decFields T lookup kvs fs keys = some x
  | [], (), ws, h, keys, kvs, hlen, _ => by
    simp only [encs, Option.some.injEq] at h; subst h
    cases keys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | f :: fs, (x, xs), ws, h, keys, kvs, hlen, hkv => by
    simp only [encs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨w, hw, ws', hws', rfl⟩ := h
    cases keys with
    | nil => simp at hlen
    | cons key keys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have hhead := hkv key w (by simp)
      have hrest : ∀ k w, (k, w) ∈ keys.zip ws' → kvs.lookup k = some w := fun k w hm =>
        hkv k w (by simp [hm])
      simp [decFields, hhead, dec_enc f x w hw, decFields_encs fs xs ws' hws' keys kvs hlen hrest]
theorem decAlts_encAlts : (vs : List (List Ty)) → (decl : List Variant) → (j : Nat) →
    (x : (Ty.semAltsWith Dsl.base vs).1) → (w : Wire) → encAlts T name decl j vs x = some w →
    ∃ kvs tag k, w = .obj kvs ∧ kvs.lookup "tag" = some (.str tag) ∧ decl.findIdx? (·.name == tag) = some k ∧
      j ≤ k ∧ decAlts T lookup decl kvs k j vs = some x
  | [], _, _, x, _, _ => nomatch x
  | fs :: _, decl, j, .inl x, w, h => by
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
      simp [decAlts, hvar, decFields_encs fs x ws hws _ _ hlen hkv]
  | _ :: vs, decl, j, .inr y, w, h => by
    simp only [encAlts] at h
    obtain ⟨kvs, tag, k, rfl, htag, hk, hle, hdec⟩ := decAlts_encAlts vs decl (j + 1) y w h
    refine ⟨kvs, tag, k, rfl, htag, hk, by omega, ?_⟩
    have hne : k ≠ j := by omega
    simp only [decAlts, hne, ↓reduceIte, hdec]; rfl
end

end

end Tazuna.Trace
