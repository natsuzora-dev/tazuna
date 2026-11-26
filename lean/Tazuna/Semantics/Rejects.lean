import Tazuna.Semantics.Eval

/-! The rejections a command's `decide` may return, read off its source, as `Fun.ruleNames` reads rule names off
`accepts`. A `decide` is written as a block of `use <- tazuna.require(holds, or: R)` and
`use v <- table.lookup(table, key, or: R)` lines, `let`s and `case`s ending in `Ok(..)` or `Error(R)`. Where every
rejection it can return is written in place as a constructor, the constructors it names are all it may return
(`Expr.rejects_sound`); anywhere else (a rejection held in a variable, a helper function's result) the reading gives
up, and every constructor of the rejection type stays possible. -/

namespace Tazuna.Ir

section
variable {G : List Ty}

/-- The constructor an expression is written as, counted from 0. -/
def Expr.ctorIndex? {Γ : List Ty} {t : Ty} : Expr G Γ t → Option Nat
  | .ctor v _ => some v.val
  | _ => none

/-- Whether the function is the built-in `p`. -/
def Expr.isPrim {Γ : List Ty} {t : Ty} (p : Prim) : Expr G Γ t → Bool
  | .prim q _ _ => q == p
  | _ => false

mutual
/-- The constructors of the rejection an expression of a `Result` type may hold in `Error`, counted from 0; none
where the source does not say. -/
def Expr.rejects {Γ : List Ty} {t : Ty} : Expr G Γ t → Option (List Nat)
  | .ctor v es => if v.val = 0 then some [] else Exprs.errorRejects es
  | .let_ _ body => Expr.rejects body
  | .case _ cs _ => Clauses.rejects cs
  | .call f args =>
    if f.isPrim .require then Exprs.thenRejects 1 args
    else if f.isPrim .tableLookup then Exprs.thenRejects 2 args
    else none
  | _ => none
/-- `Error(R)`'s field: `R`'s constructor. -/
def Exprs.errorRejects {Γ ts : List Ty} : Exprs G Γ ts → Option (List Nat)
  | .cons e .nil => e.ctorIndex?.map ([·])
  | _ => none
/-- The arguments `.., R, fn(..) { rest }` of `require` or `lookup`, after `k` others: `R`'s constructor and what
`rest` may reject with. -/
def Exprs.thenRejects {Γ ts : List Ty} : Nat → Exprs G Γ ts → Option (List Nat)
  | 0, .cons r rest => r.ctorIndex?.bind fun k => (Exprs.callbackRejects rest).map (k :: ·)
  | k + 1, .cons _ rest => Exprs.thenRejects k rest
  | _, .nil => none
/-- The last argument, a callback. -/
def Exprs.callbackRejects {Γ ts : List Ty} : Exprs G Γ ts → Option (List Nat)
  | .cons k .nil => Expr.thenRejects k
  | .nil | .cons _ (.cons _ _) => none
/-- A callback `fn(..) { rest }` written in place: what `rest` may reject with. -/
def Expr.thenRejects {Γ : List Ty} {t : Ty} : Expr G Γ t → Option (List Nat)
  | .lam body => Expr.rejects body
  | _ => none
/-- What the clauses' bodies may reject with. -/
def Clauses.rejects {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → Option (List Nat)
  | .nil => some []
  | .cons _ body rest | .guarded _ _ body rest => match Expr.rejects body, Clauses.rejects rest with
    | some ks, some ks' => some (ks ++ ks')
    | _, _ => none
end

end

/-- Which constructor built a value of a custom type, counted from 0; none for any other type. -/
def ctorIdxOf : (t : Ty) → t.den → Option Nat
  | .adt _ _ _, x => some (Alts.view x).1.val
  | _, _ => none

/-- The constructor of the rejection a `Result` holds in `Error`; none for `Ok` and any other value. -/
def errIndex : (t : Ty) → t.den → Option Nat
  | .adt _ _ [[_], [e]], .inr (.inl (x, ())) => ctorIdxOf e x
  | _, _ => none

section
variable {G : List Ty} (D : Defs G) (g : Ty.dens G)

theorem Expr.isPrim_eval {Γ : List Ty} {T : Ty} (f : Expr G Γ T) (p : Prim) (hf : f.isPrim p = true) :
    ∃ targs hp, ∃ _ : p.ty.inst targs = T, ∀ ρ, HEq (f.eval D g ρ) (p.den targs hp) := by
  cases f <;> simp [Expr.isPrim] at hf
  subst hf
  exact ⟨_, _, rfl, fun _ => HEq.rfl⟩

theorem Expr.ctorIndex?_eval {Γ : List Ty} {t : Ty} (e : Expr G Γ t) {k : Nat} (h : e.ctorIndex? = some k)
    (ρ : Ty.dens Γ) : ctorIdxOf t (e.eval D g ρ) = some k := by
  cases e <;> simp [Expr.ctorIndex?] at h
  subst h
  simp [Expr.eval, ctorIdxOf, Alts.view_inj]

theorem errIndex_some {t : Ty} {x : t.den} {n : Nat} (h : errIndex t x = some n) :
    ∃ i as a e, ∃ _ : t = .adt i as [[a], [e]], ∃ y : e.den,
      HEq x (Sum.inr (Sum.inl (y, ())) : Ty.alts [[a], [e]]) ∧ ctorIdxOf e y = some n := by
  unfold errIndex at h
  split at h
  · exact ⟨_, _, _, _, rfl, _, HEq.rfl, h⟩
  · cases h

theorem require_errIndex {a e : Ty} (hp : Prim.require.ok [a, e] = true) (b : Ty.bool.den) (rej : e.den)
    (next : (Ty.fn [] (.result a e)).den) {n : Nat}
    (h : errIndex (.result a e) (Prim.require.den [a, e] hp (b, rej, next, ())) = some n) :
    errIndex (.result a e) (next ()) = some n ∨ ctorIdxOf e rej = some n := by
  simp only [Prim.den] at h
  by_cases hb : Ty.toBool b = true
  · simp only [hb, ↓reduceIte] at h
    exact .inl h
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    exact .inr h

theorem lookup_errIndex {kt vt a e : Ty} (hp : Prim.tableLookup.ok [kt, vt, a, e] = true) (t : (Ty.table kt vt).den)
    (key : kt.den) (rej : e.den) (next : (Ty.fn [vt] (.result a e)).den) {n : Nat}
    (h : errIndex (.result a e) (Prim.tableLookup.den [kt, vt, a, e] hp (t, key, rej, next, ())) = some n) :
    ctorIdxOf e rej = some n ∨ ∃ x, errIndex (.result a e) (next (x, ())) = some n := by
  simp only [Prim.den] at h
  split at h
  · exact .inr ⟨_, h⟩
  · exact .inl h

mutual
theorem Expr.rejects_sound {Γ : List Ty} : {t : Ty} → (e : Expr G Γ t) → {ks : List Nat} →
    e.rejects = some ks → ∀ ρ n, errIndex t (e.eval D g ρ) = some n → n ∈ ks
  | _, .ctor v es, ks, h, ρ, n, hn => by
    obtain ⟨i, as, a, e, ht, y, hx, hy⟩ := errIndex_some hn
    cases ht
    obtain ⟨vv, hv⟩ := v
    simp only [Expr.eval] at hx
    match vv, hv, es, h, hx with
    | 0, _, _, _, hx => exact nomatch (eq_of_heq hx)
    | 1, _, .cons r .nil, h, hx =>
      simp only [Alts.inj, Exprs.eval] at hx
      injection hx with hx
      injection hx with hx
      injection hx with hx
      subst hx
      simp only [Expr.rejects, Nat.one_ne_zero, ↓reduceIte, Exprs.errorRejects] at h
      cases hr : r.ctorIndex? with
      | none => simp [hr] at h
      | some k =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        rw [Expr.ctorIndex?_eval D g r hr ρ] at hy
        cases hy
        exact List.mem_singleton.2 rfl
  | _, .let_ _ body, _, h, ρ, n, hn => Expr.rejects_sound body h _ n hn
  | _, .case e cs hc, _, h, ρ, n, hn => Clauses.rejects_sound cs h ρ (e.eval D g ρ) (hc.sound _) n hn
  | _, .call f .nil, _, h, _, _, _ | _, .call f (.cons _ .nil), _, h, _, _, _
  | _, .call f (.cons _ (.cons _ .nil)), _, h, _, _, _ => by
    simp [Expr.rejects, Exprs.thenRejects, Exprs.callbackRejects] at h
  | _, .call f (.cons a0 (.cons r (.cons k .nil))), ks, h, ρ, n, hn => by
    have ihk := @Expr.thenRejects_sound _ _ k
    simp only [Expr.rejects] at h
    split at h
    · rename_i hf
      obtain ⟨targs, hp, hT, hev⟩ := f.isPrim_eval D g .require hf
      have hl : targs.length = 2 := by simpa [Prim.ok, Prim.sig] using hp
      match targs, hl, hp, hT, hev with
      | [a, e], _, hp, hT, hev =>
        have hT' : Ty.fn [.bool, e, .fn [] (.result a e)] (.result a e) = _ := hT
        cases hT'
        simp only [Exprs.thenRejects] at h
        cases hr : r.ctorIndex? <;> cases hk : k.thenRejects <;>
          simp only [hr, hk, Exprs.callbackRejects, Option.bind, Option.map, reduceCtorEq, Option.some.injEq] at h
        subst h
        have hn2 : errIndex (.result a _)
            (Prim.require.den [a, _] hp (a0.eval D g ρ, r.eval D g ρ, k.eval D g ρ, ())) = some n := by
          rw [← eq_of_heq (hev ρ)]; exact hn
        rcases require_errIndex hp _ _ _ hn2 with hn | hn
        · exact List.mem_cons_of_mem _ (ihk hk rfl ρ () n hn)
        · rw [Expr.ctorIndex?_eval D g r hr ρ] at hn
          cases hn
          exact List.mem_cons_self
    · split at h
      · simp [Exprs.thenRejects, Exprs.callbackRejects] at h
      · cases h
  | _, .call f (.cons a0 (.cons a1 (.cons r (.cons k .nil)))), ks, h, ρ, n, hn => by
    have ihk := @Expr.thenRejects_sound _ _ k
    simp only [Expr.rejects] at h
    split at h
    · simp [Exprs.thenRejects, Exprs.callbackRejects] at h
    · split at h
      · rename_i hf
        obtain ⟨targs, hp, hT, hev⟩ := f.isPrim_eval D g .tableLookup hf
        have hl : targs.length = 4 := by simp [Prim.ok, Prim.sig] at hp; exact hp.1
        match targs, hl, hp, hT, hev with
        | [kt, vt, a, e], _, hp, hT, hev =>
          have hT' : Ty.fn [.table kt vt, kt, e, .fn [vt] (.result a e)] (.result a e) = _ := hT
          cases hT'
          simp only [Exprs.thenRejects] at h
          cases hr : r.ctorIndex? <;> cases hk : k.thenRejects <;>
            simp only [hr, hk, Exprs.callbackRejects, Option.bind, Option.map, reduceCtorEq, Option.some.injEq] at h
          subst h
          have hn2 : errIndex (.result a _) (Prim.tableLookup.den [_, _, a, _] hp
              (a0.eval D g ρ, a1.eval D g ρ, r.eval D g ρ, k.eval D g ρ, ())) = some n := by
            rw [← eq_of_heq (hev ρ)]; exact hn
          rcases lookup_errIndex hp _ _ _ _ hn2 with hn | ⟨x, hn⟩
          · rw [Expr.ctorIndex?_eval D g r hr ρ] at hn
            cases hn
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ihk hk rfl ρ _ n hn)
      · cases h
  | _, .call f (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _))))), _, h, _, _, _ => by
    simp [Expr.rejects, Exprs.thenRejects, Exprs.callbackRejects] at h
  | _, .int _, _, h, _, _, _ | _, .str _, _, h, _, _, _ | _, .var _, _, h, _, _, _ | _, .global _, _, h, _, _, _
  | _, .field .., _, h, _, _, _ | _, .index .., _, h, _, _, _ | _, .update .., _, h, _, _, _
  | _, .lam _, _, h, _, _, _ | _, .list _, _, h, _, _, _ | _, .tuple _, _, h, _, _, _ | _, .bin .., _, h, _, _, _
  | _, .not _, _, h, _, _, _ | _, .neg _, _, h, _, _, _ | _, .prim .., _, h, _, _, _ | _, .close .., _, h, _, _, _
  | _, .closeEffect .., _, h, _, _, _ => by simp [Expr.rejects] at h
termination_by structural _ e => e
theorem Expr.thenRejects_sound {Γ : List Ty} : {t : Ty} → (k : Expr G Γ t) → {ks : List Nat} →
    k.thenRejects = some ks → {ps : List Ty} → {r : Ty} → (ht : t = .fn ps r) → ∀ ρ xs n,
    errIndex r ((ht ▸ k.eval D g ρ : (Ty.fn ps r).den) xs) = some n → n ∈ ks
  | _, .lam body, _, h, _, _, ht, ρ, xs, n, hn => by
    cases ht
    exact Expr.rejects_sound body h _ n hn
  | _, .int _, _, h, _, _, _, _, _, _, _ | _, .str _, _, h, _, _, _, _, _, _, _
  | _, .var _, _, h, _, _, _, _, _, _, _ | _, .global _, _, h, _, _, _, _, _, _, _
  | _, .ctor .., _, h, _, _, _, _, _, _, _ | _, .field .., _, h, _, _, _, _, _, _, _
  | _, .index .., _, h, _, _, _, _, _, _, _ | _, .update .., _, h, _, _, _, _, _, _, _
  | _, .call .., _, h, _, _, _, _, _, _, _ | _, .let_ .., _, h, _, _, _, _, _, _, _
  | _, .case .., _, h, _, _, _, _, _, _, _ | _, .list _, _, h, _, _, _, _, _, _, _
  | _, .tuple _, _, h, _, _, _, _, _, _, _ | _, .bin .., _, h, _, _, _, _, _, _, _
  | _, .not _, _, h, _, _, _, _, _, _, _ | _, .neg _, _, h, _, _, _, _, _, _, _
  | _, .prim .., _, h, _, _, _, _, _, _, _ | _, .close .., _, h, _, _, _, _, _, _, _
  | _, .closeEffect .., _, h, _, _, _, _, _, _, _ => by simp [Expr.thenRejects] at h
termination_by structural _ k => k
theorem Clauses.rejects_sound {Γ : List Ty} {t r : Ty} : {sh : List Shape} → (cs : Clauses G Γ t r sh) →
    {ks : List Nat} → cs.rejects = some ks →
    ∀ ρ x hx n, errIndex r (Clauses.eval D g cs ρ x hx) = some n → n ∈ ks
  | _, .nil, _, _, _, _, hx, _, _ => by simp at hx
  | _, .cons p body rest, ks, h, ρ, x, hx, n, hn => by
    simp only [Clauses.rejects] at h
    cases hb : body.rejects <;> cases hr : rest.rejects <;> simp only [hb, hr, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [Clauses.eval] at hn
    split at hn
    · exact List.mem_append_left _ (Expr.rejects_sound body hb _ n hn)
    · exact List.mem_append_right _ (Clauses.rejects_sound rest hr ρ x _ n hn)
  | _, .guarded p guard body rest, ks, h, ρ, x, hx, n, hn => by
    simp only [Clauses.rejects] at h
    cases hb : body.rejects <;> cases hr : rest.rejects <;> simp only [hb, hr, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [Clauses.eval] at hn
    split at hn
    · split at hn
      · exact List.mem_append_left _ (Expr.rejects_sound body hb _ n hn)
      · exact List.mem_append_right _ (Clauses.rejects_sound rest hr ρ x _ n hn)
    · exact List.mem_append_right _ (Clauses.rejects_sound rest hr ρ x _ n hn)
termination_by structural _ cs => cs
end

end

end Tazuna.Ir
