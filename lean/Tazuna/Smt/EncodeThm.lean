import Tazuna.Smt.Encode

/-! T1, `encode_agrees`: in every model whose variables denote the values of the expression's variables, an encoded
expression denotes what `eval` computes. It holds for every model, so no answer of the solver can rest on a value
SMT-LIB leaves open, such as dividing by zero. -/

namespace Tazuna.Smt

open Tazuna.Ir

theorem absT_denote (M : Model) (t : Term) (n : Nat) (h : t.denote M = .int n ∨ t.denote M = .int (-(n : Int))) :
    (absT t).denote M = .int n := by
  rcases h with h | h <;> simp only [absT, Term.denote, h, Val.toInt, Val.toBool] <;> split <;> simp_all; omega

theorem tdivT_agrees (M : Model) (tx ty : Term) (x y : Int) (hx : tx.denote M = .int x)
    (hy : ty.denote M = .int y) : (tdivT tx ty).denote M = .int (Gleam.div x y) := by
  obtain ⟨m, hm⟩ := Int.eq_nat_or_neg x
  obtain ⟨n, hn⟩ := Int.eq_nat_or_neg y
  have ax := absT_denote M tx m (by rcases hm with rfl | rfl <;> simp [hx])
  have ay := absT_denote M ty n (by rcases hn with rfl | rfl <;> simp [hy])
  simp only [tdivT, Term.denote, hx, hy, ax, ay, Val.toInt, Val.toBool, Gleam.div]
  by_cases hy0 : y = 0
  · subst hy0; simp [BEq.beq, Val.beq]
  · have hn0 : (n : Int) ≠ 0 := by rcases hn with rfl | rfl <;> omega
    simp only [BEq.beq, Val.beq, hy0, decide_false, Bool.false_eq_true, ite_false, hn0]
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
      simp [Int.neg_tdiv, Int.tdiv_neg] <;>
      rcases Nat.eq_zero_or_pos m with rfl | hm <;> simp_all <;> omega

theorem tmodT_agrees (M : Model) (tx ty : Term) (x y : Int) (hx : tx.denote M = .int x)
    (hy : ty.denote M = .int y) : (tmodT tx ty).denote M = .int (Gleam.mod x y) := by
  obtain ⟨m, hm⟩ := Int.eq_nat_or_neg x
  obtain ⟨n, hn⟩ := Int.eq_nat_or_neg y
  have ax := absT_denote M tx m (by rcases hm with rfl | rfl <;> simp [hx])
  have ay := absT_denote M ty n (by rcases hn with rfl | rfl <;> simp [hy])
  simp only [tmodT, Term.denote, hx, hy, ax, ay, Val.toInt, Val.toBool, Gleam.mod]
  by_cases hy0 : y = 0
  · subst hy0; simp [BEq.beq, Val.beq]
  · have hn0 : (n : Int) ≠ 0 := by rcases hn with rfl | rfl <;> omega
    simp only [BEq.beq, Val.beq, hy0, decide_false, Bool.false_eq_true, ite_false, hn0]
    rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;>
      simp [Int.neg_tmod, Int.tmod_neg, Int.tmod_eq_emod_of_nonneg (Int.natCast_nonneg _)] <;>
      rcases Nat.eq_zero_or_pos m with rfl | hm <;> simp_all <;> omega

theorem rel_bool (x : Ty.bool.den) (v : Val) : Rel Ty.bool x v ↔ v = .bool (Ty.toBool x) := by
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨rfl, h⟩

theorem bool_beq (a b : Bool) : (Val.bool a == Val.bool b) = (a == b) := rfl

/-- SMT-LIB's `=` on encoded values is Gleam's `==` on the values, for the types of the fragment. -/
theorem rel_eq (t : Ty) (ht : (Ty.srt? t).isSome = true) (x y : t.den) (vx vy : Val) (hx : Rel t x vx)
    (hy : Rel t y vy) : (vx == vy) = t.deq x y := by
  cases t with
  | int =>
    simp only [Rel] at hx hy; subst hx hy
    simp [BEq.beq, Val.beq, Ty.deq, Ty.sem, Ty.semWith]
  | str =>
    simp only [Rel] at hx hy; subst hx hy
    simp [BEq.beq, Val.beq, Ty.deq, Ty.sem, Ty.semWith]
  | adt i a vs =>
    obtain ⟨h, hx⟩ := hx
    obtain ⟨_, hy⟩ := hy
    simp only [Ty.bool, Ty.adt.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    subst hx hy
    rw [bool_beq]
    rcases x with _ | _ | e <;> rcases y with _ | _ | e' <;> first | rfl | exact nomatch e | exact nomatch e'
  | _ => exact absurd hx (by simp [Rel])

theorem toBool_ofBool (b : Bool) : Ty.toBool (Ty.ofBool b) = b := by cases b <;> rfl

theorem encodeBin_agrees (M : Model) {a b c : Ty} (op : BinOp a b c) (tx ty : Term) (x : a.den) (y : b.den)
    (hx : Rel a x (tx.denote M)) (hy : Rel b y (ty.denote M)) (t : Term) (h : encodeBin op tx ty = .ok t) :
    Rel c (op.eval x y) (t.denote M) := by
  cases op with
  | add => cases h; simp only [Rel] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toInt, BinOp.eval]
  | sub => cases h; simp only [Rel] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toInt, BinOp.eval]
  | mul => cases h; simp only [Rel] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toInt, BinOp.eval]
  | div => cases h; simp only [Rel] at hx hy ⊢; exact tdivT_agrees M tx ty x y hx hy
  | mod => cases h; simp only [Rel] at hx hy ⊢; exact tmodT_agrees M tx ty x y hx hy
  | lt =>
    cases h
    simp only [Rel] at hx hy
    rw [rel_bool]
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLt, toBool_ofBool]
    congr 2
  | le =>
    cases h
    simp only [Rel] at hx hy
    rw [rel_bool]
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLe, toBool_ofBool]
    congr 2
  | gt =>
    cases h
    simp only [Rel] at hx hy
    rw [rel_bool]
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLt, toBool_ofBool]
    congr 2
  | ge =>
    cases h
    simp only [Rel] at hx hy
    rw [rel_bool]
    simp only [Term.denote]; rw [hx, hy]; simp only [Val.toInt, BinOp.eval, intLe, toBool_ofBool]
    congr 2
  | and =>
    cases h
    rw [rel_bool] at hx hy ⊢
    simp only [Term.denote, hx, hy, Val.toBool, BinOp.eval]
    cases Ty.toBool x <;> cases Ty.toBool y <;> rfl
  | or =>
    cases h
    rw [rel_bool] at hx hy ⊢
    simp only [Term.denote, hx, hy, Val.toBool, BinOp.eval]
    cases Ty.toBool x <;> cases Ty.toBool y <;> rfl
  | concat => cases h; simp only [Rel] at hx hy ⊢; simp [Term.denote, hx, hy, Val.toStr, BinOp.eval]
  | eq hc =>
    simp only [encodeBin] at h
    split at h
    · rename_i hs; cases h; rw [rel_bool]
      simp only [Term.denote, BinOp.eval, rel_eq _ hs x y _ _ hx hy]
      cases Ty.deq _ x y <;> rfl
    · cases h
  | ne hc =>
    simp only [encodeBin] at h
    split at h
    · rename_i hs; cases h; rw [rel_bool]
      simp only [Term.denote, BinOp.eval, Val.toBool, rel_eq _ hs x y _ _ hx hy]
      cases Ty.deq _ x y <;> rfl
    · cases h

/-- T1: an encoded expression denotes, in every model whose variables denote the expression's variables, the value
`eval` computes. -/
theorem encode_agrees {G : List Ty} (g : Ty.dens G) (M : Model) : {Γ : List Ty} → {t : Ty} → (e : Expr G Γ t) →
    (σ : List Term) → (ρ : Ty.dens Γ) → EnvRel M σ ρ → (x : Term) → encode σ e = .ok x →
    Rel t (e.eval g ρ) (x.denote M)
  | _, _, .int n, _, _, _, x, h => by cases h; simp [Rel, Expr.eval, Term.denote]
  | _, _, .str s, _, _, _, x, h => by
    simp only [encode] at h; split at h
    · cases h; simp [Rel, Expr.eval, Term.denote]
    · cases h
  | _, _, .var v, σ, ρ, hσ, x, h => by
    obtain ⟨y, hy, hr⟩ := hσ _ v
    simp only [encode, hy] at h; cases h; exact hr
  | _, _, .let_ e body, σ, ρ, hσ, x, h => by
    simp only [encode, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i te he
      refine encode_agrees g M body (te :: σ) (e.eval g ρ, ρ) ?_ x h
      intro t v
      cases v with
      | here => exact ⟨te, rfl, encode_agrees g M e σ ρ hσ te he⟩
      | there v => obtain ⟨y, hy, hr⟩ := hσ t v; exact ⟨y, hy, hr⟩
  | _, _, .bin op l r, σ, ρ, hσ, x, h => by
    simp only [encode, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i tl hl
      split at h
      · cases h
      · rename_i tr hr
        exact encodeBin_agrees M op tl tr _ _ (encode_agrees g M l σ ρ hσ tl hl)
          (encode_agrees g M r σ ρ hσ tr hr) x h
  | _, _, .not e, σ, ρ, hσ, x, h => by
    simp only [encode, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i te he
      cases h
      have := (rel_bool _ _).1 (encode_agrees g M e σ ρ hσ te he)
      rw [rel_bool]; simp only [Expr.eval, Term.denote, this, Val.toBool]
      cases Ty.toBool (e.eval g ρ) <;> rfl
  | _, _, .neg e, σ, ρ, hσ, x, h => by
    simp only [encode, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i te he
      cases h
      have := encode_agrees g M e σ ρ hσ te he
      simp only [Rel] at this ⊢
      simp [Expr.eval, Term.denote, this, Val.toInt]; omega
  | _, _, .global _, _, _, _, _, h | _, _, .ctor .., _, _, _, _, h | _, _, .field .., _, _, _, _, h
  | _, _, .index .., _, _, _, _, h | _, _, .update .., _, _, _, _, h | _, _, .call .., _, _, _, _, h
  | _, _, .lam .., _, _, _, _, h | _, _, .case .., _, _, _, _, h | _, _, .list .., _, _, _, _, h
  | _, _, .tuple .., _, _, _, _, h | _, _, .prim .., _, _, _, _, h => by simp [encode] at h

end Tazuna.Smt
