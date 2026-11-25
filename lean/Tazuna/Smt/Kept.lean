import Tazuna.Smt.Wf
import Tazuna.Semantics.Sites

/-! The code of a function a structure value keeps: its source's encoding over the program's definitions, with each
captured value as the constant that embeds it. `Fun.code_rel` (T1 at the kept source) proves the code relates to the
function the step applies, so a step encoding built from these codes rests on no assumed relation. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout)

/-- The codes of captured values: each one's embedding, or none when one has no constant (a function). -/
def envCodes : (Γ : List Ty) → Ty.dens Γ → Option (Codes Γ)
  | [], () => some ()
  | t :: Γ, (x, xs) => do
    let w ← embedV L t x
    let c ← Code.ofTerm? t w.term
    pure (c, ← envCodes Γ xs)

/-- A kept function's code and condition. -/
def _root_.Tazuna.Ir.Fun.code {t : Ty} (f : Fun t) : Enc (Code t) := do
  let σ ← need (.unexpected (.function (.tuple f.Γ))) (envCodes L f.Γ (Ty.up _ f.hΓ f.env))
  encode L (f.defs.encode L) f.body σ

/-- The code and condition of a kept function that returns effects, from its source the same way. -/
def _root_.Tazuna.Ir.EffectFun.code {ps : List Ty} {r : Ty} (f : EffectFun ps r) : Enc (Code (.fn ps r)) := do
  let σ ← need (.unexpected (.function (.tuple f.Γ))) (envCodes L f.Γ (Ty.up _ f.hΓ f.env))
  encode L (f.defs.encode L) f.body σ

end

section
variable {M : Model} {L : Layout}

theorem envCodes_rels : (Γ : List Ty) → (ρ : Ty.dens Γ) → (σ : Codes Γ) → envCodes L Γ ρ = some σ → Rels M L Γ ρ σ
  | [], (), (), _ => trivial
  | t :: Γ, (x, xs), (c, cs), h => by
    cases hw : embedV L t x with
    | none => simp [envCodes, hw] at h
    | some w =>
      cases hc : Code.ofTerm? t w.term with
      | none => simp [envCodes, hw, hc] at h
      | some c' =>
        cases hcs : envCodes L Γ xs with
        | none => simp [envCodes, hw, hcs] at h
        | some cs' =>
          simp only [envCodes, hw, hc, hcs, Option.bind_some, Option.pure_def,
            bind] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨(rel_ofTerm hc _).2 (by rw [Val.denote_term]; exact embed_rel _ _ _ hw),
            envCodes_rels Γ xs _ hcs⟩

/-- A kept function's code denotes the function the step applies, wherever its condition holds. -/
theorem _root_.Tazuna.Ir.Fun.code_rel {t : Ty} (f : Fun t) {s : Code t} {c : Term} (h : f.code L = .ok (s, c))
    (hc : Holds M c) : Smt.Rel M L t f.eval s := by
  obtain ⟨σ, hσ, h⟩ := bind_ok.1 h
  exact encode_agrees f.defs f.defs.eval (f.defs.encode L) (Defs.encode_agrees M L f.defs) f.body σ _
    (envCodes_rels _ _ σ (need_ok.1 hσ)) s c h hc

/-- The same, for the function as the step applies it to data. -/
theorem _root_.Tazuna.Ir.Fun.code_fn {t : Ty} (f : Fun t) (ht : t.isData = true) {s : Code t} {c : Term}
    (h : f.code L = .ok (s, c)) (hc : Holds M c) : Smt.Rel M L t (Ty.up t ht f.fn) s := by
  rw [Fun.fn, Ty.up_down]; exact f.code_rel h hc

/-- A kept function that returns effects, applied to codes of its arguments, yields the code of what it returns:
its effects as their variants of the effect datatype (T1 at the kept source). -/
theorem _root_.Tazuna.Ir.EffectFun.code_apply {ps : List Ty} {r : Ty} (f : EffectFun ps r) {s : Code (.fn ps r)}
    {c : Term} (h : f.code L = .ok (s, c)) (hc : Holds M c) (xs : (Ty.tuple ps).den0) (cs : Codes ps)
    (hxs : Rels M L ps (Ty.up _ f.hps xs) cs) {o : Code r} {c' : Term} (ho : s cs = .ok (o, c')) (hc' : Holds M c') :
    Smt.Rel M L r (f.apply xs) o := by
  obtain ⟨σ, hσ, h⟩ := bind_ok.1 h
  have hf := encode_agrees f.defs f.defs.eval (f.defs.encode L) (Defs.encode_agrees M L f.defs) f.body σ _
    (envCodes_rels _ _ σ (need_ok.1 hσ)) s c h hc
  exact hf _ _ hxs o c' ho hc'

end

section
variable (L : Layout)

/-- The codes of a tuple's items, each the selector of its field from `x` of the tuple datatype `d`. -/
def tupleCodes (d : Nat) : (Γ : List Ty) → Term → Nat → Option (Codes Γ)
  | [], _, _ => some ()
  | t :: Γ, x, i => do pure ((← Code.ofTerm? t (.sel d 0 i x)), (← tupleCodes d Γ x (i + 1)))

/-- The code of a site's source over the codes of the values it captured. -/
def _root_.Tazuna.Ir.Site.code {Γ : List Ty} {t : Ty} (s : Site Γ t) (σ : Codes Γ) : Enc (Code t) :=
  encode L (s.defs.encode L) s.body σ

end

section
variable {M : Model} {L : Layout}

theorem tupleCodes_rels {d : Nat} {x : Term} : (Γ : List Ty) → (pre vals : List Val) → (ρ : Ty.dens Γ) →
    (σ : Codes Γ) → x.denote M = .ctor d 0 (pre ++ vals) → RelVs L Γ ρ vals → tupleCodes d Γ x pre.length = some σ →
    Rels M L Γ ρ σ
  | [], _, _, _, _, _, _, _ => trivial
  | t :: Γ, pre, vals, (y, ys), (c, cs), hx, ⟨w, ws, hv, hw, hws⟩, h => by
    subst hv
    cases hc : Code.ofTerm? t (Term.sel d 0 pre.length x) with
    | none => simp [tupleCodes, hc] at h
    | some c' =>
    cases hcs : tupleCodes d Γ x (pre.length + 1) with
    | none => simp [tupleCodes, hc, hcs] at h
    | some cs' =>
    simp only [tupleCodes, hc, hcs, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(rel_ofTerm hc _).2 ?_, tupleCodes_rels Γ (pre ++ [w]) ws ys cs (by simpa using hx) hws (by simpa using hcs)⟩
    rw [sel_ctor _ hx]; simpa using hw

end

end Tazuna.Smt
