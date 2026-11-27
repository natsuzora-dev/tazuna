import Tazuna.Semantics.Interleave

/-! Machines whose `timer` never gives a timer, read off the definition. Such a machine fires forward by itself
(`timerForward_of_noTimer`), so prove asks its timer question only of the other machines. The reading is syntactic and
errs one way: `timer` written as a constructor of `None`, or a `let` or `case` whose bodies all are, never sets a
timer; anything else (a call, a global, a variable) is read as one that may. -/

namespace Tazuna.Ir

section
variable {G : List Ty}

mutual
/-- Whether every value of the expression is a variant other than its type's first: a constructor of a later
variant, or a `let` or `case` whose bodies all are. For an `Option`, never `Some`. -/
def Expr.laterVariant {Γ : List Ty} {t : Ty} : Expr G Γ t → Bool
  | .ctor v _ => v.val != 0
  | .let_ _ body => body.laterVariant
  | .case _ cs _ => cs.laterVariant
  | _ => false
def Clauses.laterVariant {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → Bool
  | .nil => true
  | .cons _ body rest => body.laterVariant && rest.laterVariant
  | .guarded _ _ body rest => body.laterVariant && rest.laterVariant
end

/-- A value that is a variant other than its type's first; any value of a type that is no custom type. -/
def LaterVariant : (t : Ty) → t.den → Prop
  | .adt _ _ _, x => (Alts.view x).1.val ≠ 0
  | _, _ => True

variable (D : Defs G) (g : Ty.dens G)

mutual
theorem Expr.laterVariant_eval {Γ : List Ty} {t : Ty} : (e : Expr G Γ t) → e.laterVariant = true →
    ∀ ρ, LaterVariant t (e.eval D g ρ)
  | .ctor v es, h, ρ => by
    simp only [Expr.laterVariant, bne_iff_ne, ne_eq] at h
    show (Alts.view (Alts.inj v _)).1.val ≠ 0
    rw [Alts.view_inj]; exact h
  | .let_ _ body, h, _ => body.laterVariant_eval h _
  | .case e cs hc, h, ρ => cs.laterVariant_eval h ρ _ _
  | .int _, h, _ | .str _, h, _ | .var _, h, _ | .global _, h, _ | .field .., h, _ | .index .., h, _
  | .update .., h, _ | .call .., h, _ | .lam _, h, _ | .list _, h, _ | .tuple _, h, _ | .bin .., h, _
  | .not _, h, _ | .neg _, h, _ | .prim .., h, _ | .close .., h, _ | .closeEffect .., h, _ => by
    simp [Expr.laterVariant] at h
theorem Clauses.laterVariant_eval {Γ : List Ty} {t r : Ty} {sh : List Shape} : (cs : Clauses G Γ t r sh) →
    cs.laterVariant = true → ∀ ρ x hx, LaterVariant r (cs.eval D g ρ x hx)
  | .nil, _, _, _, hx => False.elim (by simp at hx)
  | .cons p body rest, h, ρ, x, hx => by
    simp only [Clauses.laterVariant, Bool.and_eq_true] at h
    unfold Clauses.eval
    split
    · exact body.laterVariant_eval h.1 _
    · exact rest.laterVariant_eval h.2 ρ x _
  | .guarded p guard body rest, h, ρ, x, hx => by
    simp only [Clauses.laterVariant, Bool.and_eq_true] at h
    unfold Clauses.eval
    split
    · split
      · exact body.laterVariant_eval h.1 _
      · exact rest.laterVariant_eval h.2 ρ x _
    · exact rest.laterVariant_eval h.2 ρ x _
end

end

namespace Step

variable {r e : Ty}

/-- Whether the machine's `timer`, read off its definition, never gives a timer. -/
def _root_.Tazuna.Ir.MachineV.noTimer (m : MachineV r e) : Bool :=
  match m.timer.body with
  | .lam b => b.laterVariant
  | _ => false

/-- A machine whose `timer` never gives a timer has none at any key, state and records. -/
theorem timerAt_of_noTimer {m : MachineV r e} (h : m.noTimer = true) (records : r.den0) (key : m.key.den0)
    (st : m.state.den0) : m.timerAt records key st = none := by
  unfold MachineV.noTimer at h
  have hall := m.timer.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at hall
  have hr : (Ty.option (Ty.timer m.state)).isData = true := hall.2
  have hps : (Ty.tuple [Ty.timerCtx m.key m.state r]).isData = true := by
    simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true]; exact ⟨hall.1.1, trivial⟩
  have hup := Ty.up_fn _ _ m.timer.ht hps hr m.timer.fn (.inl (key, st, records, ()), ())
  conv at hup => lhs; rw [Fun.fn, Ty.up_down, Fun.eval]
  split at h
  next b hb =>
    have hl := b.laterVariant_eval m.timer.defs m.timer.defs.eval h
      (Dens.append (Ty.up _ hps (.inl (key, st, records, ()), ())) (Ty.up _ m.timer.hΓ m.timer.env))
    have he : Expr.eval m.timer.defs m.timer.defs.eval m.timer.body (Ty.up _ m.timer.hΓ m.timer.env)
        (Ty.up _ hps (.inl (key, st, records, ()), ())) =
        Expr.eval m.timer.defs m.timer.defs.eval b
          (Dens.append (Ty.up _ hps (.inl (key, st, records, ()), ())) (Ty.up _ m.timer.hΓ m.timer.env)) := by
      rw [hb]; rfl
    rw [← he, hup] at hl
    unfold MachineV.timerAt
    generalize m.timer.fn (.inl (key, st, records, ()), ()) = y at hl ⊢
    rcases y with y | y
    · have hfs : (Ty.tuple [Ty.timer m.state]).isData = true := by
        simp only [Ty.option, Ty.isData, Ty.isDatass, Ty.isDatas, Bool.and_eq_true] at hr ⊢; exact ⟨hr.1.1, trivial⟩
      erw [Ty.up_inl 3 _ _ _ hr hfs] at hl
      exact (hl rfl).elim
    · simp [timerVal]
  · simp at h

/-- A machine whose `timer` never gives a timer fires forward. -/
theorem timerForward_of_noTimer {m : MachineV r e} (h : m.noTimer = true) : TimerForward m := by
  intro records key st x hx
  simp [timerAt_of_noTimer h records key st] at hx

end Step

end Tazuna.Ir
