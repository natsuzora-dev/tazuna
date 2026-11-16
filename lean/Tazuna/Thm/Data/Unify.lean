import Tazuna.Data.Unify
import Tazuna.Thm.Data.Trace
import Tazuna.Thm.Verify.Complete.Values

namespace Tazuna.Thm.Data.Unify

open Tazuna.Data Tazuna.Thm.Data.Trace Tazuna.Thm.Verify.Matching

/-- The string that the peer's string `v` stands for under `bs`: its binding for a string of `created`, else itself. -/
def standsFor (created : List String) (bs : Bindings) (v : String) : Option String :=
  if created.contains v then bs.lookup v else none

/-- What a unification from bindings `bs` to `bs'` gives: `P` holds for the meaning of every extension of `bs'`. -/
structure Unified (created : List String) (bs bs' : Bindings) (P : (String → Option String) → Prop) : Prop where
  grows : bs <+: bs'
  oneToOne : OneToOne bs → OneToOne bs'
  sound : ∀ R, bs' <+: R → P (standsFor created R)

theorem Unified.refl (created : List String) (bs : Bindings) {P : (String → Option String) → Prop}
    (hP : ∀ R, P (standsFor created R)) : Unified created bs bs P :=
  ⟨List.prefix_refl bs, id, fun R _ => hP R⟩

theorem Unified.trans {created : List String} {bs b₁ b₂ : Bindings} {P Q : (String → Option String) → Prop}
    (h₁ : Unified created bs b₁ P) (h₂ : Unified created b₁ b₂ Q) :
    Unified created bs b₂ (fun f => P f ∧ Q f) :=
  ⟨h₁.grows.trans h₂.grows, fun h => h₂.oneToOne (h₁.oneToOne h),
    fun R hR => ⟨h₁.sound R (h₂.grows.trans hR), h₂.sound R hR⟩⟩

theorem Unified.mono {created : List String} {bs bs' : Bindings} {P Q : (String → Option String) → Prop}
    (h : Unified created bs bs' P) (hPQ : ∀ f, P f → Q f) : Unified created bs bs' Q :=
  ⟨h.grows, h.oneToOne, fun R hR => hPQ _ (h.sound R hR)⟩

set_option linter.unusedSimpArgs false in
theorem unify_sound (c : List String) :
    (∀ s t bs bs', unify c s t bs = .ok bs' → Unified c bs bs' (fun f => ValueMatches f s t)) ∧
    (∀ fs gs bs bs', unifyFields c fs gs bs = .ok bs' → Unified c bs bs' (fun f => FieldsMatch f fs gs)) ∧
    (∀ ss ts bs left bs', unifyBag c ss ts bs left = .ok bs' →
      Unified c bs bs' (fun f => ∃ zs, ts.Perm zs ∧ ListMatches f ss zs)) ∧
    (∀ first rest cands passed bs left bs', unifyBagFrom c first rest cands passed bs left = .ok bs' →
      Unified c bs bs' (fun f => ∃ zs, (passed.reverse ++ cands).Perm zs ∧ ListMatches f (first :: rest) zs)) ∧
    (∀ xs ys bs bs', unifyList c xs ys bs = .ok bs' → xs.length = ys.length →
      Unified c bs bs' (fun f => ListMatches f xs ys)) := by
  refine unify.mutual_induct c
    (fun s t bs => ∀ bs', unify c s t bs = .ok bs' → Unified c bs bs' (fun f => ValueMatches f s t))
    (fun fs gs bs => ∀ bs', unifyFields c fs gs bs = .ok bs' → Unified c bs bs' (fun f => FieldsMatch f fs gs))
    (fun ss ts bs left => ∀ bs', unifyBag c ss ts bs left = .ok bs' →
      Unified c bs bs' (fun f => ∃ zs, ts.Perm zs ∧ ListMatches f ss zs))
    (fun first rest cands passed bs left => ∀ bs', unifyBagFrom c first rest cands passed bs left = .ok bs' →
      Unified c bs bs' (fun f => ∃ zs, (passed.reverse ++ cands).Perm zs ∧ ListMatches f (first :: rest) zs))
    (fun xs ys bs => ∀ bs', unifyList c xs ys bs = .ok bs' → xs.length = ys.length →
      Unified c bs bs' (fun f => ListMatches f xs ys))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro bs v w hd bs' h
    rw [unify] at h
    simp only [hd, ite_true] at h
    cases hb : bs.bind v w with
    | none => simp [hb] at h
    | some b =>
    simp only [hb, Option.elim_some, Except.ok.injEq] at h
    subst h
    obtain ⟨hp, hl, ho⟩ := bind_spec hb
    refine ⟨hp, ho, fun R hR => ?_⟩
    simp only [ValueMatches]
    exact ⟨w, rfl, .inr (by rw [standsFor, ite_eq_left hd]; exact lookup_prefix hR hl)⟩
  · intro bs v w hd hw bs' h
    rw [unify] at h
    simp only [hd, hw, Bool.false_eq_true, ite_false, ite_true, Except.ok.injEq] at h
    subst h
    refine Unified.refl c bs fun R => ?_
    simp only [beq_iff_eq] at hw
    simp only [ValueMatches]
    exact ⟨w, rfl, .inl ⟨by rw [standsFor, ite_eq_right hd], hw⟩⟩
  · intro bs v w hd hw bs' h
    rw [unify] at h
    simp only [hd, hw, Bool.false_eq_true, ite_false] at h
    cases h
  · intro bs v t ht bs' h
    unfold unify at h
    cases t with
    | leaf x => cases x <;> first | exact absurd rfl (ht _) | simp at h
    | _ => simp at h
  · intro bs v w hv hw bs' h
    unfold unify at h
    cases v with
    | str v => exact absurd rfl (hv v)
    | _ =>
      simp only [hw, ite_true, Except.ok.injEq] at h
      subst h
      refine Unified.refl c bs fun R => ?_
      simp only [beq_iff_eq] at hw
      simp [ValueMatches, hw]
  · intro bs v w hv hw bs' h
    unfold unify at h
    cases v with
    | str v => exact absurd rfl (hv v)
    | _ => simp [hw] at h
  · intro bs xs ys hl ih bs' h
    rw [unify] at h
    simp only [hl, ite_true] at h
    exact (ih bs' h (by simpa using hl)).mono fun f hf => ⟨ys, rfl, hf⟩
  · intro bs xs ys hl bs' h
    rw [unify] at h
    simp [hl] at h
  · intro bs xs ys hl ih bs' h
    rw [unify] at h
    simp only [hl, ite_true] at h
    exact (ih bs' h (by simpa using hl)).mono fun f hf => ⟨ys, rfl, hf⟩
  · intro bs xs ys hl bs' h
    rw [unify] at h
    simp [hl] at h
  · intro bs xs ys hf ih bs' h
    rw [unify] at h
    simp only [hf, ite_true] at h
    cases hb : unifyBag c xs ys bs searchLimit with
    | error n => cases n <;> simp [hb, searched] at h
    | ok b =>
      simp only [hb, searched, Except.ok.injEq] at h
      subst h
      exact (ih b hb).mono fun f ⟨zs, hp, hm⟩ => ⟨ys, zs, rfl, hp, hm⟩
  · intro bs xs ys hf bs' h
    rw [unify] at h
    simp [hf] at h
  · intro bs fs gs hk ih bs' h
    rw [unify] at h
    simp only [hk, ite_true] at h
    exact (ih bs' h).mono fun f hf => ⟨gs, rfl, Tazuna.Thm.Verify.Complete.Values.sameKeys_iff hk, hf⟩
  · intro bs fs gs hk bs' h
    rw [unify] at h
    simp [hk] at h
  · intro s t bs h1 h2 h3 h4 h5 h6 bs' h
    rw [unify] at h
    · cases h
    all_goals assumption
  · intro gs bs bs' h
    rw [unifyFields] at h
    simp only [Except.ok.injEq] at h
    subst h
    exact Unified.refl c bs fun _ => by simp [FieldsMatch]
  · intro gs bs k v fs ih1 ih2 bs' h
    rw [unifyFields] at h
    cases hw : gs.lookup k with
    | none => simp [hw] at h
    | some w =>
    cases h₁ : unify c v w bs with
    | error => simp [hw, h₁, Except.bind] at h
    | ok b₁ =>
    simp only [hw, h₁, Except.bind, Option.elim_some] at h
    exact ((ih1 w b₁ h₁).trans (ih2 b₁ bs' h)).mono fun f hf => ⟨⟨w, hw, hf.1⟩, hf.2⟩
  · intro ss ts bs left hl bs' h
    unfold unifyBag at h
    simp [hl] at h
  · intro ts bs left hl bs' h
    unfold unifyBag at h
    simp only [List.length_nil, bne_iff_ne, ne_eq, Decidable.not_not] at hl
    simp only [List.length_nil, hl, bne_self_eq_false, Bool.false_eq_true, ite_false, Except.ok.injEq] at h
    subst h
    have : ts = [] := List.eq_nil_of_length_eq_zero hl.symm
    subst this
    exact Unified.refl c bs fun _ => ⟨[], List.Perm.refl _, trivial⟩
  · intro ts bs left first rest hl ih bs' h
    unfold unifyBag at h
    simp only [hl, Bool.false_eq_true, ite_false] at h
    exact (ih bs' h).mono fun f hf => by simpa using hf
  · intro first rest passed bs left bs' h
    rw [unifyBagFrom] at h
    cases h
  · intro first rest passed bs _ _ bs' h
    rw [unifyBagFrom] at h
    cases h
  · intro first rest passed bs t more left b₁ h₁ b₂ h₂ ihf ihr bs' h
    rw [unifyBagFrom] at h
    simp only [h₁, h₂, Except.ok.injEq] at h
    subst h
    exact ((ihf b₁ h₁).trans (ihr b₂ h₂)).mono fun f ⟨hv, zs, hp, hm⟩ =>
      ⟨t :: zs, List.perm_middle.trans (hp.cons t), hv, hm⟩
  · intro first rest passed bs t more left b₁ h₁ left' h₂ _ _ ihn bs' h
    rw [unifyBagFrom] at h
    simp only [h₁, h₂] at h
    exact (ihn bs' h).mono fun f hf => by simpa using hf
  · intro first rest passed bs t more left h₁ _ bs' h
    rw [unifyBagFrom] at h
    simp only [h₁] at h
    cases h
  · intro first rest passed bs t more left h₁ _ ihn bs' h
    rw [unifyBagFrom] at h
    simp only [h₁] at h
    exact (ihn bs' h).mono fun f hf => by simpa using hf
  · intro bs x xs y ys ih1 ih2 bs' h hl
    rw [unifyList] at h
    cases h₁ : unify c x y bs with
    | error => simp [h₁, Except.bind] at h
    | ok b₁ =>
    simp only [h₁, Except.bind] at h
    exact ((ih1 b₁ h₁).trans (ih2 b₁ bs' h (by simpa using hl))).mono fun f hf => ⟨hf.1, hf.2⟩
  · intro xs ys bs hn bs' h hl
    rw [unifyList] at h
    · simp only [Except.ok.injEq] at h
      subst h
      refine Unified.refl c bs fun _ => ?_
      cases xs <;> cases ys
      · trivial
      · simp at hl
      · simp at hl
      · exact (hn _ _ _ _ rfl rfl).elim
    · exact hn

theorem unifyAnswer_sound {c : List String} {seen form : Value → CValue} {bs bs' : Bindings} {b a : Answer}
    (h : unifyAnswer c seen form bs b a = .ok bs') :
    Unified c bs bs' (fun f => AnswerCarries (fun x y => ValueMatches f (seen x) (form y)) b a) := by
  unfold unifyAnswer at h
  split at h
  · exact ((unify_sound c).1 _ _ _ _ h).mono fun f hf => by simpa [AnswerCarries] using hf
  · cases h
    exact Unified.refl c bs fun _ => by simp [AnswerCarries]
  · exact ((unify_sound c).1 _ _ _ _ h).mono fun f hf => by simpa [AnswerCarries] using hf
  · split at h
    · next hk =>
      cases h
      exact Unified.refl c bs fun _ => by simpa [AnswerCarries] using hk
    · cases h
  · cases h

end Tazuna.Thm.Data.Unify
