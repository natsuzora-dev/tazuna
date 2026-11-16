import Tazuna.Network
import Tazuna.Thm.Verify.Complete.Values

namespace Tazuna.Thm.Semantics.System.Peer

open Tazuna.Data Tazuna.Semantics Tazuna.Network Tazuna.Thm.Verify.Matching

/-- No string of the bindings is bound to two strings, and no two strings to one. -/
def OneToOne (bs : Bindings) : Prop := ∀ p ∈ bs, ∀ q ∈ bs, (p.1 = q.1 ↔ p.2 = q.2)

/-- The string that the peer's string `v` stands for under `bs`: its binding for a string of `created`, else itself. -/
def standsFor (created : List String) (bs : Bindings) (v : String) : Option String :=
  if created.contains v then bs.lookup v else none

theorem lookup_append_of {bs rest : Bindings} {v w : String} (h : bs.lookup v = some w) :
    (bs ++ rest).lookup v = some w := by
  induction bs with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.lookup, List.cons_append] at h ⊢
    split at h <;> simp_all

theorem lookup_prefix {bs R : Bindings} (hp : bs <+: R) {v w : String} (h : bs.lookup v = some w) :
    R.lookup v = some w := by
  obtain ⟨rest, rfl⟩ := hp
  exact lookup_append_of h

theorem lookup_none {bs : Bindings} {v : String} (h : bs.lookup v = none) : ∀ q ∈ bs, q.1 ≠ v := by
  induction bs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.lookup] at h
    split at h
    · cases h
    · rename_i hne
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · intro he
        simp [he] at hne
      · exact ih h q hq

theorem lookup_append_none {bs rest : Bindings} {v : String} (h : bs.lookup v = none) :
    (bs ++ rest).lookup v = rest.lookup v := by
  induction bs with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.lookup, List.cons_append] at h ⊢
    split at h <;> simp_all

theorem bind_spec {bs bs' : Bindings} {v w : String} (h : bs.bind v w = some bs') :
    bs <+: bs' ∧ bs'.lookup v = some w ∧ (OneToOne bs → OneToOne bs') := by
  unfold Bindings.bind at h
  cases hv : bs.lookup v with
  | some x =>
    rw [hv] at h
    by_cases e : (x == w) = true
    · simp only [e, ite_true, Option.some.injEq] at h
      subst h
      simp only [beq_iff_eq] at e
      exact ⟨List.prefix_refl _, by rw [hv, e], id⟩
    · simp [e] at h
  | none =>
    rw [hv] at h
    by_cases hw : bs.any (·.2 == w) = true
    · simp [hw] at h
    · simp only [hw, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst h
      have hk := lookup_none hv
      have ht : ∀ q ∈ bs, q.2 ≠ w := by
        intro q hq he
        exact hw (List.any_eq_true.mpr ⟨q, hq, by simp [he]⟩)
      refine ⟨List.prefix_append _ _, ?_, fun ho p hp q hq => ?_⟩
      · rw [lookup_append_none hv]
        simp [List.lookup]
      · rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
        · exact ho p hp q hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact ⟨fun e => absurd e (hk p hp), fun e => absurd e (ht p hp)⟩
        · simp only [List.mem_singleton] at hp
          subst hp
          exact ⟨fun e => absurd e.symm (hk q hq), fun e => absurd e.symm (ht q hq)⟩
        · simp only [List.mem_singleton] at hp hq
          subst hp hq
          simp

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

variable {normal : String → Value → CValue} {service peer : String} {arrivals : List Nat}
  {aLines bLines : List TraceLine}

/-- The peer's createKey values, which the bindings bind. -/
abbrev createdOf (bLines : List TraceLine) : List String := bLines.flatMap (·.created.getD [])

/-- The peer's form of its value `x` of the definition `n`, with its peer keys turned back. -/
abbrev seenOf (normal : String → Value → CValue) (service : String) (aLines : List TraceLine) (n : String)
    (x : Value) : CValue :=
  normal n (Bindings.rename ((peerKeys service aLines).map fun (k, v) => (v, k)) x)

/--
Whether the scenario's value `y` of the peer's definition `n` stands for the peer's value `x` under the bindings `bs`:
in the forms that verify compares, `x` with its peer keys turned back into the run's createKey values matches `y` when
each createKey value of the peer stands for its binding (ValueMatches).
-/
def PeerSees (normal : String → Value → CValue) (service : String) (aLines bLines : List TraceLine) (bs : Bindings)
    (n : String) (x y : Value) : Prop :=
  ValueMatches (standsFor (createdOf bLines) bs) (seenOf normal service aLines n x) (normal n y)

/--
Whether the peer's line `b` emits the event `n`, at or before `time`, with a payload that `payload` stands for, as the
result of the request `resultOf` when it is given.
-/
def PeerEmits (normal : String → Value → CValue) (service : String) (aLines bLines : List TraceLine) (bs : Bindings)
    (n : String) (payload : Value) (resultOf : Option String) (time : DateTime) (b : TraceLine) : Prop :=
  ∃ id p r, b.body = .event .out id n p r ∧ (∀ q, resultOf = some q → r = some q) ∧
    b.time.time ≤ time.time ∧ PeerSees normal service aLines bLines bs n p payload

theorem peerLine_answer {bs bs' : Bindings} {i : Nat} {l : TraceLine} {id : String} {to target : String}
    {a : Answer} (hl : l.body = .answer .in id to a) (ht : peerTarget? peer aLines to = some target)
    (hu : unreached aLines to = false) (h : peerLine normal service peer arrivals aLines bLines bs i l = .ok bs') :
    ∃ t b, (answersTo (bLines.take (peerBefore arrivals bLines i)) .out to)[(answersTo (aLines.take i) .in to).length]? =
        some (t, b) ∧ t.time ≤ l.time.time ∧ Unified (createdOf bLines) bs bs'
          (fun f => AnswerCarries (fun x y => ValueMatches f (seenOf normal service aLines target x)
            (normal target y)) b a) := by
  simp only [peerLine, hl, ht, hu, Bool.false_eq_true, ite_false] at h
  split at h
  · cases h
  · split at h
    · cases h
    · next t b hb =>
      split at h
      · next bs'' hs =>
        cases h
        split at hs
        · next htime => exact ⟨t, b, hb, htime, unifyAnswer_sound hs⟩
        · cases hs
      · cases h
      · cases h

theorem getElem?_take_some {α : Type} {xs : List α} {n j : Nat} {x : α} (h : (xs.take n)[j]? = some x) :
    j < n ∧ xs[j]? = some x := by
  rw [List.getElem?_take] at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem peerLine_event {bs bs' : Bindings} {i : Nat} {l : TraceLine} {id : String} {name n : String}
    {payload : Value} {resultOf : Option String} (hl : l.body = .event .in id name payload resultOf)
    (hn : peerName? peer name = some n) (h : peerLine normal service peer arrivals aLines bLines bs i l = .ok bs') :
    ∃ j b, bLines[j]? = some b ∧ j < peerBefore arrivals bLines i ∧ ∃ id' p r, b.body = .event .out id' n p r ∧
      (∀ q, resultOf = some q → r = some q) ∧ b.time.time ≤ l.time.time ∧
      Unified (createdOf bLines) bs bs' (fun f => ValueMatches f (seenOf normal service aLines n p) (normal n payload)) := by
  simp only [peerLine, hl, hn] at h
  split at h
  · next bs'' hf =>
    cases h
    obtain ⟨x, hx, hs⟩ := List.exists_of_findSome?_eq_some hf
    obtain ⟨b, hb, hbx⟩ := List.mem_filterMap.mp hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
    split at hbx
    · next id' m p r hbody =>
      split at hbx
      · next hc =>
        cases hbx
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.all_eq_true] at hc
        obtain ⟨⟨rfl, htime⟩, hr⟩ := hc
        obtain ⟨hj, hb⟩ := getElem?_take_some hj
        cases hu : unify (createdOf bLines) (seenOf normal service aLines m p) (normal m payload) bs with
        | error => simp [hu, Except.toOption] at hs
        | ok b' =>
          simp only [hu, Except.toOption, Option.some.injEq] at hs
          subst hs
          exact ⟨j, b, hb, hj, id', p, r, hbody, fun q hq => by simpa using hr q hq,
            htime, (unify_sound _).1 _ _ _ _ hu⟩
      · cases hbx
    · cases hbx
  · cases h

theorem peerLine_grows {bs bs' : Bindings} {i : Nat} {l : TraceLine}
    (h : peerLine normal service peer arrivals aLines bLines bs i l = .ok bs') :
    bs <+: bs' ∧ (OneToOne bs → OneToOne bs') := by
  cases hb : l.body with
  | answer d _ to a =>
    cases d with
    | out => simp [peerLine, hb] at h; subst h; exact ⟨List.prefix_refl _, id⟩
    | «in» =>
      cases ht : peerTarget? peer aLines to with
      | none => simp [peerLine, hb, ht] at h; subst h; exact ⟨List.prefix_refl _, id⟩
      | some target =>
        cases hu : unreached aLines to with
        | true => simp [peerLine, hb, ht, hu] at h; subst h; exact ⟨List.prefix_refl _, id⟩
        | false =>
          obtain ⟨_, _, _, _, hU⟩ := peerLine_answer hb ht hu h
          exact ⟨hU.grows, hU.oneToOne⟩
  | event d _ name payload resultOf =>
    cases d with
    | out => simp [peerLine, hb] at h; subst h; exact ⟨List.prefix_refl _, id⟩
    | «in» =>
      cases hn : peerName? peer name with
      | none => simp [peerLine, hb, hn] at h; subst h; exact ⟨List.prefix_refl _, id⟩
      | some n =>
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hU⟩ := peerLine_event hb hn h
        exact ⟨hU.grows, hU.oneToOne⟩
  | _ => simp [peerLine, hb] at h; subst h; exact ⟨List.prefix_refl _, id⟩

theorem peerBindings_succ {i : Nat} {l : TraceLine} (hi : aLines[i]? = some l) :
    peerBindings normal service peer arrivals aLines bLines (i + 1) =
      (peerLine normal service peer arrivals aLines bLines (peerBindings normal service peer arrivals aLines bLines i) i l).toOption.getD
        (peerBindings normal service peer arrivals aLines bLines i) := by
  have hz : aLines.zipIdx[i]? = some (l, i) := by simp [List.getElem?_zipIdx, hi]
  simp only [peerBindings, List.take_add_one, List.foldl_append, hz]
  rfl

theorem peerBindings_grows (i : Nat) :
    peerBindings normal service peer arrivals aLines bLines i <+: peerBindings normal service peer arrivals aLines bLines (i + 1) ∧
      (OneToOne (peerBindings normal service peer arrivals aLines bLines i) →
        OneToOne (peerBindings normal service peer arrivals aLines bLines (i + 1))) := by
  cases hi : aLines[i]? with
  | none =>
    have hz : aLines.zipIdx[i]? = none := by simp [List.getElem?_zipIdx, hi]
    have he : peerBindings normal service peer arrivals aLines bLines (i + 1) =
        peerBindings normal service peer arrivals aLines bLines i := by
      simp only [peerBindings, List.take_add_one, List.foldl_append, hz]
      rfl
    rw [he]
    exact ⟨List.prefix_refl _, id⟩
  | some l =>
    rw [peerBindings_succ hi]
    cases h : peerLine normal service peer arrivals aLines bLines (peerBindings normal service peer arrivals aLines bLines i) i l with
    | error _ => exact ⟨List.prefix_refl _, id⟩
    | ok bs' => exact peerLine_grows h

theorem peerBindings_prefix {i j : Nat} (h : i ≤ j) :
    peerBindings normal service peer arrivals aLines bLines i <+: peerBindings normal service peer arrivals aLines bLines j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih => exact (ih (by omega)).trans (peerBindings_grows (i + k)).1

/-- The bindings that the check builds are one-to-one. -/
theorem peerBindings_oneToOne (n : Nat) : OneToOne (peerBindings normal service peer arrivals aLines bLines n) := by
  induction n with
  | zero => simp [peerBindings, OneToOne]
  | succ n ih => exact (peerBindings_grows n).2 ih

/-- No violation means that the peer's run of the derived inputs did not halt. -/
theorem peerFindings_halted {halted : Option (Origin × String)}
    (h : peerFindings normal service peer arrivals aLines bLines halted = []) : halted = none := by
  cases halted with
  | none => rfl
  | some p => simp [peerFindings] at h

theorem peerLine_ok {halted : Option (Origin × String)} {i : Nat} {l : TraceLine}
    (h : peerFindings normal service peer arrivals aLines bLines halted = []) (hi : aLines[i]? = some l) :
    peerLine normal service peer arrivals aLines bLines (peerBindings normal service peer arrivals aLines bLines i) i l =
      .ok (peerBindings normal service peer arrivals aLines bLines (i + 1)) := by
  cases peerFindings_halted h
  simp only [peerFindings] at h
  have hz : (l, i) ∈ aLines.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hi
  have := List.filterMap_eq_nil_iff.mp h _ hz
  rw [peerBindings_succ hi]
  split at this
  · cases this
  · next bs' hb => rw [hb]; rfl

/-- The bindings after the whole run: the one renaming under which the stage 1 theorems hold. -/
abbrev peerFinal (normal : String → Value → CValue) (service peer : String) (arrivals : List Nat)
    (aLines bLines : List TraceLine) : Bindings :=
  peerBindings normal service peer arrivals aLines bLines aLines.length

theorem final_of {i : Nat} {l : TraceLine} (hi : aLines[i]? = some l) :
    peerBindings normal service peer arrivals aLines bLines (i + 1) <+: peerFinal normal service peer arrivals aLines bLines :=
  peerBindings_prefix (List.getElem?_eq_some_iff.mp hi).1

/--
Stage 1 for answers: with no violation, each answer that a mock gives to a request to the peer that reached it is the
peer's answer to the request at the same place, the k-th answer to it when the mock is the k-th, as the scenario sees
the peer's values under the final bindings (PeerSees), and the peer gives it at or before the mock's time, before it
takes an input that arrives after the mock (peerBefore).
-/
theorem mocked_answer_given {halted : Option (Origin × String)} {i : Nat} {l : TraceLine} {id : String}
    {to target : String} {a : Answer}
    (h : peerFindings normal service peer arrivals aLines bLines halted = []) (hi : aLines[i]? = some l)
    (hl : l.body = .answer .in id to a) (ht : peerTarget? peer aLines to = some target)
    (hu : unreached aLines to = false) :
    ∃ t b, (answersTo (bLines.take (peerBefore arrivals bLines i)) .out to)[(answersTo (aLines.take i) .in to).length]? =
        some (t, b) ∧
      AnswerCarries (PeerSees normal service aLines bLines (peerFinal normal service peer arrivals aLines bLines) target) b a ∧
        t.time ≤ l.time.time := by
  obtain ⟨t, b, hb, htime, hU⟩ := peerLine_answer hl ht hu (peerLine_ok h hi)
  exact ⟨t, b, hb, hU.sound _ (final_of hi), htime⟩

theorem answersTo_take_getElem? {lines : List TraceLine} {n k : Nat} {d : Dir} {to : String} {x : DateTime × Answer}
    (h : (answersTo (lines.take n) d to)[k]? = some x) : (answersTo lines d to)[k]? = some x := by
  have e : answersTo lines d to = answersTo (lines.take n) d to ++ answersTo (lines.drop n) d to := by
    simp only [answersTo, ← List.filterMap_append, List.take_append_drop]
  rw [e, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem filterMap_getElem? {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (k : Nat) (y : β), (xs.filterMap f)[k]? = some y →
      ∃ i x, xs[i]? = some x ∧ f x = some y ∧ ((xs.take i).filterMap f).length = k
  | [], _, _, h => by simp at h
  | x :: xs, k, y, h => by
    rw [List.filterMap_cons] at h
    cases hf : f x with
    | none =>
      rw [hf] at h
      obtain ⟨i, z, hz, hfz, hl⟩ := filterMap_getElem? f xs k y h
      exact ⟨i + 1, z, by simpa using hz, hfz, by simp [hf, hl]⟩
    | some b =>
      rw [hf] at h
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        exact ⟨0, x, rfl, by rw [hf, h], by simp⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at h
        obtain ⟨i, z, hz, hfz, hl⟩ := filterMap_getElem? f xs k y h
        exact ⟨i + 1, z, by simpa using hz, hfz, by simp [hf, hl]⟩

/-- The k-th answer in direction `dir` to `to` is the answer of a line that k such answers come before. -/
theorem answersTo_getElem? {lines : List TraceLine} {dir : Dir} {to : String} {k : Nat} {t : DateTime} {a : Answer}
    (h : (answersTo lines dir to)[k]? = some (t, a)) :
    ∃ i l id, lines[i]? = some l ∧ l.body = .answer dir id to a ∧ l.time = t ∧
      (answersTo (lines.take i) dir to).length = k := by
  obtain ⟨i, l, hl, hf, hk⟩ := filterMap_getElem? _ lines k (t, a) h
  refine ⟨i, l, ?_⟩
  split at hf
  · next d id' to' a' hb =>
    split at hf
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      exact ⟨id', hl, hb, rfl, hk⟩
    · simp at hf
  · simp at hf

/--
Stage 1 for subscriptions and every other request: with no violation, the answers that mocks give to a request to the
peer that reached it are, in order and as the scenario sees the peer's values under the final bindings (PeerSees), a
prefix of the peer's answers to the request, each given at or before the mock's time.
-/
theorem mocked_answers_prefix {halted : Option (Origin × String)} {to target : String} {k : Nat} {t : DateTime}
    {a : Answer} (h : peerFindings normal service peer arrivals aLines bLines halted = [])
    (ht : peerTarget? peer aLines to = some target)
    (hu : unreached aLines to = false) (hk : (answersTo aLines .in to)[k]? = some (t, a)) :
    ∃ t' b, (answersTo bLines .out to)[k]? = some (t', b) ∧
      AnswerCarries (PeerSees normal service aLines bLines (peerFinal normal service peer arrivals aLines bLines) target) b a ∧
        t'.time ≤ t.time := by
  obtain ⟨i, l, id, hi, hl, rfl, rfl⟩ := answersTo_getElem? hk
  obtain ⟨t', b, hb, hc, hle⟩ := mocked_answer_given h hi hl ht hu
  exact ⟨t', b, answersTo_take_getElem? hb, hc, hle⟩

/--
Stage 1 for events: with no violation, the peer emits each event of the peer that the scenario receives, at or before
the time the scenario receives it, with a payload that the scenario's stands for under the final bindings, as the
result of the request that the scenario names as its result (PeerEmits), and before it takes an input that arrives
after the scenario's line (peerBefore).
Two deliveries of one event may name the same line of the peer.
-/
theorem received_event_emitted {halted : Option (Origin × String)} {i : Nat} {l : TraceLine} {id : String}
    {name n : String} {payload : Value} {resultOf : Option String}
    (h : peerFindings normal service peer arrivals aLines bLines halted = []) (hi : aLines[i]? = some l)
    (hl : l.body = .event .in id name payload resultOf) (hn : peerName? peer name = some n) :
    ∃ j b, bLines[j]? = some b ∧ j < peerBefore arrivals bLines i ∧
      PeerEmits normal service aLines bLines (peerFinal normal service peer arrivals aLines bLines) n payload resultOf l.time b := by
  obtain ⟨j, b, hb, hj, id', p, r, hbody, hr, htime, hU⟩ := peerLine_event hl hn (peerLine_ok h hi)
  exact ⟨j, b, hb, hj, id', p, r, hbody, hr, htime, hU.sound _ (final_of hi)⟩

end Tazuna.Thm.Semantics.System.Peer
