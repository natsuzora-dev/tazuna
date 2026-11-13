import Tazuna.Thm.Verify.Compare
import Tazuna.Thm.Verify.Matching

/-!
A value comparison that succeeds yields a match: `walk` and `walkContent` give a renaming that extends the given one,
and bags left to pair, under whose pairing the values match (ValueMatches).
-/

namespace Tazuna.Thm.Verify.Complete.Values

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching

/-- The implementation value of each declared createKey value under `R`. -/
def renameBy (d : List String) (R : Renaming) (x : String) : Option String :=
  if d.contains x then R.traceOf? x else none

/-- Each bag goal of `gs` pairs its elements under `renameBy d R`. -/
def BagsHold (d : List String) (R : Renaming) (gs : List Goal) : Prop :=
  ∀ l sl xs ys, Goal.bag l sl xs ys ∈ gs → ∃ zs, ys.Perm zs ∧ ListMatches (renameBy d R) xs zs

/-- Each goal of `gs` is a bag goal at the lines `l` and `sl` whose sides have equal lengths. -/
def BagGoals (l sl : Nat) (gs : List Goal) : Prop :=
  ∀ g ∈ gs, ∃ xs ys, g = .bag l sl xs ys ∧ xs.length = ys.length

/-- What a successful comparison from renaming `r` to `r'` with bag goals `gs` gives. -/
structure Walked (d : List String) (l sl : Nat) (r r' : Renaming) (gs : List Goal)
    (P : (String → Option String) → Prop) : Prop where
  grows : r <+: r'
  oneToOne : OneToOne r → OneToOne r'
  declared : ∀ u ∈ r', u ∈ r ∨ d.contains u.snapshot = true
  bags : BagGoals l sl gs
  sound : ∀ R, r' <+: R → BagsHold d R gs → P (renameBy d R)

theorem BagsHold.append {d : List String} {R : Renaming} {g₁ g₂ : List Goal} (h₁ : BagsHold d R g₁)
    (h₂ : BagsHold d R g₂) : BagsHold d R (g₁ ++ g₂) := by
  intro l sl xs ys h
  rcases List.mem_append.mp h with h | h
  · exact h₁ l sl xs ys h
  · exact h₂ l sl xs ys h

theorem BagsHold.left {d : List String} {R : Renaming} {g₁ g₂ : List Goal} (h : BagsHold d R (g₁ ++ g₂)) :
    BagsHold d R g₁ := fun l sl xs ys hm => h l sl xs ys (List.mem_append_left _ hm)

theorem BagsHold.right {d : List String} {R : Renaming} {g₁ g₂ : List Goal} (h : BagsHold d R (g₁ ++ g₂)) :
    BagsHold d R g₂ := fun l sl xs ys hm => h l sl xs ys (List.mem_append_right _ hm)

theorem Walked.refl (d : List String) (l sl : Nat) (r : Renaming) {P : (String → Option String) → Prop}
    (hP : ∀ R, P (renameBy d R)) : Walked d l sl r r [] P :=
  ⟨List.prefix_refl r, id, fun _ hu => .inl hu, fun _ h => absurd h List.not_mem_nil, fun R _ _ => hP R⟩

theorem Walked.trans {d : List String} {l sl : Nat} {r r₁ r₂ : Renaming} {g₁ g₂ : List Goal}
    {P Q : (String → Option String) → Prop} (h₁ : Walked d l sl r r₁ g₁ P) (h₂ : Walked d l sl r₁ r₂ g₂ Q) :
    Walked d l sl r r₂ (g₁ ++ g₂) (fun f => P f ∧ Q f) := by
  refine ⟨h₁.grows.trans h₂.grows, fun h => h₂.oneToOne (h₁.oneToOne h), fun u hu => ?_, fun g hg => ?_,
    fun R hR hb => ⟨h₁.sound R (h₂.grows.trans hR) hb.left, h₂.sound R hR hb.right⟩⟩
  · rcases h₂.declared u hu with h | h
    · exact h₁.declared u h
    · exact .inr h
  · rcases List.mem_append.mp hg with h | h
    · exact h₁.bags g h
    · exact h₂.bags g h

theorem Walked.mono {d : List String} {l sl : Nat} {r r' : Renaming} {gs : List Goal}
    {P Q : (String → Option String) → Prop} (h : Walked d l sl r r' gs P) (hPQ : ∀ f, P f → Q f) :
    Walked d l sl r r' gs Q :=
  ⟨h.grows, h.oneToOne, h.declared, h.bags, fun R hR hb => hPQ _ (h.sound R hR hb)⟩

theorem traceOf?_prefix {r R : Renaming} (hp : r <+: R) {s t : String} (h : r.traceOf? s = some t) :
    R.traceOf? s = some t := by
  obtain ⟨rest, rfl⟩ := hp
  simp only [Renaming.traceOf?, Option.map_eq_some_iff] at h ⊢
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, by rw [List.find?_append, hu]; rfl, rfl⟩

theorem traceOf?_mem {r : Renaming} {s t : String} (h : r.traceOf? s = some t) :
    ∃ u ∈ r, u.snapshot = s ∧ u.trace = t := by
  simp only [Renaming.traceOf?, Option.map_eq_some_iff] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, List.mem_of_find?_eq_some hu, by simpa using List.find?_some hu, rfl⟩

theorem traceOf?_of_mem {r : Renaming} (h : OneToOne r) {u : Use} (hu : u ∈ r) :
    r.traceOf? u.snapshot = some u.trace := by
  simp only [Renaming.traceOf?]
  cases hf : r.find? (·.snapshot == u.snapshot) with
  | none =>
    simp only [List.find?_eq_none, beq_iff_eq] at hf
    exact absurd rfl (hf u hu)
  | some v =>
    have hv := List.mem_of_find?_eq_some hf
    have hs : v.snapshot = u.snapshot := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.some.injEq]
    exact (h v hv u hu).mp hs

theorem bind_spec {r r' : Renaming} {u : Use} (hb : r.bind u = some r') :
    r <+: r' ∧ r'.traceOf? u.snapshot = some u.trace ∧ ∀ v ∈ r', v ∈ r ∨ v = u := by
  unfold Renaming.bind at hb
  cases hs : r.traceOf? u.snapshot with
  | some t =>
    rw [hs] at hb
    by_cases e : (t == u.trace) = true
    · simp only [e, ite_true, Option.some.injEq] at hb
      subst hb
      simp only [beq_iff_eq] at e
      exact ⟨List.prefix_refl _, by rw [hs, e], fun v hv => .inl hv⟩
    · simp [e] at hb
  | none =>
    rw [hs] at hb
    by_cases ht : r.takes u.trace = true
    · simp [ht] at hb
    · simp only [ht, Bool.false_eq_true, ite_false, Option.some.injEq] at hb
      subst hb
      refine ⟨List.prefix_append _ _, ?_, fun v hv => by simpa using hv⟩
      simp only [Renaming.traceOf?, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq] at hs
      simp only [Renaming.traceOf?, List.find?_append]
      rw [List.find?_eq_none.mpr (by simpa using hs)]
      simp

theorem walk_leaf_str (d : List String) (l sl : Nat) (v w : String) (r r' : Renaming) (gs : List Goal)
    (h : (if d.contains v then (r.bind { snapshot := v, trace := w, line := l, snapshotLine := sl }).map (·, [])
      else if w == v then some (r, []) else none) = some (r', gs)) :
    Walked d l sl r r' gs (fun f => ValueMatches f (.leaf (.str v)) (.leaf (.str w))) := by
  split at h
  · rename_i hd
    obtain ⟨r₁, hb, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hp, ht, hm⟩ := bind_spec hb
    refine ⟨hp, fun ho => bind_oneToOne ho hb, fun u hu => ?_, fun _ h => absurd h List.not_mem_nil,
      fun R hR _ => ?_⟩
    · rcases hm u hu with h | rfl
      · exact .inl h
      · exact .inr hd
    · simp only [ValueMatches]
      exact ⟨w, rfl, .inr (by simp [renameBy, show v ∈ d by simpa using hd, traceOf?_prefix hR ht])⟩
  · rename_i hd
    split at h
    · rename_i hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Walked.refl d l sl r fun R => ?_
      simp only [beq_iff_eq] at hw
      simp only [ValueMatches]
      exact ⟨w, rfl, .inl ⟨by simp [renameBy, show v ∉ d by simpa using hd], hw⟩⟩
    · cases h


theorem sameKeys_iff {fs gs : List (String × CValue)} (h : sameKeys fs gs = true) :
    ∀ k, k ∈ fs.map (·.1) ↔ k ∈ gs.map (·.1) := by
  simp only [sameKeys, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  intro k
  exact ⟨fun hk => h.1.2 k hk, fun hk => h.2 k hk⟩

set_option linter.unusedSimpArgs false in
theorem walk_sound (d : List String) (l sl : Nat) :
    (∀ s t r r' gs, walk d l sl s t r = some (r', gs) → Walked d l sl r r' gs (fun f => ValueMatches f s t)) ∧
    (∀ fs gs r r' g, walkFields d l sl fs gs r = some (r', g) →
      Walked d l sl r r' g (fun f => FieldsMatch f fs gs)) ∧
    (∀ xs ys r r' g, walkList d l sl xs ys r = some (r', g) → xs.length = ys.length →
      Walked d l sl r r' g (fun f => ListMatches f xs ys)) := by
  refine walk.mutual_induct d
    (fun s t r => ∀ r' gs, walk d l sl s t r = some (r', gs) → Walked d l sl r r' gs (fun f => ValueMatches f s t))
    (fun fs gs r => ∀ r' g, walkFields d l sl fs gs r = some (r', g) →
      Walked d l sl r r' g (fun f => FieldsMatch f fs gs))
    (fun xs ys r => ∀ r' g, walkList d l sl xs ys r = some (r', g) → xs.length = ys.length →
      Walked d l sl r r' g (fun f => ListMatches f xs ys))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r v w hd r' gs h
    rw [walk] at h
    exact walk_leaf_str d l sl v w r r' gs (by simpa [hd] using h)
  · intro r v w hd hw r' gs h
    rw [walk] at h
    exact walk_leaf_str d l sl v w r r' gs (by simpa [hd, hw] using h)
  · intro r v w hd hw r' gs h
    rw [walk] at h
    simp only [hd, hw, Bool.false_eq_true, ite_false] at h
    cases h
  · intro r v t ht r' gs h
    unfold walk at h
    cases t with
    | leaf x => cases x <;> first | exact absurd rfl (ht _) | simp at h
    | _ => simp at h
  · intro r v w hv hw r' gs h
    unfold walk at h
    cases v with
    | str v => exact absurd rfl (hv v)
    | _ =>
      simp only [hw, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Walked.refl d l sl r fun R => ?_
      simp only [beq_iff_eq] at hw
      simp [ValueMatches, hw]
  · intro r v w hv hw r' gs h
    unfold walk at h
    cases v with
    | str v => exact absurd rfl (hv v)
    | _ => simp [hw] at h
  · intro r xs ys hl ih r' gs h
    rw [walk] at h
    simp only [hl, ite_true] at h
    exact (ih r' gs h (by simpa using hl)).mono fun f hf => ⟨ys, rfl, hf⟩
  · intro r xs ys hl r' gs h
    rw [walk] at h
    simp [hl] at h
  · intro r xs ys hl ih r' gs h
    rw [walk] at h
    simp only [hl, ite_true] at h
    exact (ih r' gs h (by simpa using hl)).mono fun f hf => ⟨ys, rfl, hf⟩
  · intro r xs ys hl r' gs h
    rw [walk] at h
    simp [hl] at h
  · intro r xs ys hl r' gs h
    rw [walk] at h
    simp only [hl, ite_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨List.prefix_refl _, id, fun _ hu => .inl hu, fun g hg => ?_, fun R _ hb => ?_⟩
    · simp only [List.mem_singleton] at hg
      exact ⟨xs, ys, hg, by simpa using hl⟩
    · obtain ⟨zs, hp, hm⟩ := hb l sl xs ys List.mem_cons_self
      exact ⟨ys, zs, rfl, hp, hm⟩
  · intro r xs ys hl r' gs h
    rw [walk] at h
    simp [hl] at h
  · intro r fs gs hk ih r' g h
    rw [walk] at h
    simp only [hk, ite_true] at h
    exact (ih r' g h).mono fun f hf => ⟨gs, rfl, sameKeys_iff hk, hf⟩
  · intro r fs gs hk r' g h
    rw [walk] at h
    simp [hk] at h
  · intro s t r h1 h2 h3 h4 h5 h6 r' gs h
    rw [walk] at h
    · cases h
    all_goals assumption
  · intro gs r r' g h
    rw [walkFields] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Walked.refl d l sl r fun _ => by simp [FieldsMatch]
  · intro gs r k v fs ih1 ih2 r' g h
    rw [walkFields] at h
    cases hw : gs.lookup k with
    | none => simp [hw] at h
    | some w =>
    cases h₁ : walk d l sl v w r with
    | none => simp [hw, h₁] at h
    | some x₁ =>
    obtain ⟨r₁, g₁⟩ := x₁
    cases h₂ : walkFields d l sl fs gs r₁ with
    | none => simp [hw, h₁, h₂] at h
    | some x₂ =>
    obtain ⟨r₂, g₂⟩ := x₂
    rw [hw] at h; simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    rw [h₁] at h; simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    rw [h₂] at h
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ((ih1 w r₁ g₁ h₁).trans (ih2 r₁ r₂ g₂ h₂)).mono fun f hf => ⟨⟨w, hw, hf.1⟩, hf.2⟩
  · intro r x xs y ys ih1 ih2 r' g h hl
    rw [walkList] at h
    cases h₁ : walk d l sl x y r with
    | none => simp [h₁] at h
    | some x₁ =>
    obtain ⟨r₁, g₁⟩ := x₁
    cases h₂ : walkList d l sl xs ys r₁ with
    | none => simp [h₁, h₂] at h
    | some x₂ =>
    obtain ⟨r₂, g₂⟩ := x₂
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    rw [h₁] at h; simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    rw [h₂] at h
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ((ih1 r₁ g₁ h₁).trans (ih2 r₁ r₂ g₂ h₂ (by simpa using hl))).mono fun f hf => ⟨hf.1, hf.2⟩
  · intro xs ys r hn r' g h hl
    rw [walkList] at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine Walked.refl d l sl r fun _ => ?_
      cases xs <;> cases ys
      · trivial
      · simp at hl
      · simp at hl
      · exact (hn _ _ _ _ rfl rfl).elim
    · exact hn


theorem walkContent_sound {d : List String} {l sl : Nat} {s t : Option CValue} {r r' : Renaming} {gs : List Goal}
    (h : walkContent d l sl s t r = some (r', gs)) : Walked d l sl r r' gs (fun f => ContentMatches f s t) := by
  unfold walkContent at h
  split at h
  · exact (walk_sound d l sl).1 _ _ r r' gs h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Walked.refl d l sl r fun _ => trivial
  · cases h

end Tazuna.Thm.Verify.Complete.Values
