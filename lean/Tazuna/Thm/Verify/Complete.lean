import Tazuna.Thm.Verify.Complete.Induction

/-!
Verify finds every difference: a trace that compare reports nothing for matches the snapshot (Matches).
-/

namespace Tazuna.Thm.Verify.Complete

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Ids Tazuna.Thm.Verify.Complete.Lists
open Tazuna.Thm.Verify.Complete.Search Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Run
open Tazuna.Thm.Verify.Complete.Steps Tazuna.Thm.Verify.Complete.Top Tazuna.Thm.Verify.Complete.Induction

theorem traceOf?_inj {R : Renaming} (h : OneToOne R) {a b x : String} (ha : R.traceOf? a = some x)
    (hb : R.traceOf? b = some x) : a = b := by
  obtain ⟨u, hu, rfl, rfl⟩ := traceOf?_mem ha
  obtain ⟨v, hv, rfl, e⟩ := traceOf?_mem hb
  exact ((h u hu v hv).mpr e.symm)

theorem placed_of {ids : Ids} {F : Renaming} (hg : ids.bound <+: F) {sub : String → String → Prop} :
    ∀ {a b : Option String}, IdPlaced ids a b → Placed F.traceOf? sub a b
  | some _, some _, h => .inl (traceOf?_prefix hg h)
  | none, none, _ => trivial
  | some _, none, h => h.elim
  | none, some _, h => h.elim

theorem time_eq {s t : Line} (h : sameTime s t = true) : t.time.time = s.time.time := by
  simp only [sameTime, beq_iff_eq] at h; exact h.symm

/-- compare reports only the stage whose search across windows runs out, or compares the windows with a guide. -/
theorem compare_eq (snapshot lines : List (Option Line)) (internal : Line → Bool) :
    (∃ u, Verify.compare snapshot lines none internal = { findings := [.uncomparable u], bindings := [] }) ∨
      ∃ g, Verify.compare snapshot lines none internal =
        compareFrom (context snapshot internal g) lines.length none (windowsOf (steps snapshot) (steps lines)) {} := by
  unfold Verify.compare
  dsimp only
  split
  · exact .inr ⟨_, rfl⟩
  · exact .inl ⟨_, rfl⟩


theorem chain_prefix {α : Type} (f : Nat → List α) (N : Nat) (hstep : ∀ k, k + 1 < N → f k <+: f (k + 1)) :
    ∀ k, k < N → f k <+: f (N - 1) := by
  intro k hk
  have : ∀ d, k + d < N → f k <+: f (k + d) := by
    intro d
    induction d with
    | zero => intro _; exact List.prefix_refl _
    | succ d ih => intro hd; exact (ih (by omega)).trans (hstep (k + d) (by omega))
  have e : N - 1 = k + (N - 1 - k) := by omega
  rw [e]
  exact this _ (by omega)

/-- A trace that compare reports nothing for matches the snapshot. -/
theorem compare_complete (snapshot lines : List (Option Line)) (internal : Line → Bool)
    (h : (Verify.compare snapshot lines none internal).findings = []) : Matches snapshot lines internal := by
  have hlen : (steps snapshot).length = (steps lines).length :=
    (inputs_align snapshot lines none internal (by simp [h])).2
  obtain ⟨u, hu⟩ | ⟨g, hg⟩ := compare_eq snapshot lines internal
  · rw [hu] at h; cases h
  rw [hg] at h
  have hE := input_isSome_iff snapshot
  have hA := input_isSome_iff lines
  have quietAll : ∀ k, k < (steps snapshot).length →
      (compareFrom (context snapshot internal g) lines.length none ((windowsOf (steps snapshot) (steps lines)).drop k)
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)).findings = [] := by
    intro k
    induction k with
    | zero => intro _; exact h
    | succ k ih =>
      intro hk
      obtain ⟨_, _, _, _, _, _, hq⟩ := (quiet_step _ _ _ _ hlen hE hA k (by omega) (ih (by omega))).2.2 hk
      exact hq
  have quietW := fun k (hk : k < (steps snapshot).length) => quiet_step _ _ _ _ hlen hE hA k hk (quietAll k hk)
  have getE : ∀ k, k < (steps snapshot).length → ∃ e, (steps snapshot)[k]? = some e :=
    fun k hk => ⟨_, List.getElem?_eq_getElem hk⟩
  have getA : ∀ k, k < (steps snapshot).length → ∃ a, (steps lines)[k]? = some a :=
    fun k hk => ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have invAll : ∀ k, k < (steps snapshot).length →
      Inv snapshot (steps lines) (subsOf (context snapshot internal g) (steps snapshot) (steps lines)) k
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k) := by
    intro k
    induction k with
    | zero => intro _; exact Inv.zero _ _ _
    | succ k ih =>
      intro hk
      obtain ⟨e, he⟩ := getE k (by omega)
      obtain ⟨a, ha⟩ := getA k (by omega)
      have q := quietW k (by omega)
      have WS := window_step snapshot (steps lines) internal g k e a he ha (ih (by omega)) q.1 q.2.1
      obtain ⟨s, t, p, hs, ht, hsame, _⟩ := q.2.2 hk
      rw [stateAt_succ _ _ _ k hs ht hsame]
      exact (input_step WS.inv hsame).1
  have WS : ∀ k e a, (steps snapshot)[k]? = some e → (steps lines)[k]? = some a →
      WindowStep snapshot (steps lines) internal g k e a
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)
        (windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
          (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k))
        (pairingAt (context snapshot internal g) (steps snapshot) (steps lines) k) := by
    intro k e a he ha
    have hk : k < (steps snapshot).length := (List.getElem?_eq_some_iff.mp he).1
    exact window_step snapshot (steps lines) internal g k e a he ha (invAll k hk) (quietW k hk).1 (quietW k hk).2.1
  -- The state after window `k`, and the input facts of window `k`.
  have inputOf : ∀ k, k + 1 < (steps snapshot).length → ∃ s t p,
      (steps snapshot)[k]?.bind (·.input) = some s ∧ (steps lines)[k]?.bind (·.input) = some t ∧
      InputOK (windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)) s t p ∧
      stateAt (context snapshot internal g) (steps snapshot) (steps lines) (k + 1) =
        { windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
          (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k) with
          ids := p.ids, keys := p.keys } := by
    intro k hk
    obtain ⟨e, he⟩ := getE k (by omega)
    obtain ⟨a, ha⟩ := getA k (by omega)
    obtain ⟨s, t, p, hs, ht, hsame, _⟩ := (quietW k (by omega)).2.2 hk
    exact ⟨s, t, p, hs, ht, (input_step (WS k e a he ha).inv hsame).2, stateAt_succ _ _ _ k hs ht hsame⟩
  have stepKeys : ∀ k, k + 1 < (steps snapshot).length →
      (windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)).keys <+:
      (windowRun (context snapshot internal g) (steps snapshot) (steps lines) (k + 1)
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) (k + 1))).keys ∧
      (windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)).ids.bound <+:
      (windowRun (context snapshot internal g) (steps snapshot) (steps lines) (k + 1)
        (stateAt (context snapshot internal g) (steps snapshot) (steps lines) (k + 1))).ids.bound := by
    intro k hk
    obtain ⟨s, t, p, _, _, I, hst⟩ := inputOf k hk
    obtain ⟨e, he⟩ := getE (k + 1) hk
    obtain ⟨a, ha⟩ := getA (k + 1) hk
    have W1 := WS (k + 1) e a he ha
    have fk := W1.ok.frame.keys
    have fi := W1.ok.frame.ids
    rw [hst] at fk fi
    rw [W1.keys, W1.ids]
    exact ⟨I.keys.trans fk, I.ids.trans fi⟩
  have hN : 0 < (steps snapshot).length := by
    obtain ⟨ins, hi⟩ := steps_inputs snapshot
    have := congrArg List.length hi
    simp only [List.length_map, List.length_append, List.length_singleton] at this
    omega
  have monoK := chain_prefix (fun k => (windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
    (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)).keys) _ (fun k hk => (stepKeys k hk).1)
  have monoI := chain_prefix (fun k => (windowRun (context snapshot internal g) (steps snapshot) (steps lines) k
    (stateAt (context snapshot internal g) (steps snapshot) (steps lines) k)).ids.bound) _
    (fun k hk => (stepKeys k hk).2)
  generalize hF : windowRun (context snapshot internal g) (steps snapshot) (steps lines) ((steps snapshot).length - 1)
    (stateAt (context snapshot internal g) (steps snapshot) (steps lines) ((steps snapshot).length - 1)) = F
    at monoK monoI
  have last : Inv snapshot (steps lines) (subsOf (context snapshot internal g) (steps snapshot) (steps lines))
      (steps snapshot).length F := by
    obtain ⟨e, he⟩ := getE _ (by omega : (steps snapshot).length - 1 < (steps snapshot).length)
    obtain ⟨a, ha⟩ := getA _ (by omega : (steps snapshot).length - 1 < (steps snapshot).length)
    have := (WS _ e a he ha).inv
    rw [hF, show (steps snapshot).length - 1 + 1 = (steps snapshot).length by omega] at this
    exact this
  refine ⟨hlen, F.keys.traceOf?, F.ids.bound.traceOf?,
    fun k => (pairingAt (context snapshot internal g) (steps snapshot) (steps lines) k).pairs,
    subsOf (context snapshot internal g) (steps snapshot) (steps lines),
    fun a b x ha hb => traceOf?_inj last.oneToOne ha hb, fun a x ha => ?_,
    fun a b x ha hb => traceOf?_inj last.idsWf.oneToOne ha hb, ?_⟩
  · obtain ⟨u, hu, rfl, _⟩ := traceOf?_mem ha
    exact last.keysSnap u hu
  intro k e a he ha
  have hk : k < (steps snapshot).length := (List.getElem?_eq_some_iff.mp he).1
  have W1 := WS k e a he ha
  have Fr := W1.ok.frame
  have hK : (pairingAt (context snapshot internal g) (steps snapshot) (steps lines) k).keys <+: F.keys := by
    rw [← W1.keys]; exact monoK k hk
  have hI : (pairingAt (context snapshot internal g) (steps snapshot) (steps lines) k).ids.bound <+: F.ids.bound := by
    rw [← W1.ids]; exact monoI k hk
  have cont := Fr.content F.keys hK (fun _ _ _ _ h => nomatch h)
  have hren := renameBy_eq _ _ _ W1.declared F.keys
  refine ⟨W1.ok.pairsFst, W1.ok.pairsSnd, fun q hq => ?_, fun p₁ hp₁ q₁ hq₁ hf => ?_, ?_, ?_, ?_⟩
  · have po := Fr.pairs q hq
    refine ⟨po.type, time_eq po.time, ?_, ?_⟩
    · have hp := po.place
      revert hp
      cases q.1.line.body with
      | answer d i to x =>
        intro hp
        obtain ⟨t', ht', hl⟩ := hp
        show Placed _ _ (some to) q.2.line.body.to?
        rw [ht']
        exact .inl (traceOf?_prefix hI hl)
      | event d i n x r => exact fun hp => ⟨hp.1, placed_of hI hp.2⟩
      | _ => exact id
    · have := cont.2.1 q hq
      dsimp only [scopeOf] at this
      rw [hren] at this
      exact this
  · by_cases e : p₁ = q₁
    · subst e; exact absurd hf (mustFollow_irrefl _ _)
    · exact (pairwise_of_ne (fun _ _ h => h.symm) Fr.order p₁ hp₁ q₁ hq₁ e).1 (List.contains_iff_mem.mpr hf)
  · refine ⟨by rw [← W1.openS]; exact W1.ok.subsFst, by rw [← W1.openT]; exact W1.ok.subsSnd, fun q hq => ?_⟩
    obtain ⟨s', t', hs', ht', hn⟩ := Fr.subsOK q hq
    refine ⟨s', t', by rw [← W1.openS]; exact hs', by rw [← W1.openT]; exact ht', hn, ?_⟩
    have := cont.2.2 q hq s' t' hs' ht'
    dsimp only [scopeOf] at this
    rw [hren] at this
    exact this
  · have h1 := input_isSome_iff snapshot k
    have h2 := input_isSome_iff lines k
    simp only [he, ha, Option.bind_some] at h1 h2
    rw [← hlen] at h2
    exact Bool.eq_iff_iff.mpr (h1.trans h2.symm)
  · intro s t hs ht
    have hk1 : k + 1 < (steps snapshot).length := (input_isSome_iff snapshot k).mp (by simp [he, hs])
    obtain ⟨s', t', p', hs', ht', I, hst⟩ := inputOf k hk1
    simp only [he, ha, Option.bind_some, hs, ht, Option.some.injEq] at hs' ht'
    subst hs' ht'
    obtain ⟨e', he'⟩ := getE (k + 1) hk1
    obtain ⟨a', ha'⟩ := getA (k + 1) hk1
    have W2 := WS (k + 1) e' a' he' ha'
    have fk := W2.ok.frame.keys
    have fi := W2.ok.frame.ids
    rw [hst] at fk fi
    have hK' : p'.keys <+: F.keys := fk.trans (by rw [← W2.keys]; exact monoK (k + 1) hk1)
    have hI' : p'.ids.bound <+: F.ids.bound := fi.trans (by rw [← W2.ids]; exact monoI (k + 1) hk1)
    have hren' := renameBy_eq _ _ _ W1.inv.declared F.keys
    refine ⟨I.type, I.name, time_eq I.time, traceOf?_prefix hI' I.own, ?_⟩
    have hr := I.rest
    revert hr
    cases s.line.body with
    | time | restart => intro _; trivial
    | unsubscribe d i to => intro hr; exact placed_of hI' hr
    | answer d i to x =>
      intro hr
      refine ⟨?_, by rw [← hren']; exact hr.2 F.keys hK'⟩
      rcases hr.1 with ⟨l, hl, t'', ht'', hm⟩ | hid
      · rw [ht'']
        obtain ⟨j, hj, hsub⟩ := W1.inv.subs to l hl t'' hm
        exact .inr ⟨j, by omega, hsub⟩
      · exact placed_of hI' hid
    | _ => intro hr; exact ⟨placed_of hI' hr.1, by rw [← hren']; exact hr.2 F.keys hK'⟩


/-- With a malformed line, compare always reports. -/
theorem compare_malformed_found (snapshot lines : List (Option Line)) (n : Nat) (internal : Line → Bool) :
    (Verify.compare snapshot lines (some n) internal).findings ≠ [] := by
  obtain ⟨ms, u, hc⟩ := compare_malformed snapshot lines n internal
  simp [hc]

end Tazuna.Thm.Verify.Complete
