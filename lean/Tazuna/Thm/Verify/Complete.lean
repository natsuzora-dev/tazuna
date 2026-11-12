import Tazuna.Thm.Verify.Complete.Induction

/-!
Verify finds every difference: a trace that compare reports nothing for matches the snapshot (Matches), under the
narrowings of `Narrowed`.
-/

namespace Tazuna.Thm.Verify.Complete
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Bindings Tazuna.Thm.Verify.Complete.Inputs Tazuna.Thm.Verify.Complete.Steps Tazuna.Thm.Verify.Complete.Subscriptions Tazuna.Thm.Verify.Complete.Top Tazuna.Thm.Verify.Complete.Induction

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching

theorem mustFollow_irrefl (S : List (Option Line)) (n : Nat) : n ∉ mustFollow S n := by
  unfold mustFollow
  cases hh : (((steps S).flatMap fun w => w.before.zipIdx.filterMap fun (o, k) =>
      if o.index - 1 == n then some ((o.line.after.getD []).filterMap (earlierWithId (w.before.take k)))
      else none).head?) with
  | none => simp
  | some xs =>
    simp only [Option.getD_some]
    intro hn
    obtain ⟨w, hw, hx⟩ := List.mem_flatMap.mp (List.mem_of_mem_head? hh)
    obtain ⟨⟨o, k⟩, hok, hf⟩ := List.mem_filterMap.mp hx
    simp only at hf
    split at hf
    · rename_i he
      simp only [Option.some.injEq] at hf
      subst hf
      obtain ⟨id, _, hy⟩ := List.mem_filterMap.mp hn
      simp only [earlierWithId, Option.map_eq_some_iff] at hy
      obtain ⟨o', hf', ho'⟩ := hy
      have hmem : o' ∈ w.before.take k := List.mem_reverse.mp (List.mem_of_find?_eq_some hf')
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
      rw [List.getElem?_take] at hj
      split at hj
      · rename_i hjk
        have hk := List.mem_zipIdx_iff_getElem?.mp hok
        simp only at hk
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hw
        have hwa := windowAt S i w hi
        have hord := (List.pairwise_append.mp (by simpa only [List.map_append] using hwa.order)).1
        have hjl : j < w.before.length := (List.getElem?_eq_some_iff.mp hj).1
        have hkl : k < w.before.length := (List.getElem?_eq_some_iff.mp hk).1
        have := List.pairwise_iff_getElem.mp hord j k (by simpa using hjl) (by simpa using hkl) hjk
        simp only [List.getElem_map] at this
        rw [List.getElem?_eq_some_iff.mp hj |>.2, List.getElem?_eq_some_iff.mp hk |>.2] at this
        have h1 := (hwa.before o' (List.mem_of_getElem? hj)).1.1
        simp only [beq_iff_eq] at he
        omega
      · cases hj
    · cases hf

/-- The out pairing of window `k`. -/
noncomputable def outPairs (S L : List (Option Line)) (internal : Line → Bool) (k : Nat) : List Pair :=
  let c := context S internal
  let E := steps S
  let A := steps L
  let w := windowRun c E A k (stateAt c E A k)
  open Classical in
  if h : ∃ pairs : List Pair, ∃ e a, E[k]? = some e ∧ A[k]? = some a ∧
      ((pairs.map (·.1)).Perm (specCompared c e.before)) ∧ (pairs.map (·.2)).Perm (traceCompared c a.before) ∧
      (∀ p ∈ pairs, PairOK c w.ids w.values p) ∧
      (∀ p ∈ pairs, ∀ q ∈ pairs, (p.1.index - 1) ∈ mustFollow S (q.1.index - 1) → p.2.index ≤ q.2.index) ∧
      (pairs.map (·.2.index)).Nodup then Classical.choose h else []

/-- The renaming of request and subscription ids: the bound ids of everything but subscriptions. -/
noncomputable def renameIds (S : List (Option Line)) (ids : Ids) (r : String) : Option String :=
  open Classical in if SubId S r then none else ids.bound.lookup r

theorem placed_of {S L : List (Option Line)} {internal : Line → Bool} {k : Nat} {ids F : Ids}
    {sids : List (String × List String)} (hext : BoundExt ids F)
    (hsub : ∀ r qs q, sids.lookup r = some qs → q ∈ qs → ∃ j < k + 1, SubscribedAt S L internal j r q)
    {x y : Option String} (h : PlacedAt S ids sids x y) :
    Matching.Placed (renameIds S F) (Subscribed (steps S) (openPairs S L internal) k) x y := by
  cases x <;> cases y
  · trivial
  · simp [PlacedAt] at h
  · simp [PlacedAt] at h
  · simp only [PlacedAt] at h
    simp only [Matching.Placed]
    rcases h with ⟨hs, hl⟩ | ⟨qs, hl, hq⟩
    · left; simp [renameIds, hs, hext _ _ hl]
    · right
      obtain ⟨j, hj, o, a, b, h1, h2, h3, h4⟩ := hsub _ qs _ hl hq
      exact ⟨j, by omega, o, a, b, h1, h2, h3, h4⟩

theorem content_of {m M : Bindings} (hT : Tail M) (he : Ext m M) {s t : Option CValue} (h : ContentAfter m s t) :
    ContentMatches (rename M) s t := h M he hT

theorem in_not_sub {S : List (Option Line)} (hS : IdsDistinct S) {o : Out} (ho : AtLine S o)
    (hd : o.line.body.dir ≠ .out) {i : String} (hi : o.line.body.id = some i) : ¬SubId S i := by
  rintro ⟨j, l, hl, ⟨hdl, _⟩, hid⟩
  have := IdAt.unique hS ⟨l, hl, hid⟩ ⟨o.line, ho.2, hi⟩
  subst this
  rw [ho.2] at hl
  simp only [Option.some.injEq] at hl
  subst hl
  exact hd hdl

theorem specCompared_eq (S : List (Option Line)) (internal : Line → Bool) (w : Window) :
    specCompared (context S internal) w.before = pairedOut internal w := by
  simp only [specCompared, pairedOut, List.filter_filter, context]
  congr 1; funext o; rw [Bool.and_comm]

theorem traceCompared_eq (S : List (Option Line)) (internal : Line → Bool) (w : Window) :
    traceCompared (context S internal) w.before = pairedOut internal w := by
  simp only [traceCompared, pairedOut, context]
  congr 1; funext o; rw [Bool.and_comm]

theorem stateAt_zero_inv (S L : List (Option Line)) (internal : Line → Bool) (c : Ctx) :
    Inv S L internal 0 (startPos (steps S) S.length 0) (startPos (steps L) L.length 0) (stateAt c (steps S) (steps L) 0) :=
  ⟨Wf.empty _, by simp [stateAt], rfl, rfl, by simp [stateAt, openBefore], by simp [stateAt, openBefore],
    ⟨by simp [stateAt], by simp [stateAt], by simp [stateAt], by simp [stateAt], by simp [stateAt], by simp [stateAt],
      by simp [stateAt], by simp [stateAt], by simp [stateAt]⟩, by simp [stateAt]⟩

theorem time_eq {s t : Line} (h : sameTime s t = true) : t.time.time = s.time.time := by
  simp only [sameTime, beq_iff_eq] at h; exact h.symm

theorem outMatches_of {S L : List (Option Line)} {internal : Line → Bool} (hn : Narrowed S L) {k : Nat}
    {e a : Window} (ha : (steps L)[k]? = some a) {st w F : St} (wf : WindowFacts S L internal k e a st w)
    (hext : Ext w.values F.values) (hb : BoundExt w.ids F.ids) (hT : Tail F.values) {p : Pair}
    (hp1 : p.1 ∈ specCompared (context S internal) e.before) (hp2 : p.2 ∈ traceCompared (context S internal) a.before)
    (hok : PairOK (context S internal) w.ids w.values p) :
    OutMatches (rename F.values) (renameIds S F.ids) (Subscribed (steps S) (openPairs S L internal) k)
      (context S internal) p.1.line p.2.line := by
  refine ⟨hok.type, time_eq hok.time, ?_, content_of hT hext hok.value⟩
  have hplace := hok.place
  cases hb1 : p.1.line.body with
  | answer d i to x =>
    simp only [samePlace, hb1] at hplace
    cases ht : p.2.line.body.to? with
    | none => rw [ht] at hplace; simp [Ids.matches] at hplace
    | some to' =>
      rw [ht] at hplace
      refine placed_of hb wf.inv.subs ?_
      rcases matches_some _ _ _ hplace with hl | ⟨_, qs, hg, hq, _⟩
      · exact placedAt_of_lookup wf.inv.ids hl
      · exfalso
        have hG := groupsIn_of_inv wf.inv.ids to qs (mem_of_lookup hg) to' hq
        have hm : p.2 ∈ a.before := (List.mem_filter.mp hp2).1
        obtain ⟨hat, hdir, _, _⟩ := (windowAt L k a ha).before p.2 hm
        have htype := hok.type
        rw [hb1] at htype
        cases hb2 : p.2.line.body with
        | answer d' i' to'' x' =>
          rw [hb2] at ht
          simp only [TraceLine.Body.to?, Option.some.injEq] at ht
          subst ht
          exact hn.noOwnAnswer _ (mem_line hat) hdir d' i' to'' x' hb2 hG
        | _ => rw [hb2] at htype; simp [TraceLine.Body.type] at htype
  | unsubscribe d i to =>
    simp only [specCompared, List.mem_filter, Line.isSubscribing, hb1] at hp1
    simp at hp1
  | command | query | subscribe | event | operation | unacceptedOperation | time | restart =>
    simp only [samePlace, hb1, beq_iff_eq] at hplace
    exact hplace

theorem inMatches_of {S L : List (Option Line)} {internal : Line → Bool} (hn : Narrowed S L) {k : Nat} {w st' F : St}
    {s t : Out} (hif : InputFacts S w st' s.line t.line)
    (hsub : ∀ r qs q, w.subscriptionIds.lookup r = some qs → q ∈ qs → ∃ j < k + 1, SubscribedAt S L internal j r q)
    (hext : Ext st'.values F.values) (hb : BoundExt st'.ids F.ids) (hT : Tail F.values) (hs : AtLine S s)
    (hsd : s.line.body.dir ≠ .out) :
    InMatches (rename F.values) (renameIds S F.ids) (Subscribed (steps S) (openPairs S L internal) k) s.line t.line := by
  obtain ⟨hid, hrest⟩ := hif.facts
  refine ⟨hif.type, hif.name, time_eq hif.time, fun i j hi hj => ?_, ?_⟩
  · simp [renameIds, in_not_sub hn.snapshotIds hs hsd hi, hb _ _ (hid i j hi hj)]
  · cases hb1 : s.line.body with
    | time | restart => trivial
    | unsubscribe d i to =>
      simp only [hb1] at hrest
      exact placed_of hb hsub hrest
    | answer d i to x =>
      simp only [hb1] at hrest
      exact ⟨placed_of hb hsub hrest, content_of hT hext (hif.content (by simp [ComparesValue, hb1]))⟩
    | command | query | subscribe | event | operation | unacceptedOperation =>
      simp only [hb1] at hrest
      exact ⟨placed_of hb hsub hrest, content_of hT hext (hif.content (by simp [ComparesValue, hb1]))⟩

/-- A trace that compare reports nothing for matches the snapshot. -/
theorem compare_complete (snapshot lines : List (Option Line)) (internal : Line → Bool)
    (hn : Narrowed snapshot lines) (h : (Verify.compare snapshot lines none internal).findings = []) :
    Matches snapshot lines internal := by
  have hlen : (steps snapshot).length = (steps lines).length :=
    (inputs_align snapshot lines none internal (by simp [h])).2
  have hcmp : Verify.compare snapshot lines none internal = compareFrom (context snapshot internal) lines.length none
      (windowsOf (steps snapshot) (steps lines)) {} := rfl
  rw [hcmp] at h
  let c := context snapshot internal
  let E := steps snapshot
  let A := steps lines
  let N := E.length
  have quietAll : ∀ k, k < N →
      (compareFrom c lines.length none ((windowsOf E A).drop k) (stateAt c E A k)).findings = [] := by
    intro k
    induction k with
    | zero => intro _; exact h
    | succ k ih =>
      intro hk
      obtain ⟨s, t, _, _, _, hq⟩ := (quiet_step c lines.length E A hlen (input_isSome_iff snapshot)
        (input_isSome_iff lines) k (by omega) (ih (by omega))).2 hk
      exact hq
  have quietW : ∀ k, k < N → _ := fun k hk =>
    (quiet_step c lines.length E A hlen (input_isSome_iff snapshot) (input_isSome_iff lines) k hk (quietAll k hk))
  have getE : ∀ k, k < N → ∃ e, E[k]? = some e := fun k hk => ⟨_, List.getElem?_eq_getElem hk⟩
  have getA : ∀ k, k < N → ∃ a, A[k]? = some a := fun k hk =>
    ⟨_, List.getElem?_eq_getElem (show k < (steps lines).length by rw [← hlen]; exact hk)⟩
  have stepAll : ∀ k, k < N →
      Inv snapshot lines internal k (startPos E snapshot.length k) (startPos A lines.length k) (stateAt c E A k) := by
    intro k
    induction k with
    | zero => intro _; exact stateAt_zero_inv snapshot lines internal c
    | succ k ih =>
      intro hk
      obtain ⟨e, he⟩ := getE k (by omega)
      obtain ⟨a, ha⟩ := getA k (by omega)
      have wf := window_step snapshot lines internal hn k e a he ha (ih (by omega)) (quietW k (by omega)).1
      obtain ⟨s, t, hs, ht, hsame, _⟩ := (quietW k (by omega)).2 hk
      rw [he] at hs; rw [ha] at ht
      simp only [Option.bind_some] at hs ht
      exact (input_step snapshot lines internal hn k e a he ha s t hs ht _ wf.inv hsame).1
  have WF : ∀ k e a, E[k]? = some e → A[k]? = some a →
      WindowFacts snapshot lines internal k e a (stateAt c E A k) (windowRun c E A k (stateAt c E A k)) := by
    intro k e a he ha
    have hk : k < N := (List.getElem?_eq_some_iff.mp he).1
    exact window_step snapshot lines internal hn k e a he ha (stepAll k hk) (quietW k hk).1
  have IF : ∀ k e a s t, E[k]? = some e → A[k]? = some a → e.input = some s → a.input = some t →
      InputFacts snapshot (windowRun c E A k (stateAt c E A k)) (stateAt c E A (k + 1)) s.line t.line := by
    intro k e a s t he ha hs ht
    have hk : k + 1 < N := (input_isSome_iff snapshot k).mp (by rw [he]; simp [hs])
    obtain ⟨s', t', hs', ht', hsame, _⟩ := (quietW k (by omega)).2 hk
    simp only [he, ha, hs, ht, Option.bind_some, Option.some.injEq] at hs' ht'
    subst hs' ht'
    exact (input_step snapshot lines internal hn k e a he ha s t hs ht _ (WF k e a he ha).inv hsame).2
  have hN : 0 < N := by
    obtain ⟨ins, hi⟩ := steps_inputs snapshot
    have := congrArg List.length hi
    simp only [List.length_map, List.length_append, List.length_singleton] at this
    show 0 < (steps snapshot).length
    omega
  have inputOf : ∀ k e, k + 1 < N → E[k]? = some e → ∃ s, e.input = some s := by
    intro k e hk he
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp ((input_isSome_iff snapshot k).mpr hk)
    simp only [show (steps snapshot)[k]? = some e from he, Option.bind_some] at hs
    exact ⟨s, hs⟩
  have inputOfA : ∀ k a, k + 1 < N → A[k]? = some a → ∃ t, a.input = some t := by
    intro k a hk ha
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp ((input_isSome_iff lines k).mpr (by
      show k + 1 < (steps lines).length; rw [← hlen]; exact hk))
    simp only [show (steps lines)[k]? = some a from ha, Option.bind_some] at ht
    exact ⟨t, ht⟩
  let W : Nat → St := fun k => windowRun c E A k (stateAt c E A k)
  let F := W (N - 1)
  have mono : ∀ d k, N - 1 - k = d → k < N → Ext (W k).values F.values ∧ BoundExt (W k).ids F.ids := by
    intro d
    induction d with
    | zero =>
      intro k hd hk
      have : k = N - 1 := by omega
      subst this
      exact ⟨Ext.refl _, BoundExt.refl _⟩
    | succ d ih =>
      intro k hd hk
      have hk1 : k + 1 < N := by omega
      obtain ⟨e, he⟩ := getE k hk
      obtain ⟨a, ha⟩ := getA k hk
      obtain ⟨s, hs⟩ := inputOf k e hk1 he
      obtain ⟨t, ht⟩ := inputOfA k a hk1 ha
      obtain ⟨e', he'⟩ := getE (k + 1) hk1
      obtain ⟨a', ha'⟩ := getA (k + 1) hk1
      have i := IF k e a s t he ha hs ht
      have w := WF (k + 1) e' a' he' ha'
      obtain ⟨m1, m2⟩ := ih (k + 1) (by omega) hk1
      exact ⟨i.grows.trans (w.grows.trans m1), i.bound.trans (w.bound.trans m2)⟩
  have monoW : ∀ k, k < N → Ext (W k).values F.values ∧ BoundExt (W k).ids F.ids :=
    fun k hk => mono _ k rfl hk
  obtain ⟨eL, heL⟩ := getE (N - 1) (by omega)
  obtain ⟨aL, haL⟩ := getA (N - 1) (by omega)
  have last := WF (N - 1) eL aL heL haL
  have hT : Tail F.values := last.inv.wf.tail
  have hP : ∀ k e a, E[k]? = some e → A[k]? = some a →
      ((outPairs snapshot lines internal k).map (·.1)).Perm (specCompared c e.before) ∧
      ((outPairs snapshot lines internal k).map (·.2)).Perm (traceCompared c a.before) ∧
      (∀ p ∈ outPairs snapshot lines internal k, PairOK c (W k).ids (W k).values p) ∧
      (∀ p ∈ outPairs snapshot lines internal k, ∀ q ∈ outPairs snapshot lines internal k,
        (p.1.index - 1) ∈ mustFollow snapshot (q.1.index - 1) → p.2.index ≤ q.2.index) ∧
      ((outPairs snapshot lines internal k).map (·.2.index)).Nodup := by
    intro k e a he ha
    obtain ⟨pairs, p1, p2, p3, p4, p5⟩ := (WF k e a he ha).pairs
    have hex : ∃ pairs : List Pair, ∃ e a, E[k]? = some e ∧ A[k]? = some a ∧
        ((pairs.map (·.1)).Perm (specCompared c e.before)) ∧ (pairs.map (·.2)).Perm (traceCompared c a.before) ∧
        (∀ p ∈ pairs, PairOK c (W k).ids (W k).values p) ∧
        (∀ p ∈ pairs, ∀ q ∈ pairs, (p.1.index - 1) ∈ mustFollow snapshot (q.1.index - 1) → p.2.index ≤ q.2.index) ∧
        (pairs.map (·.2.index)).Nodup := ⟨pairs, e, a, he, ha, p1, p2, p3, p4, p5⟩
    have hdef : outPairs snapshot lines internal k = Classical.choose hex := by
      simp only [outPairs]
      split
      · rfl
      · contradiction
    obtain ⟨e', a', he', ha', q1, q2, q3, q4, q5⟩ := Classical.choose_spec hex
    rw [he] at he'; rw [ha] at ha'
    cases he'; cases ha'
    rw [hdef]
    exact ⟨q1, q2, q3, q4, q5⟩
  refine ⟨hlen, rename F.values, renameIds snapshot F.ids, outPairs snapshot lines internal,
    openPairs snapshot lines internal, ?_, ?_, ?_, ?_⟩
  · intro x y v hx hy
    simp only [rename, Option.bind_eq_some_iff] at hx hy
    obtain ⟨ws, hws, hv⟩ := hx
    obtain ⟨ws', hws', hv'⟩ := hy
    exact last.inv.wf.disjoint x ws y ws' v (mem_of_lookup hws) (mem_of_lookup hws')
      (List.mem_of_mem_head? hv) (List.mem_of_mem_head? hv')
  · intro x v hx
    simp only [rename, Option.bind_eq_some_iff] at hx
    obtain ⟨ws, hws, _⟩ := hx
    exact last.inv.declared x (last.inv.wf.declared x ws (mem_of_lookup hws))
  · intro x y v hx hy
    simp only [renameIds] at hx hy
    split at hx
    · cases hx
    · split at hy
      · cases hy
      · rename_i hsx hsy
        exact last.inv.ids.inj x y v (mem_of_lookup hx) (mem_of_lookup hy) hsx hsy
  · intro k e a he ha
    have hk : k < N := (List.getElem?_eq_some_iff.mp he).1
    have wf := WF k e a he ha
    obtain ⟨p1, p2, p3, p4, p5⟩ := hP k e a he ha
    obtain ⟨mv, mb⟩ := monoW k hk
    refine ⟨by rw [← specCompared_eq]; exact p1, by rw [← traceCompared_eq snapshot]; exact p2, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      exact outMatches_of hn ha wf mv mb hT (p1.subset (List.mem_map_of_mem hp))
        (p2.subset (List.mem_map_of_mem hp)) (p3 p hp)
    · intro p hp q hq hf
      have hle := p4 p hp q hq hf
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · have := eq_of_map_nodup (·.2.index) p5 hp hq heq
        subst this
        exact absurd hf (mustFollow_irrefl snapshot _)
    · obtain ⟨o1, o2, o3⟩ := wf.opens
      refine ⟨by rw [o1], o2, fun q hq => ?_⟩
      obtain ⟨s, t, h1, h2, h3, h4⟩ := o3 q hq
      exact ⟨s, t, h1, h2, h3, content_of hT mv h4⟩
    · have h1 := input_isSome_iff snapshot k
      have h2 := input_isSome_iff lines k
      simp only [show (steps snapshot)[k]? = some e from he, show (steps lines)[k]? = some a from ha,
        Option.bind_some] at h1 h2
      rw [← hlen] at h2
      exact Bool.eq_iff_iff.mpr (h1.trans h2.symm)
    · intro s t hs ht
      have hk1 : k + 1 < N := (input_isSome_iff snapshot k).mp (by
        simp [show (steps snapshot)[k]? = some e from he, hs])
      have i := IF k e a s t he ha hs ht
      obtain ⟨e', he'⟩ := getE (k + 1) hk1
      obtain ⟨a', ha'⟩ := getA (k + 1) hk1
      have w' := WF (k + 1) e' a' he' ha'
      obtain ⟨m1, m2⟩ := monoW (k + 1) hk1
      obtain ⟨hsat, hsd, _⟩ := (windowAt snapshot k e he).input s hs
      exact inMatches_of hn i wf.inv.subs (w'.grows.trans m1) (w'.bound.trans m2) hT hsat hsd

/-- With a malformed line, compare always reports. -/
theorem compare_malformed_found (snapshot lines : List (Option Line)) (n : Nat) (internal : Line → Bool) :
    (Verify.compare snapshot lines (some n) internal).findings ≠ [] := by
  obtain ⟨ms, u, hc⟩ := compare_malformed snapshot lines n internal
  simp [hc]

end Tazuna.Thm.Verify.Complete
