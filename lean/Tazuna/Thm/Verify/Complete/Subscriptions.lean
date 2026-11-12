import Tazuna.Thm.Verify.Complete.Window

namespace Tazuna.Thm.Verify.Complete.Subscriptions

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run Tazuna.Thm.Verify.Complete.Window

/-- The subscription ids after compareSubscriptions pairs `pairs`, with `o` the open snapshot subscriptions. -/
def pairedIds (o : List (String × Subscription)) (pairs : List (String × String))
    (sids : List (String × List String)) : List (String × List String) :=
  pairs.foldl (init := sids) fun all (s, _) =>
    let known := (all.lookup s).getD []
    let added := pairs.foldl (init := known) fun ids (other, t) =>
      match (o.lookup s).map (·.out.line), (o.lookup other).map (·.out.line) with
      | some a, some b => if alike a b && !ids.contains t then ids ++ [t] else ids
      | _, _ => ids
    setAt all s added

theorem pairedIds_added (o : List (String × Subscription)) (pairs : List (String × String)) (s : String) :
    ∀ (known : List String) (q : String), q ∈ pairs.foldl (init := known) (fun ids (other, t) =>
      match (o.lookup s).map (·.out.line), (o.lookup other).map (·.out.line) with
      | some a, some b => if alike a b && !ids.contains t then ids ++ [t] else ids
      | _, _ => ids) →
      q ∈ known ∨ ∃ other, (other, q) ∈ pairs ∧ ∃ a b, o.lookup s = some a ∧ o.lookup other = some b ∧
        alike a.out.line b.out.line = true := by
  induction pairs with
  | nil => intro known q h; exact Or.inl h
  | cons p ps ih =>
    intro known q h
    obtain ⟨other, t⟩ := p
    simp only [List.foldl_cons] at h
    rcases ih _ q h with h | ⟨o', ho', a, b, h1, h2, h3⟩
    · split at h
      · rename_i a b ha hb
        split at h
        · rename_i hc
          rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · simp only [List.mem_singleton] at h
            subst h
            simp only [Option.map_eq_some_iff] at ha hb
            obtain ⟨a', ha', rfl⟩ := ha
            obtain ⟨b', hb', rfl⟩ := hb
            simp only [Bool.and_eq_true] at hc
            exact Or.inr ⟨other, List.mem_cons_self, a', b', ha', hb', hc.1⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', a, b, h1, h2, h3⟩

theorem pairedIds_mem (o : List (String × Subscription)) (pairs : List (String × String))
    (sids : List (String × List String)) (r : String) (qs : List String) (q : String)
    (h : (pairedIds o pairs sids).lookup r = some qs) (hq : q ∈ qs) :
    (∃ qs', sids.lookup r = some qs' ∧ q ∈ qs') ∨ (∃ other, (other, q) ∈ pairs ∧ ∃ a b, o.lookup r = some a ∧
      o.lookup other = some b ∧ alike a.out.line b.out.line = true) := by
  unfold pairedIds at h
  revert qs
  apply foldl_preserve (fun (all : List (String × List String)) => ∀ qs, all.lookup r = some qs → q ∈ qs →
    (∃ qs', sids.lookup r = some qs' ∧ q ∈ qs') ∨ (∃ other, (other, q) ∈ pairs ∧ ∃ a b, o.lookup r = some a ∧
      o.lookup other = some b ∧ alike a.out.line b.out.line = true))
  · rintro all ⟨s, _⟩ _ hall qs hl hq
    dsimp only at hl
    rw [lookup_setAt] at hl
    split at hl
    · rename_i e
      subst e
      simp only [Option.some.injEq] at hl
      subst hl
      rcases pairedIds_added o pairs r _ q hq with h | h
      · cases hk : all.lookup r with
        | none => simp [hk] at h
        | some ks => simp only [hk, Option.getD_some] at h; exact hall ks hk h
      · exact Or.inr h
    · exact hall qs hl hq
  · intro qs hl hq; exact Or.inl ⟨qs, hl, hq⟩

theorem pairedIds_ext (o : List (String × Subscription)) (pairs : List (String × String))
    (sids : List (String × List String)) (r : String) (qs : List String) (h : sids.lookup r = some qs) :
    ∃ qs', (pairedIds o pairs sids).lookup r = some qs' ∧ ∀ q ∈ qs, q ∈ qs' := by
  unfold pairedIds
  apply foldl_preserve (fun (all : List (String × List String)) =>
    ∃ qs', all.lookup r = some qs' ∧ ∀ q ∈ qs, q ∈ qs') _ _ _ _ ⟨qs, h, fun _ hq => hq⟩
  rintro all ⟨s, _⟩ hp ⟨ks, hk, hsub⟩
  dsimp only
  rw [lookup_setAt]
  split
  · rename_i e
    subst e
    refine ⟨_, rfl, fun q hq => ?_⟩
    have hq' : q ∈ (all.lookup r).getD [] := by rw [hk]; exact hsub q hq
    generalize (all.lookup r).getD [] = known at hq'
    clear hk hp
    induction pairs generalizing known with
    | nil => exact hq'
    | cons p ps ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      · split
        · exact List.mem_append_left _ hq'
        · exact hq'
      · exact hq'
  · exact ⟨ks, hk, hsub⟩

theorem pairedIds_keys (o : List (String × Subscription)) (pairs : List (String × String))
    (sids : List (String × List String)) (r : String) (qs : List String) (h : (r, qs) ∈ pairedIds o pairs sids) :
    (∃ qs', (r, qs') ∈ sids) ∨ r ∈ pairs.map (·.1) := by
  unfold pairedIds at h
  revert h
  apply foldl_preserve (fun (all : List (String × List String)) => (r, qs) ∈ all →
    (∃ qs', (r, qs') ∈ sids) ∨ r ∈ pairs.map (·.1))
  · rintro all ⟨s, t⟩ hp hall hm
    rcases mem_setAt_any hm with ⟨e, _⟩ | hm
    · subst e; exact Or.inr (List.mem_map_of_mem hp)
    · exact hall hm
  · intro hm; exact Or.inl ⟨qs, hm⟩

/-- A pairing of the open snapshot subscriptions `o` with the open implementation subscriptions `t`. -/
def OpenOK (o t : List (String × Subscription)) (m : Bindings) (Q : List (String × String)) : Prop :=
  Q.map (·.1) = o.map (·.1) ∧ (Q.map (·.2)).Perm (t.map (·.1)) ∧
    ∀ q ∈ Q, ∃ s u, o.lookup q.1 = some s ∧ t.lookup q.2 = some u ∧ s.name = u.name ∧
      ContentAfter m s.out.line.content u.out.line.content

theorem follow_nodup (o : List (String × Subscription)) (lines : List Out) (h : (o.map (·.1)).Nodup) :
    ((follow o lines).map (·.1)).Nodup := by
  unfold follow
  apply foldl_preserve (fun o : List (String × Subscription) => (o.map (·.1)).Nodup) _ _ _ _ h
  intro o l _ ho
  split
  · split
    · exact ho
    · rename_i id _ _ hl
      simp only [Option.isSome_iff_ne_none, ne_eq, Decidable.not_not] at hl
      rw [List.map_append]
      exact List.nodup_append.mpr ⟨ho, by simp, by
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        rintro a ha b rfl rfl; exact lookup_none_iff.mp hl ha⟩
  · exact ho.sublist (List.filter_sublist.map _)
  · exact ho

mutual

theorem pairOpen_values (st : St) :
    ∀ (ss ts : List String) (m : Bindings) (pairs : List (String × String)) (m' : Bindings),
      Wf st.declared m → pairOpen st ss ts m = some (pairs, m') →
      Grows st.declared m m' ∧ ∀ p ∈ pairs, ∃ s t, st.openSnapshot.lookup p.1 = some s ∧
        st.openTrace.lookup p.2 = some t ∧ ContentAfter m' s.out.line.content t.out.line.content
  | [], ts, m, pairs, m', h, he => by
    rw [pairOpen] at he
    split at he
    · cases he; exact ⟨Grows.refl h, by simp⟩
    · cases he
  | first :: rest, ts, m, pairs, m', h, he => by
    rw [pairOpen] at he
    exact pairOpen_go_values st first rest ts [] [] m pairs m' h he

theorem pairOpen_go_values (st : St) (first : String) (rest : List String) :
    ∀ (cands passed : List String) (tried : List (Option Value)) (m : Bindings) (pairs : List (String × String))
      (m' : Bindings), Wf st.declared m → pairOpen.go st first rest cands passed tried m = some (pairs, m') →
      Grows st.declared m m' ∧ ∀ p ∈ pairs, ∃ s t, st.openSnapshot.lookup p.1 = some s ∧
        st.openTrace.lookup p.2 = some t ∧ ContentAfter m' s.out.line.content t.out.line.content
  | [], _, _, _, _, _, _, he => by rw [pairOpen.go] at he; cases he
  | id :: more, passed, tried, m, pairs, m', h, he => by
    rw [pairOpen.go] at he
    split at he
    · rename_i s t hs ht
      split at he
      · exact pairOpen_go_values st first rest more (id :: passed) tried m pairs m' h he
      · dsimp only at he
        split at he
        · exact pairOpen_go_values st first rest more (id :: passed) tried m pairs m' h he
        · split at he
          · rename_i m₁ e
            have hg := tryEqual_grows st.declared s.out.line.content t.out.line.content m h
            have hv := tryEqual_sound st.declared s.out.line.content t.out.line.content m h
            rw [e] at hg hv
            split at he
            · rename_i rp m₂ e2
              simp only [Option.some.injEq, Prod.mk.injEq] at he
              obtain ⟨hp, hm⟩ := he
              subst hp hm
              obtain ⟨hg', hr⟩ := pairOpen_values st rest _ m₁ rp m₂ hg.1 e2
              refine ⟨hg.trans hg', fun p hp => ?_⟩
              rcases List.mem_cons.mp hp with hp | hp
              · subst hp
                exact ⟨s, t, hs, ht, (hv rfl).mono hg'.2⟩
              · exact hr p hp
            · exact pairOpen_go_values st first rest more (id :: passed) _ m pairs m' h he
          · exact pairOpen_go_values st first rest more (id :: passed) _ m pairs m' h he
    · exact pairOpen_go_values st first rest more (id :: passed) tried m pairs m' h he

end

theorem perm_filter_ne {l : List String} {u : String} (hn : l.Nodup) (hu : u ∈ l) :
    (u :: l.filter (· != u)).Perm l := by
  have : l.filter (· != u) = l.erase u := by
    rw [hn.erase_eq_filter]
  rw [this]; exact (List.perm_cons_erase hu).symm

/-- The findings of a quiet comparison of the open subscriptions. -/
theorem compareSubscriptions_spec (ss ts : List Out) (n : Nat) (c : Ctx) (st : St) :
    let r := run (compareSubscriptions ss ts n) c st
    let os := follow st.openSnapshot ss
    let ot := follow st.openTrace ts
    st.findings <+: r.2.findings ∧ (Wf st.declared st.values → st.reportedMissing = [] →
      st.reportedUnexpected = [] → (os.map (·.1)).Nodup → (ot.map (·.1)).Nodup →
      (∀ x ∈ os, ∀ v, x.2.out.line.content = some v → NoBag v) → r.2.findings = st.findings →
      ∃ Q, OpenOK os ot r.2.values Q ∧ r.2.openSnapshot = os ∧ r.2.openTrace = ot ∧
        r.2.subscriptionIds = pairedIds os Q st.subscriptionIds ∧ r.2.ids = st.ids ∧ r.2.declared = st.declared ∧
        r.2.reportedMissing = [] ∧ r.2.reportedUnexpected = [] ∧ Grows st.declared st.values r.2.values) := by
  intro r os ot
  simp only [r, compareSubscriptions]
  simp_run
  let st₀ : St := { st with openSnapshot := os, openTrace := ot }
  split
  · rename_i pairs m he
    simp only [he, Option.map_some, Option.getD_some]
    simp_run
    refine ⟨List.prefix_refl _, fun hw hm hu _ _ _ _ => ?_⟩
    obtain ⟨h1, h2, _⟩ := pairOpen_spec st₀ _ _ _ pairs m he
    obtain ⟨g1, g2⟩ := pairOpen_values st₀ _ _ _ pairs m hw he
    refine ⟨pairs, ⟨h1, h2, fun q hq => ?_⟩, rfl, rfl, rfl, rfl, rfl, hm, hu, g1⟩
    obtain ⟨s, u, hs, hu', hc⟩ := g2 q hq
    obtain ⟨s', u', hs', hu'', hn⟩ := pairOpen_spec st₀ _ _ _ pairs m he |>.2.2 q hq
    rw [hs] at hs'; rw [hu'] at hu''
    cases hs'; cases hu''
    exact ⟨s, u, hs, hu', hn, hc⟩
  · rename_i he
    simp only [he, Option.map_none, Option.getD_none, run_bind]
    generalize hL : run (forIn os _ _) c _ = L
    generalize hL2 : run (forIn L.1.2 PUnit.unit _) c L.2 = L2
    simp only [run_get, run_set]
    let P1 : List (String × Subscription) → List (String × String) × List String → St → Prop := fun pre b st' =>
      st₀.findings <+: st'.findings ∧ (Wf st.declared st.values → st.reportedMissing = [] →
        (os.map (·.1)).Nodup → (ot.map (·.1)).Nodup →
        (∀ x ∈ os, ∀ v, x.2.out.line.content = some v → NoBag v) → st'.findings = st₀.findings →
        st' = st₀ ∧ b.1.map (·.1) = pre.map (·.1) ∧ (b.1.map (·.2) ++ b.2).Perm (ot.map (·.1)) ∧
        ∀ p ∈ b.1, ∃ s u, os.lookup p.1 = some s ∧ ot.lookup p.2 = some u ∧ s.name = u.name ∧
          ContentAfter st.values s.out.line.content u.out.line.content)
    have hP1 : P1 os L.1 L.2 := by
      refine forIn_eq_induct P1 ?_ ?_ ?_ hL
      · intro x b st'
        split
        · exact ⟨_, rfl⟩
        · simp_run
          split <;> exact ⟨_, rfl⟩
      · rintro pre x ⟨pairs, unpaired⟩ st' hpre ⟨hp, hq⟩
        have hx : x ∈ os := hpre.subset (by simp)
        split
        · rename_i u hf
          simp only [run_pure, ForInStep.value]
          refine ⟨hp, fun hw' hm hno hnt hnb he => ?_⟩
          obtain ⟨q1, q2, q3, q4⟩ := hq hw' hm hno hnt hnb he
          have hmem := List.mem_of_find?_eq_some hf
          have hpred := List.find?_some hf
          refine ⟨q1, by simp [q2], ?_, ?_⟩
          · have hn : unpaired.Nodup := (List.nodup_append.mp (q3.nodup_iff.mpr hnt)).2.1
            refine List.Perm.trans ?_ q3
            simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
            exact List.Perm.append_left _ (perm_filter_ne hn hmem)
          · intro p hp'
            rcases List.mem_append.mp hp' with hp' | hp'
            · exact q4 p hp'
            · simp only [List.mem_singleton] at hp'
              subst hp'
              split at hpred
              · rename_i other hl
                simp only [Bool.and_eq_true, beq_iff_eq] at hpred
                refine ⟨x.2, other, lookup_of_mem' hno hx, hl, hpred.1.symm, ?_⟩
                have hs := equalContent_sound st.declared x.2.out.line.content other.out.line.content st.values false
                  hw' hpred.2
                rwa [equalContent_noBag _ _ _ _ (hnb x hx)] at hs
              · cases hpred
        · simp_run
          split
          · refine ⟨hp.trans (List.prefix_append _ _), fun _ _ _ _ _ he => ?_⟩
            have := congrArg List.length he
            have := hp.length_le
            simp at *; omega
          · rename_i hc
            refine ⟨hp, fun hw' hm hno hnt hnb he => ?_⟩
            obtain ⟨q1, -⟩ := hq hw' hm hno hnt hnb he
            subst q1
            simp [st₀, hm] at hc
      · exact ⟨List.prefix_refl _, fun _ _ _ _ _ _ => ⟨rfl, rfl, List.Perm.refl _, by simp⟩⟩
    let P2 : List String → PUnit → St → Prop := fun pre _ st' =>
      L.2.findings <+: st'.findings ∧ (L.2.reportedUnexpected = [] → (∀ x ∈ L.1.2, (L.2.openTrace.lookup x).isSome) →
        st'.findings = L.2.findings → st' = L.2 ∧ pre = [])
    have hP2 : P2 L.1.2 L2.1 L2.2 := by
      refine forIn_eq_induct P2 ?_ ?_ ?_ hL2
      · intro x b st'
        simp_run
        split
        · split <;> exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      · rintro pre x _ st' hpre ⟨hp, hq⟩
        have hx : x ∈ L.1.2 := hpre.subset (by simp)
        simp_run
        split
        · split
          · simp_run
            refine ⟨hp.trans (List.prefix_append _ _), fun _ _ he => ?_⟩
            have := congrArg List.length he
            have := hp.length_le
            simp at *; omega
          · rename_i hc
            refine ⟨hp, fun hu hl he => ?_⟩
            obtain ⟨q1, -⟩ := hq hu hl he
            subst q1
            simp [hu] at hc
        · rename_i hn
          refine ⟨hp, fun hu hl he => ?_⟩
          obtain ⟨q1, -⟩ := hq hu hl he
          subst q1
          have := hl x hx
          simp [hn] at this
      · exact ⟨List.prefix_refl _, fun _ _ _ => ⟨rfl, rfl⟩⟩
    obtain ⟨p1, hq1⟩ := hP1
    obtain ⟨p2, hq2⟩ := hP2
    refine ⟨p1.trans p2, fun hw hm hu hno hnt hnb he => ?_⟩
    have e1 : L.2.findings = st₀.findings := prefix_squeeze p1 p2 he
    obtain ⟨f1, f2, f3, f4⟩ := hq1 hw hm hno hnt hnb e1
    have hlook : ∀ x ∈ L.1.2, (L.2.openTrace.lookup x).isSome := by
      intro x hx
      rw [f1]
      have : x ∈ ot.map (·.1) := f3.subset (List.mem_append_right _ hx)
      cases h : ot.lookup x with
      | none => exact absurd this (lookup_none_iff.mp h)
      | some _ => rfl
    obtain ⟨g1, g2⟩ := hq2 (by rw [f1]; exact hu) hlook (he.trans e1.symm)
    rw [g1, f1]
    rw [g2, List.append_nil] at f3
    refine ⟨L.1.1, ⟨by rw [f2], f3, f4⟩, rfl, rfl, rfl, rfl, rfl, hm, hu, Grows.refl hw⟩

/-- The snapshot `out` lines of a window that verify pairs. -/
abbrev specCompared (c : Ctx) (ss : List Out) : List Out :=
  (ss.filter fun s => !s.line.isSubscribing).filter fun s => !c.internal s.line

/-- The implementation `out` lines of a window that verify pairs. -/
abbrev traceCompared (c : Ctx) (ts : List Out) : List Out :=
  ts.filter fun t => !c.internal t.line && !t.line.isSubscribing

abbrev subscribing (os : List Out) : List Out := os.filter (·.line.isSubscribing)

abbrev declaredAfter (ss : List Out) (d : List String) : List String :=
  ss.foldl (fun d s => d ++ s.line.created.getD []) d

theorem declaredAfter_mono (ss : List Out) (d : List String) : ∀ x ∈ d, x ∈ declaredAfter ss d := by
  intro x hx
  unfold declaredAfter
  exact foldl_preserve (fun d => x ∈ d) _ _ _ (fun d _ _ h => List.mem_append_left _ h) hx

theorem perm_of_cover {xs ts : List Out} (hx : ∀ x ∈ xs, x ∈ ts) (hnx : (xs.map (·.index)).Nodup)
    (hnt : (ts.map (·.index)).Nodup) (hc : ∀ t ∈ ts, ∃ x ∈ xs, x.index = t.index) : xs.Perm ts := by
  refine (List.perm_ext_iff_of_nodup (nodup_of_map _ hnx) (nodup_of_map _ hnt)).mpr fun a => ⟨hx a, fun ha => ?_⟩
  obtain ⟨x, hxm, e⟩ := hc a ha
  have := eq_of_map_nodup (·.index) hnt (hx x hxm) ha e
  rwa [← this]

/-- The findings of a quiet comparison of a window. -/
theorem compareWindow_spec (ss ts : List Out) (n : Nat) (c : Ctx) (st : St) (G : List String) :
    let r := run (compareWindow ss ts n) c st
    let d := declaredAfter ss st.declared
    let os := follow st.openSnapshot (subscribing ss)
    let ot := follow st.openTrace (subscribing ts)
    let sp := specCompared c ss
    let tp := traceCompared c ts
    st.findings <+: r.2.findings ∧ (Wf st.declared st.values → st.reportedMissing = [] →
      st.reportedUnexpected = [] → (os.map (·.1)).Nodup → (ot.map (·.1)).Nodup →
      (∀ x ∈ os, ∀ v, x.2.out.line.content = some v → NoBag v) → Reported c sp tp → (tp.map (·.index)).Nodup →
      GroupsIn G st.ids → (∀ t ∈ tp, t.line.isRequest = true → ∀ q, t.line.body.id = some q → q ∈ G) →
      (∀ t ∈ tp, ∀ to, t.line.body.to? = some to → to ∉ G) → r.2.findings = st.findings →
      ∃ (Q : List (String × String)) (pairs requests : List Pair),
        OpenOK os ot r.2.values Q ∧ r.2.subscriptionIds = pairedIds os Q st.subscriptionIds ∧
        (pairs.map (·.1)).Perm sp ∧ (pairs.map (·.2)).Perm tp ∧ (∀ p ∈ pairs, PairOK c r.2.ids r.2.values p) ∧
        (∀ p ∈ pairs, ∀ q ∈ pairs, (p.1.index - 1) ∈ c.follows (q.1.index - 1) → p.2.index ≤ q.2.index) ∧
        (pairs.map (·.2.index)).Nodup ∧
        r.2.ids = groupedIds requests st.ids ∧ requests.map (·.1) = sp.filter (·.line.isRequest) ∧
        (∀ p ∈ requests, p.2 ∈ tp) ∧ (∃ others, pairs = requests ++ others) ∧ r.2.openSnapshot = os ∧ r.2.openTrace = ot ∧ r.2.declared = d ∧
        r.2.reportedMissing = [] ∧ r.2.reportedUnexpected = [] ∧ Grows d st.values r.2.values ∧
        GroupsIn G r.2.ids) := by
  intro r d os ot sp tp
  simp only [r, compareWindow]
  simp_run
  simp only [run_bind, run_pure]
  generalize hS : run (compareSubscriptions _ _ _) c _ = S
  generalize hW : run (pairWindow _ _ _) c _ = W
  generalize hO : run (forIn W.1 PUnit.unit _) c W.2 = O
  generalize hU : run (forIn (List.filter _ ts) PUnit.unit _) c O.2 = U
  obtain ⟨s1, s2⟩ := compareSubscriptions_spec (subscribing ss) (subscribing ts) n c
    { st with declared := d }
  rw [hS] at s1 s2
  obtain ⟨w1, w2⟩ := pairWindow_spec (specCompared c ss) (traceCompared c ts) n c S.2 G
  rw [hW] at w1 w2
  obtain ⟨o1, o2⟩ := forIn_checks (fun (p : Pair) => ∀ q ∈ W.1, ¬(q.2.index > p.2.index ∧
    (c.follows (p.1.index - 1)).contains (q.1.index - 1) = true)) (fun x st' => by
      split
      · rename_i q bt hf
        simp only [run_bind_report, run_pure]
        exact ⟨trivial, Or.inr ⟨_, rfl⟩⟩
      · rename_i hf
        refine ⟨rfl, Or.inl ⟨rfl, fun q hq hc => ?_⟩⟩
        have := List.find?_eq_none.mp (by
          cases h : List.find? _ W.1 with
          | none => rfl
          | some y => exact absurd h (by obtain ⟨a, b⟩ := y; exact hf a b)) q hq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this hc) hO
  obtain ⟨u1, u2⟩ := forIn_checks (fun (t : Out) => (W.1.any fun x => x.2.index == t.index) = true)
    (fun x st' => by
      split
      · simp only [run_bind_report, run_pure]
        exact ⟨trivial, Or.inr ⟨_, rfl⟩⟩
      · rename_i h
        exact ⟨rfl, Or.inl ⟨rfl, by simpa using h⟩⟩) hU
  refine ⟨s1.trans (w1.trans (o1.trans u1)), fun hw hm hu hno hnt hnb hr hn hG hreq hans he => ?_⟩
  have eS : S.2.findings = st.findings := prefix_squeeze s1 (w1.trans (o1.trans u1)) he
  have eW : W.2.findings = st.findings := prefix_squeeze (s1.trans w1) (o1.trans u1) he
  have eO : O.2.findings = W.2.findings := prefix_squeeze o1 u1 (he.trans eW.symm)
  have eU : U.2.findings = O.2.findings := he.trans (eO.trans eW).symm
  obtain ⟨Q, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    s2 (hw.mono (declaredAfter_mono ss _)) hm hu hno hnt hnb eS
  obtain ⟨requests, v1, v2, v3, v10, v4, v5, v6, v7, v8, v9⟩ :=
    w2 (q6 ▸ q9.1) hr hn (q5 ▸ hG) hreq hans (eW.trans eS.symm)
  obtain ⟨o3, o4⟩ := o2 eO
  obtain ⟨u3, u4⟩ := u2 eU
  rw [u3, o3]
  refine ⟨Q, W.1, requests, ?_, by rw [v7.subscriptionIds, q4], ?_, ?_, fun p hp => (v5 p hp).2, ?_, v6,
    by rw [v1, q5], v2, v3, v10, by rw [v7.openSnapshot, q2], by rw [v7.openTrace, q3], by rw [v7.declared, q6],
    by rw [v7.reportedMissing, q7], by rw [v7.reportedUnexpected, q8], ?_, v9⟩
  · obtain ⟨a, b, c'⟩ := q1
    exact ⟨a, b, fun x hx => by
      obtain ⟨s, u, h1, h2, h3, h4⟩ := c' x hx
      exact ⟨s, u, h1, h2, h3, h4.mono v8.2⟩⟩
  · exact v4
  · refine perm_of_cover (fun x hx => ?_) (by rw [List.map_map]; exact v6) hn (fun t ht => ?_)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (v5 p hp).1
    · have := u4 t ht
      simp only [List.any_eq_true, beq_iff_eq] at this
      obtain ⟨p, hp, e⟩ := this
      exact ⟨p.2, List.mem_map_of_mem hp, e⟩
  · intro p hp q hq hf
    have := o4 q hq p hp
    simp only [gt_iff_lt, List.contains_iff_mem, not_and] at this
    exact Nat.le_of_not_lt fun h => this h hf
  · exact q9.trans (by rw [q6] at v8; exact v8)

end Tazuna.Thm.Verify.Complete.Subscriptions
