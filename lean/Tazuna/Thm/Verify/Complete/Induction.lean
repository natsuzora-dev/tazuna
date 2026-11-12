import Tazuna.Thm.Verify.Complete.Top

namespace Tazuna.Thm.Verify.Complete.Induction

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Bindings Tazuna.Thm.Verify.Complete.Inputs Tazuna.Thm.Verify.Complete.Steps Tazuna.Thm.Verify.Complete.Subscriptions Tazuna.Thm.Verify.Complete.Top

theorem runWindow_eq (c : Ctx) (st : St) (ss ts : List Out) (n : Nat) :
    runWindow c st ss ts n = ((run (compareWindow ss ts n) c { st with findings := [] }).2.findings,
      (run (compareWindow ss ts n) c { st with findings := [] }).2) := rfl

/-- The snapshot `S` and the trace `L` that verify finds every difference between. -/
structure Narrowed (S L : List (Option Line)) : Prop where
  /-- Verify binds a repeated snapshot id only once. -/
  snapshotIds : IdsDistinct S
  /-- Verify binds a repeated implementation id to more than one snapshot id. -/
  traceIds : IdsDistinct L
  /-- Verify can bind two snapshot requests to one implementation request that `out` answers name. -/
  noOwnAnswer : ∀ a, some a ∈ L → a.body.dir = .out → ∀ d i to x, a.body = .answer d i to x → to ∉ requestIds L
  /-- Verify reports no difference in the payload of an `out` operation. -/
  noOutOperation : ∀ l, some l ∈ S → l.body.dir = .out →
    (∀ d i n p, l.body ≠ .operation d i n p) ∧ ∀ d i n p, l.body ≠ .unacceptedOperation d i n p
  /-- Verify reports no difference in the output of a fulfilled answer to a request that is not a query. -/
  fulfilled : ∀ l, some l ∈ S → ∀ d i to o, l.body = .answer d i to (.fulfilled o) →
    (context S fun _ => false).answersQuery to = true
  /-- Pairing open subscriptions without backtracking drops the createKey values that their bags bind. -/
  noBag : ∀ l, some l ∈ S → OutSubscribe l → ∀ v, l.content = some v → NoBag v

/-- The open subscription pairing of window `k`. -/
noncomputable def openPairs (S L : List (Option Line)) (internal : Line → Bool) (k : Nat) : List (String × String) :=
  let E := steps S
  let A := steps L
  let st := stateAt (context S internal) E A k
  let w := windowRun (context S internal) E A k st
  open Classical in
  if h : ∃ Q, OpenOK (openAfter E k) (openAfter A k) w.values Q ∧
      w.subscriptionIds = pairedIds (openAfter E k) Q st.subscriptionIds then Classical.choose h else []

/-- Subscription `q` was paired after window `j` with an open subscription alike `r`. -/
def SubscribedAt (S L : List (Option Line)) (internal : Line → Bool) (j : Nat) (r q : String) : Prop :=
  ∃ o a b, (o, q) ∈ openPairs S L internal j ∧ (openAfter (steps S) j).lookup r = some a ∧
    (openAfter (steps S) j).lookup o = some b ∧ alike a.out.line b.out.line = true

/-- The invariant of a state between windows: `k` windows have opened their subscriptions, and bound ids come from
lines before `bS` and `bI`. -/
structure Inv (S L : List (Option Line)) (internal : Line → Bool) (k bS bI : Nat) (st : St) : Prop where
  wf : Wf st.declared st.values
  declared : ∀ x ∈ st.declared, ∃ l, some l ∈ S ∧ x ∈ l.created.getD []
  missing : st.reportedMissing = []
  unexpected : st.reportedUnexpected = []
  openS : st.openSnapshot = openBefore (steps S) k
  openT : st.openTrace = openBefore (steps L) k
  ids : IdsInv S L bS bI st.ids st.subscriptionIds
  subs : ∀ r qs q, st.subscriptionIds.lookup r = some qs → q ∈ qs → ∃ j < k, SubscribedAt S L internal j r q

theorem mem_requestIds {L : List (Option Line)} {i : Nat} {l : Line} {q : String} (hl : L[i]? = some (some l))
    (hr : OutRequest l) (hq : l.body.id = some q) : q ∈ requestIds L := by
  unfold requestIds
  refine List.mem_filterMap.mpr ⟨some l, List.mem_of_getElem? hl, ?_⟩
  simp [hr.1, hr.2, hq]

theorem groupsIn_of_inv {S L : List (Option Line)} {bS bI : Nat} {ids : Ids} {sids : List (String × List String)}
    (h : IdsInv S L bS bI ids sids) : GroupsIn (requestIds L) ids := by
  intro r qs hm q hq
  obtain ⟨i, _, l, hl, hr, hid⟩ := h.groupValues r qs hm q hq
  exact mem_requestIds hl hr hid

theorem mem_line {ls : List (Option Line)} {o : Out} (h : AtLine ls o) : some o.line ∈ ls :=
  List.mem_of_getElem? h.2

theorem reported_of {S L : List (Option Line)} {internal : Line → Bool} (hn : Narrowed S L) {k : Nat} {e : Window}
    (he : (steps S)[k]? = some e) (ts : List Out) :
    Reported (context S internal) (specCompared (context S internal) e.before) ts := by
  intro s hs t _ htype m
  simp only [specCompared, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
  obtain ⟨⟨hsm, hsub⟩, _⟩ := hs
  obtain ⟨hat, hdir, _, _⟩ := (windowAt S k e he).before s hsm
  have hS := mem_line hat
  unfold valueMismatch
  cases hb : s.line.body with
  | command | query | event => simp
  | subscribe | unsubscribe => simp [Line.isSubscribing, hb] at hsub
  | time d | restart d => rw [hb] at hdir; cases d; simp [TraceLine.Body.dir] at hdir
  | operation d i n p => exact absurd hb ((hn.noOutOperation _ hS hdir).1 d i n p)
  | unacceptedOperation d i n p => exact absurd hb ((hn.noOutOperation _ hS hdir).2 d i n p)
  | answer d i to x =>
    cases htb : t.line.body with
    | answer d' i' to' x' =>
      simp only [htb]
      by_cases hq : (context S internal).answersQuery to = true
      · simp [hq]
      · simp only [hq, Bool.false_eq_true, ite_false]
        by_cases hres : (x.result != x'.result) = true
        · simp [hres]
        · simp only [hres, Bool.false_eq_true, ite_false]
          cases x with
          | fulfilled o => exact absurd (hn.fulfilled _ hS d i to o hb) hq
          | accepted o => cases x' <;> simp_all [Answer.result]
          | rejected r => cases x' <;> simp_all [Answer.result]
    | _ => rw [hb, htb] at htype; simp [TraceLine.Body.type] at htype

theorem _root_.Tazuna.Thm.Verify.Complete.Bindings.IdsInv.sids {S L : List (Option Line)} {bS bI : Nat} {ids : Ids} {sids sids' : List (String × List String)}
    (h : IdsInv S L bS bI ids sids)
    (hext : ∀ r qs, sids.lookup r = some qs → ∃ qs', sids'.lookup r = some qs' ∧ ∀ q ∈ qs, q ∈ qs')
    (hkeys : ∀ r qs, (r, qs) ∈ sids' → ∃ j < bS, ∃ l, S[j]? = some (some l) ∧ OutSubscribe l ∧ l.body.id = some r) :
    IdsInv S L bS bI ids sids' :=
  ⟨h.keys, h.taken, h.snap, h.impl, fun r q hm hs => by
    obtain ⟨qs, hl, hq⟩ := h.sub r q hm hs
    obtain ⟨qs', hl', hsub⟩ := hext r qs hl
    exact ⟨qs', hl', hsub q hq⟩, h.inj, h.groupKeys, h.groupValues, hkeys⟩

theorem declaredAfter_mem {ss : List Out} {d : List String} {x : String} (h : x ∈ declaredAfter ss d) :
    x ∈ d ∨ ∃ o ∈ ss, x ∈ o.line.created.getD [] := by
  unfold declaredAfter at h
  revert h
  apply foldl_preserve (fun d' => x ∈ d' → x ∈ d ∨ ∃ o ∈ ss, x ∈ o.line.created.getD [])
  · intro d' o ho hd hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hd hx
    · exact Or.inr ⟨o, ho, hx⟩
  · exact Or.inl

theorem pos_lt_inputPos (ls : List (Option Line)) {j k : Nat} (hjk : j ≤ k) {wj wk : Window}
    (hj : (steps ls)[j]? = some wj) (hk : (steps ls)[k]? = some wk) {o : Out} (ho : o ∈ wj.before) :
    o.index - 1 < inputPos (steps ls) ls.length k := by
  rcases Nat.lt_or_eq_of_le hjk with hlt | rfl
  · obtain ⟨hf, _, _, _⟩ := steps_spec ls
    have hat := ((windowAt ls j wj hj).before o ho).1
    cases hi : wk.input with
    | none =>
      simp only [inputPos, hk, Option.bind_some, hi, Option.map_none, Option.getD_none]
      have := (List.getElem?_eq_some_iff.mp hat.2).1
      omega
    | some i =>
      have := flat_order hf hlt hj hk o (by simp [windowLines, ho]) i (by simp [windowLines, hi])
      have := (((windowAt ls k wk hk).input i hi).2.2)
      have := hat.1
      omega
  · rw [hj] at hk; cases hk; exact ((windowAt ls j wj hj).before o ho).2.2.2

theorem idPairs_snd_nodup {L : List (Option Line)} (hL : IdsDistinct L) :
    ∀ (pairs : List Pair), (pairs.map (·.2.index)).Nodup → (∀ p ∈ pairs, AtLine L p.2) →
      ((idPairs pairs).map (·.2)).Nodup
  | [], _, _ => by simp [idPairs]
  | p :: ps, hn, ha => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have ih := idPairs_snd_nodup hL ps hn.2 (fun q hq => ha q (List.mem_cons_of_mem _ hq))
    rcases hs : p.1.line.body.id with _ | si <;> rcases ht : p.2.line.body.id with _ | ti <;>
      simp only [idPairs, List.filterMap_cons, hs, ht] at ih ⊢
    · exact ih
    · exact ih
    · exact ih
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hti => ?_, ih⟩
      obtain ⟨⟨a, b⟩, hab, hb⟩ := List.mem_map.mp hti
      simp only at hb
      rw [hb] at hab
      obtain ⟨q, hq, _, hqt⟩ := mem_idPairs (pairs := ps) hab
      have hp := ha p List.mem_cons_self
      have hq' := ha q (List.mem_cons_of_mem _ hq)
      have := IdAt.unique hL ⟨p.2.line, hp.2, ht⟩ ⟨q.2.line, hq'.2, hqt⟩
      exact hn.1 ⟨q, hq, by have := hp.1; have := hq'.1; omega⟩

/-- What window `k` gives when its comparison is quiet. -/
structure WindowFacts (S L : List (Option Line)) (internal : Line → Bool) (k : Nat) (e a : Window) (st w : St) :
    Prop where
  inv : Inv S L internal (k + 1) (inputPos (steps S) S.length k) (inputPos (steps L) L.length k) w
  grows : Ext st.values w.values
  bound : BoundExt st.ids w.ids
  sids : ∀ r qs, st.subscriptionIds.lookup r = some qs → ∃ qs', w.subscriptionIds.lookup r = some qs' ∧ ∀ q ∈ qs, q ∈ qs'
  pairs : ∃ pairs : List Pair, ((pairs.map (·.1)).Perm (specCompared (context S internal) e.before)) ∧
    (pairs.map (·.2)).Perm (traceCompared (context S internal) a.before) ∧
    (∀ p ∈ pairs, PairOK (context S internal) w.ids w.values p) ∧
    (∀ p ∈ pairs, ∀ q ∈ pairs, (p.1.index - 1) ∈ mustFollow S (q.1.index - 1) → p.2.index ≤ q.2.index) ∧
    (pairs.map (·.2.index)).Nodup
  opens : OpenOK (openAfter (steps S) k) (openAfter (steps L) k) w.values (openPairs S L internal k)

theorem window_step (S L : List (Option Line)) (internal : Line → Bool) (hn : Narrowed S L) (k : Nat)
    (e a : Window) (he : (steps S)[k]? = some e) (ha : (steps L)[k]? = some a)
    (hinv : Inv S L internal k (startPos (steps S) S.length k) (startPos (steps L) L.length k)
      (stateAt (context S internal) (steps S) (steps L) k))
    (hq : (runWindow (context S internal) (stateAt (context S internal) (steps S) (steps L) k)
      ((((steps S))[k]?.map (·.before)).getD []) ((((steps L))[k]?.map (·.before)).getD [])
      (((if k == 0 then none else (steps L)[k - 1]?.bind (·.input)).map (·.index)).getD 1)).1 = []) :
    WindowFacts S L internal k e a (stateAt (context S internal) (steps S) (steps L) k)
      (windowRun (context S internal) (steps S) (steps L) k (stateAt (context S internal) (steps S) (steps L) k)) := by
  let c := context S internal
  let st := stateAt c (steps S) (steps L) k
  let n := ((if k == 0 then none else (steps L)[k - 1]?.bind (·.input)).map (·.index)).getD 1
  have hw : windowRun c (steps S) (steps L) k st = (run (compareWindow e.before a.before n) c { st with findings := [] }).2 := by
    simp only [windowRun, he, ha, Option.map_some, Option.getD_some, runWindow_eq]; rfl
  rw [he, ha] at hq
  simp only [Option.map_some, Option.getD_some, runWindow_eq] at hq
  have hwa := windowAt S k e he
  have haa := windowAt L k a ha
  obtain ⟨_, spec⟩ := compareWindow_spec e.before a.before n c { st with findings := [] } (requestIds L)
  have hos : follow st.openSnapshot (subscribing e.before) = openAfter (steps S) k := by
    rw [hinv.openS, openAfter_eq, openBefore_succ _ k e he]
  have hot : follow st.openTrace (subscribing a.before) = openAfter (steps L) k := by
    rw [hinv.openT, openAfter_eq, openBefore_succ _ k a ha]
  have htp : ∀ t ∈ traceCompared c a.before, t ∈ a.before := fun t ht => (List.mem_filter.mp ht).1
  obtain ⟨Q, pairs, requests, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h18, h11, h12, h13, h14, h15, h16, h17⟩ :=
    spec
    hinv.wf hinv.missing hinv.unexpected
    (show ((follow st.openSnapshot (subscribing e.before)).map (·.1)).Nodup by rw [hos]; exact openBefore_nodup _ _)
    (show ((follow st.openTrace (subscribing a.before)).map (·.1)).Nodup by rw [hot]; exact openBefore_nodup _ _)
    (by
      intro x hx v hv
      have hx' : x ∈ openBefore (steps S) (k + 1) := by rw [← openAfter_eq, ← hos]; exact hx
      obtain ⟨j, _, w', hw', hout, d, nm, vv, hb⟩ := mem_openBefore hx'
      obtain ⟨hat, hdir, _, _⟩ := (windowAt S j w' hw').before _ hout
      exact hn.noBag _ (mem_line hat) ⟨hdir, d, some x.1, nm, vv, hb⟩ v hv)
    (reported_of hn he _)
    (by
      have := (List.pairwise_append.mp (by simpa using haa.order)).1
      exact (List.Pairwise.sublist (List.filter_sublist.map _) this).imp (fun h => Nat.ne_of_lt h))
    (groupsIn_of_inv hinv.ids)
    (by
      intro t ht hr q hq
      obtain ⟨hat, hdir, _, _⟩ := haa.before t (htp t ht)
      exact mem_requestIds hat.2 ⟨hdir, hr⟩ hq)
    (by
      intro t ht to hto
      obtain ⟨hat, hdir, _, _⟩ := haa.before t (htp t ht)
      simp only [traceCompared, List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ht
      cases hb : t.line.body with
      | answer d i to' x =>
        simp only [hb, TraceLine.Body.to?, Option.some.injEq] at hto
        subst hto
        exact hn.noOwnAnswer _ (mem_line hat) hdir d i to' x hb
      | unsubscribe d i to' => simp [Line.isSubscribing, hb] at ht
      | _ => simp [hb, TraceLine.Body.to?] at hto)
    hq
  rw [← hw] at h1 h2 h5 h8 h11 h12 h13 h14 h15 h16 h17
  generalize hW : windowRun c (steps S) (steps L) k st = w at h1 h2 h5 h8 h11 h12 h13 h14 h15 h16 h17 ⊢
  rw [hos] at h1 h2 h11
  rw [hot] at h1 h12
  have hR : ∃ Q, OpenOK (openAfter (steps S) k) (openAfter (steps L) k) w.values Q ∧
      w.subscriptionIds = pairedIds (openAfter (steps S) k) Q st.subscriptionIds := ⟨Q, h1, h2⟩
  have hQ : openPairs S L internal k = Classical.choose hR := by
    simp only [openPairs]
    rw [hW]
    split
    · rfl
    · contradiction
  obtain ⟨q1, q2⟩ := Classical.choose_spec hR
  rw [← hQ] at q1 q2
  have hsl : startPos (steps S) S.length k ≤ inputPos (steps S) S.length k :=
    startPos_le_inputPos S k (List.getElem?_eq_some_iff.mp he).1
  have hll : startPos (steps L) L.length k ≤ inputPos (steps L) L.length k :=
    startPos_le_inputPos L k (List.getElem?_eq_some_iff.mp ha).1
  have hreq : ∀ p ∈ requests, p ∈ pairs := by
    obtain ⟨others, e1⟩ := h18; intro p hp; rw [e1]; exact List.mem_append_left _ hp
  have hreqs : ∀ p ∈ requests, p.1 ∈ e.before ∧ p.1.line.isRequest = true := by
    intro p hp
    have : p.1 ∈ (specCompared c e.before).filter (·.line.isRequest) := h9 ▸ List.mem_map_of_mem hp
    simp only [specCompared, List.mem_filter] at this
    exact ⟨this.1.1.1, this.2⟩
  have hids : IdsInv S L (inputPos (steps S) S.length k) (inputPos (steps L) L.length k) w.ids w.subscriptionIds := by
    rw [h8, q2]
    have step1 : IdsInv S L (inputPos (steps S) S.length k) (startPos (steps L) L.length k) st.ids
        (pairedIds (openAfter (steps S) k) (openPairs S L internal k) st.subscriptionIds) := by
      refine (hinv.ids.mono hsl (Nat.le_refl _)).sids (pairedIds_ext _ _ _) ?_
      intro r qs hm
      rcases pairedIds_keys _ _ _ r qs hm with ⟨qs', hm'⟩ | hr
      · obtain ⟨j, hj, hj'⟩ := hinv.ids.subKeys r qs' hm'
        exact ⟨j, by omega, hj'⟩
      · rw [q1.1] at hr
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
        obtain ⟨j, hj, w', hw', hout, d, nm, vv, hb⟩ := mem_openBefore (show x ∈ openBefore (steps S) (k + 1) from hx)
        obtain ⟨hat, hdir, _, _⟩ := (windowAt S j w' hw').before _ hout
        exact ⟨_, pos_lt_inputPos S (by omega) hw' he hout, _, hat.2, ⟨hdir, d, some x.1, nm, vv, hb⟩, by rw [hb]; rfl⟩
    refine step1.groupedIds hn.snapshotIds hn.traceIds requests hll ?_ ?_ ?_
    · intro p hp
      obtain ⟨hm, hr⟩ := hreqs p hp
      obtain ⟨hat, hdir, _, hlt⟩ := hwa.before p.1 hm
      exact ⟨_, hlt, hat.2, hdir, hr⟩
    · intro p hp
      have ht : p.2 ∈ a.before := htp _ (h10 p hp)
      obtain ⟨hat, hdir, hge, hlt⟩ := haa.before p.2 ht
      have hok := h5 p (hreq p hp)
      exact ⟨_, hge, hlt, hat.2, hdir, by rw [isRequest_of_type hok.type]; exact (hreqs p hp).2⟩
    · obtain ⟨others, e1⟩ := h18
      have := h7
      rw [e1, List.map_append] at this
      refine idPairs_snd_nodup hn.traceIds requests (List.nodup_append.mp this).1 (fun p hp => ?_)
      exact (haa.before p.2 (htp _ (h10 p hp))).1
  refine ⟨⟨by rw [h13]; exact h16.1, ?_, h14, h15, by rw [h11, openAfter_eq], by rw [h12, openAfter_eq], hids, ?_⟩,
    h16.2, by rw [h8]; exact BoundExt.groupedIds _ _, by rw [q2]; exact pairedIds_ext _ _ _,
    ⟨pairs, h3, h4, h5, h6, h7⟩, q1⟩
  · intro x hx
    rw [h13] at hx
    rcases declaredAfter_mem hx with hx | ⟨o, ho, hx⟩
    · exact hinv.declared x hx
    · exact ⟨o.line, mem_line (hwa.before o ho).1, hx⟩
  · intro r qs q hl hq
    rw [q2] at hl
    rcases pairedIds_mem _ _ _ r qs q hl hq with ⟨qs', hl', hq'⟩ | ⟨o, ho, a', b, h1', h2', h3'⟩
    · obtain ⟨j, hj, hsj⟩ := hinv.subs r qs' q hl' hq'
      exact ⟨j, by omega, hsj⟩
    · exact ⟨k, by omega, o, a', b, ho, h1', h2', h3'⟩

/-- What the `in` lines of window `k` give when they are the same. -/
structure InputFacts (S : List (Option Line)) (w w' : St) (s t : Line) : Prop where
  type : t.body.type = s.body.type
  name : t.body.name? = s.body.name?
  time : sameTime s t = true
  facts : InFacts S w'.ids w.subscriptionIds s t
  content : ComparesValue s → ContentAfter w'.values s.content t.content
  grows : Ext w.values w'.values
  bound : BoundExt w.ids w'.ids
  sids : w'.subscriptionIds = w.subscriptionIds

theorem input_step (S L : List (Option Line)) (internal : Line → Bool) (hn : Narrowed S L) (k : Nat)
    (e a : Window) (he : (steps S)[k]? = some e) (ha : (steps L)[k]? = some a) (s t : Out)
    (hs : e.input = some s) (ht : a.input = some t) (w : St)
    (hinv : Inv S L internal (k + 1) (inputPos (steps S) S.length k) (inputPos (steps L) L.length k) w)
    (hq : (sameInput w s.line t.line).1 = true) :
    Inv S L internal (k + 1) (startPos (steps S) S.length (k + 1)) (startPos (steps L) L.length (k + 1))
        (inputRun (steps S) (steps L) k w) ∧
      InputFacts S w (inputRun (steps S) (steps L) k w) s.line t.line := by
  have hrun : inputRun (steps S) (steps L) k w =
      { (sameInput w s.line t.line).2 with ids := inputIds (sameInput w s.line t.line).2.ids s.line t.line } := by
    simp [inputRun, he, ha, hs, ht]
  rw [hrun]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := sameInput_true w s.line t.line hq
  generalize hv : (sameInput w s.line t.line).2.values = v at h4 h6 h7
  rw [h4]
  obtain ⟨hsat, hsd, hsp⟩ := (windowAt S k e he).input s hs
  obtain ⟨htat, _, htp⟩ := (windowAt L k a ha).input t ht
  have hS : S[inputPos (steps S) S.length k]? = some (some s.line) := by rw [← hsp]; exact hsat.2
  have hL : L[inputPos (steps L) L.length k]? = some (some t.line) := by rw [← htp]; exact htat.2
  obtain ⟨i1, i2, i3⟩ := inputIds_spec w hn.snapshotIds hn.traceIds hinv.ids hS hsd hL h5
  have hg : Grows w.declared w.values v := by
    by_cases hc : ComparesValue s.line
    · have := equalContent_grows w.declared s.line.content t.line.content w.values true hinv.wf
      rw [h6 hc] at this; exact this
    · rw [h7 hc]; exact Grows.refl hinv.wf
  refine ⟨⟨hg.1, hinv.declared, hinv.missing, hinv.unexpected, hinv.openS, hinv.openT, i1, hinv.subs⟩,
    ⟨h1, h2, h3, i3, fun hc => ?_, hg.2, i2, rfl⟩⟩
  have := equalContent_sound w.declared s.line.content t.line.content w.values true hinv.wf (by rw [h6 hc])
  rwa [h6 hc] at this

end Tazuna.Thm.Verify.Complete.Induction
