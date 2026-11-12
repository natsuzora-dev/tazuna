import Tazuna.Thm.Verify.Complete.Run

namespace Tazuna.Thm.Verify.Complete.Window

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Run

/-- The fields that pairing lines leaves alone. -/
structure Rest (st st' : St) : Prop where
  ids : st'.ids = st.ids
  declared : st'.declared = st.declared
  openSnapshot : st'.openSnapshot = st.openSnapshot
  openTrace : st'.openTrace = st.openTrace
  subscriptionIds : st'.subscriptionIds = st.subscriptionIds
  reportedMissing : st'.reportedMissing = st.reportedMissing
  reportedUnexpected : st'.reportedUnexpected = st.reportedUnexpected

theorem Rest.refl (st : St) : Rest st st := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What a quiet pairing tells about a pair: equal type, place and time, and values that match. -/
structure PairOK (c : Ctx) (ids : Ids) (m : Bindings) (p : Pair) : Prop where
  type : p.2.line.body.type = p.1.line.body.type
  place : samePlace ids p.1.line p.2.line = true
  time : sameTime p.1.line p.2.line = true
  value : ContentAfter m (c.compared p.1.line p.2.line).1 (c.compared p.1.line p.2.line).2

theorem PairOK.mono {c : Ctx} {ids : Ids} {m m' : Bindings} {p : Pair} (h : PairOK c ids m p) (he : Ext m m') :
    PairOK c ids m' p := ⟨h.type, h.place, h.time, h.value.mono he⟩

/-- Binding the request of a paired answer leaves the ids alone. -/
def IdsStay (ids : Ids) (ss ts : List Out) : Prop :=
  ∀ s ∈ ss, ∀ t ∈ ts, samePlace ids s.line t.line = true → idsAfter s.line t ids = ids

/-- A paired line with a different value is reported. -/
def Reported (c : Ctx) (ss ts : List Out) : Prop :=
  ∀ s ∈ ss, ∀ t ∈ ts, t.line.body.type = s.line.body.type → ∀ m, valueMismatch c s.line t m ≠ none

theorem missing_run (s : Out) (n : Nat) (c : Ctx) (st : St) :
    ∃ m, (run (missing s n) c st).2.findings = st.findings ++ [m] := by
  simp only [missing]
  simp_run
  split <;> exact ⟨_, rfl⟩

theorem orElse_mem {α : Type} {a b : Option α} {x : α} (h : (a <|> b) = some x) : a = some x ∨ b = some x := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem chosen_mem {α : Type} {p q : α → Bool} {l : List α} {x : α}
    (h : (l.find? p <|> l.find? q <|> l.head?) = some x) : x ∈ l := by
  rcases orElse_mem h with h | h
  · exact List.mem_of_find?_eq_some h
  · rcases orElse_mem h with h | h
    · exact List.mem_of_find?_eq_some h
    · exact List.mem_of_mem_head? h

/-- The findings of a quiet pairing for report, which reports each line that it cannot pair. -/
theorem pairForReport_spec (ss ts : List Out) (missingAt : Nat) (c : Ctx) (st : St) :
    let r := run (pairForReport ss ts missingAt) c st
    st.findings <+: r.2.findings ∧ (Wf st.declared st.values → IdsStay st.ids ss ts → Reported c ss ts →
      r.2.findings = st.findings →
      r.1.map (·.1) = ss ∧ (∀ p ∈ r.1, p.2 ∈ ts ∧ PairOK c st.ids r.2.values p) ∧
      (r.1.map (·.2.index)).Nodup ∧ Rest st r.2 ∧ Grows st.declared st.values r.2.values) := by
  simp only [pairForReport, run_bind, run_pure]
  let P : List Out → List Nat × List Pair → St → Prop := fun pre b st' =>
    st.findings <+: st'.findings ∧ (Wf st.declared st.values → IdsStay st.ids ss ts → Reported c ss ts →
      st'.findings = st.findings → b.2.map (·.1) = pre ∧ b.1 = (b.2.map (·.2.index)).reverse ∧
      (∀ p ∈ b.2, p.2 ∈ ts ∧ PairOK c st.ids st'.values p) ∧
      (b.2.map (·.2.index)).Nodup ∧ Rest st st' ∧ Grows st.declared st.values st'.values)
  refine forIn_apply ss ([], []) _ c st P (fun r => st.findings <+: r.2.findings ∧ (Wf st.declared st.values →
      IdsStay st.ids ss ts → Reported c ss ts → r.2.findings = st.findings →
      r.1.2.map (·.1) = ss ∧ (∀ p ∈ r.1.2, p.2 ∈ ts ∧ PairOK c st.ids r.2.values p) ∧
      (r.1.2.map (·.2.index)).Nodup ∧ Rest st r.2 ∧ Grows st.declared st.values r.2.values)) ?_ ?_ ?_ ?_
  · intro x b st'
    simp_run
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rintro pre x ⟨used, pairs⟩ st' hpre ⟨hp, hq⟩
    have hx : x ∈ ss := hpre.subset (by simp)
    simp_run
    split
    · obtain ⟨m, hm⟩ := missing_run x missingAt c st'
      simp only [P, run_bind, run_pure, hm]
      refine ⟨hp.trans (List.prefix_append _ _), fun _ _ _ he => ?_⟩
      have := congrArg List.length he
      have := hp.length_le
      simp at *; omega
    · rename_i t hch
      have hmem := chosen_mem hch
      simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at hmem
      obtain ⟨htm, ⟨hused, htype⟩, hplace⟩ := hmem
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := matchLine_run x.line t c st'
      simp only [P, run_bind, run_pure]
      refine ⟨hp.trans m1, fun hw hb hr he => ?_⟩
      have hq' : st'.findings = st.findings := prefix_squeeze hp m1 he
      obtain ⟨q1, q2, q3, q4, ⟨r1, r2, r3, r4, r5, r6, r7⟩, q6⟩ := hq hw hb hr hq'
      dsimp only [ForInStep.value] at q1 q2 q3 q4 ⊢
      rw [r1] at hplace
      obtain ⟨ht, he'⟩ := m10 (he.trans hq'.symm) (hr x hx t htm htype)
      rw [r2] at he'
      have hg := tryEqual_grows st.declared (c.compared x.line t.line).1 (c.compared x.line t.line).2 st'.values q6.1
      have hs := tryEqual_sound _ _ _ _ q6.1 he'
      refine ⟨by simp [q1], by simp [q2], ?_, ?_, ?_, ?_⟩
      · intro p hp'
        rw [m2, r2]
        rcases List.mem_append.mp hp' with hp' | hp'
        · exact ⟨(q3 p hp').1, (q3 p hp').2.mono hg.2⟩
        · simp only [List.mem_singleton] at hp'
          subst hp'
          exact ⟨htm, htype, hplace, ht, hs⟩
      · rw [List.map_append]
        refine List.nodup_append.mpr ⟨q4, by simp, ?_⟩
        intro a ha b hb e
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        have h2 := List.contains_iff_mem.mpr
          (show t.index ∈ used by rw [q2, List.mem_reverse, ← hb, ← e]; exact ha)
        rw [hused] at h2; cases h2
      · refine ⟨?_, m4.trans r2, m5.trans r3, m6.trans r4, m7.trans r5, m8.trans r6, m9.trans r7⟩
        rw [m3, r1]
        exact hb x hx t htm (r1 ▸ hplace)
      · rw [m2, r2]; exact q6.trans hg
  · exact ⟨List.prefix_refl _, fun hw _ _ _ => ⟨rfl, rfl, by simp, by simp, Rest.refl st, Grows.refl hw⟩⟩
  · rintro r ⟨h1, h2⟩
    exact ⟨h1, fun hw hb hr hq => by obtain ⟨a, _, b, c, d⟩ := h2 hw hb hr hq; exact ⟨a, b, c, d⟩⟩

mutual

theorem pairExactly_grows (c : Ctx) (ids : Ids) (d : List String) :
    ∀ (ss ts : List Out) (m : Bindings) (pairs : List Pair) (m' : Bindings), Wf d m →
      pairExactly c ids d ss ts m = some (pairs, m') → Grows d m m'
  | [], ts, m, pairs, m', h, he => by rw [pairExactly] at he; cases he; exact Grows.refl h
  | first :: rest, ts, m, pairs, m', h, he => by
    rw [pairExactly] at he
    exact pairExactly_go_grows c ids d first rest ts [] [] m pairs m' h he

theorem pairExactly_go_grows (c : Ctx) (ids : Ids) (d : List String) (first : Out) (rest : List Out) :
    ∀ (cands passed : List Out) (tried : List Value) (m : Bindings) (pairs : List Pair) (m' : Bindings), Wf d m →
      pairExactly.go c ids d first rest cands passed tried m = some (pairs, m') → Grows d m m'
  | [], _, _, _, _, _, _, he => by rw [pairExactly.go] at he; cases he
  | t :: more, passed, tried, m, pairs, m', h, he => by
    rw [pairExactly.go] at he
    split at he
    · exact pairExactly_go_grows c ids d first rest more (t :: passed) tried m pairs m' h he
    · dsimp only at he
      split at he
      · exact pairExactly_go_grows c ids d first rest more (t :: passed) tried m pairs m' h he
      · split at he
        · rename_i m₁ e
          have hg := tryEqual_grows d (c.compared first.line t.line).1 (c.compared first.line t.line).2 m h
          rw [e] at hg
          split at he
          · rename_i rp m₂ e2
            simp only [Option.some.injEq, Prod.mk.injEq] at he
            rw [← he.2]
            exact hg.trans (pairExactly_grows c ids d rest _ m₁ rp m₂ hg.1 e2)
          · exact pairExactly_go_grows c ids d first rest more (t :: passed) _ m pairs m' h he
        · exact pairExactly_go_grows c ids d first rest more (t :: passed) _ m pairs m' h he

end

theorem perm_append_mem {α : Type} {xs r ts : List α} (h : (xs ++ r).Perm ts) {x : α} (hx : x ∈ xs) : x ∈ ts :=
  h.subset (List.mem_append_left _ hx)

/-- The findings of a quiet pairing. -/
theorem pairLines_spec (ss ts : List Out) (missingAt : Nat) (c : Ctx) (st : St) :
    let r := run (pairLines ss ts missingAt) c st
    st.findings <+: r.2.findings ∧ (Wf st.declared st.values → IdsStay st.ids ss ts → Reported c ss ts →
      (ts.map (·.index)).Nodup → r.2.findings = st.findings →
      r.1.map (·.1) = ss ∧ (∀ p ∈ r.1, p.2 ∈ ts ∧ PairOK c st.ids r.2.values p) ∧
      (r.1.map (·.2.index)).Nodup ∧ Rest st r.2 ∧ Grows st.declared st.values r.2.values) := by
  simp only [pairLines]
  simp_run
  split
  · obtain ⟨h1, h2⟩ := pairForReport_spec ss ts missingAt c st
    exact ⟨h1, fun hw hb hr _ => h2 hw hb hr⟩
  · rename_i pairs m he
    obtain ⟨h1, ⟨r, hperm⟩, h3⟩ := pairExactly_spec c st.ids st.declared ss ts st.values pairs m he
    simp only [run_bind, run_pure]
    let st₀ : St := { st with values := m }
    let P : List Pair → PUnit → St → Prop := fun pre _ st' =>
      st.findings <+: st'.findings ∧ (Wf st.declared st.values → IdsStay st.ids ss ts → Reported c ss ts →
        st'.findings = st.findings → (∀ p ∈ pre, PairOK c st.ids st'.values p) ∧ Rest st st' ∧ Grows st.declared st.values st'.values)
    refine forIn_apply pairs ⟨⟩ _ c st₀ P (fun r => st.findings <+: r.2.findings ∧ (Wf st.declared st.values →
      IdsStay st.ids ss ts → Reported c ss ts → (ts.map (·.index)).Nodup → r.2.findings = st.findings →
      pairs.map (·.1) = ss ∧ (∀ p ∈ pairs, p.2 ∈ ts ∧ PairOK c st.ids r.2.values p) ∧
      (pairs.map (·.2.index)).Nodup ∧ Rest st r.2 ∧ Grows st.declared st.values r.2.values)) ?_ ?_ ?_ ?_
    · rintro ⟨s, t⟩ b st'
      simp only [run_bind, run_pure]
      exact ⟨⟨⟩, trivial⟩
    · rintro pre ⟨s, t⟩ _ st' hpre ⟨hp, hq⟩
      have hx : (s, t) ∈ pairs := hpre.subset (by simp)
      have hs : s ∈ ss := h1 ▸ List.mem_map_of_mem (f := (·.1)) hx
      have ht : t ∈ ts := perm_append_mem hperm (List.mem_map_of_mem (f := (·.2)) hx)
      obtain ⟨pt, pp, ptime⟩ := h3 _ hx
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := matchLine_run s.line t c st'
      simp only [P, run_bind, run_pure]
      refine ⟨hp.trans m1, fun hw hb hr he => ?_⟩
      have hq' : st'.findings = st.findings := prefix_squeeze hp m1 he
      obtain ⟨q1, ⟨r1, r2, r3, r4, r5, r6, r7⟩, q3⟩ := hq hw hb hr hq'
      obtain ⟨_, he'⟩ := m10 (he.trans hq'.symm) (hr s hs t ht pt)
      rw [r2] at he'
      have hg' := tryEqual_grows st.declared (c.compared s.line t.line).1 (c.compared s.line t.line).2 st'.values q3.1
      have hv := tryEqual_sound _ _ _ _ q3.1 he'
      refine ⟨?_, ?_, ?_⟩
      · intro p hp'
        rw [m2, r2]
        rcases List.mem_append.mp hp' with hp' | hp'
        · exact (q1 p hp').mono hg'.2
        · simp only [List.mem_singleton] at hp'
          subst hp'
          exact ⟨pt, pp, ptime, hv⟩
      · refine ⟨?_, m4.trans r2, m5.trans r3, m6.trans r4, m7.trans r5, m8.trans r6, m9.trans r7⟩
        rw [m3, r1]
        exact hb s hs t ht pp
      · rw [m2, r2]; exact q3.trans hg'
    · exact ⟨List.prefix_refl _, fun hw _ _ _ =>
        ⟨by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, pairExactly_grows c st.ids st.declared ss ts st.values pairs m hw he⟩⟩
    · rintro ⟨_, st'⟩ ⟨h1', h2'⟩
      refine ⟨h1', fun hw hb hr hn hq => ?_⟩
      obtain ⟨a, b, d⟩ := h2' hw hb hr hq
      refine ⟨h1, fun p hp => ⟨perm_append_mem hperm (List.mem_map_of_mem (f := (·.2)) hp), a p hp⟩, ?_, b, d⟩
      have := (hperm.map (·.index)).nodup_iff.mpr hn
      rw [List.map_append, List.map_map] at this
      exact (List.nodup_append.mp this).1

/-- The request groups that `groupRequests` collects. -/
def requestGroups (pairs : List Pair) : List (Line × List String × List String) :=
  pairs.foldl (init := ([] : List (Line × List String × List String))) fun groups (s, t) =>
    match s.line.body.id, t.line.body.id with
    | some si, some ti =>
      match groups.findIdx? (fun (l, _, _) => alike l s.line) with
      | some i => groups.modify i fun (l, ss, ts) => (l, ss ++ [si], ts ++ [ti])
      | none => groups ++ [(s.line, [si], [ti])]
    | _, _ => groups

/-- The ids after `groupRequests pairs`. -/
def groupedIds (pairs : List Pair) (ids : Ids) : Ids :=
  (requestGroups pairs).foldl (fun ids (_, ss, ts) => ids.group ss ts) ids

theorem groupRequests_run (pairs : List Pair) (c : Ctx) (st : St) :
    run (groupRequests pairs) c st = (⟨⟩, { st with ids := groupedIds pairs st.ids }) := rfl

/-- The implementation ids that request groups hold are in `G`. -/
def GroupsIn (G : List String) (ids : Ids) : Prop := ∀ r qs, (r, qs) ∈ ids.groups → ∀ q ∈ qs, q ∈ G

theorem mem_setAt_any {β : Type} : ∀ {m : List (String × β)} {k k' : String} {v v' : β},
    (k', v') ∈ setAt m k v → (k' = k ∧ v' = v) ∨ (k', v') ∈ m
  | [], k, k', v, v', h => by simp [setAt] at h; left; exact h
  | (a, b) :: rest, k, k', v, v', h => by
    by_cases e : a = k
    · subst e
      simp only [setAt, beq_self_eq_true, ite_true, List.mem_cons, Prod.mk.injEq] at h
      rcases h with h | h
      · left; exact h
      · right; exact List.mem_cons_of_mem _ h
    · have : (a == k) = false := by simpa using e
      simp only [setAt, this, Bool.false_eq_true, ite_false, List.mem_cons] at h
      rcases h with h | h
      · right; rw [h]; exact List.mem_cons_self
      · rcases mem_setAt_any h with h | h
        · left; exact h
        · right; exact List.mem_cons_of_mem _ h

theorem GroupsIn.bind {G : List String} {ids : Ids} (h : GroupsIn G ids) (s t : Option String) :
    GroupsIn G (ids.bind s t) := by
  unfold Ids.bind
  split
  · split
    · exact h
    · intro r qs hm q hq
      simp only [List.mem_filter] at hm
      exact h r qs hm.1 q hq
  · exact h

theorem GroupsIn.group {G : List String} {ids : Ids} (h : GroupsIn G ids) (snapshot trace : List String)
    (ht : ∀ q ∈ trace, q ∈ G) : GroupsIn G (ids.group snapshot trace) := by
  unfold Ids.group
  split
  · exact h.bind _ _
  · intro r qs hm q hq
    simp only at hm
    revert hm
    apply foldl_preserve (fun g => (r, qs) ∈ g → q ∈ G)
    · intro g id _ hg hm
      rcases mem_setAt_any hm with ⟨_, e⟩ | hm
      · subst e; exact ht q hq
      · exact hg hm
    · intro hm; exact h r qs hm q hq

theorem mem_modify {α : Type} (f : α → α) : ∀ (l : List α) (i : Nat) (x : α), x ∈ l.modify i f → x ∈ l ∨ ∃ y ∈ l, x = f y
  | [], _, _, h => by simp at h
  | a :: l, 0, x, h => by
    simp only [List.modify_zero_cons, List.mem_cons] at h
    rcases h with h | h
    · right; exact ⟨a, List.mem_cons_self, h⟩
    · left; exact List.mem_cons_of_mem _ h
  | a :: l, i + 1, x, h => by
    simp only [List.modify_succ_cons, List.mem_cons] at h
    rcases h with h | h
    · left; rw [h]; exact List.mem_cons_self
    · rcases mem_modify f l i x h with h | ⟨y, hy, e⟩
      · left; exact List.mem_cons_of_mem _ h
      · right; exact ⟨y, List.mem_cons_of_mem _ hy, e⟩

theorem requestGroups_trace (pairs : List Pair) :
    ∀ g ∈ requestGroups pairs, ∀ q ∈ g.2.2, ∃ p ∈ pairs, p.2.line.body.id = some q := by
  unfold requestGroups
  refine foldl_preserve (fun (gs : List (Line × List String × List String)) =>
    ∀ g ∈ gs, ∀ q ∈ g.2.2, ∃ p ∈ pairs, p.2.line.body.id = some q) _ _ _ ?_ ?_
  · rintro gs ⟨s, t⟩ hp hgs
    dsimp only
    split
    · rename_i si ti _ ht
      split
      · rename_i i _
        intro g hg q hq
        rcases mem_modify _ gs i g hg with hg | ⟨y, hy, e⟩
        · exact hgs g hg q hq
        · subst e
          simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with hq | hq
          · exact hgs y hy q hq
          · exact ⟨(s, t), hp, by rw [ht, hq]⟩
      · intro g hg q hq
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | hg
        · exact hgs g hg q hq
        · subst hg
          simp only [List.mem_singleton] at hq
          exact ⟨(s, t), hp, by rw [ht, hq]⟩
    · exact hgs
  · simp

theorem groupedIds_in {G : List String} {ids : Ids} (pairs : List Pair) (h : GroupsIn G ids)
    (hp : ∀ p ∈ pairs, ∀ q, p.2.line.body.id = some q → q ∈ G) : GroupsIn G (groupedIds pairs ids) := by
  unfold groupedIds
  apply foldl_preserve (GroupsIn G) _ _ _ _ h
  rintro ids ⟨l, ss, ts⟩ hg hi
  apply hi.group
  intro q hq
  obtain ⟨p, hp', e⟩ := requestGroups_trace pairs _ hg q hq
  exact hp p hp' q e

theorem idsStay_of {G : List String} {ids : Ids} {ss ts : List Out} (h : GroupsIn G ids)
    (ht : ∀ t ∈ ts, ∀ to, t.line.body.to? = some to → to ∉ G) : IdsStay ids ss ts := by
  intro s _ t htm hp
  unfold idsAfter
  split
  · rename_i to _ hb
    simp only [samePlace, hb] at hp
    unfold Ids.bind
    split
    · rename_i s' t' e1 e2
      simp only [Option.some.injEq] at e1
      subst e1
      split
      · rfl
      · rename_i hn
        exfalso
        simp only [Ids.matches, e2] at hp
        split at hp
        · rename_i b hl; simp [hl] at hn
        · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
          obtain ⟨hg, _⟩ := hp
          cases hgl : ids.groups.lookup to with
          | none => simp [hgl] at hg
          | some qs =>
            simp only [hgl, Option.map_some, Option.getD_some, List.contains_iff_mem] at hg
            exact ht t htm t' e2 (h to qs (mem_of_lookup hgl) t' hg)
    · rfl
  · rfl

theorem samePlace_request {s t : Line} (ids ids' : Ids) (h : s.isRequest = true) :
    samePlace ids s t = samePlace ids' s t := by
  unfold samePlace
  split
  · simp_all [Line.isRequest]
  · simp_all [Line.isRequest]
  · rfl

/-- The fields that pairing a window leaves alone. -/
structure Keeps (st st' : St) : Prop where
  declared : st'.declared = st.declared
  openSnapshot : st'.openSnapshot = st.openSnapshot
  openTrace : st'.openTrace = st.openTrace
  subscriptionIds : st'.subscriptionIds = st.subscriptionIds
  reportedMissing : st'.reportedMissing = st.reportedMissing
  reportedUnexpected : st'.reportedUnexpected = st.reportedUnexpected

theorem Rest.keeps {st st' : St} (h : Rest st st') : Keeps st st' :=
  ⟨h.declared, h.openSnapshot, h.openTrace, h.subscriptionIds, h.reportedMissing, h.reportedUnexpected⟩

theorem Keeps.trans {a b c : St} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  ⟨h₂.declared.trans h₁.declared, h₂.openSnapshot.trans h₁.openSnapshot, h₂.openTrace.trans h₁.openTrace,
    h₂.subscriptionIds.trans h₁.subscriptionIds, h₂.reportedMissing.trans h₁.reportedMissing,
    h₂.reportedUnexpected.trans h₁.reportedUnexpected⟩

theorem isRequest_of_type {s t : Line} (h : t.body.type = s.body.type) : t.isRequest = s.isRequest := by
  unfold Line.isRequest
  cases hs : s.body <;> cases ht : t.body <;> simp_all [TraceLine.Body.type]

theorem idsAfter_request {s : Line} (t : Out) (ids : Ids) (h : s.isRequest = true) : idsAfter s t ids = ids := by
  unfold idsAfter
  split
  · rename_i hb; simp [Line.isRequest, hb] at h
  · rfl

/-- The findings of a quiet pairing of a window. `G` holds the ids of the implementation's requests. -/
theorem pairWindow_spec (ss ts : List Out) (missingAt : Nat) (c : Ctx) (st : St) (G : List String) :
    let r := run (pairWindow ss ts missingAt) c st
    st.findings <+: r.2.findings ∧ (Wf st.declared st.values → Reported c ss ts → (ts.map (·.index)).Nodup →
      GroupsIn G st.ids → (∀ t ∈ ts, t.line.isRequest = true → ∀ q, t.line.body.id = some q → q ∈ G) →
      (∀ t ∈ ts, ∀ to, t.line.body.to? = some to → to ∉ G) → r.2.findings = st.findings →
      ∃ requests : List Pair, r.2.ids = groupedIds requests st.ids ∧
        requests.map (·.1) = ss.filter (·.line.isRequest) ∧ (∀ p ∈ requests, p.2 ∈ ts) ∧
        (∃ others, r.1 = requests ++ others) ∧ (r.1.map (·.1)).Perm ss ∧ (∀ p ∈ r.1, p.2 ∈ ts ∧ PairOK c r.2.ids r.2.values p) ∧
        (r.1.map (·.2.index)).Nodup ∧ Keeps st r.2 ∧ Grows st.declared st.values r.2.values ∧
        GroupsIn G r.2.ids) := by
  simp only [pairWindow, run_bind, run_pure, groupRequests_run]
  obtain ⟨a1, a2⟩ := pairLines_spec (ss.filter (·.line.isRequest)) ts missingAt c st
  generalize hR : run (pairLines (ss.filter (·.line.isRequest)) ts missingAt) c st = R at a1 a2
  obtain ⟨requests, st₁⟩ := R
  simp only at a1 a2 ⊢
  let left := ts.filter fun t => !requests.any fun x => x.snd.index == t.index
  obtain ⟨b1, b2⟩ := pairLines_spec (ss.filter fun x => !x.line.isRequest) left missingAt c
    { st₁ with ids := groupedIds requests st₁.ids }
  refine ⟨a1.trans b1, fun hw hr hn hG hreq hans he => ?_⟩
  have hq₁ : st₁.findings = st.findings := prefix_squeeze a1 b1 he
  have hleft : ∀ t ∈ left, t ∈ ts := fun t ht => (List.mem_filter.mp ht).1
  have hb₁ : IdsStay st.ids (ss.filter (·.line.isRequest)) ts := by
    intro s hs t _ _
    exact idsAfter_request t st.ids (List.mem_filter.mp hs).2
  obtain ⟨c1, c2, c3, c4, c5⟩ := a2 hw hb₁ (fun s hs => hr s (List.mem_filter.mp hs).1) hn hq₁
  have hreqs : ∀ p ∈ requests, p.1 ∈ ss.filter (·.line.isRequest) := fun p hp => c1 ▸ List.mem_map_of_mem hp
  have hG₂ : GroupsIn G (groupedIds requests st₁.ids) := by
    refine groupedIds_in requests (c4.ids ▸ hG) ?_
    intro p hp q hq
    obtain ⟨htm, hok⟩ := c2 p hp
    refine hreq p.2 htm ?_ q hq
    rw [isRequest_of_type hok.type]
    exact (List.mem_filter.mp (hreqs p hp)).2
  obtain ⟨d1, d2, d3, d4, d5⟩ := b2 (c4.declared ▸ c5.1) (idsStay_of hG₂ (fun t ht => hans t (hleft t ht)))
    (fun s hs t ht => hr s (List.mem_filter.mp hs).1 t (hleft t ht))
    (hn.sublist (List.filter_sublist.map _)) (he.trans hq₁.symm)
  generalize hO : run (pairLines (ss.filter fun x => !x.line.isRequest) left missingAt) c
    { st₁ with ids := groupedIds requests st₁.ids } = O at d1 d2 d3 d4 d5
  obtain ⟨others, st₃⟩ := O
  simp only at d1 d2 d3 d4 d5 ⊢
  refine ⟨requests, by rw [d4.ids, c4.ids], c1, fun p hp => (c2 p hp).1, ⟨others, rfl⟩, ?_, ?_, ?_, ?_, ?_,
    d4.ids ▸ hG₂⟩
  · rw [List.map_append, c1, d1]; exact List.filter_append_perm _ _
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨htm, hok⟩ := c2 p hp
      refine ⟨htm, ⟨hok.type, ?_, hok.time, hok.value.mono ?_⟩⟩
      · rw [samePlace_request _ _ (List.mem_filter.mp (hreqs p hp)).2]; exact hok.place
      · exact d5.2
    · obtain ⟨htm, hok⟩ := d2 p hp
      exact ⟨hleft _ htm, by rw [d4.ids]; exact hok⟩
  · rw [List.map_append]
    refine List.nodup_append.mpr ⟨c3, d3, ?_⟩
    intro a ha b hb e
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    have := (List.mem_filter.mp (d2 q hq).1).2
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, beq_iff_eq] at this
    exact this p hp e
  · exact c4.keeps.trans ⟨d4.declared, d4.openSnapshot, d4.openTrace, d4.subscriptionIds, d4.reportedMissing,
      d4.reportedUnexpected⟩
  · exact c4.declared ▸ c5.trans (by simpa [d4.declared, c4.declared] using d5)

end Tazuna.Thm.Verify.Complete.Window
