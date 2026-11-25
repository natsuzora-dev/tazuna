import Tazuna.Smt.PairLine

/-! Every own effect waiting in a cascade is one a script can hold (`EffCoded`), wherever the cascade starts with
such effects and every step it takes fits the slots: an own step's encoding relates each own effect it queues to a
value of the effect datatype (`AccRel`'s own slots), and a value that codes data has its sort (`sorted_of_relD`),
so each queued effect is coded. Where the pair lines read `Prove.proved`, every step from a state that fits the
slots fits too (the bound question of the effect's pair with itself is unsat), so the lines need no more than the
states to fit; where they read `Prove.withinBounds`, the steps' fit is the scope they state. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout}

theorem sortedAlts_ge {d : Nat} : (k : Nat) → (vs : List (List Ty)) → {w : Val} → SortedAlts L d k vs w →
    ∃ k' vals, w = .ctor d k' vals ∧ k ≤ k'
  | k, [], _, ⟨_, h⟩ => ⟨0, [], h, by omega⟩
  | k, _ :: vs, _, ⟨k', vals, h, hc⟩ => by
    rcases hc with ⟨rfl, -⟩ | ⟨hne, hr⟩
    · exact ⟨k', vals, h, Nat.le_refl _⟩
    · obtain ⟨k'', vals', h', hle⟩ := sortedAlts_ge (k + 1) vs hr
      exact ⟨k'', vals', h', by omega⟩

theorem occupied_mem {sv : List (Bool × List Val)} {p : Bool × List Val} (hp : p ∈ sv) (h : p.1 = true) :
    p.2 ∈ occupied sv := by
  simp only [occupied, List.mem_filterMap]
  exact ⟨p, hp, by simp [h]⟩

mutual
/-- A value that codes data has its type's sort. -/
theorem sorted_of_relD : (t : Ty) → (x : t.den0) → (z : Val) → RelD L t x z → Sorted L t z
  | .int, x, _, h | .date, x, _, h => ⟨x, h⟩
  | .str, x, _, h => ⟨x, h⟩
  | .dsl .fresh _, x, _, h => ⟨_, h⟩
  | .id, x, _, ⟨d, n, hf, h⟩ => by
    subst h
    cases x with
    | fresh s i => exact ⟨d, n, hf, .inl ⟨s, i, rfl⟩⟩
    | named s => exact ⟨d, n, hf, .inr ⟨s, rfl⟩⟩
  | .adt 0 _ vs, _, _, ⟨h, hz⟩ => ⟨h, _, hz⟩
  | .adt (i + 1) a vs, x, z, ⟨d, n, hf, h⟩ => ⟨d, n, hf, sortedAlts_of_relD d 0 vs x z h⟩
  | .tuple ts, x, z, ⟨d, n, vals, hf, hz, h⟩ => ⟨d, n, vals, hf, hz, sortedVs_of_relDs ts x vals h⟩
  | .bag t, _, _, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, _, _, hh⟩ => by
    subst h3 h4
    refine ⟨d, sv.length, dt, m, sv, h1, h2, collView_slots sv h5, fun p hp hb z hz => ?_⟩
    obtain ⟨y, -, z', hz', hr⟩ := forall2_mem_right hh p.2 (occupied_mem hp hb)
    rw [hz] at hz'
    cases hz'
    exact sorted_of_relD t y _ hr
  | .list t, _, _, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, hh⟩ => by
    subst h3 h4
    refine ⟨d, sv.length, dt, m, sv, h1, h2, collView_slots sv h5, fun p hp hb z hz => ?_⟩
    obtain ⟨y, -, z', hz', hr⟩ := forall2_mem_right hh p.2 (occupied_mem hp hb)
    rw [hz] at hz'
    cases hz'
    exact sorted_of_relD t y _ hr
  | .table k w, _, _, ⟨d, n, dt, m, sv, h1, h2, h3, h4, h5, _, _, hh⟩ => by
    subst h3 h4
    refine ⟨d, sv.length, dt, m, sv, h1, h2, collView_slots sv h5, fun p hp hb zk zv hz => ?_⟩
    obtain ⟨y, -, zk', zv', hz', hk, hw⟩ := forall2_mem_right hh p.2 (occupied_mem hp hb)
    rw [hz] at hz'
    cases hz'
    exact ⟨sorted_of_relD k y.1 _ hk, sorted_of_relD w y.2 _ hw⟩
theorem sortedVs_of_relDs : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (zs : List Val) → RelDs L ts x zs →
    SortedVs L ts zs
  | [], _, _, h => by subst h; trivial
  | t :: ts, (x, xs), _, ⟨z, zs, h, hz, hzs⟩ => by
    subst h
    exact ⟨sorted_of_relD t x z hz, sortedVs_of_relDs ts xs zs hzs⟩
theorem sortedAlts_of_relD (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) →
    (z : Val) → RelDAlts L d k vs x z → SortedAlts L d k vs z
  | k, fs :: _, .inl x, _, ⟨vals, h, hr⟩ => ⟨k, vals, h, .inl ⟨rfl, sortedVs_of_relDs fs x vals hr⟩⟩
  | k, _ :: vs, .inr y, z, h => by
    have hs := sortedAlts_of_relD d (k + 1) vs y z h
    obtain ⟨k', vals, hz, hle⟩ := sortedAlts_ge (k + 1) vs hs
    exact ⟨k', vals, hz, .inr ⟨by omega, hs⟩⟩
end

theorem sorted_capRel {t : Ty} {f : Fun t} {z : Val} (h : CapRel L f z) : Sorted L (.tuple f.Γ) z := by
  obtain ⟨d, n, vals, hf, hz, hr⟩ := h
  exact ⟨d, n, vals, hf, hz, sortedVs_of_relDs f.Γ f.env vals hr⟩

/-- A value that codes an own effect has the effect datatype's sort. -/
theorem effSorted_of_rel {e : Ty} {x : EffectV e} (hown : x.isRequest = false) {z : Val}
    (h : RelV L (.dsl .effect [e]) x z) : EffSorted L e z := by
  obtain ⟨d, n, hf, hr⟩ := h
  rcases hr with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, hz, hh⟩
  · cases x with
    | request => simp [EffectV.isRequest] at hown
    | command => exact hh.elim
    | query => exact hh.elim
  refine ⟨d, n, _, vals, hf, hz, .inl ⟨key.fields, ?_, ?_⟩⟩
  · rw [Layout.effectFields, List.getElem?_append_right (by simp)]
    simp [hk]
  · cases key with
    | command e' name c i j a =>
      cases x with
      | request => exact hh.elim
      | query => exact hh.elim
      | command name' c' i' j' caller value onAnswer =>
        obtain ⟨-, rfl, rfl, -, -, hΓ, vc, vi, va, rfl, hc, hi, hcap⟩ := hh
        exact ⟨sorted_of_relD _ _ _ hc, sorted_of_relD _ _ _ hi, hΓ ▸ sorted_capRel hcap, trivial⟩
    | query e' name c i o a =>
      cases x with
      | request => exact hh.elim
      | command => exact hh.elim
      | query name' c' i' o' caller value onAnswer =>
        obtain ⟨-, rfl, rfl, -, -, hΓ, vc, vi, va, rfl, hc, hi, hcap⟩ := hh
        exact ⟨sorted_of_relD _ _ _ hc, sorted_of_relD _ _ _ hi, hΓ ▸ sorted_capRel hcap, trivial⟩

/-- An own effect that some value codes is one a script can hold. -/
theorem effCoded_of_rel {e : Ty} {x : EffectV e} (hown : x.isRequest = false) {z : Val}
    (h : RelV L (.dsl .effect [e]) x z) : EffCoded L x :=
  ⟨z, h, effSorted_of_rel hown h⟩

end

section
variable {L : Layout} {M : Model} {T : List TypeDecl} {v : ServiceV}

/-- A pair question's encoding of its first step: where the codes hold and the effect's own step fits the slots, each
own effect the step queues is coded. -/
theorem pair_queued {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) {S : SymState v} {a0 : Step.Acc v} (hR : StateRel M L T (shapes v) S a0.state)
    {t1 t2 : Term} {x1 : EffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1 (t1.denote M))
    (hown1 : x1.isRequest = false) (hreach1 : x1.Reach P)
    {k1 k2 : Nat} (ht1 : Holds M (.is senv.dE ((L.effectsOf v.event).length + k1) t1))
    {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o) (hcodes : Holds M o.codes)
    (hfit : ownFits L.count T a0.state x1) :
    ∀ b, Step.runOwn T a0 x1 = .ok b → ∃ os, b.own = a0.own ++ os ∧ ∀ y ∈ os, ∃ z, RelV L (.dsl .effect [v.event]) y z := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨key1, hkey1, henc⟩ := bind_ok.1 henc
  obtain ⟨key2, -, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko1, a1⟩, c1, y1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcodes
  obtain ⟨hca, hy1, -, -, -⟩ := hcodes
  have hshs : ∀ sh ∈ shapes v, sh.InSites P := fun _ => shapes_inSites chk.reach
  obtain ⟨vals1, he1, hk1⟩ := own_key hown1 hx1 ht1 rfl (need_ok.1 hkey1)
  have hq0 : (Term.int 0).denote M = .int ((0 : Nat) : Int) := rfl
  have eA1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0
    hR.machines x1 hreach1 he1 hk1 h1 hy1
  obtain ⟨-, hA1⟩ := eA1.2 (eA1.1.2 hfit)
  intro b hb
  revert hA1
  cases ko1.fault? M with
  | some g => intro hA1; rw [hA1] at hb; cases hb
  | none =>
    intro hA1
    rw [hb] at hA1
    obtain ⟨-, -, -, -, -, os, hos, -, hrel⟩ := hA1.ends
    exact ⟨os, hos, ownRel_coded hrel⟩

end

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- What a pair line says of a waiting own effect's step from a state that fits the slots: where the bound question of
each listed pair is unsat, or its codes fit and the step fits, each own effect the step queues is coded. -/
theorem queued_at {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hrc : v.records.comparable = true) (hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true)
    {a0 : Step.Acc v} (hkeys : Step.KeysOk T a0.state) (hW : Within L (shapes v) a0.state)
    (hinv : Step.Inv P a0.state) (hsupp : Step.StateSupp a0.state) (hqk : Step.QueueOk P a0)
    {x : EffectV v.event} (hx : EffCoded L x) (hown : x.isRequest = false) (hreach : x.Reach P)
    (hcf : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L T P v senv p.1 p.2 = .ok (bq, tq) ∧
      (Unsat L (pairTys v) bq ∨ PairCodesFit L P v p.1 p.2 ∧ ownFits L.count T a0.state x)) :
    ∀ b, Step.runOwn T a0 x = .ok b → ∃ os, b.own = a0.own ++ os ∧ ∀ y ∈ os, ∃ z, RelV L (.dsl .effect [v.event]) y z := by
  obtain ⟨M, hM, hS, hx1, hx2⟩ := pair_model hkeys hW hx hx
  obtain ⟨p, hp, d, n, vals1, vals2, hd, hz1, hz2⟩ := ownPairs_complete hx1 hx2 hown hown
  obtain rfl := find_det hd senv.hE
  obtain ⟨bq, tq, hq, hor⟩ := hcf p hp
  have htest : ∀ (j : Nat) (vals : List Val) (i : Nat), M.vars i = .ctor senv.dE ((L.effectsOf v.event).length + j) vals →
      Holds M (.is senv.dE ((L.effectsOf v.event).length + j) (.var i)) := fun j vals i h => by
    simp [Holds, Term.denote, h, Val.toBool]
  have ht1 := htest _ _ _ hz1
  have ht2 := htest _ _ _ hz2
  obtain ⟨o, ho, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, hbl, hq⟩ := bind_ok.1 hq
  obtain ⟨names, hnames, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hR := decode_state hS
  have hfit : Holds M o.codes ∧ ownFits L.count T a0.state x := by
    rcases hor with hb | ⟨hpc, hof⟩
    · have hpre : ∀ a ∈ [wf, below, names, Term.is senv.dE ((L.effectsOf v.event).length + p.1) (.var (pairVar v)),
          .is senv.dE ((L.effectsOf v.event).length + p.2) (.var (pairVar v + 1))], Holds M a := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro a (rfl | rfl | rfl | rfl | rfl)
        · exact wf_of_decodeState (need_ok.1 hwf) hS
        · exact (pendingBelow_iff hR.pending hR.nextId hbl).2 hinv.below
        · exact stateSupp_names hR hsupp hrc hmc (need_ok.1 hnames)
        · exact ht1
        · exact ht2
      obtain ⟨a, ha, hna⟩ := hb.noModel M hM
      rcases List.mem_append.1 ha with ha | ha
      · exact (hna (hpre a ha)).elim
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only [holds_or, holds_not, not_or, Classical.not_not] at hna
      exact ⟨hna.1, ((pair_fits chk senv hR hinv hqk hx1 hx2 hown hown hreach hreach ht1 ht2 ho hna.1).1 hna.2).1⟩
    · exact ⟨(pair_codes ho).2 hpc, hof⟩
  exact pair_queued chk senv hR (t1 := .var (pairVar v)) hx1 hown hreach ht1 ho hfit.1 hfit.2

/-- A cascade's step keeps every waiting own effect coded where the pair lines speak for it (`queued_at`). -/
theorem coded_step {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hrc : v.records.comparable = true) (hmc : ∀ m ∈ v.machines, m.key.comparable = true ∧ m.state.comparable = true)
    {a : Step.Acc v} (hkeys : Step.KeysOk T a.state) (hW : Within L (shapes v) a.state) (hinv : Step.Inv P a.state)
    (hsupp : Step.Supp a) (hpend : Step.PendAt a.state.fresh a) (hqk : Step.QueueOk P a)
    (hc : ∀ x ∈ a.own, EffCoded L x) {i : Nat} (hi : i < a.own.length)
    (hcf : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L T P v senv p.1 p.2 = .ok (bq, tq) ∧
      (Unsat L (pairTys v) bq ∨ PairCodesFit L P v p.1 p.2 ∧ ownFits L.count T a.state a.own[i]))
    {d : Step.Acc v} (hd : Step.runOwn T { a with own := a.own.eraseIdx i } a.own[i] = .ok d) :
    ∀ y ∈ d.own, EffCoded L y := by
  have hmem : a.own[i] ∈ a.own := List.getElem_mem hi
  have hq' : Step.QueueOk P { a with own := a.own.eraseIdx i } := fun x hx => hqk x (Step.mem_eraseIdx hx)
  have hs : Step.StateSupp a.state := Step.StateSupp.of_supp hsupp hpend
  obtain ⟨os, hos, hcod⟩ := queued_at chk senv hrc hmc (a0 := { a with own := a.own.eraseIdx i }) hkeys hW hinv hs hq'
    (hc _ hmem) (hqk _ hmem).1 (hqk _ hmem).2 hcf d hd
  have hqd := Step.runOwn_queue T chk.reach { a with own := a.own.eraseIdx i } hinv hq' _ hd
  intro y hy
  have hy' := hy
  rw [hos] at hy'
  rcases List.mem_append.1 hy' with h | h
  · exact hc y (Step.mem_eraseIdx h)
  · obtain ⟨z, hz⟩ := hcod y h
    exact effCoded_of_rel (hqd y hy).1 hz

end

end Tazuna.Smt
