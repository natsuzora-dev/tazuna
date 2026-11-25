import Tazuna.Smt.Pair
import Tazuna.Smt.Cover

/-! What a pair line's answers say of a state: where a pair's questions are unsat, the two effects of its kinds
commute from every step in progress whose state fits the slots and whose two effects a script can hold. The state's
values and the two effects' make a model of the question's variables (`coverModel`), as for the step questions, so
the per-model theorems (`pairs_sound`, `pair_commutes`) apply. A line reads `Prove.proved` when both questions are
unsat (`pairs_at`); `Prove.withinBounds` when only the target question is, which says the same where the codes of the
two kinds and of `apply` fit (`PairCodesFit`) and every internal step the two orders run fits (`PairFits`,
`pairsWithin_at`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- An own effect a script can hold as a variable: a value of its event type's effect datatype that codes it. -/
def EffCoded (L : Layout) {e : Ty} (x : EffectV e) : Prop :=
  ∃ z, RelV L (.dsl .effect [e]) x z ∧ EffSorted L e z

/-- A model of a pair question's variables: the state's values, then the two effects'. -/
theorem pair_model {s : State v} (hkeys : Step.KeysOk T s) (hW : Within L (shapes v) s) {x1 x2 : EffectV v.event}
    (he1 : EffCoded L x1) (he2 : EffCoded L x2) :
    ∃ M : Model, (∀ n (h : n < (pairTys v).length), VarSorted L (pairTys v)[n] (M.vars n)) ∧
      (SymState.vars (v := v) 0).decode M L T (shapes v) = some s ∧
      RelV L (.dsl .effect [v.event]) x1 (M.vars (pairVar v)) ∧
      RelV L (.dsl .effect [v.event]) x2 (M.vars (pairVar v + 1)) := by
  obtain ⟨pv, hpv, hsome⟩ := hW
  obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨z1, hz1, hs1⟩ := he1
  obtain ⟨z2, hz2, hs2⟩ := he2
  have hsorted := embedState_sorted hvals
  have hlen : vals.length = (stateTys v (shapes v)).length := (forall2_length hsorted).symm
  have hst : ∀ j (hj : j < vals.length), (coverModel (vals ++ [z1, z2])).vars (0 + j) = vals[j] := fun j hj =>
    coverModel_vars (by rw [Nat.zero_add, List.getElem?_append_left hj, List.getElem?_eq_getElem hj])
  have hv1 : (coverModel (vals ++ [z1, z2])).vars (pairVar v) = z1 :=
    coverModel_vars (by rw [pairVar, ← hlen, List.getElem?_append_right (Nat.le_refl _)]; simp)
  have hv2 : (coverModel (vals ++ [z1, z2])).vars (pairVar v + 1) = z2 :=
    coverModel_vars (by rw [pairVar, ← hlen, List.getElem?_append_right (by omega)]; simp)
  refine ⟨coverModel (vals ++ [z1, z2]), fun n hn => ?_,
    decode_embedState 0 T s pv hpv (fun sm h => (hkeys sm h).2) vals hvals hst, by rw [hv1]; exact hz1, by rw [hv2]; exact hz2⟩
  have hpl : (pairTys v).length = (stateTys v (shapes v)).length + 2 := by simp [pairTys]
  by_cases hlt : n < (stateTys v (shapes v)).length
  · have hget : (pairTys v)[n] = (stateTys v (shapes v))[n] := List.getElem_append_left hlt
    obtain ⟨w, hw, hsw⟩ := forall2_getElem? hsorted (List.getElem?_eq_getElem hlt)
    rw [hget, coverModel_vars (by rw [List.getElem?_append_left (hlen ▸ hlt), hw])]
    exact varSorted_of_sorted hsw
  · have hget : (pairTys v)[n] = .dsl .effect [v.event] := by
      simp only [pairTys]
      rw [List.getElem_append_right (by omega)]
      have : n - (stateTys v (shapes v)).length < 2 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
      · simp [show n - (stateTys v (shapes v)).length = 0 by omega]
      · simp [h]
    rw [hget]
    simp only [VarSorted]
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show n < (stateTys v (shapes v)).length + 2 by omega) with h | h
    · have hn : n = pairVar v := by unfold pairVar; omega
      rw [hn, hv1]; exact hs1
    · have hn : n = pairVar v + 1 := by unfold pairVar; omega
      rw [hn, hv2]; exact hs2

/-- What a pair line reading `Prove.proved` says of a state: where every listed pair of own kinds has both questions
unsat, any two waiting own effects commute from every step in progress whose state fits the slots, whose names are
below its counter, whose pending requests and waiting effects are the program's, and whose two effects a script can
hold. -/
theorem pairs_at {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hall : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L T P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) bq ∧ Unsat L (pairTys v) tq)
    {a0 : Step.Acc v} (hkeys : Step.KeysOk T a0.state) (hW : Within L (shapes v) a0.state)
    (hinv : Step.Inv P a0.state) (hsupp : Step.StateSupp a0.state) (hqk : Step.QueueOk P a0)
    (hsa : Step.SelfAt a0.state.fresh a0) {x1 x2 : EffectV v.event} (he1 : EffCoded L x1) (he2 : EffCoded L x2)
    (hown1 : x1.isRequest = false) (hown2 : x2.isRequest = false) (hreach1 : x1.Reach P) (hreach2 : x2.Reach P) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨M, hM, hS, hx1, hx2⟩ := pair_model hkeys hW he1 he2
  exact pairs_sound (M := M) chk senv hall hM hS hinv.below hsupp rfl hqk hsa hx1 hx2 hown1 hown2 hreach1
    hreach2

/-- What a pair question's codes condition says: `apply` fits, and so do the functions of each of the two own kinds
the question names. -/
def PairCodesFit (L : Layout) (P : List AnySite) (v : ServiceV) (k1 k2 : Nat) : Prop :=
  (v.apply.fits L.count).1 ∧ ∀ k ∈ [k1, k2], ∀ key, (L.ownsOf v.event)[k]? = some key → (ownShape v P key).CodesFit L.count

theorem pair_codes {M : Model} {P : List AnySite} {senv : StepEnv L (shapes v)} {S : SymState v} {t1 t2 : Term}
    {k1 k2 : Nat} {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o) :
    Holds M o.codes ↔ PairCodesFit L P v k1 k2 := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨key1, hkey1, henc⟩ := bind_ok.1 henc
  obtain ⟨key2, hkey2, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨_, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hk1 := need_ok.1 hkey1
  have hk2 := need_ok.1 hkey2
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    (v.apply.code_exact (M := M) happ).1, ownKind_codes h1, ownKind_codes h2, ownKind_codes h3, ownKind_codes h4,
    PairCodesFit, hk1, hk2, Option.some.injEq, forall_eq']
  exact ⟨fun ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c, c, b⟩⟩

/-- What a pair line reading `Prove.withinBounds` says of a state: where every listed pair of own kinds has its target
question unsat and its codes fit, two waiting own effects commute from every step in progress `pairs_at` speaks of
where every internal step the two orders run fits the slots. -/
theorem pairsWithin_at {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v))
    (hall : ∀ p ∈ L.ownPairs v.event, ∃ bq tq, pairQuestions L T P v senv p.1 p.2 = .ok (bq, tq) ∧
      Unsat L (pairTys v) tq ∧ PairCodesFit L P v p.1 p.2)
    {a0 : Step.Acc v} (hkeys : Step.KeysOk T a0.state) (hW : Within L (shapes v) a0.state)
    (hinv : Step.Inv P a0.state) (hsupp : Step.StateSupp a0.state) (hqk : Step.QueueOk P a0)
    (hsa : Step.SelfAt a0.state.fresh a0) {x1 x2 : EffectV v.event} (he1 : EffCoded L x1) (he2 : EffCoded L x2)
    (hown1 : x1.isRequest = false) (hown2 : x2.isRequest = false) (hreach1 : x1.Reach P) (hreach2 : x2.Reach P)
    (hfit : PairFits L.count T a0 x1 x2) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨M, hM, hS, hx1, hx2⟩ := pair_model hkeys hW he1 he2
  obtain ⟨p, hp, d, n, vals1, vals2, hd, hz1, hz2⟩ := ownPairs_complete hx1 hx2 hown1 hown2
  obtain rfl := find_det hd senv.hE
  obtain ⟨bq, tq, hq, ht, hcf⟩ := hall p hp
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
  have hinv' := decode_inv chk.reach hS hinv.below
  have hcodes : Holds M o.codes := (pair_codes ho).2 hcf
  have hcond : Holds M o.cond := (pair_fits chk senv hR hinv' hqk hx1 hx2 hown1 hown2 hreach1 hreach2 ht1 ht2 ho
    hcodes).2 hfit
  have hpre : ∀ a ∈ [wf, below, names, Term.is senv.dE ((L.effectsOf v.event).length + p.1) (.var (pairVar v)),
      .is senv.dE ((L.effectsOf v.event).length + p.2) (.var (pairVar v + 1))], Holds M a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl | rfl | rfl | rfl)
    · exact wf_of_decodeState (need_ok.1 hwf) hS
    · exact (pendingBelow_iff hR.pending hR.nextId hbl).2 hinv.below
    · exact stateSupp_names hR hsupp chk.recordsComparable chk.machinesComparable (need_ok.1 hnames)
    · exact ht1
    · exact ht2
  obtain ⟨a, ha, hna⟩ := ht.noModel M hM
  rcases List.mem_append.1 ha with ha | ha
  · exact (hna (hpre a ha)).elim
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact (hna hcodes).elim
  · exact (hna hcond).elim
  exact pair_commutes chk senv hR hinv' hqk hsa (t1 := .var (pairVar v)) (t2 := .var (pairVar v + 1)) hx1
    hx2 hown1 hown2 hreach1 hreach2 ht1 ht2 ho hcodes hcond hna

end

end Tazuna.Smt
