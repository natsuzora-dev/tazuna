import Tazuna.Smt.Pair
import Tazuna.Smt.Cover
import Tazuna.Smt.NoGap

/-! What a pair line's answers say of a state: the two effects of its kinds commute from every step in progress whose
state fits the slots and whose two effects some value codes (`pairs_at`). The state's values and the two effects'
make a model of the question's variables (`coverModel`), as for the step questions, so the per-model theorem
(`pair_sound`) applies. A line reads `Prove.proved` when both questions are unsat; `Prove.withinBounds` when only the
target question is, which says the same where the codes of the two kinds and of `apply` fit (`PairCodesFit`) and
every internal step the two orders run fits (`PairFits`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV}

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
  | .str, x, _, h => ⟨(x : Str).1, (x : Str).2, h⟩
  | .dsl .fresh _, x, _, h => ⟨_, h⟩
  | .id, x, _, ⟨d, n, hf, h⟩ => by
    subst h
    cases x with
    | fresh s i => exact ⟨d, n, hf, .inl ⟨s, i, rfl⟩⟩
    | named s => exact ⟨d, n, hf, .inr ⟨s.1, s.2, rfl⟩⟩
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
theorem effSorted_of_rel {e : Ty} {x : OwnEffectV e} {z : Val}
    (h : RelV L (.dsl .effect [e]) x.effect z) : EffSorted L e z := by
  obtain ⟨d, n, hf, hr⟩ := h
  rcases hr with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, hz, hh⟩
  · cases x <;> exact hh.elim
  refine ⟨d, n, _, vals, hf, hz, .inl ⟨key.fields, ?_, ?_⟩⟩
  · rw [Layout.effectFields, List.getElem?_append_right (by simp)]
    simp [hk]
  · cases key with
    | command e' name c i j a =>
      cases x with
      | query => exact hh.elim
      | command name' c' i' j' value onAnswer =>
        obtain ⟨-, rfl, rfl, -, -, hΓ, vi, va, rfl, hi, hcap⟩ := hh
        exact ⟨sorted_of_relD _ _ _ hi, hΓ ▸ sorted_capRel hcap, trivial⟩
    | query e' name c i o a =>
      cases x with
      | command => exact hh.elim
      | query name' c' i' o' value onAnswer =>
        obtain ⟨-, rfl, rfl, -, -, hΓ, vi, va, rfl, hi, hcap⟩ := hh
        exact ⟨sorted_of_relD _ _ _ hi, hΓ ▸ sorted_capRel hcap, trivial⟩

/-- An own effect some value codes is coded by one of its effect datatype's sort: its fields fixed (`fixV`), which
keeps them related. -/
theorem effFix (hL : SortedLayout L) {e : Ty} {x : OwnEffectV e} {z : Val} (h : RelV L (.dsl .effect [e]) x.effect z) :
    ∃ z', RelV L (.dsl .effect [e]) x.effect z' ∧
      ∀ dts σ, L.datatypes? = some dts → L.srt? (.dsl .effect [e]) = some σ → Val.InSrt dts σ z' := by
  obtain ⟨d, n, hf, hr⟩ := h
  rcases hr with ⟨k, key, vals, -, -, hh⟩ | ⟨k, key, vals, hk, -, hh⟩
  · cases x <;> exact hh.elim
  have hfs : (L.effectFields e)[(L.effectsOf e).length + k]? = some key.fields := by
    rw [Layout.effectFields, List.getElem?_append_right (by simp)]
    simp [hk]
  refine ⟨.ctor d ((L.effectsOf e).length + k) (fixVs L key.fields vals), ⟨d, n, hf, .inr ⟨k, key, _, hk, rfl, ?_⟩⟩,
    fun dts σ hd hs => ?_⟩
  · cases key with
    | command e' name c i j a =>
      cases x with
      | query => exact hh.elim
      | command name' c' i' j' value onAnswer =>
        obtain ⟨h1, h2, rfl, h4, h5, h6, vi, va, rfl, hi, dg, ng, valsg, hfg, rfl, hrs⟩ := hh
        refine ⟨h1, h2, rfl, h4, h5, h6, _, _, rfl, fixV_relD _ _ _ hi, dg, ng, _, hfg, ?_, fixVs_relDs _ _ _ hrs⟩
        simp [fixV, ← h6, hfg, Val.args]
    | query e' name c i o a =>
      cases x with
      | command => exact hh.elim
      | query name' c' i' o' value onAnswer =>
        obtain ⟨h1, h2, rfl, h4, h5, h6, vi, va, rfl, hi, dg, ng, valsg, hfg, rfl, hrs⟩ := hh
        refine ⟨h1, h2, rfl, h4, h5, h6, _, _, rfl, fixV_relD _ _ _ hi, dg, ng, _, hfg, ?_, fixVs_relDs _ _ _ hrs⟩
        simp [fixV, ← h6, hfg, Val.args]
  · obtain ⟨d', n', hf', rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    rw [hf] at hf'
    cases hf'
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    have hdata : Ty.isDatas key.fields = true := by
      simpa [Ty.isData] using (effectFields_sorted hL (List.mem_of_getElem? hfs)).2
    simp only [Layout.datatype?] at hD1
    split at hD1
    · rename_i hnil; rw [hnil] at hfs; simp at hfs
    · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hD1
      obtain ⟨fss, hfss, rfl⟩ := hD1
      have hss := mapM_getElem? hfss ((L.effectsOf e).length + k)
      rw [hfs, Option.bind_some] at hss
      have hsome : (key.fields.mapM L.srt?).isSome := by
        have := mapM_isSome (fun x => x.mapM L.srt?) (L.effectFields e)
        rw [hfss] at this
        exact List.all_eq_true.1 this.symm _ (List.mem_of_getElem? hfs)
      obtain ⟨ss, hss''⟩ := Option.isSome_iff_exists.1 hsome
      have hss' : fss[(L.effectsOf e).length + k]? = some ss := hss.trans hss''
      exact inSrt_ctor hD2 hss' (fixVs_inSrts hd key.fields hdata vals ss hss'')

/-- A model of a pair question's variables: the state's values, then the two effects'. -/
theorem pair_model (hL : SortedLayout L) {s : State v} (hkeys : Step.KeysOk T s) (hW : Within L (shapes v) s)
    {x1 x2 : OwnEffectV v.event}
    (he1 : ∃ z, RelV L (.dsl .effect [v.event]) x1.effect z) (he2 : ∃ z, RelV L (.dsl .effect [v.event]) x2.effect z) :
    ∃ M : Model, (∀ n (h : n < (pairTys v).length), VarSorted L (pairTys v)[n] (M.vars n)) ∧
      LayoutSorted L (pairTys v) M ∧
      (SymState.vars (v := v) 0).decode M L T (shapes v) = some s ∧
      RelV L (.dsl .effect [v.event]) x1.effect (M.vars (pairVar v)) ∧
      RelV L (.dsl .effect [v.event]) x2.effect (M.vars (pairVar v + 1)) := by
  obtain ⟨pv, hpv, hsome⟩ := hW
  obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨z1, hz1, hi1⟩ := effFix hL he1.choose_spec
  obtain ⟨z2, hz2, hi2⟩ := effFix hL he2.choose_spec
  have hs1 := effSorted_of_rel hz1
  have hs2 := effSorted_of_rel hz2
  have hsorted := embedState_sorted hvals
  have hsrt := embedState_srtVal hvals
  have hlen : vals.length = (stateTys v (shapes v)).length := (forall2_length hsorted).symm
  have hst : ∀ j (hj : j < vals.length), (coverModel L (vals ++ [z1, z2])).vars (0 + j) = vals[j] := fun j hj =>
    coverModel_vars (by rw [Nat.zero_add, List.getElem?_append_left hj, List.getElem?_eq_getElem hj])
  have hv1 : (coverModel L (vals ++ [z1, z2])).vars (pairVar v) = z1 :=
    coverModel_vars (by rw [pairVar, stateWidth, ← hlen, List.getElem?_append_right (Nat.le_refl _)]; simp)
  have hv2 : (coverModel L (vals ++ [z1, z2])).vars (pairVar v + 1) = z2 :=
    coverModel_vars (by rw [pairVar, stateWidth, ← hlen, List.getElem?_append_right (by omega)]; simp)
  have hpl : (pairTys v).length = (stateTys v (shapes v)).length + 2 := by simp [pairTys]
  have hLS : LayoutSorted L (pairTys v) (coverModel L (vals ++ [z1, z2])) := by
    refine layoutSorted_of (fun _ h => selSorted_coverModel L _ h) fun n t ht dts σ hD hs => ?_
    by_cases hlt : n < (stateTys v (shapes v)).length
    · have hget : (stateTys v (shapes v))[n]? = some t := by
        rw [← ht]; simp only [pairTys]; rw [List.getElem?_append_left hlt]
      obtain ⟨w, hw, hsw⟩ := forall2_getElem? hsrt hget
      rw [coverModel_vars (by rw [List.getElem?_append_left (hlen ▸ hlt), hw])]
      exact hsw (stateTys_data v t (List.mem_of_getElem? hget)) dts σ hD hs
    · have hn : n < (pairTys v).length := (List.getElem?_eq_some_iff.1 ht).1
      have ht' : t = .dsl .effect [v.event] := by
        simp only [pairTys] at ht
        rw [List.getElem?_append_right (by omega)] at ht
        have : n - (stateTys v (shapes v)).length < 2 := by omega
        rcases Nat.lt_succ_iff_lt_or_eq.1 this with h | h
        · simpa [show n - (stateTys v (shapes v)).length = 0 by omega] using ht.symm
        · simpa [h] using ht.symm
      subst ht'
      rcases Nat.lt_succ_iff_lt_or_eq.1 (show n < (stateTys v (shapes v)).length + 2 by omega) with h | h
      · have hn : n = pairVar v := by unfold pairVar stateWidth; omega
        rw [hn, hv1]; exact hi1 dts σ hD hs
      · have hn : n = pairVar v + 1 := by unfold pairVar stateWidth; omega
        rw [hn, hv2]; exact hi2 dts σ hD hs
  refine ⟨coverModel L (vals ++ [z1, z2]), fun n hn => ?_, hLS,
    decode_embedState 0 T s pv hpv (fun sm h => (hkeys sm h).2) vals hvals hst, by rw [hv1]; exact hz1, by rw [hv2]; exact hz2⟩
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
    · have hn : n = pairVar v := by unfold pairVar stateWidth; omega
      rw [hn, hv1]; exact hs1
    · have hn : n = pairVar v + 1 := by unfold pairVar stateWidth; omega
      rw [hn, hv2]; exact hs2

/-- What the pair lines say of a state, whichever verdict each reads: any two waiting own effects commute from every
step in progress whose state fits the slots, whose names are below its counter, whose pending requests and waiting
effects are the program's, and whose two effects some value codes, where every line reading within the bounds has the
two orders fit the slots. -/
theorem pairs_at {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hL : SortedLayout L)
    (senv : StepEnv L (shapes v))
    {a0 : Step.Acc v} {x1 x2 : OwnEffectV v.event}
    (hall : ∀ p ∈ L.ownPairs v.event, PairLine L T P v senv (PairFits L.count T a0 x1 x2) p)
    (hkeys : Step.KeysOk T a0.state) (hW : Within L (shapes v) a0.state)
    (hinv : Step.Inv P a0.state) (hsupp : Step.StateSupp a0.state) (hqk : Step.QueueOk P a0)
    (hsa : Step.Supp a0) (he1 : ∃ z, RelV L (.dsl .effect [v.event]) x1.effect z)
    (he2 : ∃ z, RelV L (.dsl .effect [v.event]) x2.effect z)
    (hreach1 : x1.effect.Reach P) (hreach2 : x2.effect.Reach P) :
    Step.PairCommutes T a0 x1 x2 := by
  obtain ⟨M, hM, hsel, hS, hx1, hx2⟩ := pair_model hL hkeys hW he1 he2
  obtain ⟨p, hp, ht1, ht2⟩ := pair_kinds senv hx1 hx2
  exact pair_sound chk hL senv (hall p hp) hM hsel hS hinv.below hsupp hqk hsa hx1 hx2 hreach1 hreach2 ht1 ht2

end

end Tazuna.Smt
