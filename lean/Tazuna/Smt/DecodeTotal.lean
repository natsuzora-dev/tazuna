import Tazuna.Smt.Sorts
import Tazuna.Smt.Unroll

/-! Decoding never fails on a model the solver may give: for every question family whose models `prove` reads
back (an input kind's step and bound questions, a timer machine's, a pair of own kinds'), and for the unrolled run
generate reads (`unroll_inputs_decode`), every model whose variables
hold values of their sorts and that satisfies the family's context decodes. The context asserts the well-formedness
of each value it reads (`SymState.wf`, `SymInput.wf`, `wfT`, `ownWf`), and for values of the right sort
well-formedness is exactly decoding (`wf_iff`). So the CLI's "does not decode" lines are unreachable while the solver
answers as SMT-LIB says. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {M : Model} {L : Layout}

theorem decode_of_wf {t : Ty} {x c : Term} (hc : wfT L t x = some c) (hs : Sorted L t (x.denote M))
    (h : Holds M c) : ∃ y, decodeV L t (x.denote M) = some y :=
  Option.isSome_iff_exists.1 ((wf_iff t x c hc hs).1 h)

/-- A data type's variable holds a value of its sort as `Sorted` reads it: only an effect type's is read otherwise,
and an effect type is no data. -/
theorem sorted_of_varSorted {t : Ty} {w : Val} (ht : t.isData = true) (h : VarSorted L t w) : Sorted L t w := by
  unfold VarSorted at h
  split at h
  · simp [Ty.isData] at ht
  · exact h

theorem sorted_append_left {A B : List Ty} (hM : ∀ n (h : n < (A ++ B).length), VarSorted L (A ++ B)[n] (M.vars n))
    (hA : ∀ t ∈ A, t.isData = true) : ∀ n (h : n < A.length), Sorted L A[n] (M.vars (0 + n)) := by
  intro n h
  have hs := hM n (by simp; omega)
  rw [List.getElem_append_left h] at hs
  rw [Nat.zero_add]
  exact sorted_of_varSorted (hA _ (List.getElem_mem h)) hs

theorem sorted_append_right {A B : List Ty} (hM : ∀ n (h : n < (A ++ B).length), VarSorted L (A ++ B)[n] (M.vars n))
    (hB : ∀ t ∈ B, t.isData = true) : ∀ n (h : n < B.length), Sorted L B[n] (M.vars (A.length + n)) := by
  intro n h
  have hs := hM (A.length + n) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at hs
  simp only [Nat.add_sub_cancel_left] at hs
  exact sorted_of_varSorted (hB _ (List.getElem_mem h)) hs

/-- Constants from `v<b>` on whose values have the types' sorts, as terms. -/
theorem forall2_vars : (tys : List Ty) → (b : Nat) → (∀ n (h : n < tys.length), Sorted L tys[n] (M.vars (b + n))) →
    Forall2 (fun t x => Sorted L t (Term.denote M x)) tys ((List.range tys.length).map fun i => .var (b + i))
  | [], _, _ => trivial
  | t :: ts, b, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    refine ⟨by simpa [Term.denote] using h0, ?_⟩
    have := forall2_vars ts (b + 1) fun n hn => by
      have := h (n + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 n] using this
    simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm 1] using this

theorem machinesSorted_vars {v : ServiceV} : (ms : List (MachineV v.records v.event)) → (k : Nat) →
    (∀ i (h : i < ms.length), Sorted L ms[i].table (M.vars (k + i))) → MachinesSorted M L ms (machineVars ms k)
  | [], _, _ => trivial
  | m :: ms, k, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    refine ⟨by simpa [Term.denote] using h0, machinesSorted_vars ms (k + 1) fun i hi => ?_⟩
    have := h (i + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- A state whose constants from `v<b>` on hold values of their sorts and satisfy the state's well-formedness
decodes. -/
theorem vars_decode (b : Nat) (T : List TypeDecl) {v : ServiceV} (shs : List (PendingShape v.event)) {c : Term}
    (hw : (SymState.vars (v := v) b).wf L shs = some c) (hH : Holds M c)
    (hs : ∀ n (h : n < (stateTys v shs).length), Sorted L (stateTys v shs)[n] (M.vars (b + n))) :
    ∃ s, (SymState.vars (v := v) b).decode M L T shs = some s := by
  have h0 := hs 0 (by simp [stateTys])
  have h1 := hs 1 (by simp [stateTys])
  have h2 := hs 2 (by simp [stateTys])
  have h3 := hs 3 (by simp [stateTys])
  have h4 := hs 4 (by simp [stateTys])
  have hm : ∀ i (h : i < v.machines.length), Sorted L v.machines[i].table (M.vars (b + 5 + i)) := fun i h => by
    have := hs (5 + i) (by simp [stateTys]; omega)
    simp only [stateTys] at this
    rw [List.getElem_append_right (by simp)] at this
    simpa [Nat.add_assoc] using this
  simp only [stateTys] at h0 h1 h2 h3 h4
  rw [List.getElem_append_left (by simp)] at h0 h1 h2 h3 h4
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero, Sorted] at h0 h1 h2 h3 h4
  exact Option.isSome_iff_exists.1 ((wf_decode (T := T) hw (by simpa [SymState.vars, Term.denote] using h0)
    (by simpa [PendingSorted, SymState.vars, Term.denote] using h4)
    (machinesSorted_vars v.machines (b + 5) hm) (by simpa [SymState.vars, Term.denote] using h1)
    (by simpa [SymState.vars, Term.denote] using h2) (by simpa [SymState.vars, Term.denote] using h3)).1 hH)

/-- An input whose terms hold values of their types' sorts and satisfy the input's well-formedness decodes, where
its types are data. -/
theorem SymInput.decode_total {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}
    (hc : v.caller.isData = true) {inp : SymInput v shs n} (hin : ∀ t ∈ inp.tys, t.isData = true) {c : Term}
    (hw : inp.wf L = some c) (hH : Holds M c) (hs : Forall2 (fun t x => Sorted L t (Term.denote M x)) inp.tys inp.terms) :
    ∃ x, inp.decode M L hc = some x := by
  have answer : ∀ {t : Ty} {to value : Term}, t.isData = true → (wfT L t value).map (andT (.le (.int 0) to)) = some c →
      Sorted L .int (to.denote M) → Sorted L t (value.denote M) → ∃ x : Input v, decodeAnswer M L t to value = some x := by
    intro t to value ht hw hto hv
    obtain ⟨cv, hcv, rfl⟩ := map_some.1 hw
    rw [holds_andT] at hH
    obtain ⟨y, hy⟩ := decode_of_wf hcv hv hH.2
    obtain ⟨k, hk⟩ := hto
    have h0 : 0 ≤ k := by simpa [Holds, Term.denote, hk, Val.toBool, Val.toInt] using hH.1
    exact Option.isSome_iff_exists.1 (by simp [decodeAnswer, ht, natOf, hk, h0, hy])
  cases inp with
  | command i caller input | query i caller input =>
    obtain ⟨c1, hc1, hw⟩ := bind_some.1 hw
    obtain ⟨c2, hc2, rfl⟩ := map_some.1 hw
    rw [holds_andT] at hH
    obtain ⟨y1, h1⟩ := decode_of_wf hc1 hs.1 hH.1
    obtain ⟨y2, h2⟩ := decode_of_wf hc2 hs.2.1 hH.2
    simp only [List.get_eq_getElem] at h2
    exact Option.isSome_iff_exists.1 (by simp [SymInput.decode, h1, h2])
  | answer k j to value => exact answer (hin _ (by simp [SymInput.tys])) hw hs.1 hs.2.1
  | unmatched t to value => exact answer (hin _ (by simp [SymInput.tys])) hw hs.1 hs.2.1
  | event i value =>
    obtain ⟨y, h⟩ := decode_of_wf hw hs.1 hH
    simp only [List.get_eq_getElem] at h
    exact Option.isSome_iff_exists.1 (by simp [SymInput.decode, h])
  | clock time =>
    obtain ⟨k, hk⟩ := hs.1
    exact Option.isSome_iff_exists.1 (by simp [SymInput.decode, hk, intOf])

end

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n b : Nat}

theorem stepInputs_terms {inp : SymInput v shs n} (h : inp ∈ stepInputs v shs n b) :
    inp.terms = (List.range inp.tys.length).map fun i => .var (b + i) := by
  simp only [stepInputs, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with ((⟨i, -, rfl⟩ | ⟨k, -, j, -, rfl⟩) | ⟨i, -, rfl⟩) | rfl <;> rfl


end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV}

/-- An input kind's step and bound questions never yield a model that does not decode: a model of their context
whose variables hold values of their sorts decodes to a state and an input. -/
theorem questions_decode (senv : StepEnv L (shapes v)) {inp : SymInput v (shapes v) senv.nT}
    (hmem : inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v)) (hc : v.caller.isData = true) {gs : List Target}
    {qs : List (Question v (shapes v) senv.nT)} (hq : questions L T P v senv inp = .ok (gs, qs))
    {q : Question v (shapes v) senv.nT} (hqm : q ∈ qs)
    (hM : ∀ n (h : n < q.ask.tys.length), VarSorted L q.ask.tys[n] (M.vars n)) (hctx : ∀ a ∈ q.ask.context, Holds M a) :
    ∃ s x, (SymState.vars (v := v) 0).decode M L T (shapes v) = some s ∧ inp.decode M L hc = some x := by
  have htys := questions_tys L T P v senv hq q hqm
  rw [htys] at hM
  have hin := stepInputs_data hc hmem
  have hst := sorted_append_left hM (stateTys_data v)
  have hip := sorted_append_right hM hin
  obtain ⟨t, -, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨iwf, hiwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hcx : q.ask.context = [wf, iwf, below, t.out.case] := by
    rcases List.mem_cons.1 hqm with rfl | hqm
    · rfl
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 hqm; rfl
  rw [hcx] at hctx
  obtain ⟨s, hs⟩ := vars_decode 0 T (shapes v) (need_ok.1 hwf) (hctx wf (by simp)) hst
  have hterms := stepInputs_terms hmem
  have hw := SymInput.decode_total hc hin (need_ok.1 hiwf) (hctx iwf (by simp))
    (hterms ▸ forall2_vars inp.tys (stateTys v (shapes v)).length hip)
  obtain ⟨x, hx⟩ := hw
  exact ⟨s, x, hs, hx⟩

/-- A timer machine's questions never yield a model that does not decode: a model of their context whose variables
hold values of their sorts gives an instance context. -/
theorem timer_decode {r e : Ty} {m : MachineV r e} {bq tq : TypedScript} (hq : timerQuestions L m = .ok (bq, tq))
    {q : TypedScript} (hqm : q = bq ∨ q = tq) (hM : ∀ n (h : n < q.tys.length), VarSorted L q.tys[n] (M.vars n))
    (hctx : ∀ a ∈ q.context, Holds M a) : ∃ x, TimerVals.decode L m M = some x := by
  simp only [timerQuestions] at hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨wfs, hwfs, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have htys : q.tys = timerTys m := by rcases hqm with rfl | rfl <;> rfl
  have hcx : q.context = wfs := by rcases hqm with rfl | rfl <;> rfl
  rw [hcx] at hctx
  rw [htys] at hM
  have hF := mapM_ok _ _ _ hwfs
  have hdata : ∀ t ∈ timerTys m, t.isData = true := by
    simp only [timerTys, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl | rfl)
    · exact m.key_data
    · exact m.state_data
    · exact m.records_data
    · rfl
  have hs := sorted_append_left (B := []) (by simpa using hM) hdata
  have hat : ∀ i (h : i < (timerTys m).length), ∃ y, decodeV L (timerTys m)[i] (M.vars i) = some y := by
    intro i h
    obtain ⟨w, hw, hR⟩ := forall2_getElem? hF (i := i) (a := ((timerTys m)[i], i))
      (by simp [h])
    have := decode_of_wf (M := M) (need_ok.1 hR) (by simpa [Term.denote] using hs i h)
      (hctx w (List.mem_of_getElem? hw))
    simpa [Term.denote] using this
  obtain ⟨k, hk⟩ := hat 0 (by simp [timerTys])
  obtain ⟨st, hst⟩ := hat 1 (by simp [timerTys])
  obtain ⟨rc, hrc⟩ := hat 2 (by simp [timerTys])
  obtain ⟨now, hnow⟩ := hs 3 (by simp [timerTys])
  simp only [timerTys] at hk hst hrc hnow
  unfold TimerVals.decode
  split
  · exact ⟨_, rfl⟩
  · rename_i hne
    exact (hne _ _ _ _ hk hst hrc hnow).elim

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV}

theorem sortedVs_getElem? : {ts : List Ty} → {ws : List Val} → SortedVs L ts ws → {j : Nat} → {t : Ty} →
    ts[j]? = some t → ∃ w, ws[j]? = some w ∧ Sorted L t w
  | [], [], _, _, _, h => by cases h
  | _ :: _, _ :: _, ⟨hs, _⟩, 0, _, h => by cases h; exact ⟨_, rfl, hs⟩
  | _ :: _, _ :: _, ⟨_, hs⟩, j + 1, _, h => sortedVs_getElem? hs (j := j) (by simpa using h)
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

theorem readData_some {t : Ty} {z : Val} (ht : t.isData = true) {y : t.den} (h : decodeV L t z = some y) :
    ∃ x, readData L t z = some x := ⟨Ty.down t ht y, by simp [readData, ht, h]⟩

theorem isDatas_mem : {ts : List Ty} → Ty.isDatas ts = true → ∀ t ∈ ts, t.isData = true
  | [], _, _, h => by cases h
  | _ :: _, h, _, hm => by
    simp only [Ty.isDatas, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1
    · exact isDatas_mem h.2 _ hm


/-- A model's effect of a kind the program builds, of its sort, at the kind's variant, with well-formed fields,
decodes. -/
theorem decodeOwn_total (hL : SortedLayout L) {d n : Nat} (hE : L.find? (.dsl .effect [v.event]) = some (d, n))
    {k : OwnPlace L v.event} {i : Nat} (hz : EffSorted L v.event (M.vars i))
    (ht : Holds M (.is d (L.ownCtor v.event k) (.var i))) {c : Term} (hw : ownWf L v.event d k (.var i) = some c)
    (hH : Holds M c) (hf : ownFound P L v.event k = true) : ∃ x, decodeOwn L P v k (M.vars i) = some x := by
  obtain ⟨d', n', kc, vals, hE', hzv, hfs⟩ := hz
  rw [hE] at hE'
  cases hE'
  have hkc : kc = L.ownCtor v.event k := by simpa [Holds, Term.denote, hzv, Val.toBool] using ht
  subst hkc
  have hfsk : (L.effectFields v.event)[L.ownCtor v.event k]? = some (L.ownsOf v.event)[k].fields := by
    simp [Layout.effectFields, Layout.ownCtor]
  have hsv : SortedVs L (L.ownsOf v.event)[k].fields vals := by
    rcases hfs with ⟨fs, hfs', hs⟩ | ⟨he, -, -⟩
    · rw [hfsk] at hfs'; cases hfs'; exact hs
    · rw [he] at hfsk; cases hfsk
  have hdata : (Ty.tuple (L.ownsOf v.event)[k].fields).isData = true :=
    (hL.owns _ (List.mem_filter.1 (List.getElem_mem k.isLt)).1).2
  unfold ownWf at hw
  obtain ⟨cs, hcs, rfl⟩ := map_some.1 hw
  rw [holds_allT] at hH
  have hF := forall2_flip (mapM_forall2 (E := fun c q => wfT L q.1 (.sel d (L.ownCtor v.event k) q.2 (.var i)) = some c)
    (fun _ _ h => h) _ _ hcs)
  have hdec : ∀ (j : Nat) (t : Ty), (L.ownsOf v.event)[k].fields[j]? = some t → ∃ z, vals[j]? = some z ∧ ∃ x, readData L t z = some x := by
    intro j t hj
    obtain ⟨cj, hcj, hwj⟩ := forall2_getElem? hF (i := j) (a := (t, j)) (by simp [List.getElem?_zipIdx]; simpa using hj)
    obtain ⟨z, hzj, hs⟩ := sortedVs_getElem? hsv hj
    have hden : (Term.sel d (L.ownCtor v.event k) j (.var i)).denote M = z := by
      simp [Term.denote, hzv, hzj]
    obtain ⟨y, hy⟩ := decode_of_wf (M := M) hwj (hden ▸ hs) (hH cj (List.mem_of_getElem? hcj))
    have htd : t.isData = true := by
      exact isDatas_mem (by simpa [Ty.isData] using hdata) t (List.mem_of_getElem? hj)
    exact ⟨z, hzj, readData_some htd (hden ▸ hy)⟩
  unfold ownFound at hf
  unfold decodeOwn
  rw [hzv]
  simp only [ne_eq, not_true_eq_false, ite_false]
  generalize (L.ownsOf v.event)[k] = key at hf hdec hsv
  cases key with
  | command e name c j rj a =>
    obtain ⟨⟨Γ, site⟩, hs⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨-, -, rfl⟩ := siteFor_spec hs
    match vals, hsv with
    | [vc, vi, va], _ =>
      obtain ⟨_, h0, x0, hx0⟩ := hdec 0 c rfl
      obtain ⟨_, h1, x1, hx1⟩ := hdec 1 j rfl
      obtain ⟨_, h2, x2, hx2⟩ := hdec 2 (.tuple a.Γ) rfl
      cases h0; cases h1; cases h2
      simp only [OwnKey.answerFn, OwnKey.answer] at hs
      exact ⟨_, by simp [hs, hx0, hx1, hx2]; rfl⟩
  | query e name c j o a =>
    obtain ⟨⟨Γ, site⟩, hs⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨-, -, rfl⟩ := siteFor_spec hs
    match vals, hsv with
    | [vc, vi, va], _ =>
      obtain ⟨_, h0, x0, hx0⟩ := hdec 0 c rfl
      obtain ⟨_, h1, x1, hx1⟩ := hdec 1 j rfl
      obtain ⟨_, h2, x2, hx2⟩ := hdec 2 (.tuple a.Γ) rfl
      cases h0; cases h1; cases h2
      simp only [OwnKey.answerFn, OwnKey.answer] at hs
      exact ⟨_, by simp [hs, hx0, hx1, hx2]; rfl⟩


/-- A pair of own kinds' questions never yield a model that does not decode: a model of their context whose variables
hold values of their sorts decodes to a state and two own effects. -/
theorem pair_decode (hL : SortedLayout L) (senv : StepEnv L (shapes v)) {k1 k2 : OwnPlace L v.event}
    {bq tq : TypedScript} (hq : pairQuestions L T P v senv k1 k2 = .ok (bq, tq)) {q : TypedScript} (hqm : q = bq ∨ q = tq)
    (hM : ∀ n (h : n < q.tys.length), VarSorted L q.tys[n] (M.vars n)) (hctx : ∀ a ∈ q.context, Holds M a) :
    ∃ s e1 e2, (SymState.vars (v := v) 0).decode M L T (shapes v) = some s ∧
      decodeOwn L P v k1 (M.vars (pairVar v)) = some e1 ∧ decodeOwn L P v k2 (M.vars (pairVar v + 1)) = some e2 := by
  obtain ⟨o, -, hq⟩ := bind_ok.1 hq
  obtain ⟨wf, hwf, hq⟩ := bind_ok.1 hq
  obtain ⟨below, -, hq⟩ := bind_ok.1 hq
  obtain ⟨names, -, hq⟩ := bind_ok.1 hq
  obtain ⟨w1, hw1, hq⟩ := bind_ok.1 hq
  obtain ⟨w2, hw2, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have htys : q.tys = pairTys v := by rcases hqm with rfl | rfl <;> rfl
  have hcx : q.context = [wf, below, names] ++ [Term.is senv.dE (L.ownCtor v.event k1) (.var (pairVar v)),
      .is senv.dE (L.ownCtor v.event k2) (.var (pairVar v + 1))] ++ [w1, w2] ++
      (if ownFound P L v.event k1 && ownFound P L v.event k2 then [] else [Term.bool false]) := by
    rcases hqm with rfl | rfl <;> rfl
  rw [hcx] at hctx
  rw [htys] at hM
  have hfound : ownFound P L v.event k1 = true ∧ ownFound P L v.event k2 = true := by
    have hfalse : ¬ Holds M (.bool false) := by simp [Holds, Term.denote, Val.toBool]
    cases h1 : ownFound P L v.event k1 <;> cases h2 : ownFound P L v.event k2 <;>
      first | exact ⟨rfl, rfl⟩ | exact (hfalse (hctx (.bool false) (List.mem_append_right _ (by simp [h1, h2])))).elim
  have hst := sorted_append_left hM (stateTys_data v)
  obtain ⟨s, hs⟩ := vars_decode 0 T (shapes v) (need_ok.1 hwf) (hctx wf (by simp)) hst
  have heff : ∀ j (hj : j < 2), EffSorted L v.event (M.vars (pairVar v + j)) := by
    intro j hj
    have := hM (pairVar v + j) (by simp [pairTys, pairVar, stateWidth]; omega)
    simp only [pairTys, pairVar, stateWidth] at this ⊢
    rw [List.getElem_append_right (by omega)] at this
    have e : (stateTys v (shapes v)).length + j - (stateTys v (shapes v)).length = j := by omega
    simp only [e] at this
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · obtain rfl : j = 0 := by omega
      simpa [VarSorted] using this
    · simpa [VarSorted] using this
  obtain ⟨e1, he1⟩ := decodeOwn_total hL senv.hE (by simpa using heff 0 (by omega)) (hctx _ (by simp))
    (need_ok.1 hw1) (hctx w1 (by simp)) hfound.1
  obtain ⟨e2, he2⟩ := decodeOwn_total hL senv.hE (heff 1 (by omega)) (hctx _ (by simp))
    (need_ok.1 hw2) (hctx w2 (by simp)) hfound.2
  exact ⟨s, e1, e2, hs, he1, he2⟩

end


section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- Each kind of an unrolled step takes as many constants as its types, its terms from the constant it is placed at,
and data types. -/
theorem unrollKinds_shape (hc : v.caller.isData = true) {ans : Bool} {p : Nat × (Nat → SymInput v shs n)}
    (hp : p ∈ unrollKinds v shs n ans) (c : Nat) :
    (p.2 c).tys.length = p.1 ∧ (p.2 c).terms = (List.range p.1).map (fun i => .var (c + i)) ∧
      ∀ t ∈ (p.2 c).tys, t.isData = true := by
  simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hp) | ⟨i, -, rfl⟩) | rfl
  · refine ⟨rfl, rfl, ?_⟩
    simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl)
    · exact hc
    · exact CommandV.input_data _
  · refine ⟨rfl, rfl, ?_⟩
    simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl)
    · exact hc
    · exact QueryV.input_data _
  · split at hp
    · simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨k, hk, j, -, rfl⟩ := hp
      refine ⟨rfl, rfl, ?_⟩
      simp only [answerShapes, List.mem_filter] at hk
      simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false]
      rintro t (rfl | rfl)
      · rfl
      · exact hk.2
    · cases hp
  · refine ⟨rfl, rfl, ?_⟩
    simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false]
    rintro t rfl; exact SubscriptionV.event_data _
  · refine ⟨rfl, rfl, ?_⟩
    simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false]
    rintro t rfl; rfl

/-- Placing kinds takes the constants their types list, in order: each placed input's terms are the constants at its
place in that list, and the constant after the last is past them all. -/
theorem placeKinds_at : (ks : List (Nat × (Nat → SymInput v shs n))) → (b : Nat) →
    (∀ p ∈ ks, ∀ c, (p.2 c).tys.length = p.1 ∧ (p.2 c).terms = (List.range p.1).map (fun i => .var (c + i))) →
    (placeKinds ks b).2 = b + ((placeKinds ks b).1.flatMap SymInput.tys).length ∧
    ∀ x ∈ (placeKinds ks b).1, (∃ p ∈ ks, ∃ c, x = p.2 c) ∧ ∃ j,
      x.terms = (List.range x.tys.length).map (fun i => .var (b + j + i)) ∧
      ∀ i (h : i < x.tys.length), ((placeKinds ks b).1.flatMap SymInput.tys)[j + i]? = some x.tys[i]
  | [], b, _ => ⟨rfl, fun _ h => by cases h⟩
  | (w, f) :: ks, b, hk => by
    have hf := hk (w, f) (by simp) b
    obtain ⟨he, hx⟩ := placeKinds_at ks (b + w) fun p hp => hk p (by simp [hp])
    simp only [placeKinds, List.flatMap_cons, List.length_append, List.mem_cons] at he hx ⊢
    refine ⟨by rw [he, hf.1]; omega, fun x hm => ?_⟩
    rcases hm with rfl | hm
    · refine ⟨⟨(w, f), by simp, b, rfl⟩, 0, by rw [hf.2, hf.1]; simp, fun i h => ?_⟩
      rw [Nat.zero_add, List.getElem?_append_left h]
      exact List.getElem?_eq_getElem h
    · obtain ⟨⟨p, hp, c, rfl⟩, j, ht, hi⟩ := hx _ hm
      refine ⟨⟨p, by simp [hp], c, rfl⟩, w + j, by rw [ht]; simp [Nat.add_assoc], fun i h => ?_⟩
      rw [List.getElem?_append_right (by rw [hf.1]; omega), hf.1, show w + j + i - w = j + i by omega]
      exact hi i h

end


section
variable {M : Model} {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV} (senv : StepEnv L (shapes v))

theorem unrollKinds_terms {ans : Bool} :
    ∀ p ∈ unrollKinds v (shapes v) senv.nT ans, ∀ c, (p.2 c).tys.length = p.1 ∧
      (p.2 c).terms = (List.range p.1).map (fun i => .var (c + i)) := by
  intro p hp c
  simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hp) | ⟨i, -, rfl⟩) | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split at hp
    · simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨k, -, j, -, rfl⟩ := hp
      exact ⟨rfl, rfl⟩
    · cases hp
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- An unrolled step's constants: its selector, then its kinds' terms, so the next step starts past them. -/
theorem unrollOne_next (S : SymState v) (i b : Nat) :
    (unrollOne L T P v senv S i b).2.2.2.2 = b + (unrollOne L T P v senv S i b).1.length := by
  have hk := placeKinds_at (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1) (unrollKinds_terms senv)
  rcases hp : placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1) with ⟨inps, e⟩
  rw [hp] at hk
  simp only [unrollOne, hp, List.length_append, List.length_cons, List.length_nil] at hk ⊢
  have e1 : (inps.flatMap fun x => x.tys).length = (inps.flatMap SymInput.tys).length := rfl
  omega

/-- Each step of an unrolled run is one `unrollOne` at a base constant, whose types sit at that base in the run's
types and whose assertions are among the run's. -/
theorem unrollSteps_at : (d : Nat) → (S : SymState v) → (i b : Nat) →
    ∀ st ∈ (unrollSteps L T P v senv S i b d).2.2.1, ∃ S' i' bs, b ≤ bs ∧ (unrollOne L T P v senv S' i' bs).2.2.1 = st ∧
      (∀ p (h : p < (unrollOne L T P v senv S' i' bs).1.length),
        (unrollSteps L T P v senv S i b d).1[bs - b + p]? = some (unrollOne L T P v senv S' i' bs).1[p]) ∧
      ∀ a ∈ (unrollOne L T P v senv S' i' bs).2.1, a ∈ (unrollSteps L T P v senv S i b d).2.1
  | 0, _, _, _, st, h => by cases h
  | d + 1, S, i, b, st, h => by
    have hn := unrollOne_next (T := T) (P := P) senv S i b
    rcases h1 : unrollOne L T P v senv S i b with ⟨tys, asserts, st0, refused, b'⟩
    rw [h1] at hn
    simp only at hn
    have ih := unrollSteps_at d st0.after (i + 1) b'
    rcases h2 : unrollSteps L T P v senv st0.after (i + 1) b' d with ⟨tys', asserts', sts, refused'⟩
    rw [h2] at ih
    simp only [unrollSteps, h1, h2, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · refine ⟨S, i, b, Nat.le_refl _, by rw [h1], fun p hp => ?_, fun a ha => ?_⟩
      · have hp' : p < tys.length := by rw [h1] at hp; exact hp
        simp [h1, List.getElem?_append_left hp']
      · rw [h1] at ha; exact List.mem_append_left _ ha
    · obtain ⟨S', i', bs, hle, hst, hty, has⟩ := ih st h
      refine ⟨S', i', bs, by omega, hst, fun p hp => ?_, fun a ha => List.mem_append_right _ (has a ha)⟩
      rw [List.getElem?_append_right (by omega), show bs - b + p - tys.length = bs - b' + p by omega]
      exact hty p hp

theorem unrollKind_ok {S : SymState v} {sel : Term} {inp : SymInput v (shapes v) senv.nT}
    {x : (SymInput v (shapes v) senv.nT × EncodedStep v) × Term × Term × SymState v}
    (h : unrollKind L T P v senv S sel inp = .ok x) :
    ∃ t valid wf, encodeStep L T P v senv S inp = .ok t ∧ inp.validT L S.fresh = .ok valid ∧ inp.wf L = some wf ∧
      x = ((inp, t), andT (.eq sel (.int inp.pick)) t.out.case,
        .or (.not (andT (.eq sel (.int inp.pick)) t.out.case))
          (andT wf (andT t.codes (andT t.sites (andT t.cond (andT (t.out.after S inp).1 valid))))),
        (t.out.after S inp).2) := by
  unfold unrollKind at h
  split at h
  · rename_i t valid wf he hv hw
    cases h
    exact ⟨t, valid, wf, he, hv, need_ok.1 hw, rfl⟩
  all_goals cases h

/-- An unrolled run never yields a model whose inputs do not decode: in a model of its assertions whose variables
hold values of their sorts, the input each step's selector picks decodes. -/
theorem unroll_inputs_decode (hc : v.caller.isData = true) {d : Nat} {B : UnrollBase v senv.nT}
    (hB : unrollBase L T P v senv d = .ok B)
    (hM : ∀ n (h : n < B.tys.length), VarSorted L B.tys[n] (M.vars n)) (hA : ∀ a ∈ B.asserts, Holds M a) :
    ∀ st ∈ B.steps, ∃ x, st.decode M L hc = some x := by
  simp only [unrollBase] at hB
  obtain ⟨S0, -, hB⟩ := bind_ok.1 hB
  obtain ⟨dts, -, hB⟩ := bind_ok.1 hB
  rcases hr : unrollSteps L T P v senv S0 0 0 d with ⟨tys, asserts, steps, refused⟩
  have hat := unrollSteps_at (T := T) (P := P) senv d S0 0 0
  rw [hr] at hB hat
  obtain ⟨vars, -, hB⟩ := bind_ok.1 hB
  cases pure_ok.1 hB
  intro st hst
  obtain ⟨S, i, bs, -, hst, hty, has⟩ := hat st hst
  subst hst
  simp only [Nat.sub_zero] at hty
  have hk := placeKinds_at (unrollKinds v (shapes v) senv.nT (i != 0)) (bs + 1) (unrollKinds_terms senv)
  rcases hp : placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (bs + 1) with ⟨inps, e⟩
  rw [hp] at hk
  simp only [unrollOne, hp] at hty has ⊢
  have hsorted : ∀ q (h : q < ([Ty.int] ++ inps.flatMap (·.tys)).length),
      ∀ t, ([Ty.int] ++ inps.flatMap (·.tys))[q]? = some t → t.isData = true →
        Sorted L t (M.vars (bs + q)) := by
    intro q h t ht hd
    have hq := hty q h
    rw [List.getElem?_eq_getElem h] at ht
    cases ht
    have hlt : bs + q < tys.length := (List.getElem?_eq_some_iff.1 hq).1
    have := hM (bs + q) (by simpa using hlt)
    simp only at this
    rw [(List.getElem?_eq_some_iff.1 hq).2] at this
    exact sorted_of_varSorted hd this
  let rs := inps.map fun inp => unrollKind L T P v senv S (.var bs) inp
  let oks := rs.filterMap fun | .ok x => some x | .error _ => none
  have hany : Holds M (anyT (oks.map (·.2.1))) :=
    hA _ (has _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))
  obtain ⟨_, hx, hxe⟩ := (holds_anyT _).1 hany
  obtain ⟨x, hxo, rfl⟩ := List.mem_map.1 hx
  have hok : ∀ y ∈ oks, ∃ inp ∈ inps, unrollKind L T P v senv S (.var bs) inp = .ok y := fun y hy => by
    obtain ⟨r, hrm, hro⟩ := List.mem_filterMap.1 hy
    obtain ⟨inp, hi, rfl⟩ := List.mem_map.1 hrm
    refine ⟨inp, hi, ?_⟩
    cases hu : unrollKind L T P v senv S (.var bs) inp with
    | error _ => simp [hu] at hro
    | ok x0 => simp [hu] at hro; rw [hro]
  have hpick : ∀ y ∈ oks, y.2.1 = andT (.eq (.var bs) (.int y.1.1.pick)) y.1.2.out.case := fun y hy => by
    obtain ⟨inp, -, hu⟩ := hok y hy
    obtain ⟨t, -, -, -, -, -, rfl⟩ := unrollKind_ok senv hu
    rfl
  obtain ⟨y, hy⟩ : ∃ y, (oks.map (·.1)).find? (fun k => ((andT (.eq (.var bs) (.int k.1.pick)) k.2.out.case).denote M).toBool) = some y :=
    Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨x.1, List.mem_map_of_mem hxo, by rw [← hpick x hxo]; exact hxe⟩)
  have hyp := List.find?_some hy
  obtain ⟨x', hx'o, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hy)
  obtain ⟨inp, hik, hkind⟩ := hok x' hx'o
  obtain ⟨t, valid, wf, -, -, hwf, hx'⟩ := unrollKind_ok senv hkind
  have hassert : Holds M x'.2.2.1 := hA _ (has _ (List.mem_append_left _ (List.mem_map_of_mem hx'o)))
  subst hx'
  have hwfH : Holds M wf := by
    simp only [holds_or, holds_not, holds_andT] at hassert
    rcases hassert with h | h
    · exact (h ((holds_andT _ _).1 hyp)).elim
    · exact h.1
  obtain ⟨⟨p, hpk, c, rfl⟩, j, hterms, hflat⟩ := hk.2 _ hik
  have hdata := (unrollKinds_shape hc hpk c).2.2
  have hs : ∀ q (h : q < (p.2 c).tys.length), Sorted L (p.2 c).tys[q] (M.vars (bs + 1 + j + q)) := by
    intro q h
    have hf : (inps.flatMap (·.tys))[j + q]? = some (p.2 c).tys[q] := hflat q h
    have hlt := (List.getElem?_eq_some_iff.1 hf).1
    have hget : ([Ty.int] ++ inps.flatMap (·.tys))[1 + (j + q)]? = some (p.2 c).tys[q] := by
      rw [List.singleton_append, show 1 + (j + q) = (j + q) + 1 by omega, List.getElem?_cons_succ]
      exact hf
    have := hsorted (1 + (j + q)) (List.getElem?_eq_some_iff.1 hget).1 _ hget (hdata _ (List.getElem_mem h))
    simpa [Nat.add_assoc] using this
  obtain ⟨z, hz⟩ := SymInput.decode_total hc hdata hwf hwfH (hterms ▸ forall2_vars _ (bs + 1 + j) hs)
  refine ⟨z, ?_⟩
  change UnrollStep.decode M L hc ⟨.var bs, S, _, oks.map (·.1)⟩ = some z
  simp only [UnrollStep.decode, UnrollStep.taken, UnrollStep.picks]
  rw [hy]
  exact hz

end

end Tazuna.Smt
