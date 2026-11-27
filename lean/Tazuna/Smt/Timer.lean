import Tazuna.Smt.ReactExact
import Tazuna.Smt.Verdict
import Tazuna.Semantics.Interleave

/-! The question T5 asks of a timer machine (`Step.TimerForward`): can the state its timer enters wait for a timer
before the one that entered it? The instance's key and state and the records are free, so one question per machine
covers every timer it fires (`Step.firesForward_iff`). The encoding applies the `timer` code at those terms, then
again at the state the first timer enters (`timer_encode`). No time is free: `timer` sees none. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {r e : Ty}

/-- Whether the timer the state `st`'s timer enters waits for is before that timer, the condition that `timer` fits at
both contexts (the second only where the first gives a timer), and its code's own condition. -/
def encodeTimer (m : MachineV r e) (key st records : Term) : Except Refusal (Term × Term × Term) := do
  let (tc, c0) ← m.timer.code L
  let (dopt, _) ← L.findE (Ty.option (Ty.timer m.state))
  let (dtm, _) ← L.findE (Ty.timer m.state)
  let cx1 ← Code.ofDataE _ (← timerCtxT L m key st records)
  let (a1, c1) ← tc (cx1, ())
  let t1 ← Code.dataTermE _ a1
  let t1 := Term.share t1
  let cx2 ← Code.ofDataE _ (← timerCtxT L m key (targetT dopt dtm t1) records)
  let (a2, c2) ← tc (cx2, ())
  let t2 ← Code.dataTermE _ a2
  let at1 := Term.sel dtm 0 0 (.sel dopt 0 0 t1)
  let at2 := Term.sel dtm 0 0 (.sel dopt 0 0 t2)
  pure (.and (.is dopt 0 t1) (.and (.is dopt 0 t2) (.lt at2 at1)), andT c1 (.ite (.is dopt 0 t1) c2 tt), c0)

/-- The types of a timer machine's question variables, `v0` to `v2`: the instance's key and state, and the records. -/
def timerTys (m : MachineV r e) : List Ty := [m.key, m.state, r]

/-- A timer machine's two questions, over well-formed variables: the bound question, whether `timer` or its code's
captured values leave the slots at some context; and the target question, whether the state a timer enters waits for
an earlier timer where everything fits. -/
def timerQuestions (m : MachineV r e) : Except Refusal (TypedScript × TypedScript) := do
  let (back, c, c0) ← encodeTimer L m (.var 0) (.var 1) (.var 2)
  let wfs ← (timerTys m).zipIdx.mapM fun (t, i) => need (lacksData t) (wfT L t (.var i))
  let vars ← (timerTys m).mapM fun t => need (lacks t) (L.srt? t)
  let dts ← need (.layout (.type r)) L.datatypes?
  let script (asserts : List Term) : TypedScript := ⟨dts, timerTys m, vars, wfs, asserts⟩
  pure (script [.or (.not c0) (.not c)], script [c0, c, back])

end

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- Whether `timer` fits at the context of the instance of `k` in `st`, and at the state its timer enters. -/
def TimerFits (S : Ty → Nat) (m : MachineV r e) (recs : r.den0) (k : m.key.den0) (st : m.state.den0) : Prop :=
  m.timer.appFits S (.inl (k, st, recs, ()), ()) ∧
    ∀ x ∈ m.timerAt recs k st, m.timer.appFits S (.inl (k, x.2, recs, ()), ())

/-- A timer machine's question: where the terms code an instance's key and state and the records, the code's own
condition holds exactly when `timer`'s captured values fit; where it holds, the condition holds exactly when `timer`
fits at both contexts; and where that holds, the question's term holds exactly when the state the timer enters waits
for an earlier timer. -/
theorem timer_encode (m : MachineV r e) {key st records : Term} {k : m.key.den0} {sv : m.state.den0}
    {recs : r.den0} (hk : RelV L m.key (Ty.up _ m.key_data k) (key.denote M))
    (hs : RelV L m.state (Ty.up _ m.state_data sv) (st.denote M))
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M))
    {back c c0 : Term} (henc : encodeTimer L m key st records = .ok (back, c, c0)) :
    (Holds M c0 ↔ (m.timer.fits L.count).1) ∧
    (Holds M c0 → (Holds M c ↔ TimerFits L.count m recs k sv) ∧
      (Holds M c → (Holds M back ↔ ∃ x ∈ m.timerAt recs k sv, ∃ y ∈ m.timerAt recs k x.2, y.1 < x.1))) := by
  obtain ⟨⟨tc, c0'⟩, g0, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dopt, n1⟩, g1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dtm, n2⟩, g2, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx1, g3, henc⟩ := bind_ok.1 henc
  obtain ⟨cx1, g4, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨a1, c1⟩, g5, henc⟩ := bind_ok.1 henc
  obtain ⟨t1, g6, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx2, g7, henc⟩ := bind_ok.1 henc
  obtain ⟨cx2, g8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨a2, c2⟩, g9, henc⟩ := bind_ok.1 henc
  obtain ⟨t2, g10, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  replace g1 := need_ok.1 g1
  replace g2 := need_ok.1 g2
  refine ⟨(m.timer.code_exact g0).1, fun hc0 => ?_⟩
  have hctx : ∀ t ∈ [Ty.timerCtx m.key m.state r], t.isFn = false := by simp [Ty.timerCtx, Ty.isFn]
  have htc := m.timer.code_fn m.timer.ht g0 hc0
  have hcx1 := tctx_rel m hk hs hrec g3 (need_ok.1 g4)
  have e1 := m.timer.app_exact g0 hc0 hctx _ _ (tctx_rels m hcx1 m.timer.args_data) g5
  -- Where `timer` fits at the first context, its terms read the first timer.
  have view1 : Holds M c1 → _ := fun hc1 =>
    timer_view m g1 g2 _ (by rw [Term.denote_share]; exact (rel_term (need_ok.1 g6) _).1 (timer_app m htc hcx1 g5 hc1))
  have hite : ∀ (b : Bool) (x : Term), (Term.is dopt 0 (Term.share t1)).denote M = .bool b →
      (Holds M (.ite (.is dopt 0 (Term.share t1)) x tt) ↔ (b = true → Holds M x)) := by
    intro b x hb; cases b <;> simp [holds_ite, hb, Val.toBool, holds_tt]
  unfold MachineV.timerAt
  refine ⟨?_, fun hc => ?_⟩
  · rw [holds_andT, e1]
    unfold TimerFits MachineV.timerAt
    constructor
    · rintro ⟨p1, p2⟩
      refine ⟨p1, fun x hx => ?_⟩
      obtain ⟨his, hsel⟩ := view1 (e1.2 p1)
      rw [Option.mem_def] at hx
      rw [hx] at his
      have hp2 := (hite true _ his).1 p2 rfl
      have hcx2 := tctx_rel m hk (hsel x.1 x.2 hx).2 hrec g7 (need_ok.1 g8)
      exact (m.timer.app_exact g0 hc0 hctx _ _ (tctx_rels m hcx2 m.timer.args_data) g9).1 hp2
    · rintro ⟨p1, p2⟩
      refine ⟨p1, ?_⟩
      obtain ⟨his, hsel⟩ := view1 (e1.2 p1)
      cases hv : Step.timerVal (m.timer.fn (.inl (k, sv, recs, ()), ())) with
      | none => rw [hv] at his; exact (hite false _ his).2 (fun h => nomatch h)
      | some x =>
        rw [hv] at his
        refine (hite true _ his).2 fun _ => ?_
        have hcx2 := tctx_rel m hk (hsel x.1 x.2 hv).2 hrec g7 (need_ok.1 g8)
        exact (m.timer.app_exact g0 hc0 hctx _ _ (tctx_rels m hcx2 m.timer.args_data) g9).2 (p2 x hv)
  · obtain ⟨hc1, hc2'⟩ := (holds_andT _ _).1 hc
    obtain ⟨his, hsel⟩ := view1 hc1
    have hand : ∀ a b : Term, (Term.and a b).denote M = .bool ((a.denote M).toBool && (b.denote M).toBool) :=
      fun _ _ => rfl
    simp only [Holds]
    rw [hand, hand, his]
    cases hv : Step.timerVal (m.timer.fn (.inl (k, sv, recs, ()), ())) with
    | none => simp [Val.toBool]
    | some x =>
      have hc2 := (hite true _ (by rw [his, hv]; rfl)).1 hc2' rfl
      obtain ⟨hat1, htg⟩ := hsel x.1 x.2 hv
      have hcx2 := tctx_rel m hk htg hrec g7 (need_ok.1 g8)
      obtain ⟨his2, hsel2⟩ := timer_view m g1 g2 _ ((rel_term (need_ok.1 g10) _).1 (timer_app m htc hcx2 g9 hc2))
      rw [his2]
      cases hv2 : Step.timerVal (m.timer.fn (.inl (k, x.2, recs, ()), ())) with
      | none => simp [Val.toBool, hv2]
      | some y =>
        have hat2 := (hsel2 y.1 y.2 hv2).1
        have hlt : (Term.lt (.sel dtm 0 0 (.sel dopt 0 0 t2)) (.sel dtm 0 0 (.sel dopt 0 0 (Term.share t1)))).denote M =
            .bool (decide (y.1 < x.1)) := by
          show Val.bool _ = _
          rw [hat2, show (Term.sel dtm 0 0 (.sel dopt 0 0 (Term.share t1))).denote M = .int x.1 from hat1]
          rfl
        rw [hlt]
        simp only [Val.toBool, hv2, Option.mem_def, Option.some.injEq, exists_eq_left']
        simp

/-- The values of an instance's timer context, as the question's variables hold them. -/
structure TimerVals (L : Layout) (m : MachineV r e) (M : Model) where
  key : m.key.den0
  state : m.state.den0
  records : r.den0
  hkey : decodeV L m.key (M.vars 0) = some (Ty.up _ m.key_data key)
  hstate : decodeV L m.state (M.vars 1) = some (Ty.up _ m.state_data state)
  hrecords : decodeV L r (M.vars 2) = some (Ty.up _ m.records_data records)

/-- The values a model gives a timer question's variables, where they decode. -/
def TimerVals.decode (L : Layout) (m : MachineV r e) (M : Model) : Option (TimerVals L m M) :=
  match hk : decodeV L m.key (M.vars 0), hs : decodeV L m.state (M.vars 1), hr : decodeV L r (M.vars 2) with
  | some k, some st, some rc =>
    some ⟨Ty.down _ m.key_data k, Ty.down _ m.state_data st, Ty.down _ m.records_data rc,
      by rw [hk, Ty.up_down], by rw [hs, Ty.up_down], by rw [hr, Ty.up_down]⟩
  | _, _, _ => none

theorem wfs_hold (m : MachineV r e) (x : TimerVals L m M) {wfs : List Term}
    (h : (timerTys m).zipIdx.mapM (fun (t, i) => need (lacksData t) (wfT L t (.var i))) = .ok wfs) :
    ∀ w ∈ wfs, Holds M w := by
  have hF := mapM_ok _ _ _ h
  intro w hw
  obtain ⟨⟨t, i⟩, hti, hR⟩ := forall2_mem_right hF w hw
  have hc := need_ok.1 hR
  simp only [timerTys, List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
    or_false] at hti
  have hdec : ∀ {u : Ty} {j : Nat} {y : u.den}, decodeV L u (M.vars j) = some y → wfT L u (.var j) = some w →
      Holds M w := by
    intro u j y hd hw'
    exact (wf_iff u _ w hw' (decode_sorted u _ _ hd)).2 (by simp [Term.denote, hd])
  rcases hti with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hdec x.hkey hc
  · exact hdec x.hstate hc
  · exact hdec x.hrecords hc

/-- What a timer machine's questions say: a model of the target question's assertions holds a context whose timer
enters a state that waits for an earlier timer, so the machine's timers do not fire forward (the counterexample is
honest). -/
theorem timer_exact (m : MachineV r e) {bq tq : TypedScript} (hq : timerQuestions L m = .ok (bq, tq)) (x : TimerVals L m M) :
    (∀ a ∈ tq.asserts, Holds M a) →
      ∃ y ∈ m.timerAt x.records x.key x.state, ∃ z ∈ m.timerAt x.records x.key y.2, z.1 < y.1 := by
  intro hall
  obtain ⟨⟨back, c, c0⟩, he, hq⟩ := bind_ok.1 hq
  obtain ⟨wfs, -, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hk := decode_rel _ _ _ x.hkey
  have hs := decode_rel _ _ _ x.hstate
  have hr := decode_rel _ _ _ x.hrecords
  have henc := timer_encode m hk hs hr he
  have hin : ∀ a ∈ [c0, c, back], Holds M a := hall
  have hc0 := hin c0 (by simp)
  exact (((henc.2 hc0).2 (hin c (by simp))).1 (hin back (by simp)))

/-- A model of a timer machine's target question is a counterexample to T5's timer hypothesis. -/
theorem timer_violates {ms : List (MachineV r e)} {m : MachineV r e} (hm : m ∈ ms) {bq tq : TypedScript}
    (hq : timerQuestions L m = .ok (bq, tq)) (x : TimerVals L m M) (hall : ∀ a ∈ tq.asserts, Holds M a) :
    ¬ Step.FiresForward ms := fun h => by
  obtain ⟨y, hy, z, hz, hlt⟩ := timer_exact m hq x hall
  exact Int.lt_irrefl _ (Int.lt_of_lt_of_le hlt ((Step.firesForward_iff ms).1 h m hm x.records x.key x.state y hy z hz))

/-- Where the target question is unsat, the state a timer enters at every context whose values fit, where `timer`
and its captured values fit, waits for no earlier timer; where the bound question is unsat too, at every context whose
values fit. -/
theorem timer_sound (m : MachineV r e) {bq tq : TypedScript} (hq : timerQuestions L m = .ok (bq, tq))
    (ht : Unsat L tq) (hM : ∀ n (h : n < (timerTys m).length), Sorted L (timerTys m)[n] (M.vars n))
    (hsel : LayoutSorted L (timerTys m) M) (x : TimerVals L m M) :
    ((m.timer.fits L.count).1 → TimerFits L.count m x.records x.key x.state →
      ∀ y ∈ m.timerAt x.records x.key x.state, ∀ z ∈ m.timerAt x.records x.key y.2, y.1 ≤ z.1) ∧
    (Unsat L bq → ∀ y ∈ m.timerAt x.records x.key x.state, ∀ z ∈ m.timerAt x.records x.key y.2, y.1 ≤ z.1) := by
  obtain ⟨⟨back, c, c0⟩, he, hq'⟩ := bind_ok.1 hq
  obtain ⟨wfs, hwfs, hq'⟩ := bind_ok.1 hq'
  obtain ⟨vars, hvars, hq'⟩ := bind_ok.1 hq'
  obtain ⟨dts, hdts, hq'⟩ := bind_ok.1 hq'
  cases pure_ok.1 hq'
  have hW := hsel _ _ (need_ok.1 hdts) (mapM_need hvars)
  have hk := decode_rel _ _ _ x.hkey
  have hs := decode_rel _ _ _ x.hstate
  have hr := decode_rel _ _ _ x.hrecords
  have henc := timer_encode m hk hs hr he
  have hw := wfs_hold m x hwfs
  have hfwd : Holds M c0 → Holds M c →
      ∀ y ∈ m.timerAt x.records x.key x.state, ∀ z ∈ m.timerAt x.records x.key y.2, y.1 ≤ z.1 := by
    intro hc0 hc y hy z hz
    refine Int.not_lt.1 fun hlt => ?_
    obtain ⟨a, ha, hna⟩ := ht.noModel M (fun n h => varSorted_of_sorted (hM n h)) hW
    simp only [TypedScript.script, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl | rfl
    · exact hna (hw a ha)
    · exact hna hc0
    · exact hna hc
    · exact hna (((henc.2 hc0).2 hc).2 ⟨y, hy, z, hz, hlt⟩)
  refine ⟨fun hf ha => ?_, fun hb => ?_⟩
  · have hc0 := henc.1.2 hf
    exact hfwd hc0 (((henc.2 hc0).1).2 ha)
  · obtain ⟨a, ha, hna⟩ := hb.noModel M (fun n h => varSorted_of_sorted (hM n h)) hW
    simp only [TypedScript.script, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl
    · exact (hna (hw a ha)).elim
    · simp only [holds_or, holds_not, not_or, Classical.not_not] at hna
      exact hfwd hna.1 hna.2

end

end Tazuna.Smt
