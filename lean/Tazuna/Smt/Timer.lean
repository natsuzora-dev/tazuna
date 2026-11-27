import Tazuna.Smt.ReactExact
import Tazuna.Smt.Verdict
import Tazuna.Semantics.Interleave

/-! The question T5 asks of a timer machine (`Step.TimerForward`): can its `after` set a timer before the time it is
set at? The instance's key and state, the records and the time are free, so one question per machine covers every
timer it fires (`Step.firesForward_iff`). The encoding applies the `after` code to the context of those terms and reads
the timer it asks for as an entry holds it (`timerT`); the timer falls back where it is set and its deadline is
before the time (`timer_encode`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {r e : Ty}

/-- Whether the timer `m`'s `after` sets at the context of these terms is before `now`, the condition that `after`
fits there, and its code's own condition. -/
def encodeTimer (m : MachineV r e) (key st records now : Term) : Except Refusal (Term × Term × Term) := do
  let (af, c0) ← m.after.code L
  let nctx ← Code.ofDataE _ (← instCtxT L m key st records now)
  let (a, c) ← af (nctx, ())
  let at_ ← Code.dataTermE _ a
  let tm ← timerT L m now at_
  let (dent, _) ← L.findE (Ty.option (.tuple [.int, m.state]))
  let dp ← tupleD L [.int, m.state]
  pure (.and (.is dent 0 tm) (.lt (.sel dp 0 0 (.sel dent 0 0 tm)) now), c, c0)

/-- The types of a timer machine's question variables, `v0` to `v3`: the instance's key and state, the records and the
time. -/
def timerTys (m : MachineV r e) : List Ty := [m.key, m.state, r, .int]

/-- A timer machine's two questions, over well-formed variables: the bound question, whether `after` or its code's
captured values leave the slots at some context; and the target question, whether `after` sets a timer before the time
it is set at where everything fits. -/
def timerQuestions (m : MachineV r e) : Except Refusal (TypedScript × TypedScript) := do
  let (back, c, c0) ← encodeTimer L m (.var 0) (.var 1) (.var 2) (.var 3)
  let wfs ← (timerTys m).zipIdx.mapM fun (t, i) => need (lacksData t) (wfT L t (.var i))
  let vars ← (timerTys m).mapM fun t => need (lacks t) (L.srt? t)
  let dts ← need (.layout (.type r)) L.datatypes?
  let script (asserts : List Term) : TypedScript := ⟨dts, timerTys m, vars, wfs, asserts⟩
  pure (script [.or (.not c0) (.not c)], script [c0, c, back])

end

section
variable {L : Layout} {M : Model} {r e : Ty}

/-- An entry's timer term is set before `now` exactly when the timer it codes is. -/
theorem timer_den (m : MachineV r e) {dent n dp np : Nat}
    (hdent : L.find? (Ty.option (.tuple [.int, m.state])) = some (dent, n)) (hdp : L.find? (.tuple [.int, m.state]) = some (dp, np))
    {tm now : Term} {tnow : Int} (hnow : now.denote M = .int tnow) (t : Option (Int × m.state.den0))
    (ht : RelV L _ (Ty.up _ m.timer_data (timerVal t)) (tm.denote M)) :
    Holds M (.and (.is dent 0 tm) (.lt (.sel dp 0 0 (.sel dent 0 0 tm)) now)) ↔ ∃ x ∈ t, x.1 < tnow := by
  have hs := m.state_data
  have hent1 : (Ty.tuple [.tuple [.int, m.state]]).isData = true := by simp [Ty.isData, Ty.isDatas, hs]
  have hpair : (Ty.tuple [.int, m.state]).isData = true := by simp [Ty.isData, Ty.isDatas, hs]
  have hnone' : (Ty.adt 3 [.tuple [.int, m.state]] [[]]).isData = true := by simp [Ty.isData, Ty.isDatass, Ty.isDatas]
  obtain ⟨d', n', hf', hra⟩ := ht
  obtain rfl := find_det hf' hdent
  cases t with
  | some p =>
    obtain ⟨dl, tg⟩ := p
    change RelAlts L d' 0 _ (Ty.up _ m.timer_data (.inl ((dl, tg, ()), ()))) _ at hra
    erw [Ty.up_inl 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hent1] at hra
    obtain ⟨vals, hv, hvals⟩ := hra
    erw [Ty.up_tuple _ _ _ hpair rfl] at hvals
    obtain ⟨v0, _, rfl, ⟨dp', np', vals7, hf7, hv7, hvals7⟩, rfl⟩ := hvals
    obtain rfl := find_det hf7 hdp
    erw [Ty.up_tuple _ _ _ rfl (by simp [Ty.isData, Ty.isDatas, hs])] at hvals7
    obtain ⟨vd, vs7, rfl, hvd, hvals7⟩ := hvals7
    erw [Ty.up_tuple _ _ _ hs rfl] at hvals7
    obtain ⟨vt, _, rfl, -, rfl⟩ := hvals7
    change vd = .int dl at hvd
    subst hvd
    simp [Holds, Term.denote, hv, hv7, hnow, Val.toBool, Val.toInt]
  | none =>
    change RelAlts L d' 0 _ (Ty.up _ m.timer_data (.inr (.inl ()))) _ at hra
    erw [Ty.up_inr 3 _ [.tuple [.int, m.state]] [[]] m.timer_data hnone', Ty.up_inl 3 _ [] [] hnone' rfl] at hra
    obtain ⟨vals, hv, -⟩ := hra
    simp [Holds, Term.denote, hv, Val.toBool]

/-- A timer machine's question: where the terms code an instance's key and state, the records and the time, the
code's own condition holds exactly when `after`'s captured values fit; where it holds, the condition holds exactly when
`after` fits at that context; and where that holds, the question's term holds exactly when the timer `after` sets
there is before the time. -/
theorem timer_encode (m : MachineV r e) {key st records now : Term} {k : m.key.den0} {sv : m.state.den0}
    {recs : r.den0} {tnow : Int} (hk : RelV L m.key (Ty.up _ m.key_data k) (key.denote M))
    (hs : RelV L m.state (Ty.up _ m.state_data sv) (st.denote M))
    (hrec : RelV L r (Ty.up _ m.records_data recs) (records.denote M)) (hnow : now.denote M = .int tnow)
    {back c c0 : Term} (henc : encodeTimer L m key st records now = .ok (back, c, c0)) :
    (Holds M c0 ↔ (m.after.fits L.count).1) ∧
    (Holds M c0 → (Holds M c ↔ m.after.appFits L.count (.inl (k, sv, recs, tnow, ()), ())) ∧
      (Holds M c → (Holds M back ↔
        ∃ x ∈ Step.timerAt tnow (m.after.fn (.inl (k, sv, recs, tnow, ()), ())), x.1 < tnow))) := by
  obtain ⟨⟨af, c0'⟩, g0, henc⟩ := bind_ok.1 henc
  obtain ⟨ctxT, g1, henc⟩ := bind_ok.1 henc
  obtain ⟨nctx, g2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨a, ca⟩, g3, henc⟩ := bind_ok.1 henc
  obtain ⟨at_, g4, henc⟩ := bind_ok.1 henc
  obtain ⟨tm, g5, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dent, nent⟩, g6, henc⟩ := bind_ok.1 henc
  obtain ⟨dp, g7, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  refine ⟨(m.after.code_exact g0).1, fun hc0 => ?_⟩
  have hcx := ctx_rel m hk hs hrec hnow g1 (need_ok.1 g2)
  have hctx : ∀ t ∈ [Ty.machineCtx m.key m.state r], t.isFn = false := by simp [Ty.machineCtx, Ty.isFn]
  refine ⟨m.after.app_exact g0 hc0 hctx _ _ (ctx_rels m hcx m.after.args_data) g3, fun hca => ?_⟩
  have ha := after_app m (m.after.code_fn m.after.ht g0 hc0) hcx g3 hca
  have htm := timerT_rel m hnow _ ((rel_term (need_ok.1 g4) _).1 ha) g5
  obtain ⟨np, hdp⟩ := tupleD_ok g7
  exact timer_den m (need_ok.1 g6) hdp hnow _ htm

/-- The values of an instance context, as the question's variables hold them. -/
structure TimerVals (L : Layout) (m : MachineV r e) (M : Model) where
  key : m.key.den0
  state : m.state.den0
  records : r.den0
  now : Int
  hkey : decodeV L m.key (M.vars 0) = some (Ty.up _ m.key_data key)
  hstate : decodeV L m.state (M.vars 1) = some (Ty.up _ m.state_data state)
  hrecords : decodeV L r (M.vars 2) = some (Ty.up _ m.records_data records)
  hnow : M.vars 3 = .int now

/-- The values a model gives a timer question's variables, where they decode. -/
def TimerVals.decode (L : Layout) (m : MachineV r e) (M : Model) : Option (TimerVals L m M) :=
  match hk : decodeV L m.key (M.vars 0), hs : decodeV L m.state (M.vars 1), hr : decodeV L r (M.vars 2),
    hn : M.vars 3 with
  | some k, some st, some rc, .int now =>
    some ⟨Ty.down _ m.key_data k, Ty.down _ m.state_data st, Ty.down _ m.records_data rc, now,
      by rw [hk, Ty.up_down], by rw [hs, Ty.up_down], by rw [hr, Ty.up_down], hn⟩
  | _, _, _, _ => none

/-- The context the values make for `after`. -/
def TimerVals.ctx {m : MachineV r e} (x : TimerVals L m M) : (Ty.tuple [Ty.machineCtx m.key m.state r]).den0 :=
  (.inl (x.key, x.state, x.records, x.now, ()), ())

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
  rcases hti with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hdec x.hkey hc
  · exact hdec x.hstate hc
  · exact hdec x.hrecords hc
  · exact hdec (u := .int) (y := x.now) (by simp [x.hnow, decodeV]) hc

/-- What a timer machine's questions say: a model of the target question's assertions holds a context where `after`
sets a timer before the time it is set at, so the machine's timers do not fire forward (the counterexample is
honest); and where the target question is unsat, no context whose values fit and at which `after` fits does so. -/
theorem timer_exact (m : MachineV r e) {bq tq : TypedScript} (hq : timerQuestions L m = .ok (bq, tq)) (x : TimerVals L m M) :
    (∀ a ∈ tq.asserts, Holds M a) →
      ∃ y ∈ Step.timerAt x.now (m.after.fn x.ctx), y.1 < x.now := by
  intro hall
  obtain ⟨⟨back, c, c0⟩, he, hq⟩ := bind_ok.1 hq
  obtain ⟨wfs, -, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, -, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, -, hq⟩ := bind_ok.1 hq
  cases pure_ok.1 hq
  have hk := decode_rel _ _ _ x.hkey
  have hs := decode_rel _ _ _ x.hstate
  have hr := decode_rel _ _ _ x.hrecords
  have henc := timer_encode m hk hs hr (tnow := x.now) (by simp [Term.denote, x.hnow]) he
  have hin : ∀ a ∈ [c0, c, back], Holds M a := hall
  have hc0 := hin c0 (by simp)
  exact (((henc.2 hc0).2 (hin c (by simp))).1 (hin back (by simp)))

/-- A model of a timer machine's target question is a counterexample to T5's timer hypothesis. -/
theorem timer_violates {ms : List (MachineV r e)} {m : MachineV r e} (hm : m ∈ ms) {bq tq : TypedScript}
    (hq : timerQuestions L m = .ok (bq, tq)) (x : TimerVals L m M) (hall : ∀ a ∈ tq.asserts, Holds M a) :
    ¬ Step.FiresForward ms := fun h => by
  obtain ⟨y, hy, hlt⟩ := timer_exact m hq x hall
  exact Int.lt_irrefl _ (Int.lt_of_lt_of_le hlt ((Step.firesForward_iff ms).1 h m hm x.records x.now x.key x.state y hy))

/-- Where the target question is unsat, the timer `after` sets at every context whose values fit, where `after` and its
captured values fit, is no earlier than the time it is set at; where the bound question is unsat too, at every context
whose values fit. -/
theorem timer_sound (m : MachineV r e) {bq tq : TypedScript} (hq : timerQuestions L m = .ok (bq, tq))
    (ht : Unsat L tq) (hM : ∀ n (h : n < (timerTys m).length), Sorted L (timerTys m)[n] (M.vars n))
    (hsel : LayoutSel L M) (x : TimerVals L m M) :
    ((m.after.fits L.count).1 → m.after.appFits L.count x.ctx →
      ∀ y ∈ Step.timerAt x.now (m.after.fn x.ctx), x.now ≤ y.1) ∧
    (Unsat L bq → ∀ y ∈ Step.timerAt x.now (m.after.fn x.ctx), x.now ≤ y.1) := by
  obtain ⟨⟨back, c, c0⟩, he, hq'⟩ := bind_ok.1 hq
  obtain ⟨wfs, hwfs, hq'⟩ := bind_ok.1 hq'
  obtain ⟨vars, -, hq'⟩ := bind_ok.1 hq'
  obtain ⟨dts, hdts, hq'⟩ := bind_ok.1 hq'
  cases pure_ok.1 hq'
  have hk := decode_rel _ _ _ x.hkey
  have hs := decode_rel _ _ _ x.hstate
  have hr := decode_rel _ _ _ x.hrecords
  have henc := timer_encode m hk hs hr (tnow := x.now) (by simp [Term.denote, x.hnow]) he
  have hw := wfs_hold m x hwfs
  have hfwd : Holds M c0 → Holds M c → ∀ y ∈ Step.timerAt x.now (m.after.fn x.ctx), x.now ≤ y.1 := by
    intro hc0 hc y hy
    refine Int.not_lt.1 fun hlt => ?_
    obtain ⟨a, ha, hna⟩ := ht.noModel M (fun n h => varSorted_of_sorted (hM n h)) (hsel _ (need_ok.1 hdts))
    simp only [TypedScript.script, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl | rfl | rfl
    · exact hna (hw a ha)
    · exact hna hc0
    · exact hna hc
    · exact hna (((henc.2 hc0).2 hc).2 ⟨y, hy, hlt⟩)
  refine ⟨fun hf ha => ?_, fun hb => ?_⟩
  · have hc0 := henc.1.2 hf
    exact hfwd hc0 (((henc.2 hc0).1).2 ha)
  · obtain ⟨a, ha, hna⟩ := hb.noModel M (fun n h => varSorted_of_sorted (hM n h)) (hsel _ (need_ok.1 hdts))
    simp only [TypedScript.script, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | rfl
    · exact (hna (hw a ha)).elim
    · simp only [holds_or, holds_not, not_or, Classical.not_not] at hna
      exact hfwd hna.1 hna.2

end

end Tazuna.Smt
