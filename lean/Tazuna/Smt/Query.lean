import Tazuna.Smt.Admit

/-! The query step: a listed caller's input passes `accepts`, then `resolve` answers at the context, and the state
stays. `query_encode` proves T2 and the exactness of the condition together. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The codes of a query's functions. -/
structure QueryCode {r c : Ty} (q : QueryV r c) where
  accepts : Code (Ty.fn [q.input] Ty.rules)
  resolve : Code (Ty.fn [Ty.queryCtx r q.input c] q.output)

/-- A query's types are data, as the `query` built-in demands of its type arguments. -/
structure QueryData {r c : Ty} (q : QueryV r c) : Prop where
  records : r.isData = true
  caller : c.isData = true
  input : q.input.isData = true
  output : q.output.isData = true

/-- A query's types are data, since its `resolve` is. -/
theorem _root_.Tazuna.Ir.QueryV.data {r c : Ty} (q : QueryV r c) : QueryData q := by
  have h := q.resolve.ht
  simp only [Ty.queryCtx, Ty.origin, Ty.isData, Ty.isDatas, Ty.isDatass, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all

section
variable {r c : Ty} {q : QueryV r c} (hd : QueryData q)
include hd

theorem QueryData.accepts : (Ty.fn [q.input] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.input]
theorem QueryData.origin : (Ty.origin c).isData = true := by
  simp [Ty.origin, Ty.isData, Ty.isDatas, Ty.isDatass, hd.caller]
theorem QueryData.ctx : (Ty.queryCtx r q.input c).isData = true := by
  simp [Ty.queryCtx, Ty.origin, Ty.isData, Ty.isDatas, Ty.isDatass, hd.records, hd.input, hd.caller]
theorem QueryData.resolve : (Ty.fn [Ty.queryCtx r q.input c] q.output).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx, hd.output]
theorem QueryData.ctxArgs : (Ty.tuple [Ty.queryCtx r q.input c]).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx]

end

/-- The codes relate to the query's functions in the model. -/
structure QueryCode.Rel (M : Model) (L : Layout) {r c : Ty} {q : QueryV r c} (qc : QueryCode q) :
    Prop where
  accepts : Smt.Rel M L _ (Ty.up _ q.data.accepts q.accepts.fn) qc.accepts
  resolve : Smt.Rel M L _ (Ty.up _ q.data.resolve q.resolve.fn) qc.resolve

/-- A query's codes, from the sources it keeps, with their condition. -/
def QueryCode.of (L : Layout) {r c : Ty} (q : QueryV r c) : Except Refusal (QueryCode q × Term) := do
  let (a, c1) ← q.accepts.code L
  let (x, c2) ← q.resolve.code L
  pure (⟨a, x⟩, andT c1 c2)

theorem QueryCode.rel_of {M : Model} {L : Layout} {r c : Ty} {q : QueryV r c} {qc : QueryCode q}
    {cq : Term} (h : QueryCode.of L q = .ok (qc, cq)) (hc : Holds M cq) : qc.Rel M L := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨x, c2⟩, h2, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hc := (holds_andT _ _).1 hc
  exact ⟨q.accepts.code_fn _ h1 hc.1, q.resolve.code_fn _ h2 hc.2⟩

/-- A query's codes' own condition is exact: it holds exactly when its two kept sources fit. -/
theorem queryCode_exact {M : Model} {L : Layout} {r c : Ty} {q : QueryV r c} {qc : QueryCode q} {cq : Term}
    (h : QueryCode.of L q = .ok (qc, cq)) :
    Holds M cq ↔ (q.accepts.fits L.count).1 ∧ (q.resolve.fits L.count).1 := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨x, c2⟩, h2, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  rw [holds_andT, (q.accepts.code_exact (M := M) h1).1, (q.resolve.code_exact (M := M) h2).1]

/-- The terms of a query step's outcome: whether the caller is one the query lists, each `accepts` rule's name and
whether it holds, and the output. -/
structure QueryOut where
  callerOk : Term
  rules : List (Term × Term)
  output : Term

section
variable (L : Layout)

/-- A query step's outcome terms and its condition, from the terms of the records, the time, the outside caller and
the input, and the constants of the listed origins. The condition asks only for what the step computes:
the rules when the origin is listed, the output when the rules hold too. -/
def encodeQuery {r c : Ty} {v : ServiceV} (q : QueryV r c) (qc : QueryCode q) (callers : List Term)
    (S : SymState v) (caller input : Term) : Except Refusal (QueryOut × Term) := do
  let origin ← outsideT L (c := c) caller
  let (a, c1) ← encodeAdmit (c := Ty.origin c) L qc.accepts callers origin input
  let cx ← encodeQueryCtx L S.records S.now origin input
  let (o, c2) ← qc.resolve (cx, ())
  let ot ← Code.dataTermE q.output o
  pure (⟨a.callerOk, a.rules, ot⟩, .ite a.callerOk (andT c1 (.ite (allT (a.rules.map (·.2))) c2 tt)) tt)

end

/-- What the outcome terms say in the model: Invalid with the reasons, or none for Answered. -/
def QueryOut.invalid (M : Model) (o : QueryOut) : Option (List String) :=
  if (o.callerOk.denote M).toBool then
    match brokenIn M o.rules with
    | [] => none
    | n :: ns => some (n :: ns)
  else some ["callers"]

/-- The outcome terms denote the outcome: the same reasons for Invalid, or an output the output term codes. -/
def QueryOut.Rel (M : Model) (L : Layout) {output : Ty} (hout : output.isData = true) (o : QueryOut) : Outcome → Prop
  | .invalid ns => o.invalid M = some ns
  | .answered ⟨t, y⟩ => o.invalid M = none ∧ ∃ h : t = output, RelV L output (Ty.up _ hout (h ▸ y)) (o.output.denote M)
  | _ => False

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- Whether what a query step applies fits: for a listed origin, `accepts` at the input and, where its rules hold,
`resolve` at the context. -/
def queryFits (S : Ty → Nat) {v : ServiceV} (s : State v) (q : QueryV v.records v.caller) (caller : v.caller.den0)
    (input : q.input.den0) : Prop :=
  q.callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 (Step.outside caller)) = true →
    q.accepts.appFits S (input, ()) ∧
      (Step.broken (q.accepts.fn (input, ())) = [] →
        q.resolve.appFits S (Step.queryCtx s s.records (Step.outside caller) input, ()))

/-- A query step's condition is exact and gives T2: where the codes' condition holds, the condition holds exactly
when what the step applies fits (`queryFits`), and wherever it holds the outcome terms denote the step's outcome and
the state stays. -/
theorem query_encode {v : ServiceV} (s : State v) (i : Fin v.queries.length) (caller : v.caller.den0)
    (input : (v.queries.get i).input.den0) {qc : QueryCode (v.queries.get i)}
    {cq : Term} (hqc : QueryCode.of L _ = .ok (qc, cq)) (hcq : Holds M cq) {ks : List Term}
    (hks : callerTerms L ((v.queries.get i).data).origin (v.queries.get i).callers = some ks) {shs : List (PendingShape v.event)} {S : SymState v} (hR : StateRel M L T shs S s) {sc si : Term}
    (hsc : RelV L v.caller (Ty.up _ ((v.queries.get i).data).caller caller) (sc.denote M))
    (hsi : RelV L (v.queries.get i).input (Ty.up _ ((v.queries.get i).data).input input) (si.denote M))
    {o : QueryOut} {cond : Term} (henc : encodeQuery L (v.queries.get i) qc ks S sc si = .ok (o, cond)) :
    (Holds M cond ↔ queryFits L.count s (v.queries.get i) caller input) ∧
    (Holds M cond → (step T v s (.query i caller input)).state = s ∧
      o.Rel M L ((v.queries.get i).data).output (step T v s (.query i caller input)).outcome) := by
  have hq := QueryCode.rel_of hqc hcq
  obtain ⟨⟨a, ca1⟩, g1, hqc'⟩ := bind_ok.1 hqc
  obtain ⟨⟨x, ca2⟩, g2, hqc'⟩ := bind_ok.1 hqc'
  cases pure_ok.1 hqc'
  obtain ⟨hca1, hca2⟩ := (holds_andT _ _).1 hcq
  obtain ⟨sco, h0, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨cx, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨ot, h9, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hso := outsideT_rel ((v.queries.get i).data).caller ((v.queries.get i).data).origin hsc h0
  obtain ⟨hok, hbr⟩ := admit_rel ((v.queries.get i).data).input ((v.queries.get i).data).origin _
    ((v.queries.get i).data).accepts hq.accepts _ hks (Step.outside caller) input hso hsi h1
  have hcx := queryCtx_rel ((v.queries.get i).data).records ((v.queries.get i).data).input
    ((v.queries.get i).data).origin ((v.queries.get i).data).ctx s (Step.outside caller) input hR.records hR.now hso hsi
    h7
  have e1 := admit_exact ((v.queries.get i).data).input (v.queries.get i).accepts g1 hca1 input hsi h1
  have e2 : Holds M c2 ↔
      (v.queries.get i).resolve.appFits L.count (Step.queryCtx s s.records (Step.outside caller) input, ()) :=
    (v.queries.get i).resolve.app_exact g2 hca2 (by simp [Ty.queryCtx, Ty.isFn]) _ _ (rels1 ((v.queries.get i).data).ctx ((v.queries.get i).data).ctxArgs hcx) h8
  have hrules : ∀ hc1 : Holds M c1, ((allT (adm.rules.map (·.2))).denote M).toBool =
      decide (Step.broken ((v.queries.get i).accepts.fn (input, ())) = []) := fun hc1 => by
    rw [toBool_allT_rules, hbr hc1]
  by_cases hin : (v.queries.get i).callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 (Step.outside caller)) = true
  · have hite : Holds M (.ite adm.callerOk (andT c1 (.ite (allT (adm.rules.map (·.2))) c2 tt)) tt) ↔
        Holds M c1 ∧ Holds M (.ite (allT (adm.rules.map (·.2))) c2 tt) := by
      rw [holds_ite, hok]; simp only [Val.toBool, hin, ite_true]; exact holds_andT _ _
    rw [hite]
    refine ⟨⟨fun ⟨hc1, hc2⟩ _ => ⟨e1.1 hc1, fun hb => e2.1 ?_⟩, fun h => ?_⟩, fun ⟨hc1, hc2⟩ => ?_⟩
    · have := (holds_ite _ _ _).1 hc2
      rw [hrules hc1, decide_eq_true hb] at this
      simpa using this
    · obtain ⟨p1, p2⟩ := h hin
      have hc1 := e1.2 p1
      refine ⟨hc1, (holds_ite _ _ _).2 ?_⟩
      rw [hrules hc1]
      by_cases hb : Step.broken ((v.queries.get i).accepts.fn (input, ())) = []
      · rw [decide_eq_true hb]; simpa using e2.2 (p2 hb)
      · rw [decide_eq_false hb]; simpa using holds_tt (M := M)
    · simp only [step]
      refine ⟨by split <;> rfl, ?_⟩
      simp only [Step.execQuery, Step.admit, hin, ite_true]
      have hbroken := hbr hc1
      cases hb : Step.broken ((v.queries.get i).accepts.fn (input, ())) with
      | cons n ns =>
        simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken, hb]
      | nil =>
        rw [hb] at hbroken
        have hc2' : Holds M c2 := by
          have := (holds_ite _ _ _).1 hc2
          rw [hrules hc1, hb] at this
          simpa using this
        have hres := hq.resolve _ (cx, ()) (rels1 ((v.queries.get i).data).ctx ((v.queries.get i).data).ctxArgs hcx) out c2 h8 hc2'
        erw [Ty.up_fn _ _ _ ((v.queries.get i).data).ctxArgs ((v.queries.get i).data).output] at hres
        simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken]
        exact ⟨trivial, trivial, (rel_term (need_ok.1 h9) _).1 hres⟩
  · have hin' : (v.queries.get i).callers.any ((Ty.semWith Dsl.base (Ty.origin v.caller)).2 (Step.outside caller)) = false := by simpa using hin
    have hite : Holds M (.ite adm.callerOk (andT c1 (.ite (allT (adm.rules.map (·.2))) c2 tt)) tt) := by
      rw [holds_ite, hok]; simp only [Val.toBool, hin', Bool.false_eq_true, ite_false]; exact holds_tt
    refine ⟨⟨fun _ h => absurd h hin, fun _ => hite⟩, fun _ => ?_⟩
    simp only [step]
    refine ⟨by split <;> rfl, ?_⟩
    simp only [Step.execQuery, Step.admit, hin', Bool.false_eq_true, ite_false]
    simp only [QueryOut.Rel, QueryOut.invalid, hok, hin', Val.toBool]
    rfl

end

end Tazuna.Smt
