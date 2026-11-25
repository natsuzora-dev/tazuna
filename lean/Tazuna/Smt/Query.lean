import Tazuna.Smt.Admit

/-! The query step: a listed caller's input passes `accepts`, then `resolve` answers at the context, and the state
stays. `query_encode` proves T2 and the exactness of the condition together. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The codes of a query's functions. -/
structure QueryCode {r c : Ty} (q : QueryV r c) where
  accepts : Code (Ty.fn [q.input] Ty.rules)
  resolve : Code (Ty.fn [Ty.ctx r q.input c] q.output)

/-- A query's types are data, as the `query` built-in demands of its type arguments. -/
structure QueryData {r c : Ty} (q : QueryV r c) : Prop where
  records : r.isData = true
  caller : c.isData = true
  input : q.input.isData = true
  output : q.output.isData = true

section
variable {r c : Ty} {q : QueryV r c} (hd : QueryData q)
include hd

theorem QueryData.accepts : (Ty.fn [q.input] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.input]
theorem QueryData.args : (Ty.tuple [q.input]).isData = true := by simp [Ty.isData, Ty.isDatas, hd.input]
theorem QueryData.ctx : (Ty.ctx r q.input c).isData = true := by
  simp [Ty.ctx, Ty.isData, Ty.isDatas, Ty.isDatass, hd.records, hd.input, hd.caller]
theorem QueryData.resolve : (Ty.fn [Ty.ctx r q.input c] q.output).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx, hd.output]
theorem QueryData.ctxArgs : (Ty.tuple [Ty.ctx r q.input c]).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx]

end

/-- The codes relate to the query's functions in the model. -/
structure QueryCode.Rel (M : Model) (L : Layout) {r c : Ty} {q : QueryV r c} (hd : QueryData q) (qc : QueryCode q) :
    Prop where
  accepts : Smt.Rel M L _ (Ty.up _ hd.accepts q.accepts.fn) qc.accepts
  resolve : Smt.Rel M L _ (Ty.up _ hd.resolve q.resolve.fn) qc.resolve

/-- A query's codes, from the sources it keeps, with their condition. -/
def QueryCode.of (L : Layout) {r c : Ty} (q : QueryV r c) : Except Refusal (QueryCode q × Term) := do
  let (a, c1) ← q.accepts.code L
  let (x, c2) ← q.resolve.code L
  pure (⟨a, x⟩, andT c1 c2)

theorem QueryCode.rel_of {M : Model} {L : Layout} {r c : Ty} {q : QueryV r c} (hd : QueryData q) {qc : QueryCode q}
    {cq : Term} (h : QueryCode.of L q = .ok (qc, cq)) (hc : Holds M cq) : qc.Rel M L hd := by
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

/-- A query step's outcome terms and its condition, from the terms of the records, the time, the fresh counter, the
caller and the input, and the constants of the listed callers. The condition asks only for what the step computes:
the rules when the caller is listed, the output when the rules hold too. -/
def encodeQuery {r c : Ty} (q : QueryV r c) (qc : QueryCode q) (callers : List Term)
    (records now fresh caller input : Term) : Except Refusal (QueryOut × Term) := do
  let (a, c1) ← encodeAdmit L qc.accepts callers records now fresh caller input
  let (o, c2) ← qc.resolve (a.ctx, ())
  let ot ← need "an output that has no term" (Code.term? q.output o)
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

/-- Whether what a query step applies fits: for a listed caller, `accepts` at the input and, where its rules hold,
`resolve` at the context. -/
def queryFits (S : Ty → Nat) {v : ServiceV} (s : State v) (q : QueryV v.records v.caller) (caller : v.caller.den0)
    (input : q.input.den0) : Prop :=
  q.callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true →
    q.accepts.appFits S (input, ()) ∧
      (Step.broken (q.accepts.fn (input, ())) = [] → q.resolve.appFits S (Step.ctx s s.records caller input, ()))

/-- A query step's condition is exact and gives T2: where the codes' condition holds, the condition holds exactly
when what the step applies fits (`queryFits`), and wherever it holds the outcome terms denote the step's outcome and
the state stays. -/
theorem query_encode {v : ServiceV} (s : State v) (i : Fin v.queries.length) (caller : v.caller.den0)
    (input : (v.queries.get i).input.den0) (hd : QueryData (v.queries.get i)) {qc : QueryCode (v.queries.get i)}
    {cq : Term} (hqc : QueryCode.of L _ = .ok (qc, cq)) (hcq : Holds M cq) {ks : List Term}
    (hks : callerTerms L hd.caller (v.queries.get i).callers = some ks) {records now fresh sc si : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L (v.queries.get i).input (Ty.up _ hd.input input) (si.denote M))
    {o : QueryOut} {cond : Term} (henc : encodeQuery L (v.queries.get i) qc ks records now fresh sc si = .ok (o, cond)) :
    (Holds M cond ↔ queryFits L.count s (v.queries.get i) caller input) ∧
    (Holds M cond → (step T v s (.query i caller input)).state = s ∧
      o.Rel M L hd.output (step T v s (.query i caller input)).outcome) := by
  have hq := QueryCode.rel_of hd hqc hcq
  obtain ⟨⟨a, ca1⟩, g1, hqc'⟩ := bind_ok.1 hqc
  obtain ⟨⟨x, ca2⟩, g2, hqc'⟩ := bind_ok.1 hqc'
  cases pure_ok.1 hqc'
  obtain ⟨hca1, hca2⟩ := (holds_andT _ _).1 hcq
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨ot, h9, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hok, hbr, hcx⟩ := admit_rel hd.records hd.input hd.caller hd.ctx _ hd.accepts hq.accepts _ hks s caller input
    hrec hnow hfresh hsc hsi h1
  have e1 := admit_exact hd.input (v.queries.get i).accepts g1 hca1 input hsi h1
  have e2 : Holds M c2 ↔ (v.queries.get i).resolve.appFits L.count (Step.ctx s s.records caller input, ()) :=
    (v.queries.get i).resolve.app_exact g2 hca2 (by simp [Ty.ctx, Ty.isFn]) _ _ (rels1 hd.ctx hd.ctxArgs hcx) h8
  have hrules : ∀ hc1 : Holds M c1, ((allT (adm.rules.map (·.2))).denote M).toBool =
      decide (Step.broken ((v.queries.get i).accepts.fn (input, ())) = []) := fun hc1 => by
    rw [toBool_allT_rules, hbr hc1]
  by_cases hin : (v.queries.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true
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
        have hres := hq.resolve _ (adm.ctx, ()) (rels1 hd.ctx hd.ctxArgs hcx) out c2 h8 hc2'
        erw [Ty.up_fn _ _ _ hd.ctxArgs hd.output] at hres
        simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken]
        exact ⟨trivial, trivial, (rel_term (need_ok.1 h9) _).1 hres⟩
  · have hin' : (v.queries.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = false := by simpa using hin
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
