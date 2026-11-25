import Tazuna.Smt.Kept
import Tazuna.Smt.State

/-! T2, the step encoding: for each step kind, terms for the next state and the outcome, computed from the symbolic
state and input by the codes of the service's functions, with a condition that holds when no collection outgrew its
slots. `query_step` proves the query kind: in every model where the condition holds and whose state and input terms
denote a state and an input, the outcome terms denote the outcome `step` computes, and the state stays. The
transition is a function of the state and input, so one statement gives both directions: a model's decoded state
and input step to the outcome its terms denote (a decoded counterexample is a real step), and every concrete state
and input are some model's (`decode_embedState`), so a script with no model has no step that breaks it.

The codes of a definition's functions are the codes of the sources its structure value keeps (`QueryCode.of` and
the like), so each theorem rests on `Fun.code_rel` (T1 at those sources), not on an assumed relation. -/

namespace Tazuna.Smt

variable {T : List Ir.TypeDecl}

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

/-- The terms of a query step's outcome: whether the caller is one the query lists, each `accepts` rule's name and
whether it holds, and the output. -/
structure QueryOut where
  callerOk : Term
  rules : List (Term × Term)
  output : Term

section
variable (L : Layout)

/-- The constants of the callers a definition lists. -/
def callerTerms {c : Ty} (hc : c.isData = true) (callers : List c.den0) : Option (List Term) :=
  callers.mapM fun x => (embedV L c (Ty.up c hc x)).map Val.term

/-- The terms of the rules' names and of whether each holds, one per slot of the rules' list: a free slot's rule
holds, so it is never broken. -/
def ruleTerms (rs : Term) : Except Refusal (List (Term × Term)) := do
  let (dl, n, dt) ← collD L Ty.rules [.tuple [.str, Ty.bool]]
  let d ← tupleD L [.str, Ty.bool]
  pure ((slotsOf dl dt n 1 rs).map fun sl =>
    (.sel d 0 0 (sl.2.headD tt), .or (.not sl.1) (.sel d 0 1 (sl.2.headD tt))))

/-- The terms of a request's admission, which commands and queries share: whether the caller is listed, the `accepts`
rules, and the context their functions read. -/
structure AdmitOut (r i c : Ty) where
  callerOk : Term
  rules : List (Term × Term)
  ctx : Code (Ty.ctx r i c)

/-- A request's admission terms and `accepts`' condition, from its code, the constants of the listed callers, and the
terms of the records, the time, the fresh counter, the caller and the input. -/
def encodeAdmit {r i c : Ty} (accepts : Code (Ty.fn [i] Ty.rules)) (callers : List Term)
    (records now fresh caller input : Term) : Except Refusal (AdmitOut r i c × Term) := do
  let cc ← need "a caller that has no term" (Code.ofTerm? c caller)
  let eqs ← callers.mapM fun k => do eqCode L c cc (← need "a caller that has no term" (Code.ofTerm? c k))
  let ic ← need "an input that has no term" (Code.ofTerm? i input)
  let (rs, c1) ← accepts (ic, ())
  let rules ← ruleTerms L rs
  let ctx ← adtCtor L 5 [r, i, c] [[r, i, c, .int, .dsl .fresh []]] 0 [records, input, caller, now, fresh]
  let cx ← need "a context that has no term" (Code.ofTerm? (Ty.ctx r i c) (Term.share ctx))
  pure (⟨anyT eqs, rules, cx⟩, c1)

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

/-- The names of the rules that do not hold in the model. -/
def brokenIn (M : Model) (rules : List (Term × Term)) : List String :=
  rules.filterMap fun (n, b) => if (b.denote M).toBool then none else some (n.denote M).toStr

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
variable {M : Model} {L : Layout}

theorem brokenIn_nil (rules : List (Term × Term)) :
    brokenIn M rules = [] ↔ (rules.map (·.2)).all (fun t => (t.denote M).toBool) = true := by
  induction rules with
  | nil => simp [brokenIn]
  | cons p rules ih =>
    obtain ⟨n, b⟩ := p
    simp only [brokenIn, List.filterMap_cons, List.map_cons, List.all_cons, Bool.and_eq_true] at ih ⊢
    split <;> simp_all

/-- The rules' conjunction holds exactly when none is broken. -/
theorem allT_rules (rules : List (Term × Term)) :
    (allT (rules.map (·.2))).denote M = .bool (brokenIn M rules).isEmpty := by
  rw [allT_denote]
  congr 1
  cases h : brokenIn M rules with
  | nil => exact (brokenIn_nil rules).1 h
  | cons n ns =>
    have : ¬ (rules.map (·.2)).all (fun t => (t.denote M).toBool) = true := fun h' => by
      rw [(brokenIn_nil rules).2 h'] at h; cases h
    simpa using this

theorem toBool_allT_rules (rules : List (Term × Term)) :
    ((allT (rules.map (·.2))).denote M).toBool = decide (brokenIn M rules = []) := by
  rw [allT_rules]; cases brokenIn M rules <;> rfl

/-- The callers' test: an equality term per listed caller, any of which holds when the caller is listed. -/
theorem callers_any {c : Ty} (hc : c.isData = true) {caller : c.den0} {cc : Code c}
    (hcc : Smt.Rel M L c (Ty.up c hc caller) cc) : (callers : List c.den0) → (ks : List Term) →
    callerTerms L hc callers = some ks → (eqs : List Term) →
    ks.mapM (fun k => do eqCode L c cc (← need "a caller that has no term" (Code.ofTerm? c k))) = .ok eqs →
    (anyT eqs).denote M = .bool (callers.any ((Ty.semWith Dsl.base c).2 caller))
  | [], ks, hk, eqs, he => by
    simp only [callerTerms, List.mapM_nil, Option.pure_def, Option.some.injEq] at hk; subst hk
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at he; subst he; rfl
  | x :: xs, ks, hk, eqs, he => by
    simp only [callerTerms, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hk
    obtain ⟨k, hk1, ks', hks, rfl⟩ := hk
    obtain ⟨w, hw, rfl⟩ := map_some.1 hk1
    rw [List.mapM_cons] at he
    obtain ⟨e, he1, he⟩ := bind_ok.1 he
    obtain ⟨es, he2, he⟩ := bind_ok.1 he
    cases pure_ok.1 he
    obtain ⟨kc, hkc, he1⟩ := bind_ok.1 he1
    have hkc' := need_ok.1 hkc
    have hxk : Smt.Rel M L c (Ty.up c hc x) kc := (rel_ofTerm hkc' _).2 (by rw [Val.denote_term]; exact embed_rel _ _ _ hw)
    have heq := eqCode_rel hcc hxk he1
    rw [show Ty.deq c (Ty.up c hc caller) (Ty.up c hc x) = _ from Ty.deq_up c hc caller x] at heq
    have ih := callers_any hc hcc xs ks' hks es he2
    simp only [anyT, Term.denote, heq, ih, Val.toBool, List.any_cons]

theorem rules_broken_map {d m : Nat} (hdm : L.find? (.tuple [.str, Ty.bool]) = some (d, m)) :
    (S : List Slot) → (sv : List (Bool × List Val)) → SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 1) →
    (xs : Ty.rules.den0) → Holds2 (EBag L (.tuple [.str, Ty.bool])) (xs.map (Ty.up (.tuple [.str, Ty.bool]) rfl)) sv →
    brokenIn M (S.map fun sl => (.sel d 0 0 (sl.2.headD tt), .or (.not sl.1) (.sel d 0 1 (sl.2.headD tt)))) =
      Step.broken xs
  | [], [], _, _, xs, hx => by
    cases xs with
    | nil => rfl
    | cons _ _ => exact hx.elim
  | (f, ys) :: S, (b, vs) :: sv, ⟨hf, hys, hS⟩, hw, xs, hx => by
    have hw' : ∀ p ∈ sv, p.2.length = 1 := fun p hp => hw p (by simp [hp])
    cases b with
    | false =>
      have ih := rules_broken_map hdm S sv hS hw' xs (by simpa [Holds2, occupied] using hx)
      simp only [brokenIn, List.map_cons, List.filterMap_cons] at ih ⊢
      rw [← ih]
      simp [Term.denote, hf, Val.toBool]
    | true =>
      match xs, hx with
      | (n, bb, ()) :: xs, ⟨⟨z, hz, hxt⟩, hxs⟩ =>
        subst hz
        have hl := hw (true, [z]) (by simp)
        obtain ⟨y0, rfl, hy0⟩ : ∃ y0, ys = [y0] ∧ y0.denote M = z := by
          match ys, hys with
          | [y0], h => exact ⟨y0, rfl, by simpa [Term.denotes] using h⟩
        have ih := rules_broken_map hdm S sv hS hw' xs hxs
        obtain ⟨d', m', vals, hf', hv, hrel⟩ := hxt
        rw [hdm] at hf'; cases hf'
        obtain ⟨vn, vs, rfl, hn, vb, vs', rfl, hb, rfl⟩ := hrel
        simp only [RelV] at hn
        obtain ⟨_, hb⟩ := hb
        simp only [brokenIn, Step.broken] at ih
        simp only [brokenIn, Step.broken, List.map_cons, List.filterMap_cons]
        rw [ih]
        simp only [List.headD_cons, Term.denote, hf, hy0, hv, hn, hb, and_self, ite_true, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, Val.toBool, Val.toStr, Bool.not_true, Bool.false_or]
        rcases bb with ⟨⟩ | ⟨⟨⟩⟩ | e
        · rfl
        · rfl
        · exact e.elim
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => h.elim

/-- The rules' terms: each name and holds term denotes the rule's name and whether it holds. -/
theorem rules_broken {rs : Term} {rules : List (Term × Term)} (hr : ruleTerms L rs = .ok rules)
    (xs : Ty.rules.den0) (hx : Smt.Rel M L Ty.rules (Ty.up Ty.rules rfl xs) rs) :
    brokenIn M rules = Step.broken xs := by
  obtain ⟨⟨dl, n, dt⟩, hc, hr⟩ := bind_ok.1 hr
  obtain ⟨d, hd, hr⟩ := bind_ok.1 hr
  cases pure_ok.1 hr
  obtain ⟨m, hdm⟩ := tupleD_ok hd
  obtain ⟨sv, hS, -, hw, hh⟩ := list_view hx hc
  erw [Ty.up_list _ _ rfl] at hh
  exact rules_broken_map hdm _ sv hS hw xs hh

/-- The context a step builds for a query or command, read at the level codes relate to. -/
theorem up_ctx {v : ServiceV} {r i c : Ty} (hr : r.isData = true) (hi : i.isData = true) (hc : c.isData = true)
    (h : (Ty.ctx r i c).isData = true) (s : State v) (records : r.den0) (caller : c.den0) (input : i.den0) :
    Ty.up _ h (Step.ctx s records caller input) =
      Alts.inj (vs := [[r, i, c, .int, .dsl .fresh []]]) ⟨0, by simp⟩
        (Ty.up r hr records, Ty.up i hi input, Ty.up c hc caller, s.now, s.fresh, ()) := by
  unfold Step.ctx
  refine (Ty.up_inl 5 [r, i, c] [r, i, c, .int, .dsl .fresh []] [] h
    (by simp [Ty.isData, Ty.isDatas, hr, hi, hc]) _).trans ?_
  show Sum.inl _ = Sum.inl _
  congr 1
  refine (Ty.up_tuple _ _ _ hr (by simp [Ty.isData, Ty.isDatas, hi, hc]) _).trans (congrArg _ ?_)
  refine (Ty.up_tuple _ _ _ hi (by simp [Ty.isData, Ty.isDatas, hc]) _).trans (congrArg _ ?_)
  refine (Ty.up_tuple _ _ _ hc (by simp [Ty.isData, Ty.isDatas]) _).trans (congrArg _ ?_)
  refine (Ty.up_tuple _ _ _ rfl (by simp [Ty.isData, Ty.isDatas]) _).trans (congrArg _ ?_)
  exact (Ty.up_tuple _ _ _ (by simp [Ty.isData]) rfl _)

theorem rels1 {a : Ty} (ha : a.isData = true) (h : (Ty.tuple [a]).isData = true) {x : a.den0} {cx : Code a}
    (hx : Smt.Rel M L a (Ty.up a ha x) cx) : Smt.Rels M L [a] (Ty.up (.tuple [a]) h (x, ())) (cx, ()) := by
  show Smt.Rel M L _ (Ty.up (.tuple [a]) h (x, ())).1 cx ∧ True
  erw [Ty.up_tuple _ _ _ ha rfl]; exact ⟨hx, trivial⟩

/-- What a request's admission terms say: whether the caller is listed, the rules `accepts` breaks wherever its
condition holds, and the context at the state the terms denote. -/
theorem admit_rel {v : ServiceV} {i : Ty} (hr : v.records.isData = true) (hi : i.isData = true)
    (hc : v.caller.isData = true) (hctx : (Ty.ctx v.records i v.caller).isData = true)
    (accepts : Fun (Ty.fn [i] Ty.rules)) (hA : (Ty.fn [i] Ty.rules).isData = true) {ac : Code (Ty.fn [i] Ty.rules)}
    (hac : Smt.Rel M L _ (Ty.up _ hA accepts.fn) ac) (callers : List v.caller.den0) {ks : List Term}
    (hks : callerTerms L hc callers = some ks) (s : State v) (caller : v.caller.den0) (input : i.den0)
    {records now fresh sc si : Term} (hrec : RelV L v.records (Ty.up _ hr s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hsc : RelV L v.caller (Ty.up _ hc caller) (sc.denote M)) (hsi : RelV L i (Ty.up _ hi input) (si.denote M))
    {a : AdmitOut v.records i v.caller} {c1 : Term} (henc : encodeAdmit L ac ks records now fresh sc si = .ok (a, c1)) :
    a.callerOk.denote M = .bool (callers.any ((Ty.semWith Dsl.base v.caller).2 caller)) ∧
      (Holds M c1 → brokenIn M a.rules = Step.broken (accepts.fn (input, ()))) ∧
      Smt.Rel M L _ (Ty.up _ hctx (Step.ctx s s.records caller input)) a.ctx := by
  obtain ⟨cc0, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1'⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cx, h7, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc0 : Smt.Rel M L v.caller (Ty.up _ hc caller) cc0 := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  refine ⟨callers_any hc hcc0 callers ks hks eqs h2, fun hc1 => ?_, ?_⟩
  · have hic : Smt.Rel M L _ (Ty.up _ hi input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
    have hargs : (Ty.tuple [i]).isData = true := by simp [Ty.isData, Ty.isDatas, hi]
    have hacc := hac _ (ic, ()) (rels1 hi hargs hic) rs c1 h4 hc1
    erw [Ty.up_fn _ Ty.rules _ hargs rfl] at hacc
    exact rules_broken h5 _ hacc
  · have hctxT := adtCtor_rel (L := L) (M := M) (vs := [[v.records, i, v.caller, .int, .dsl .fresh []]])
      ⟨0, by simp⟩ _ _ h6
      (Ty.up _ hr s.records, Ty.up _ hi input, Ty.up _ hc caller, s.now, s.fresh, ())
      ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
    rw [← up_ctx hr hi hc hctx] at hctxT
    exact (rel_ofTerm (need_ok.1 h7) _).2 (by rw [Term.denote_share]; exact hctxT)

/-- T2 for a query: wherever the condition holds, the outcome terms denote the outcome of the step from the state
and input the terms denote, and the state stays. -/
theorem query_step {v : ServiceV} (s : State v) (i : Fin v.queries.length) (caller : v.caller.den0)
    (input : (v.queries.get i).input.den0) (hd : QueryData (v.queries.get i)) {qc : QueryCode (v.queries.get i)}
    {cq : Term} (hqc : QueryCode.of L _ = .ok (qc, cq)) (hcq : Holds M cq) {ks : List Term} (hks : callerTerms L hd.caller (v.queries.get i).callers = some ks)
    {records now fresh sc si : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L (v.queries.get i).input (Ty.up _ hd.input input) (si.denote M))
    {o : QueryOut} {cond : Term} (henc : encodeQuery L (v.queries.get i) qc ks records now fresh sc si = .ok (o, cond))
    (hc : Holds M cond) :
    (step T v s (.query i caller input)).state = s ∧ o.Rel M L hd.output (step T v s (.query i caller input)).outcome := by
  have hq := QueryCode.rel_of hd hqc hcq
  obtain ⟨⟨adm, c1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨ot, h9, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  obtain ⟨hok, hbr, hcx⟩ := admit_rel hd.records hd.input hd.caller hd.ctx _ hd.accepts hq.accepts _ hks s caller input
    hrec hnow hfresh hsc hsi h1
  simp only [step]
  refine ⟨by split <;> rfl, ?_⟩
  simp only [Step.execQuery, Step.admit]
  by_cases hin : (v.queries.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true
  · simp only [hin, ite_true]
    simp only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] at hc
    have hc' : Holds M (andT c1 (.ite (allT (adm.rules.map (·.2))) c2 tt)) := hc
    rw [holds_andT] at hc'
    have hbroken := hbr hc'.1
    cases hb : Step.broken ((v.queries.get i).accepts.fn (input, ())) with
    | cons n ns =>
      simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken, hb]
    | nil =>
      rw [hb] at hbroken
      have hallT : (allT (adm.rules.map (·.2))).denote M = .bool true := by
        rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil adm.rules).1 hbroken)
      have hc2 : Holds M c2 := by
        have := hc'.2; simp only [Holds, Term.denote, hallT, Val.toBool, ite_true] at this; exact this
      have hres := hq.resolve _ (adm.ctx, ()) (rels1 hd.ctx hd.ctxArgs hcx) out c2 h8 hc2
      erw [Ty.up_fn _ _ _ hd.ctxArgs hd.output] at hres
      simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken]
      exact ⟨trivial, trivial, (rel_term (need_ok.1 h9) _).1 hres⟩
  · have hin' : (v.queries.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = false := by simpa using hin
    simp only [hin', Bool.false_eq_true, ite_false]
    simp only [QueryOut.Rel, QueryOut.invalid, hok, hin', Val.toBool]
    rfl

end

/-! The event kind's service part: the subscription wraps the value into an event, the records apply it, and the
service's invariants are checked on the result. `EventStep` adds the machines. -/

/-- The codes of the functions an event step reads. -/
structure EventCode (v : ServiceV) (i : Fin v.subscribes.length) where
  apply : Code (Ty.fn [v.records, v.event] v.records)
  wrap : Code (Ty.fn [(v.subscribes.get i).event] v.event)
  invariants : Code (Ty.fn [v.records] Ty.rules)

/-- An event step's types are data, as the `service` and `subscription` built-ins demand. -/
structure EventData (v : ServiceV) (i : Fin v.subscribes.length) : Prop where
  records : v.records.isData = true
  event : v.event.isData = true
  value : (v.subscribes.get i).event.isData = true

section
variable {v : ServiceV} {i : Fin v.subscribes.length} (hd : EventData v i)
include hd

theorem EventData.apply : (Ty.fn [v.records, v.event] v.records).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.records, hd.event]
theorem EventData.wrap : (Ty.fn [(v.subscribes.get i).event] v.event).isData = true := by
  simp only [Ty.isData, Ty.isDatas, hd.value, hd.event, Bool.and_self]
theorem EventData.wrapArgs : (Ty.tuple [(v.subscribes.get i).event]).isData = true := by
  simp only [Ty.isData, Ty.isDatas, hd.value, Bool.and_self]
theorem EventData.invariants : (Ty.fn [v.records] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.records]

end

/-- The codes relate to the service's and the subscription's functions in the model. -/
structure EventCode.Rel (M : Model) (L : Layout) {v : ServiceV} {i : Fin v.subscribes.length} (hd : EventData v i)
    (ec : EventCode v i) : Prop where
  apply : Smt.Rel M L _ (Ty.up _ hd.apply v.apply.fn) ec.apply
  wrap : Smt.Rel M L _ (Ty.up _ hd.wrap (v.subscribes.get i).wrap.fn) ec.wrap
  invariants : Smt.Rel M L _ (Ty.up _ hd.invariants v.invariants.fn) ec.invariants

/-- An event step's codes, from the sources the service and the subscription keep, with their condition. -/
def EventCode.of (L : Layout) (v : ServiceV) (i : Fin v.subscribes.length) : Except Refusal (EventCode v i × Term) := do
  let (a, c1) ← v.apply.code L
  let (w, c2) ← (v.subscribes.get i).wrap.code L
  let (n, c3) ← v.invariants.code L
  pure (⟨a, w, n⟩, andT c1 (andT c2 c3))

theorem EventCode.rel_of {M : Model} {L : Layout} {v : ServiceV} {i : Fin v.subscribes.length} (hd : EventData v i)
    {ec : EventCode v i} {ce : Term} (h : EventCode.of L v i = .ok (ec, ce)) (hc : Holds M ce) : ec.Rel M L hd := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨w, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hc := (holds_andT _ _).1 hc
  have hc' := (holds_andT _ _).1 hc.2
  exact ⟨v.apply.code_fn _ h1 hc.1, (v.subscribes.get i).wrap.code_fn _ h2 hc'.1, v.invariants.code_fn _ h3 hc'.2⟩

/-! A command's codes and the facts its data types give. `Tazuna.Smt.CommandStep` encodes the command kind. -/

/-- The codes of a command's functions. -/
structure CommandCode {r e c : Ty} (x : CommandV r e c) where
  accepts : Code (Ty.fn [x.input] Ty.rules)
  decide : Code (Ty.fn [Ty.ctx r x.input c] (Ty.result (.list e) x.rejection))
  ensures : Code (Ty.fn [Ty.ctx r x.input c, r] Ty.rules)

/-- A command's types are data, as the `command` built-in demands of its type arguments. -/
structure CommandData {r e c : Ty} (x : CommandV r e c) : Prop where
  records : r.isData = true
  event : e.isData = true
  caller : c.isData = true
  input : x.input.isData = true
  rejection : x.rejection.isData = true

section
variable {r e c : Ty} {x : CommandV r e c} (hd : CommandData x)
include hd

theorem CommandData.accepts : (Ty.fn [x.input] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.input]
theorem CommandData.args : (Ty.tuple [x.input]).isData = true := by simp [Ty.isData, Ty.isDatas, hd.input]
theorem CommandData.ctx : (Ty.ctx r x.input c).isData = true := by
  simp [Ty.ctx, Ty.isData, Ty.isDatas, Ty.isDatass, hd.records, hd.input, hd.caller]
theorem CommandData.ctxArgs : (Ty.tuple [Ty.ctx r x.input c]).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx]
theorem CommandData.events : (Ty.list e).isData = true := by simp [Ty.isData, hd.event]
theorem CommandData.result : (Ty.result (.list e) x.rejection).isData = true := by
  simp [Ty.result, Ty.isData, Ty.isDatas, Ty.isDatass, hd.event, hd.rejection]
theorem CommandData.decide : (Ty.fn [Ty.ctx r x.input c] (Ty.result (.list e) x.rejection)).isData = true := by
  simp only [Ty.isData, Ty.isDatas, hd.ctx, hd.result, Bool.and_self]
theorem CommandData.ensures : (Ty.fn [Ty.ctx r x.input c, r] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.ctx, hd.records]
theorem CommandData.ensArgs : (Ty.tuple [Ty.ctx r x.input c, r]).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx, hd.records]
theorem CommandData.apply : (Ty.fn [r, e] r).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.records, hd.event]
theorem CommandData.invariants : (Ty.fn [r] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.records]

end

/-- The codes relate to the command's functions in the model. -/
structure CommandCode.Rel (M : Model) (L : Layout) {r e c : Ty} {x : CommandV r e c} (hd : CommandData x)
    (cc : CommandCode x) : Prop where
  accepts : Smt.Rel M L _ (Ty.up _ hd.accepts x.accepts.fn) cc.accepts
  decide : Smt.Rel M L _ (Ty.up _ hd.decide x.decide.fn) cc.decide
  ensures : Smt.Rel M L _ (Ty.up _ hd.ensures x.ensures.fn) cc.ensures

/-- A command's codes, from the sources it keeps, with their condition. -/
def CommandCode.of (L : Layout) {r e c : Ty} (x : CommandV r e c) : Except Refusal (CommandCode x × Term) := do
  let (a, c1) ← x.accepts.code L
  let (d, c2) ← x.decide.code L
  let (n, c3) ← x.ensures.code L
  pure (⟨a, d, n⟩, andT c1 (andT c2 c3))

theorem CommandCode.rel_of {M : Model} {L : Layout} {r e c : Ty} {x : CommandV r e c} (hd : CommandData x)
    {cc : CommandCode x} {cx : Term} (h : CommandCode.of L x = .ok (cc, cx)) (hc : Holds M cx) : cc.Rel M L hd := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨d, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hc := (holds_andT _ _).1 hc
  have hc' := (holds_andT _ _).1 hc.2
  exact ⟨x.accepts.code_fn _ h1 hc.1, x.decide.code_fn _ h2 hc'.1, x.ensures.code_fn _ h3 hc'.2⟩

end Tazuna.Smt
