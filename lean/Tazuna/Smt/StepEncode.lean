import Tazuna.Smt.State

/-! T2, the step encoding: for each step kind, terms for the next state and the outcome, computed from the symbolic
state and input by the codes of the service's functions, with a condition that holds when no collection outgrew its
slots. `query_step` proves the query kind: in every model where the condition holds and whose state and input terms
denote a state and an input, the outcome terms denote the outcome `step` computes, and the state stays. The
transition is a function of the state and input, so one statement gives both directions: a model's decoded state
and input step to the outcome its terms denote (a decoded counterexample is a real step), and every concrete state
and input are some model's (`decode_embedState`), so a script with no model has no step that breaks it.

The codes of a definition's functions come with the hypothesis that they relate to the functions (`Rel`), which
`encode_agrees` (T1) gives when they are the encodings of the functions' expressions. -/

namespace Tazuna.Smt

open Tazuna.Ir

mutual
/-- The term that writes a value as a constant. -/
def Val.term : Val → Term
  | .int n => .int n
  | .bool b => .bool b
  | .str s => .str s
  | .ctor d k args => .ctor d k (Val.terms args)
def Val.terms : List Val → List Term
  | [] => []
  | w :: ws => w.term :: Val.terms ws
end

mutual
theorem Val.denote_term (M : Model) : (w : Val) → w.term.denote M = w
  | .int _ | .bool _ | .str _ => rfl
  | .ctor d k args => by simp only [Val.term, Term.denote, Val.denotes_terms M args]
theorem Val.denotes_terms (M : Model) : (ws : List Val) → Term.denotes M (Val.terms ws) = ws
  | [] => rfl
  | w :: ws => by simp only [Val.terms, Term.denotes, Val.denote_term M w, Val.denotes_terms M ws]
end

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
  accepts : Smt.Rel M L _ (Ty.up _ hd.accepts q.accepts) qc.accepts
  resolve : Smt.Rel M L _ (Ty.up _ hd.resolve q.resolve) qc.resolve

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

/-- The terms of the rules' names and of whether each holds. -/
def ruleTerms (rs : List Term) : Except Refusal (List (Term × Term)) := do
  let d ← tupleD L [.str, Ty.bool]
  pure (rs.map fun t => (.sel d 0 0 t, .sel d 0 1 t))

/-- A query step's outcome terms and its condition, from the terms of the records, the time, the fresh counter, the
caller and the input, and the constants of the listed callers. The condition asks only for what the step computes:
the rules when the caller is listed, the output when the rules hold too. -/
def encodeQuery {r c : Ty} (q : QueryV r c) (qc : QueryCode q) (callers : List Term)
    (records now fresh caller input : Term) : Except Refusal (QueryOut × Term) := do
  let cc ← need "a caller that has no term" (Code.ofTerm? c caller)
  let eqs ← callers.mapM fun k => do eqCode L c cc (← need "a caller that has no term" (Code.ofTerm? c k))
  let ic ← need "an input that has no term" (Code.ofTerm? q.input input)
  let (rs, c1) ← qc.accepts (ic, ())
  let rules ← ruleTerms L rs
  let ctx ← adtCtor L 5 [r, q.input, c] [[r, q.input, c, .int, .dsl .fresh []]] 0 [records, input, caller, now, fresh]
  let cx ← need "a context that has no term" (Code.ofTerm? (Ty.ctx r q.input c) ctx)
  let (o, c2) ← qc.resolve (cx, ())
  let ot ← need "an output that has no term" (Code.term? q.output o)
  let callerOk := anyT eqs
  pure (⟨callerOk, rules, ot⟩, .ite callerOk (andT c1 (.ite (allT (rules.map (·.2))) c2 tt)) tt)

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

theorem anyT_denote : (ts : List Term) → (anyT ts).denote M = .bool (ts.any fun t => (t.denote M).toBool)
  | [] => rfl
  | t :: ts => by simp [anyT, Term.denote, anyT_denote ts, Val.toBool]

theorem allT_denote : (ts : List Term) → (allT ts).denote M = .bool (ts.all fun t => (t.denote M).toBool)
  | [] => rfl
  | t :: ts => by simp [allT, Term.denote, allT_denote ts, Val.toBool]

theorem brokenIn_nil (rules : List (Term × Term)) :
    brokenIn M rules = [] ↔ (rules.map (·.2)).all (fun t => (t.denote M).toBool) = true := by
  induction rules with
  | nil => simp [brokenIn]
  | cons p rules ih =>
    obtain ⟨n, b⟩ := p
    simp only [brokenIn, List.filterMap_cons, List.map_cons, List.all_cons, Bool.and_eq_true] at ih ⊢
    split <;> simp_all

theorem up_id {t : Ty} (h : t.isData = true) (e : t.den0 = (Ty.semWith Dsl.val t).1) (x : t.den0) :
    Ty.up t h x = cast e x := rfl

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

theorem rules_broken_map {d m : Nat} (hdm : L.find? (.tuple [.str, Ty.bool]) = some (d, m)) : (xs : Ty.rules.den0) →
    (rs : List Term) →
    Forall2 (Smt.Rel M L (.tuple [.str, Ty.bool])) (xs.map (Ty.up (.tuple [.str, Ty.bool]) rfl)) rs →
    brokenIn M (rs.map fun t => (.sel d 0 0 t, .sel d 0 1 t)) = Step.broken xs
  | [], [], _ => rfl
  | [], _ :: _, hx | _ :: _, [], hx => hx.elim
  | (n, b, ()) :: xs, t :: rs, ⟨hxt, hxs⟩ => by
    obtain ⟨d', m', vals, hf, hv, hrel⟩ := hxt
    rw [hdm] at hf; cases hf
    obtain ⟨vn, vs, rfl, hn, vb, vs', rfl, hb, rfl⟩ := hrel
    simp only [RelV] at hn
    obtain ⟨_, hb⟩ := hb
    have ih := rules_broken_map hdm xs rs hxs
    simp only [brokenIn, Step.broken] at ih
    simp only [brokenIn, Step.broken, List.map_cons, List.filterMap_cons]
    rw [ih]
    simp only [Term.denote, hv, hn, hb, and_self, ite_true, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Val.toBool, Val.toStr]
    rcases b with ⟨⟩ | ⟨⟨⟩⟩ | e
    · rfl
    · rfl
    · exact e.elim

/-- The rules' terms: each name and holds term denotes the rule's name and whether it holds. -/
theorem rules_broken {rs : List Term} {rules : List (Term × Term)} (hr : ruleTerms L rs = .ok rules)
    (xs : Ty.rules.den0)
    (hx : Forall2 (Smt.Rel M L (.tuple [.str, Ty.bool])) (xs.map (Ty.up (.tuple [.str, Ty.bool]) rfl)) rs) :
    brokenIn M rules = Step.broken xs := by
  obtain ⟨d, hd, hr⟩ := bind_ok.1 hr
  cases pure_ok.1 hr
  obtain ⟨m, hdm⟩ := tupleD_ok hd
  exact rules_broken_map hdm xs rs hx

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

/-- T2 for a query: wherever the condition holds, the outcome terms denote the outcome of the step from the state
and input the terms denote, and the state stays. -/
theorem query_step {v : ServiceV} (s : State v) (i : Fin v.queries.length) (caller : v.caller.den0)
    (input : (v.queries.get i).input.den0) (hd : QueryData (v.queries.get i)) (qc : QueryCode (v.queries.get i))
    (hq : qc.Rel M L hd) {ks : List Term} (hks : callerTerms L hd.caller (v.queries.get i).callers = some ks)
    {records now fresh sc si : Term}
    (hrec : RelV L v.records (Ty.up _ hd.records s.records) (records.denote M))
    (hnow : now.denote M = .int s.now) (hfresh : fresh.denote M = .int (Int.ofNat s.fresh))
    (hsc : RelV L v.caller (Ty.up _ hd.caller caller) (sc.denote M))
    (hsi : RelV L (v.queries.get i).input (Ty.up _ hd.input input) (si.denote M))
    {o : QueryOut} {cond : Term} (henc : encodeQuery L (v.queries.get i) qc ks records now fresh sc si = .ok (o, cond))
    (hc : Holds M cond) :
    (step v s (.query i caller input)).state = s ∧ o.Rel M L hd.output (step v s (.query i caller input)).outcome := by
  obtain ⟨cc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨eqs, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨rules, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨ctx, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨cx, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨out, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨ot, h9, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hcc : Smt.Rel M L v.caller (Ty.up _ hd.caller caller) cc := (rel_ofTerm (need_ok.1 h1) _).2 hsc
  have hok := callers_any hd.caller hcc (v.queries.get i).callers ks hks eqs h2
  simp only [step]
  refine ⟨by split <;> rfl, ?_⟩
  simp only [Step.admit]
  by_cases hin : (v.queries.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = true
  · simp only [hin, ite_true]
    have hic : Smt.Rel M L (v.queries.get i).input (Ty.up _ hd.input input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
    simp only [Holds, Term.denote, hok, hin, Val.toBool, ite_true] at hc
    have hc' : Holds M (andT c1 (.ite (allT (rules.map (·.2))) c2 tt)) := hc
    rw [holds_andT] at hc'
    have hargs : Smt.Rels M L [(v.queries.get i).input] (Ty.up (.tuple [(v.queries.get i).input]) hd.args (input, ()))
        (ic, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [(v.queries.get i).input]) hd.args (input, ())).1 ic ∧ True
      erw [Ty.up_tuple _ _ _ hd.input rfl]; exact ⟨hic, trivial⟩
    have hacc := hq.accepts _ (ic, ()) hargs rs c1 h4 hc'.1
    erw [Ty.up_fn _ Ty.rules _ hd.args rfl, Ty.up_list _ _ rfl] at hacc
    have hbroken := rules_broken h5 _ hacc
    have hall := (brokenIn_nil (M := M) rules)
    cases hb : Step.broken ((v.queries.get i).accepts (input, ())) with
    | cons n ns =>
      simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken, hb]
    | nil =>
      rw [hb] at hbroken
      have hallT : (allT (rules.map (·.2))).denote M = .bool true := by
        rw [allT_denote]; exact congrArg Val.bool (hall.1 hbroken)
      have hc2 : Holds M c2 := by
        have := hc'.2; simp only [Holds, Term.denote, hallT, Val.toBool, ite_true] at this; exact this
      have hctx := adtCtor_rel (L := L) (M := M) (vs := [[v.records, (v.queries.get i).input, v.caller, .int, .dsl .fresh []]])
        ⟨0, by simp⟩ _ _ h6
        (Ty.up _ hd.records s.records, Ty.up _ hd.input input, Ty.up _ hd.caller caller, s.now, s.fresh, ())
        ⟨_, _, rfl, hrec, _, _, rfl, hsi, _, _, rfl, hsc, _, _, rfl, hnow, _, _, rfl, hfresh, rfl⟩
      rw [← up_ctx hd.records hd.input hd.caller hd.ctx] at hctx
      have hcx : Smt.Rel M L _ (Ty.up _ hd.ctx (Step.ctx s s.records caller input)) cx :=
        (rel_ofTerm (need_ok.1 h7) _).2 hctx
      have hargs' : Smt.Rels M L [Ty.ctx v.records (v.queries.get i).input v.caller]
          (Ty.up (.tuple [Ty.ctx v.records (v.queries.get i).input v.caller]) hd.ctxArgs
            (Step.ctx s s.records caller input, ())) (cx, ()) := by
        show Smt.Rel M L _ (Ty.up (.tuple [Ty.ctx v.records (v.queries.get i).input v.caller]) hd.ctxArgs
          (Step.ctx s s.records caller input, ())).1 cx ∧ True
        erw [Ty.up_tuple _ _ _ hd.ctx rfl]; exact ⟨hcx, trivial⟩
      have hres := hq.resolve _ (cx, ()) hargs' out c2 h8 hc2
      erw [Ty.up_fn _ _ _ hd.ctxArgs hd.output] at hres
      simp only [QueryOut.Rel, QueryOut.invalid, hok, hin, Val.toBool, ite_true, hbroken]
      exact ⟨trivial, trivial, (rel_term (need_ok.1 h9) _).1 hres⟩
  · have hin' : (v.queries.get i).callers.any ((Ty.semWith Dsl.base v.caller).2 caller) = false := by simpa using hin
    simp only [hin', Bool.false_eq_true, ite_false]
    simp only [QueryOut.Rel, QueryOut.invalid, hok, hin', Val.toBool]
    rfl

end

end Tazuna.Smt
