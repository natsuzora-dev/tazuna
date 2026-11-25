import Tazuna.Smt.EncodeExact
import Tazuna.Smt.State

/-! A request's admission, which commands and queries share before they differ: whether the caller is listed, the
`accepts` rules' terms, and the context their functions read (`encodeAdmit`, `admit_rel`, `admit_exact`), with the
rules' terms every step kind reads (`ruleTerms`, `brokenIn`). -/

namespace Tazuna.Smt

variable {T : List Ir.TypeDecl}

open Tazuna.Ir

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
    (.sel d 0 0 sl.2[0], .or (.not sl.1) (.sel d 0 1 sl.2[0])))

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

end

/-- The names of the rules that do not hold in the model. -/
def brokenIn (M : Model) (rules : List (Term × Term)) : List String :=
  rules.filterMap fun (n, b) => if (b.denote M).toBool then none else some (n.denote M).toStr

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
    (S : List (Slot 1)) → (sv : List (Bool × List Val)) → SlotsDen M S sv →
    (xs : Ty.rules.den0) → Holds2 (EBag L (.tuple [.str, Ty.bool])) (xs.map (Ty.up (.tuple [.str, Ty.bool]) rfl)) sv →
    brokenIn M (S.map fun sl => (.sel d 0 0 sl.2[0], .or (.not sl.1) (.sel d 0 1 sl.2[0]))) =
      Step.broken xs
  | [], [], _, xs, hx => by
    cases xs with
    | nil => rfl
    | cons _ _ => exact hx.elim
  | (f, ys) :: S, (b, vs) :: sv, ⟨hf, hys, hS⟩, xs, hx => by
    obtain ⟨y0, rfl⟩ := ys.one
    cases b with
    | false =>
      have ih := rules_broken_map hdm S sv hS xs (by simpa [Holds2, occupied] using hx)
      simp only [brokenIn, List.map_cons, List.filterMap_cons] at ih ⊢
      rw [← ih]
      simp [Term.denote, hf, Val.toBool]
    | true =>
      match xs, hx with
      | (n, bb, ()) :: xs, ⟨⟨z, hz, hxt⟩, hxs⟩ =>
        subst hz
        have hy0 : y0.denote M = z := by simpa [Term.denotes] using hys
        have ih := rules_broken_map hdm S sv hS xs hxs
        obtain ⟨d', m', vals, hf', hv, hrel⟩ := hxt
        rw [hdm] at hf'; cases hf'
        obtain ⟨vn, vs, rfl, hn, vb, vs', rfl, hb, rfl⟩ := hrel
        simp only [RelV] at hn
        obtain ⟨_, hb⟩ := hb
        simp only [brokenIn, Step.broken] at ih
        simp only [brokenIn, Step.broken, List.map_cons, List.filterMap_cons]
        rw [ih]
        simp only [SlotItems.getElem_mk, List.getElem_cons_zero, Term.denote, hf, hy0, hv, hn, hb, and_self, ite_true, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, Val.toBool, Val.toStr, Bool.not_true, Bool.false_or]
        rcases bb with ⟨⟩ | ⟨⟨⟩⟩ | e
        · rfl
        · rfl
        · exact e.elim
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- The rules' terms: each name and holds term denotes the rule's name and whether it holds. -/
theorem rules_broken {rs : Term} {rules : List (Term × Term)} (hr : ruleTerms L rs = .ok rules)
    (xs : Ty.rules.den0) (hx : Smt.Rel M L Ty.rules (Ty.up Ty.rules rfl xs) rs) :
    brokenIn M rules = Step.broken xs := by
  obtain ⟨⟨dl, n, dt⟩, hc, hr⟩ := bind_ok.1 hr
  obtain ⟨d, hd, hr⟩ := bind_ok.1 hr
  cases pure_ok.1 hr
  obtain ⟨m, hdm⟩ := tupleD_ok hd
  obtain ⟨sv, hS, -, -, hh⟩ := list_view hx hc
  erw [Ty.up_list _ _ rfl] at hh
  exact rules_broken_map hdm _ sv hS xs hh

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

end

section
variable {M : Model} {L : Layout}

theorem up_app2 {r e : Ty} (hr : r.isData = true) (he : e.isData = true) (h : (Ty.fn [r, e] r).isData = true)
    (g : (Ty.fn [r, e] r).den0) (x : r.den0) (ev : e.den0) :
    (Ty.up _ h g) (Ty.up r hr x, Ty.up e he ev, ()) = Ty.up r hr (g (x, ev, ())) := by
  have hargs : (Ty.tuple [r, e]).isData = true := by simp [Ty.isData, Ty.isDatas, hr, he]
  have := Ty.up_fn [r, e] r h hargs hr g (x, ev, ())
  erw [Ty.up_tuple _ _ _ hr (by simp [Ty.isData, Ty.isDatas, he]), Ty.up_tuple _ _ _ he rfl] at this
  exact this

theorem rels2 {a b : Ty} (ha : a.isData = true) (hb : b.isData = true) (h : (Ty.tuple [a, b]).isData = true)
    {x : a.den0} {y : b.den0} {cx : Code a} {cy : Code b} (hx : Smt.Rel M L a (Ty.up a ha x) cx)
    (hy : Smt.Rel M L b (Ty.up b hb y) cy) : Smt.Rels M L [a, b] (Ty.up (.tuple [a, b]) h (x, y, ())) (cx, cy, ()) := by
  show Smt.Rel M L _ (Ty.up (.tuple [a, b]) h (x, y, ())).1 cx ∧
    Smt.Rels M L [b] (Ty.up (.tuple [a, b]) h (x, y, ())).2 (cy, ())
  erw [Ty.up_tuple _ _ _ ha (by simp [Ty.isData, Ty.isDatas, hb])]
  refine ⟨hx, ?_⟩
  show Smt.Rel M L _ (Ty.up (.tuple [b]) (by simp [Ty.isData, Ty.isDatas, hb]) (y, ())).1 cy ∧ True
  erw [Ty.up_tuple _ _ _ hb rfl]; exact ⟨hy, trivial⟩

/-- `accepts`' condition in a request's admission is exact. -/
theorem admit_exact {r i c : Ty} (hi : i.isData = true) (accepts : Fun (Ty.fn [i] Ty.rules))
    {ac : Code (Ty.fn [i] Ty.rules)} {ca : Term} (hcode : accepts.code L = .ok (ac, ca)) (hca : Holds M ca)
    {ks : List Term} (input : i.den0) {records now fresh sc si : Term} (hsi : RelV L i (Ty.up _ hi input) (si.denote M))
    {a : AdmitOut r i c} {c1 : Term} (henc : encodeAdmit L ac ks records now fresh sc si = .ok (a, c1)) :
    Holds M c1 ↔ accepts.appFits L.count (input, ()) := by
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1'⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hic : Smt.Rel M L _ (Ty.up _ hi input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  exact accepts.app_exact hcode hca (by simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h3))
    _ _ (rels1 hi accepts.args_data hic) h4

end

end Tazuna.Smt
