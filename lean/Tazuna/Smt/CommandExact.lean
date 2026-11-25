import Tazuna.Smt.EventExact
import Tazuna.Smt.AnswerStep

/-! The conditions `command_step` and `answer_step` take are exact: each holds exactly when the functions the step
applies fit the layout's slot counts, where the step applies them. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Whether folding `events` into the records with `f` fits at each event in turn. -/
def _root_.Tazuna.Ir.Fun.foldFits (S : Ty → Nat) {r e : Ty} (f : Fun (.fn [r, e] r)) : List e.den0 → r.den0 → Prop
  | [], _ => True
  | ev :: evs, x => f.appFits S (x, ev, ()) ∧ f.foldFits S evs (f.fn (x, ev, ()))

section
variable {M : Model} {L : Layout}

theorem holds_ite_tt {c a : Term} {b : Bool} (h : (c.denote M).toBool = b) : Holds M (.ite c a tt) ↔ (b = true → Holds M a) := by
  rw [holds_ite, h]; cases b <;> simp [holds_tt]

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

theorem rels1 {a : Ty} (ha : a.isData = true) (h : (Ty.tuple [a]).isData = true) {x : a.den0} {cx : Code a}
    (hx : Smt.Rel M L a (Ty.up a ha x) cx) : Smt.Rels M L [a] (Ty.up (.tuple [a]) h (x, ())) (cx, ()) := by
  show Smt.Rel M L _ (Ty.up (.tuple [a]) h (x, ())).1 cx ∧ True
  erw [Ty.up_tuple _ _ _ ha rfl]; exact ⟨hx, trivial⟩

/-- `applyAll`'s condition is exact: it holds exactly when `f` fits at each event the slots hold, in turn. -/
theorem applyAll_exact {r e : Ty} (f : Fun (.fn [r, e] r)) {apply : Code (.fn [r, e] r)} {ca : Term}
    (hf : f.code L = .ok (apply, ca)) (hca : Holds M ca) (hr : r.isData = true) (he : e.isData = true) :
    (S : List Slot) → (sv : List (Bool × List Val)) → SlotsDen M S sv → (∀ p ∈ sv, p.2.length = 1) →
    (evs : List e.den0) → Holds2 (EBag L e) (evs.map (Ty.up e he)) sv → (r0 : r.den0) → (rt : Term) →
    RelV L r (Ty.up r hr r0) (rt.denote M) → (rf c : Term) → applyAll apply rt S = .ok (rf, c) →
    (Holds M c ↔ f.foldFits L.count evs r0)
  | [], [], _, _, evs, hev, r0, rt, hr0, rf, c, h => by
    cases evs with
    | nil => simp only [applyAll] at h; cases h; simp [holds_tt, Fun.foldFits]
    | cons _ _ => exact hev.elim
  | (fl, xs) :: S, (b, vs) :: sv, ⟨hfl, hxs, hS⟩, hw, evs, hev, r0, rt, hr0, rf, c, h => by
    have hd : (Ty.fn [r, e] r).isData = true := by simp [Ty.isData, Ty.isDatas, hr, he]
    have hg := f.code_fn hd hf hca
    simp only [applyAll] at h
    obtain ⟨rc, h1, h⟩ := bind_ok.1 h
    obtain ⟨ec, h2, h⟩ := bind_ok.1 h
    obtain ⟨⟨r', c0⟩, h3, h⟩ := bind_ok.1 h
    obtain ⟨r't, h4, h⟩ := bind_ok.1 h
    obtain ⟨⟨rf', c'⟩, h5, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_andT]
    have hw' : ∀ p ∈ sv, p.2.length = 1 := fun p hp => hw p (by simp [hp])
    cases b with
    | false =>
      have hite : (Term.share (.ite fl r't rt)).denote M = rt.denote M := by
        simp [Term.denote, hfl, Val.toBool]
      rw [holds_ite_tt (b := false) (by simp [hfl, Val.toBool])]
      simp only [Bool.false_eq_true, false_implies, true_and]
      exact applyAll_exact f hf hca hr he S sv hS hw' evs (by simpa [Holds2, occupied] using hev) r0 _ (hite ▸ hr0)
        _ c' h5
    | true =>
      match evs, hev with
      | ev :: evs, ⟨⟨z, hz, hez⟩, hrest⟩ =>
        subst hz
        obtain ⟨x0, rfl, hx0⟩ : ∃ x0, xs = [x0] ∧ x0.denote M = z := by
          match xs, hxs with
          | [x0], h => exact ⟨x0, rfl, by simpa [Term.denotes] using h⟩
        rw [holds_ite_tt (b := true) (by simp [hfl, Val.toBool])]
        simp only [true_implies, Fun.foldFits]
        have hrc : Smt.Rel M L r (Ty.up r hr r0) rc := (rel_ofTerm (need_ok.1 h1) _).2 hr0
        have hec : Smt.Rel M L e (Ty.up e he ev) ec := (rel_ofTerm (need_ok.1 h2) _).2 (by simpa [hx0] using hez)
        have hargs := rels2 hr he f.args_data hrc hec
        have e1 : Holds M c0 ↔ f.appFits L.count (r0, ev, ()) :=
          f.app_exact hf hca (by
            intro t ht
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl
            · exact ofTerm_notFn (need_ok.1 h1)
            · exact ofTerm_notFn (need_ok.1 h2)) _ _ hargs h3
        have e2 : Holds M c0 → (Holds M c' ↔ f.foldFits L.count evs (f.fn (r0, ev, ()))) := fun hc0 => by
          have hr' := hg (Ty.up r hr r0, Ty.up e he ev, ()) (rc, ec, ()) ⟨hrc, hec, trivial⟩ r' c0 h3 hc0
          rw [up_app2 hr he hd] at hr'
          have hite : (Term.share (.ite fl r't rt)).denote M = r't.denote M := by
            simp [Term.denote, hfl, Val.toBool]
          exact applyAll_exact f hf hca hr he S sv hS hw' evs hrest _ _ (hite ▸ (rel_term (need_ok.1 h4) _).1 hr')
            _ c' h5
        exact ⟨fun ⟨p0, p1⟩ => ⟨e1.1 p0, (e2 p0).1 p1⟩, fun ⟨p0, p1⟩ => ⟨e1.2 p0, (e2 (e1.2 p0)).2 p1⟩⟩
  | [], _ :: _, h, _, _, _, _, _, _, _, _, _ | _ :: _, [], h, _, _, _, _, _, _, _, _, _ => h.elim

end

section
variable {M : Model} {L : Layout}

/-- A command's codes' own condition is exact: it holds exactly when its three kept sources fit. -/
theorem commandCode_exact {r e c : Ty} {x : CommandV r e c} {cc : CommandCode x} {cx : Term}
    (h : CommandCode.of L x = .ok (cc, cx)) :
    Holds M cx ↔ (x.accepts.fits L.count).1 ∧ (x.decide.fits L.count).1 ∧ (x.ensures.fits L.count).1 := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨d, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  rw [holds_andT, holds_andT, (x.accepts.code_exact (M := M) h1).1, (x.decide.code_exact (M := M) h2).1,
    (x.ensures.code_exact (M := M) h3).1]

end

section
variable {M : Model} {L : Layout}

theorem holds_ite_hit {c a : Term} : Holds M (.ite c a tt) ↔ (Holds M c → Holds M a) := by
  rw [holds_ite]; unfold Holds; cases (c.denote M).toBool <;> simp; rfl

theorem tupleCodes_notFn {d : Nat} {x : Term} : (Γ : List Ty) → (i : Nat) → (σ : Codes Γ) →
    tupleCodes d Γ x i = some σ → ∀ t ∈ Γ, t.isFn = false
  | [], _, _, _ => by simp
  | t :: Γ, i, (c, cs), h => by
    cases hc : Code.ofTerm? t (Term.sel d 0 i x) with
    | none => simp [tupleCodes, hc] at h
    | some c' =>
    cases hcs : tupleCodes d Γ x (i + 1) with
    | none => simp [tupleCodes, hc, hcs] at h
    | some cs' =>
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ofTerm_notFn hc
    · exact tupleCodes_notFn Γ (i + 1) cs' hcs u hu

end

section
variable {v : ServiceV}

/-- Whether a query's `ensures`, if any, fits as a source and at the input and the answer. -/
def ensuresFits (S : Ty → Nat) {i a : Ty} : Option (Fun (Ty.fn [i, a] Ty.rules)) → i.den0 → a.den0 → Prop
  | none, _, _ => True
  | some f, x, y => (f.fits S).1 ∧ f.appFits S (x, y, ())

/-- Whether what an answer step applies fits, for the pending request `p` and the answer `a` of `p`'s type: the
request's `on_answer` source and its application to the answer, a query's `ensures` source and its application to
the input and the answer, and, where those rules hold, `apply` at each event in turn and the invariants on the
records they leave. An answer of another type applies nothing. -/
def answerFits (S : Ty → Nat) (p : Step.Pending v.event) (recs : v.records.den0) (a : (t : Ty) × t.den0) : Prop :=
  match Ty.same a.1 (answerTy p.request.output p.request.rejection) with
  | none => True
  | some ⟨h⟩ =>
    let evs := p.request.onAnswer.fn (h ▸ a.2, ())
    (p.request.onAnswer.fits S).1 ∧ p.request.onAnswer.appFits S (h ▸ a.2, ()) ∧
      ensuresFits S p.request.ensures p.request.value (h ▸ a.2) ∧
      (Step.broken (p.request.holds (h ▸ a.2)) = [] →
        v.apply.foldFits S evs recs ∧ v.invariants.appFits S (evs.foldl (fun r ev => v.apply.fn (r, ev, ())) recs, ()))

end

section
variable {M : Model} {L : Layout} {v : ServiceV}

/-- The condition of an answer's step at the slot `j` and the shape `sh` is exact: where the slot holds the request
the answer names, it holds exactly when what the step applies for that request fits (`answerFits`). -/
theorem answer_exact (s : State v) (hrd : v.records.isData = true)
    {shs : List (PendingShape v.event)} {k : Nat} {sh : PendingShape v.event} (hk : shs[k]? = some sh) (j : Nat)
    (to : Nat) (value : (answerTy sh.output sh.rejection).den0)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hinv : v.invariants.code L = .ok (inv, ci)) (hci : Holds M ci)
    {records pending toT valT : Term}
    (hrec : RelV L v.records (Ty.up _ hrd s.records) (records.denote M))
    (hpend : PendingRel L shs (pending.denote M) s.pending) (hto : toT.denote M = .int (Int.ofNat to))
    (hans : (answerTy sh.output sh.rejection).isData = true)
    (hval : RelV L _ (Ty.up _ hans value) (valT.denote M))
    {o : AnswerOut} {cond : Term} (henc : encodeAnswer L shs k sh j apply inv records pending toT valT = .ok (o, cond)) :
    Holds M cond ↔ (Holds M o.hit →
      ∀ p, s.pending.find? (·.id == to) = some p → answerFits L.count p s.records ⟨_, value⟩) := by
  have hed : v.event.isData = true := by
    have := sh.onAnswer.ht; simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at this; exact this.2
  have happ' := v.apply.code_fn (by simp [Ty.isData, Ty.isDatas, hrd, hed]) happ hca
  have hinv' := v.invariants.code_fn (by simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hrd]) hinv hci
  match shs, hk, hpend, henc with
  | sh0 :: rest, hk, ⟨tbl, htbl, hlist⟩, henc =>
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨de, dn⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨f, xs⟩, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨da, dan⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨σa, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨vc, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c1⟩, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rules, c3⟩, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dtl⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rf, c4⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨rfc, h13, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c5⟩, h14, henc⟩ := bind_ok.1 henc
  obtain ⟨invR, h15, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  rw [holds_ite_hit]
  refine imp_congr_right fun hhit => ?_
  -- The slot holds the request `to` names, as an entry of the shape `sh`.
  obtain ⟨hhf, hhrest⟩ := (holds_and _ _).1 hhit
  obtain ⟨hheq, hhis⟩ := (holds_and _ _).1 hhrest
  obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view (M := M) htbl h1
  obtain ⟨b, hbsv, hfb⟩ := slot_at hS j (need_ok.1 h3)
  have hb : b = true := by simpa [Holds, hfb, Val.toBool] using hhf
  subst hb
  obtain ⟨y, hy, zk, zv, hxs, hzk, hzv⟩ := forall2_mem' hh _ (by
    simp only [occupied, List.mem_filterMap]; exact ⟨_, hbsv, rfl⟩)
  obtain ⟨tk, te, rfl⟩ : ∃ tk te, xs = [tk, te] := by
    match xs, hxs with
    | [tk, te], _ => exact ⟨tk, te, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨htk, hte⟩ := hxs
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at hheq hhis h5 h9
  have hkey : (y.1 : Nat) = to := by
    have e := Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at hheq; exact hheq)
    change zk = Val.int (Int.ofNat y.1) at hzk
    rw [htk, hzk, hto] at e
    exact Int.ofNat.inj (Val.int.inj e)
  obtain ⟨d', n', hf', hra⟩ := hzv
  have hde := find_det hf' (need_ok.1 h2)
  subst d'
  obtain ⟨j', sh', fx, vals, hj', hzv', hfx, hpo⟩ := relAlts_pending (L := L) to (sh0 :: rest) 0 y.2 zv hra
  have hjk : j' = k := by
    have := hhis
    simp only [Holds, Term.denote, hte, hzv', Val.toBool, beq_self_eq_true, Bool.true_and, beq_iff_eq] at this
    omega
  subst j'
  rw [hk] at hj'
  cases hj'
  have hfind : s.pending.find? (·.id == to) = some (sh.pending to fx) := by
    rw [← hlist, ← hpo, ← hkey]
    exact find_pending (sh0 :: rest) tbl.1 tbl.2 y (hperm.mem_iff.1 hy)
  -- The entry's fields: the sender's key, the input, and each site's captured values.
  obtain ⟨f0, f1, f2, f3, ⟨⟩⟩ := fx
  obtain ⟨v0, vs0, rfl, -, v1, vs1, rfl, hv1, v2, vs2, rfl, hv2, v3, vs3, rfl, hv3, rfl⟩ := hfx
  have hsel (i : Nat) (w : Val) (hw : [v0, v1, v2, v3][i]? = some w) : (Term.sel de k i te).denote M = w := by
    rw [Nat.zero_add] at hzv'
    rw [sel_ctor _ (hte.trans hzv'), hw]; rfl
  have hd0 : (Ty.tuple sh.ks).isData = true := sh.hks
  have hdata := sh.hfields
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true, Bool.and_true] at hdata
  obtain ⟨hd1, hd2, hd3⟩ := hdata
  replace hd2 : (Ty.tuple sh.ensuresΓ).isData = true := hd2
  replace hd3 : (Ty.tuple sh.answerΓ).isData = true := hd3
  have hdown : Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ()) =
      (Ty.down _ hd0 f0, Ty.down _ hd1 f1, Ty.down _ hd2 f2, Ty.down _ hd3 f3, ()) := by
    simp only [PendingShape.fields, RequestShape.fields]
    have e2 : (Ty.tuple [Ty.tuple sh.ensuresΓ, Ty.tuple sh.answerΓ]).isData = true := by
      simp only [Ty.isData, Ty.isDatas] at hd2 hd3 ⊢; simp [hd2, hd3]
    have e1 : (Ty.tuple [sh.input, Ty.tuple sh.ensuresΓ, Ty.tuple sh.answerΓ]).isData = true := by
      simp only [Ty.isData, Ty.isDatas] at hd1 hd2 hd3 ⊢; simp [hd1, hd2, hd3]
    have e3 : (Ty.tuple [Ty.tuple sh.answerΓ]).isData = true := by
      simp only [Ty.isData, Ty.isDatas] at hd3 ⊢; simp [hd3]
    erw [down_tuple _ _ _ hd0 e1, down_tuple _ _ _ hd1 e2, down_tuple _ _ _ hd2 e3, down_tuple _ _ _ hd3 rfl]
    rfl
  have hY1 : (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.1 = Ty.down _ hd1 f1 := by rw [hdown]
  have hY2 : (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.1 = Ty.down _ hd2 f2 := by rw [hdown]
  have hY3 : (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.2.1 = Ty.down _ hd3 f3 := by rw [hdown]
  -- `on_answer` at the captured values, applied to the answer.
  obtain ⟨da', na', vals3, hfa, hv3e, hrel3⟩ := hv3
  obtain rfl := find_det hfa (need_ok.1 h4)
  have hσa : Rels M L sh.answerΓ f3 σa :=
    tupleCodes_rels sh.answerΓ [] vals3 f3 σa (by rw [hsel 3 v3 rfl, hv3e]; rfl) hrel3 (need_ok.1 h5)
  have hdom : (∀ p, s.pending.find? (·.id == to) = some p → answerFits L.count p s.records ⟨_, value⟩) ↔
      answerFits L.count (sh.pending to (f0, f1, f2, f3, ())) s.records ⟨_, value⟩ :=
    ⟨fun h => h _ hfind, fun h p hp => by rw [hfind] at hp; cases hp; exact h⟩
  rw [hdom]
  show _ ↔ answerFits L.count (sh.pending to (f0, f1, f2, f3, ())) s.records
    ⟨answerTy (sh.pending to (f0, f1, f2, f3, ())).request.output (sh.pending to (f0, f1, f2, f3, ())).request.rejection,
      value⟩
  simp only [answerFits, Ty_same_rfl]
  have hOA : (sh.pending to (f0, f1, f2, f3, ())).request.onAnswer = sh.onAnswer.fn (Ty.down _ hd3 f3) := by
    show sh.onAnswer.fn _ = _; rw [hY3]
  rw [hOA]
  have hvc : Smt.Rel M L _ (Ty.up _ hans value) vc := (rel_ofTerm (need_ok.1 h6) _).2 hval
  have hta : (Ty.tuple [answerTy sh.output sh.rejection]).isData = true := by simp [Ty.isData, Ty.isDatas, hans]
  have hargs := rels1 hans hta hvc
  have hnfa : ∀ t ∈ [answerTy sh.output sh.rejection], t.isFn = false := by
    simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h6)
  have x1 := encode_exact sh.onAnswer.defs sh.onAnswer.defs.eval (sh.onAnswer.defs.encode L)
    (sh.onAnswer.defs.fits L.count) (Defs.encode_agrees M L sh.onAnswer.defs) (Defs.encode_exact M L sh.onAnswer.defs)
    sh.onAnswer.body σa f3 (FTs.dflt _) hσa (frels_of_notFn (tupleCodes_notFn _ _ _ (need_ok.1 h5)) _ _ _) oa c1 h7
  have hfit3 : (sh.onAnswer.fn (Ty.down _ hd3 f3)).fits L.count = Expr.fits L.count sh.onAnswer.defs
      sh.onAnswer.defs.eval (sh.onAnswer.defs.fits L.count) sh.onAnswer.body f3 (FTs.dflt _) := by
    have e : Ty.up (.tuple sh.answerΓ) sh.onAnswer.hΓ (Ty.down _ hd3 f3) = f3 := Ty.up_down _ hd3 f3
    simp only [Fun.fits, Site.fn]; rw [e]
  have e1 : Holds M c1 ↔ ((sh.onAnswer.fn (Ty.down _ hd3 f3)).fits L.count).1 := by rw [hfit3]; exact x1.1
  have e2 : Holds M c1 → (Holds M c2 ↔ (sh.onAnswer.fn (Ty.down _ hd3 f3)).appFits L.count (value, ())) := fun hc1 => by
    have := (x1.2 hc1 _ (FTs.dflt _) (vc, ()) hargs (frels_of_notFn hnfa _ _ _) evs c2 h8).1
    rw [this]; unfold Fun.appFits; rw [hfit3]
  have hEns : (sh.pending to (f0, f1, f2, f3, ())).request.ensures = ensuresFn sh.ensures (Ty.down _ hd2 f2) := by
    show ensuresFn _ _ = _; rw [hY2]; rfl
  have hValR : (sh.pending to (f0, f1, f2, f3, ())).request.value = Ty.down _ hd1 f1 := hY1
  have hholds : (sh.pending to (f0, f1, f2, f3, ())).request.holds value =
      (match ensuresFn sh.ensures (Ty.down _ hd2 f2) with
        | some f => f.fn (Ty.down _ hd1 f1, value, ())
        | none => []) := by
    unfold RequestV.holds; rw [hEns, hValR]; split <;> (rename_i h; rw [h])
    rfl
  rw [hEns, hValR, hholds]
  have hens : (Holds M c3 ↔ ensuresFits L.count (ensuresFn sh.ensures (Ty.down _ hd2 f2)) (Ty.down _ hd1 f1) value) ∧
      (Holds M c3 → brokenIn M rules = Step.broken (match ensuresFn sh.ensures (Ty.down _ hd2 f2) with
        | some f => f.fn (Ty.down _ hd1 f1, value, ())
        | none => [])) := by
    unfold ensuresTerms at h9
    obtain ⟨⟨_, _, si, so, sj, ens, _, _, _⟩, _, _, _⟩ := sh
    cases ens with
    | none =>
      cases pure_ok.1 h9
      simp [ensuresFn, ensuresFits, brokenIn, Step.broken, holds_tt]
    | some es =>
      obtain ⟨Γ, es⟩ := es
      obtain ⟨⟨dn, dnn⟩, g1, h9⟩ := bind_ok.1 h9
      obtain ⟨σe, g2, h9⟩ := bind_ok.1 h9
      obtain ⟨ic, g3, h9⟩ := bind_ok.1 h9
      obtain ⟨⟨oe, ce⟩, g4, h9⟩ := bind_ok.1 h9
      obtain ⟨⟨rs, ce'⟩, g5, h9⟩ := bind_ok.1 h9
      obtain ⟨rl, g6, h9⟩ := bind_ok.1 h9
      cases pure_ok.1 h9
      obtain ⟨dn', nn', vals2, hfe, hv2e, hrel2⟩ := hv2
      obtain rfl := find_det hfe (need_ok.1 g1)
      have hσe : Rels M L Γ f2 σe :=
        tupleCodes_rels Γ [] vals2 f2 σe (by rw [hsel 2 v2 rfl, hv2e]; rfl) hrel2 (need_ok.1 g2)
      have x3 := encode_exact es.defs es.defs.eval (es.defs.encode L) (es.defs.fits L.count)
        (Defs.encode_agrees M L es.defs) (Defs.encode_exact M L es.defs) es.body σe f2 (FTs.dflt _) hσe
        (frels_of_notFn (tupleCodes_notFn _ _ _ (need_ok.1 g2)) _ _ _) oe ce g4
      have hfit2 : (es.fn (Ty.down _ hd2 f2)).fits L.count = Expr.fits L.count es.defs es.defs.eval
          (es.defs.fits L.count) es.body f2 (FTs.dflt _) := by
        have e : Ty.up (.tuple Γ) es.hΓ (Ty.down _ hd2 f2) = f2 := Ty.up_down _ hd2 f2
        simp only [Fun.fits, Site.fn]; rw [e]
      have hic : Smt.Rel M L si (Ty.up _ hd1 (Ty.down _ hd1 f1)) ic := by
        rw [Ty.up_down]; exact (rel_ofTerm (need_ok.1 g3) _).2 (by rw [hsel 1 v1 rfl]; exact hv1)
      have hte2 : (Ty.tuple [si, answerTy so sj]).isData = true := by
        simp [Ty.isData, Ty.isDatas, hd1, hans]
      have hargs2 : Smt.Rels M L [si, answerTy so sj]
          (Ty.up (.tuple [si, answerTy so sj]) hte2 (Ty.down _ hd1 f1, value, ())) (ic, vc, ()) :=
        rels2 hd1 hans hte2 hic hvc
      have hnf2 : ∀ t ∈ [si, answerTy so sj], t.isFn = false := by
        intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact ofTerm_notFn (need_ok.1 g3)
        · exact ofTerm_notFn (need_ok.1 h6)
      have e3a : Holds M ce ↔ ((es.fn (Ty.down _ hd2 f2)).fits L.count).1 := by rw [hfit2]; exact x3.1
      have e3b : Holds M ce → (Holds M ce' ↔ (es.fn (Ty.down _ hd2 f2)).appFits L.count (Ty.down _ hd1 f1, value, ())) :=
        fun hce => by
          have := (x3.2 hce _ (FTs.dflt _) (ic, vc, ()) hargs2 (frels_of_notFn hnf2 _ _ _) rs ce' g5).1
          rw [this]; unfold Fun.appFits; rw [hfit2]
      refine ⟨?_, fun hc3 => ?_⟩
      · rw [holds_andT]
        simp only [ensuresFn, ensuresFits]
        exact ⟨fun ⟨a, b⟩ => ⟨e3a.1 a, (e3b a).1 b⟩, fun ⟨a, b⟩ => ⟨e3a.2 a, (e3b (e3a.2 a)).2 b⟩⟩
      · rw [holds_andT] at hc3
        have hoe := encode_agrees es.defs es.defs.eval (es.defs.encode L) (Defs.encode_agrees M L es.defs) es.body σe
          f2 hσe oe ce g4 hc3.1
        have hoe' : Rel M L _ (Ty.up _ es.ht (es.fn (Ty.down _ hd2 f2)).fn) oe := by
          rw [Fun.fn, Ty.up_down]
          have e : Ty.up (.tuple Γ) es.hΓ (Ty.down _ hd2 f2) = f2 := Ty.up_down _ hd2 f2
          simp only [Fun.eval, Site.fn]; rw [e]; exact hoe
        have hrs := hoe' _ _ hargs2 rs ce' g5 hc3.2
        erw [Ty.up_fn _ Ty.rules _ hte2 rfl] at hrs
        rw [rules_broken g6 _ hrs]
        rfl
  have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, hed]
  have e45 : Holds M c1 → Holds M c2 → Holds M c3 → (Holds M (.ite (allT (rules.map (·.2))) (andT c4 c5) tt) ↔
      (Step.broken (match ensuresFn sh.ensures (Ty.down _ hd2 f2) with
          | some f => f.fn (Ty.down _ hd1 f1, value, ())
          | none => []) = [] →
        v.apply.foldFits L.count ((sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ())) s.records ∧
          v.invariants.appFits L.count (((sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ())).foldl
            (fun r ev => v.apply.fn (r, ev, ())) s.records, ()))) := by
    intro hc1 hc2 hc3
    have hoa := encode_agrees sh.onAnswer.defs sh.onAnswer.defs.eval (sh.onAnswer.defs.encode L)
      (Defs.encode_agrees M L sh.onAnswer.defs) sh.onAnswer.body σa f3 hσa oa c1 h7 hc1
    have hoa' : Rel M L _ (Ty.up _ sh.onAnswer.ht (sh.onAnswer.fn (Ty.down _ hd3 f3)).fn) oa := by
      rw [Fun.fn, Ty.up_down]
      have e : Ty.up (.tuple sh.answerΓ) sh.onAnswer.hΓ (Ty.down _ hd3 f3) = f3 := Ty.up_down _ hd3 f3
      simp only [Fun.eval, Site.fn]; rw [e]; exact hoa
    have hevs := hoa' _ (vc, ()) hargs evs c2 h8 hc2
    erw [Ty.up_fn _ _ _ hta hle] at hevs
    have hevs' : RelV L (.list v.event) (Ty.up _ hle ((sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ())))
        (evt.denote M) := (rel_term (need_ok.1 h10) _).1 hevs
    have hlv := (rel_term (need_ok.1 h10) _).2 hevs'
    have hee : evs = evt := Option.some.inj (need_ok.1 h10)
    subst hee
    obtain ⟨svl, hSl, -, hswl, hhl⟩ := list_view (M := M) hlv h11
    erw [Ty.up_list _ _ hed] at hhl
    have hbroken := hens.2 hc3
    have hall : ((allT (rules.map (·.2))).denote M).toBool = decide (Step.broken (match ensuresFn sh.ensures
        (Ty.down _ hd2 f2) with
          | some f => f.fn (Ty.down _ hd1 f1, value, ())
          | none => []) = []) := by
      rw [allT_denote, Val.toBool, ← hbroken]
      by_cases hb : brokenIn M rules = []
      · simp [(brokenIn_nil rules).1 hb, hb]
      · have : (rules.map (·.2)).all (fun t => (t.denote M).toBool) ≠ true := fun h =>
          hb ((brokenIn_nil (M := M) rules).2 h)
        simp [hb]; simpa using this
    rw [holds_ite_tt hall, decide_eq_true_iff]
    refine imp_congr_right fun _ => ?_
    rw [holds_andT]
    have e4 := applyAll_exact v.apply happ hca hrd hed _ svl hSl hswl _ hhl s.records records hrec rf c4 h12
    have e5 : Holds M c4 → (Holds M c5 ↔ v.invariants.appFits L.count
        (((sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ())).foldl (fun r ev => v.apply.fn (r, ev, ())) s.records, ())) :=
      fun hc4 => by
        have hrf := applyAll_rel happ' _ svl hSl hswl _ hhl _ records hrec rf c4 h12 hc4
        erw [← up_foldl hrd hed (by simp [Ty.isData, Ty.isDatas, hrd, hed])] at hrf
        have hrfc : Smt.Rel M L v.records _ rfc := (rel_ofTerm (need_ok.1 h13) _).2 hrf
        exact v.invariants.app_exact hinv hci (by simpa using ofTerm_notFn (need_ok.1 h13)) _ _
          (rels1 hrd (by simp [Ty.isData, Ty.isDatas, hrd]) hrfc) h14
    exact ⟨fun ⟨a, b⟩ => ⟨e4.1 a, (e5 a).1 b⟩, fun ⟨a, b⟩ => ⟨e4.2 a, (e5 (e4.2 a)).2 b⟩⟩
  rw [holds_andT, holds_andT, holds_andT]
  constructor
  · rintro ⟨hc1, hc2, hc3, hc45⟩
    exact ⟨e1.1 hc1, (e2 hc1).1 hc2, hens.1.1 hc3, (e45 hc1 hc2 hc3).1 hc45⟩
  · rintro ⟨p1, p2, p3, p45⟩
    have hc1 := e1.2 p1
    have hc2 := (e2 hc1).2 p2
    have hc3 := hens.1.2 p3
    exact ⟨hc1, hc2, hc3, (e45 hc1 hc2 hc3).2 p45⟩

end

end Tazuna.Smt
