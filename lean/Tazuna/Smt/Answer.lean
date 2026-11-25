import Tazuna.Smt.Finish

/-! T2 for an answer. The answer names the pending request by its wire id `to`; the pending table's slot that holds
`to` holds the request as an entry of one shape, so the step runs that shape's sites at the captured values the entry
holds: its query's `ensures` on the input and the answer, then its `on_answer`, whose events run through the events
loop (machines and reactions react) before the step ends (`encodeFinish`). The request leaves the table. An answer
that names no request of a shape with its type is `Fault.answerUnmatched` (`answer_unmatched`), so the two cases
cover every answer of a given type. -/

namespace Tazuna.Smt

open Tazuna.Ir

variable {T : List Ir.TypeDecl}

section
variable {M : Model} {L : Layout}

theorem slot_at {w : Nat} : {S : List (Slot w)} → {sv : List (Bool × List Val)} → SlotsDen M S sv → (j : Nat) →
    {f : Term} → {xs : SlotItems w} → S[j]? = some (f, xs) → ∃ b, (b, Term.denotes M xs.1) ∈ sv ∧ f.denote M = .bool b
  | [], [], _, _, _, _, h => by simp at h
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, by simp [hxs], hf⟩
  | _ :: S, _ :: sv, ⟨_, _, hS⟩, j + 1, _, _, h => by
    obtain ⟨b, hb, hf⟩ := slot_at hS j (by simpa using h)
    exact ⟨b, by simp [hb], hf⟩
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => h.elim

theorem relAlts_pending {e : Ty} {d : Nat} (id : Nat) : (shs : List (PendingShape e)) → (k0 : Nat) →
    (x : Ty.alts (shs.map PendingShape.fields)) → (w : Val) → RelAlts L d k0 (shs.map PendingShape.fields) x w →
    ∃ j sh fx vals, shs[j]? = some sh ∧ w = .ctor d (k0 + j) vals ∧ RelVs L sh.fields fx vals ∧
      pendingOf shs id x = sh.pending id fx
  | sh :: _, k0, .inl fx, _, ⟨vals, e, h⟩ => ⟨0, sh, fx, vals, rfl, by simpa using e, h, rfl⟩
  | _ :: shs, k0, .inr y, w, h => by
    obtain ⟨j, sh, fx, vals, hj, e, h, hp⟩ := relAlts_pending id shs (k0 + 1) y w h
    exact ⟨j + 1, sh, fx, vals, by simpa using hj, by rw [e]; congr 1; omega, h, hp⟩

theorem find_pending {e : Ty} (shs : List (PendingShape e)) :
    (tbl : List (Nat × Ty.alts (shs.map PendingShape.fields))) →
    tbl.Pairwise (fun a b => (a.1 == b.1) = false ∧ (b.1 == a.1) = false) → (a : Nat × _) → a ∈ tbl →
    (tbl.map fun x => pendingOf shs x.1 x.2).find? (·.id == a.1) = some (pendingOf shs a.1 a.2)
  | [], _, _, h => by simp at h
  | b :: tbl, hu, a, ha => by
    rw [List.pairwise_cons] at hu
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [pendingOf_id]
    · have hne : (b.1 == a.1) = false := (hu.1 a ha).1
      rw [List.map_cons, List.find?_cons, pendingOf_id, hne]
      exact find_pending shs tbl hu.2 a ha

theorem down_tuple (t : Ty) (ts : List Ty) (h : (Ty.tuple (t :: ts)).isData = true) (ht : t.isData = true)
    (hts : (Ty.tuple ts).isData = true) (x : Ty.dens (t :: ts)) :
    Ty.down (.tuple (t :: ts)) h x = (Ty.down t ht x.1, Ty.down (.tuple ts) hts x.2) := by
  have hu := Ty.up_tuple t ts h ht hts (Ty.down (.tuple (t :: ts)) h x)
  erw [Ty.up_down] at hu
  have e1 : x.1 = Ty.up t ht (Ty.down (.tuple (t :: ts)) h x).1 := congrArg Prod.fst hu
  have e2 : x.2 = Ty.up (.tuple ts) hts (Ty.down (.tuple (t :: ts)) h x).2 := congrArg Prod.snd hu
  rw [e1, e2]; erw [Ty.down_up, Ty.down_up]; rfl

end

section
variable (L : Layout) {v : ServiceV}

/-- The rules a query's `ensures` keeps for an answer, from the entry's input and captured values, with their
condition; a command's answers keep none. -/
def ensuresTerms {e : Ty} (sh : PendingShape e) (de k : Nat) (entry : Term)
    (vc : Code (answerTy sh.output sh.rejection)) : Except Refusal (List (Term × Term) × Term) :=
  match sh.ensures with
  | none => pure ([], tt)
  | some ⟨Γ, es⟩ => do
    let (dn, _) ← need "a layout without the captures' tuple" (L.find? (.tuple Γ))
    let σe ← need "captures that have no term" (tupleCodes dn Γ (.sel de k 2 entry) 0)
    let ic ← need "an input that has no term" (Code.ofTerm? sh.input (.sel de k 1 entry))
    let (oe, c) ← es.code L σe
    let (rs, c') ← oe (ic, vc, ())
    pure (← ruleTerms L rs, andT c c')

/-- Whether no slot holds the request `to` names as an entry of a shape whose answers have the type `t`. -/
def answerUnmatchedT {shs : List (PendingShape v.event)} (senv : StepEnv L shs) (t : Ty) (pending to : Term) : Term :=
  let typed := (List.range shs.length).filter fun k => match shs[k]? with
    | some sh => (Ty.same (answerTy sh.output sh.rejection) t).isSome
    | none => false
  allT ((pendingSlotsOf senv.dT senv.dtT senv.nT pending).map fun s =>
    .not (.and s.flag (.and (.eq s.id to) (anyT (typed.map fun k => .is senv.dP k s.entry)))))

end

section
variable {M : Model} {L : Layout} {v : ServiceV}

theorem filter_pendingList (shs : List (PendingShape v.event)) (to : Nat)
    (xs : List (Nat × Ty.alts (shs.map PendingShape.fields))) :
    (xs.filter fun e => !((to == e.1) || (e.1 == to))).map (fun x => pendingOf shs x.1 x.2) =
      (xs.map fun x => pendingOf shs x.1 x.2).filter (·.id != to) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Function.comp, pendingOf_id, bne]
  by_cases h : e.1 = to
  · simp [h]
  · simp [h, Ne.symm h]

theorem slot_mem {w : Nat} : {S : List (Slot w)} → {sv : List (Bool × List Val)} → SlotsDen M S sv → ∀ p ∈ sv,
    ∃ q ∈ S, q.1.denote M = .bool p.1 ∧ Term.denotes M q.2.1 = p.2
  | [], [], _, _, hp => by simp at hp
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨(f, xs), by simp, hf, hxs⟩
    · obtain ⟨q, hq, h⟩ := slot_mem hS p hp; exact ⟨q, by simp [hq], h⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- Where the term holds, the request the wire id names, if any, has answers of another type than `t`. -/
theorem unmatched_types (s : State v) {shs : List (PendingShape v.event)} (to : Nat) (t : Ty)
    {pending toT : Term} (hpend : PendingRel L shs (pending.denote M) s.pending)
    (hto : toT.denote M = .int (Int.ofNat to)) (senv : StepEnv L shs) (hu : Holds M (answerUnmatchedT L senv t pending toT)) (p : Step.Pending v.event) (hf : s.pending.find? (·.id == to) = some p) :
    Ty.same t (answerTy p.request.output p.request.rejection) = none := by
  match shs, hpend, senv, hu with
  | [], ⟨tbl, _, hlist⟩, _, _ =>
    match tbl, hlist with
    | ⟨[], _⟩, hlist => simp only [pendingList, List.map_nil] at hlist; simp [← hlist] at hf
    | ⟨(_, x) :: _, _⟩, _ => exact nomatch x
  | sh0 :: rest, ⟨tbl, htbl, hlist⟩, senv, hu =>
  -- The request found sits in an occupied slot with its wire id.
  have hp := List.mem_of_find?_eq_some hf
  have hpid : p.id = to := by simpa using List.find?_some hf
  rw [← hlist] at hp
  obtain ⟨⟨y1, y2⟩, hy, rfl⟩ := List.mem_map.1 hp
  obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view (M := M) htbl senv.hT
  obtain ⟨vs, hvs, zk, zv, hxs, hzk, hzv⟩ := forall2_mem_left hh (y1, y2) (hperm.mem_iff.2 hy)
  have hocc : (true, vs) ∈ sv := by
    simp only [occupied, List.mem_filterMap] at hvs
    obtain ⟨⟨b, vs'⟩, hm, he⟩ := hvs
    cases b <;> simp at he
    exact he ▸ hm
  rw [← pendingSlotsOf_slot] at hS
  obtain ⟨q, hq0, hf1, hxs2⟩ := slot_mem hS _ hocc
  obtain ⟨⟨f, tk, te⟩, hq, rfl⟩ := List.mem_map.1 hq0
  rw [hxs] at hxs2
  simp only [PendingSlot.slot, Term.denotes, List.cons.injEq, and_true] at hxs2 hf1
  obtain ⟨htk, hte⟩ := hxs2
  obtain ⟨d', n', hf', hra⟩ := hzv
  have hde := find_det hf' senv.hPE
  subst d'
  obtain ⟨j', sh', fx, vals, hj', hzv', -, hpo⟩ := relAlts_pending (L := L) y1 (sh0 :: rest) 0 y2 zv hra
  -- The slot's test is false, so no shape of the answer's type is that entry's.
  have hslot := (holds_allT _).1 hu _ (List.mem_map_of_mem hq)
  have hkey : (y1 : Nat) = to := (pendingOf_id _ _ _).symm.trans hpid
  change zk = Val.int (Int.ofNat y1) at hzk
  dsimp only
  rw [hpo]
  cases hsame : Ty.same t (answerTy (sh'.pending y1 fx).request.output (sh'.pending y1 fx).request.rejection) with
  | none => rfl
  | some e =>
    exfalso
    obtain ⟨heq⟩ := e
    have hlt : j' < (sh0 :: rest).length := (List.getElem?_eq_some_iff.1 hj').1
    have htyped : j' ∈ (List.range (sh0 :: rest).length).filter fun k => match (sh0 :: rest)[k]? with
        | some sh => (Ty.same (answerTy sh.output sh.rejection) t).isSome
        | none => false := by
      subst heq
      simp only [List.mem_filter, List.mem_range, hlt, hj', true_and]
      exact Ty_same_self _
    have hX : Holds M (f.and ((tk.eq toT).and (anyT (((List.range (sh0 :: rest).length).filter fun k =>
        match (sh0 :: rest)[k]? with
        | some sh => (Ty.same (answerTy sh.output sh.rejection) t).isSome
        | none => false).map fun k => Term.is senv.dP k te)))) := by
      rw [holds_and, holds_and]
      refine ⟨by simp [Holds, hf1, Val.toBool], ?_, ?_⟩
      · simp only [Holds, Term.denote, htk, hzk, hto, hkey, Val.toBool]
        show Val.beq (.int _) (.int _) = true
        simp [Val.beq]
      · simp only [Holds]; rw [anyT_denote]
        rw [Nat.zero_add] at hzv'
        refine List.any_eq_true.2 ⟨Term.is senv.dP j' te, List.mem_map_of_mem htyped, ?_⟩
        simp [Term.denote, hte, hzv', Val.toBool]
    have hX' : (Term.denote M _).toBool = true := hX
    have hs' : (Val.bool !(Term.denote M _).toBool).toBool = true := hslot
    rw [hX'] at hs'
    simp [Val.toBool] at hs'

/-- T2 for an answer that names no request of a shape whose answers have its type: wherever the term holds, the step
is `Fault.answerUnmatched`, whatever the records. -/
theorem answer_unmatched (s : State v) {shs : List (PendingShape v.event)} (to : Nat) (t : Ty) (value : t.den0)
    {pending toT : Term} (hpend : PendingRel L shs (pending.denote M) s.pending)
    (hto : toT.denote M = .int (Int.ofNat to)) (senv : StepEnv L shs) (hu : Holds M (answerUnmatchedT L senv t pending toT)) :
    step T v s (.answer to ⟨t, value⟩) = ⟨s, .fault .answerUnmatched, [], []⟩ := by
  cases hf : s.pending.find? (·.id == to) with
  | none => simp only [step, hf]
  | some p => simp only [step, hf, unmatched_types s to t hpend hto senv hu p hf]

end

section
variable {v : ServiceV}

/-- Whether a query's `ensures`, if any, fits as a source and at the input and the answer. -/
def ensuresFits (S : Ty → Nat) {i a : Ty} : Option (Fun (Ty.fn [i, a] Ty.rules)) → i.den0 → a.den0 → Prop
  | none, _, _ => True
  | some f, x, y => (f.fits S).1 ∧ f.appFits S (x, y, ())

end

/-- The terms of an answer step at one slot: whether the slot holds the request `to` names as an entry of the shape,
the `ensures` rules, the events of `on_answer`, what the events loop leaves, and the step's end from the pending table
without the request. -/
structure AnswerOut (v : ServiceV) where
  hit : Term
  rules : List (Term × Term)
  events : Term
  after : EventsOut v
  finish : FinishOut v

section
variable (L : Layout) (T : List TypeDecl) {v : ServiceV}

/-- An answer step's terms at slot `j` for requests of the shape `sh`, the `k`-th of `shs`, its condition and the
codes' condition, from the codes of the service's `apply` and `invariants` and the terms of the state, the wire id
the answer names and the answer. -/
def encodeAnswer (P : List AnySite) (shs : List (PendingShape v.event)) (k : Nat) (sh : PendingShape v.event)
    (senv : StepEnv L shs) (j : Fin senv.nT) (apply : Code (Ty.fn [v.records, v.event] v.records))
    (invariants : Code (Ty.fn [v.records] Ty.rules)) (S : SymState v) (to value : Term) : Except Refusal (Encoded (AnswerOut v)) := do
  let de := senv.dP
  let PS := slotsOf senv.dT senv.dtT senv.nT 2 S.pending
  let sl := pendingSlotAt senv.dT senv.dtT j S.pending
  let entry := sl.entry
  let hit := Term.and sl.flag (.and (.eq sl.id to) (.is de k entry))
  let (da, _) ← need "a layout without the captures' tuple" (L.find? (.tuple sh.answerΓ))
  let σa ← need "captures that have no term" (tupleCodes da sh.answerΓ (.sel de k 3 entry) 0)
  let vc ← need "an answer that has no term" (Code.ofTerm? _ value)
  let (oa, c1) ← sh.onAnswer.code L σa
  let (evs, c2) ← oa (vc, ())
  let (rules, c3) ← ensuresTerms L sh de k entry vc
  let evt ← need "events that have no term" (Code.term? _ evs)
  let (dl, nl, dtl) ← collD L (.list v.event) [v.event]
  let (o, c4) ← encodeEvents L T v shs senv apply S.now (slotsOf dl dtl nl 1 evt) S.records S.machines S.nextId (.int 0)
  let ⟨fo, cf, cfx⟩ ← encodeFinish L T P v shs senv apply invariants S.now S.fresh
    (slotsTerm senv.dT senv.dtT (filterSlots PS (keepQs to PS))) o
  pure ⟨⟨hit, rules, evt, o, fo⟩,
    .ite hit (andT c1 (andT c2 (andT c3 (.ite (allT (rules.map (·.2))) (andT c4 cf) tt)))) tt, cfx⟩

end

section
variable {P : List AnySite} {v : ServiceV}

/-- Dropping pending requests keeps the step invariant. -/
theorem _root_.Tazuna.Ir.Step.Inv.filterPending {s : State v} (h : Step.Inv P s) (q : Step.Pending v.event → Bool) :
    Step.Inv P { s with pending := s.pending.filter q } :=
  ⟨fun p hp => h.below p ((List.mem_filter.1 hp).1), h.nodup.sublist ((List.filter_sublist).map _),
    fun p hp => h.reach p ((List.mem_filter.1 hp).1),
    fun p hp => h.shaped p ((List.mem_filter.1 hp).1)⟩

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

end

section
variable {v : ServiceV}

/-- Whether what an answer step applies fits, for the pending request `p` the answer names by `to` and the answer `a`
of `p`'s type: the request's `on_answer` source and its application to the answer, a query's `ensures` source and
its application to the input and the answer, and, where those rules hold, the events' applications in turn on the
state without the request (`eventsFit`) and the step's end (`finishFits`). An answer of another type applies
nothing. -/
def answerFits (S : Ty → Nat) (T : List TypeDecl) (shs : List (PendingShape v.event)) (s : State v)
    (p : Step.Pending v.event) (to : Nat) (a : (t : Ty) × t.den0) : Prop :=
  match Ty.same a.1 (answerTy p.request.output p.request.rejection) with
  | none => True
  | some ⟨h⟩ =>
    let evs := p.request.onAnswer.fn (h ▸ a.2, ())
    (p.request.onAnswer.fits S).1 ∧ p.request.onAnswer.appFits S (h ▸ a.2, ()) ∧
      ensuresFits S p.request.ensures p.request.value (h ▸ a.2) ∧
      (Step.broken (p.request.holds (h ▸ a.2)) = [] →
        eventsFit S T { s with pending := s.pending.filter (·.id != to) } evs ∧
          finishFits S T shs (Step.applyEvents T { state := { s with pending := s.pending.filter (·.id != to) } } evs))

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- An answer at the slot `j` and the shape `sh`: where the codes' conditions hold and the slot holds the request the
answer names, the condition holds exactly when what the step applies for that request fits (`answerFits`); wherever
it holds, a broken `ensures` rule makes the answer Invalid, and otherwise the request leaves the pending table, the
events of `on_answer` run through the events loop and the step ends as its end terms say (`Finished`). -/
theorem answer_encode {P : List AnySite} (chk : Checked P T v)
    {shs : List (PendingShape v.event)} (hshs : ∀ sh ∈ shs, sh.InSites P)
    (s : State v) (hsinv : Step.Inv P s)
    {k : Nat} {sh : PendingShape v.event} (hk : shs[k]? = some sh)
    (to : Nat) (value : (answerTy sh.output sh.rejection).den0)
    {apply : Code (Ty.fn [v.records, v.event] v.records)} {ca : Term} (happ : v.apply.code L = .ok (apply, ca))
    (hca : Holds M ca)
    {inv : Code (Ty.fn [v.records] Ty.rules)} {ci : Term} (hinv : v.invariants.code L = .ok (inv, ci)) (hci : Holds M ci)
    (senv : StepEnv L shs) (j : Fin senv.nT)
    {S : SymState v} (hR : StateRel M L T shs S s) {toT valT : Term} (hto : toT.denote M = .int (Int.ofNat to))
    (hans : (answerTy sh.output sh.rejection).isData = true)
    (hval : RelV L _ (Ty.up _ hans value) (valT.denote M))
    {o : AnswerOut v} {cond cfx : Term}
    (henc : encodeAnswer L T P shs k sh senv j apply inv S toT valT =
      .ok ⟨o, cond, cfx⟩) (hcfx : Holds M cfx) :
    let r := step T v s (.answer to ⟨_, value⟩)
    (Holds M cond ↔ (Holds M o.hit →
      ∀ p, s.pending.find? (·.id == to) = some p → answerFits L.count T shs s p to ⟨_, value⟩)) ∧
    (Holds M cond → Holds M o.hit →
      match brokenIn M o.rules with
      | n :: ns => r = ⟨s, .invalid (n :: ns), [], []⟩
      | [] => Finished M L T shs o.finish s { state := { s with pending := s.pending.filter (·.id != to) } }
          .accepted r) := by
  intro r
  unfold encodeAnswer at henc
  have h1 := senv.hT
  have h2 := senv.hPE
  have h3' := pendingSlot_at (d := senv.dT) (dt := senv.dtT) j.2 S.pending
  generalize pendingSlotAt senv.dT senv.dtT j S.pending = sl at h3' henc
  obtain ⟨f, tk, te⟩ := sl
  generalize (j : Nat) = jn at h3'
  generalize senv.dT = d at h1 h3' henc
  generalize senv.dtT = dt at h1 h3' henc
  generalize senv.nT = n at h1 h3' henc
  generalize senv.dP = de at h2 henc
  obtain ⟨⟨da, dan⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨σa, h5, henc⟩ := bind_ok.1 henc
  obtain ⟨vc, h6, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oa, c1⟩, h7, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨evs, c2⟩, h8, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rules, c3⟩, h9, henc⟩ := bind_ok.1 henc
  obtain ⟨evt, h10, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨dl, nl, dtl⟩, h11, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨oe, c4⟩, h12, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨fo, cf, cfx'⟩, h12', henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  refine ⟨?_, fun hc hhit => ?_⟩
  · have v.event_data : v.event.isData = true := by
      have := sh.onAnswer.ht; simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at this; exact this.2
    have hinv' := v.invariants.code_fn (by simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, v.records_data]) hinv hci
    match shs, hk, hR.pending, henc, hshs, senv with
    | sh0 :: rest, hk, ⟨tbl, htbl, hlist⟩, henc, hshs, senv =>
    rw [holds_ite_hit]
    refine imp_congr_right fun hhit => ?_
    -- The slot holds the request `to` names, as an entry of the shape `sh`.
    obtain ⟨hhf, hhrest⟩ := (holds_and _ _).1 hhit
    obtain ⟨hheq, hhis⟩ := (holds_and _ _).1 hhrest
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view (M := M) htbl h1
    obtain ⟨b, hbsv, hfb⟩ := slot_at hS jn h3'
    have hb : b = true := by simpa [Holds, hfb, Val.toBool] using hhf
    subst hb
    obtain ⟨y, hy, zk, zv, hxs, hzk, hzv⟩ := forall2_mem_right hh _ (by
      simp only [occupied, List.mem_filterMap]; exact ⟨_, hbsv, rfl⟩)
    simp only [Term.denotes, List.cons.injEq, and_true] at hxs
    obtain ⟨htk, hte⟩ := hxs
    have hkey : (y.1 : Nat) = to := by
      have e := Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at hheq; exact hheq)
      change zk = Val.int (Int.ofNat y.1) at hzk
      rw [htk, hzk, hto] at e
      exact Int.ofNat.inj (Val.int.inj e)
    obtain ⟨d', n', hf', hra⟩ := hzv
    have hde := find_det hf' h2
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
    have hdom : (∀ p, s.pending.find? (·.id == to) = some p → answerFits L.count T (sh0 :: rest) s p to ⟨_, value⟩) ↔
        answerFits L.count T (sh0 :: rest) s (sh.pending to (f0, f1, f2, f3, ())) to ⟨_, value⟩ :=
      ⟨fun h => h _ hfind, fun h p hp => by rw [hfind] at hp; cases hp; exact h⟩
    rw [hdom]
    show _ ↔ answerFits L.count T (sh0 :: rest) s (sh.pending to (f0, f1, f2, f3, ())) to
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
    have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, v.event_data]
    have hrem : PendingRel L (sh0 :: rest) ((slotsTerm d dt (filterSlots (slotsOf d dt n 2 S.pending)
        (keepQs toT (slotsOf d dt n 2 S.pending)))).denote M) (s.pending.filter (·.id != to)) := by
      have ha := keep_aligned (L := L) (k := .dsl .fresh []) (w := pendingEntry (sh0 :: rest)) rfl (to : Nat) toT hto hS hh
      obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
      have hl' : sv'.length = n := by rw [← hl]; simpa using congrArg List.length hsnd
      have hw' : ∀ p ∈ sv', p.2.length = 2 := fun p hp' => by
        have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
        obtain ⟨q, hq, e⟩ := List.mem_map.1 this
        rw [← e]; exact hw q hq
      let Q := fun (e : (Ty.dsl .fresh []).den × (pendingEntry (sh0 :: rest)).den) =>
        !((Ty.dsl .fresh []).deq (to : Nat) e.1 || (Ty.dsl .fresh []).deq e.1 (to : Nat))
      let tbl' : (pendingTable (sh0 :: rest)).den := ⟨tbl.1.filter Q, tbl.2.filter Q⟩
      have hrel := table_mk (x := tbl') h1 hS' hl' hw' (hperm.filter _) hh'
      refine ⟨tbl', hrel, ?_⟩
      rw [← hlist]
      exact filter_pendingList (sh0 :: rest) to tbl.1
    have e45 : Holds M c1 → Holds M c2 → Holds M c3 →
        (Holds M (.ite (allT (rules.map (·.2))) (andT c4 cf) tt) ↔
        (Step.broken (match ensuresFn sh.ensures (Ty.down _ hd2 f2) with
            | some f => f.fn (Ty.down _ hd1 f1, value, ())
            | none => []) = [] →
          eventsFit L.count T { s with pending := s.pending.filter (·.id != to) }
              ((sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ())) ∧
            finishFits L.count T (sh0 :: rest) (Step.applyEvents T
              { state := { s with pending := s.pending.filter (·.id != to) } }
              ((sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ()))))) := by
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
      obtain ⟨svl, hSl, -, -, hhl⟩ := list_view (M := M) hlv h11
      erw [Ty.up_list _ _ v.event_data] at hhl
      have hbroken := hens.2 hc3
      have hall : ((allT (rules.map (·.2))).denote M).toBool = decide (Step.broken (match ensuresFn sh.ensures
          (Ty.down _ hd2 f2) with
            | some f => f.fn (Ty.down _ hd1 f1, value, ())
            | none => []) = []) := by
        rw [toBool_allT_rules, hbroken]
      rw [holds_ite_tt hall, decide_eq_true_iff]
      refine imp_congr_right fun _ => ?_
      rw [holds_andT]
      let s' : State v := { s with pending := s.pending.filter (·.id != to) }
      let evL := (sh.onAnswer.fn (Ty.down _ hd3 f3)).fn (value, ())
      let sA := (Step.reactAll T s' evL).1
      have v.apply.ht : (Ty.fn [v.records, v.event] v.records).isData = true := by simp [Ty.isData, Ty.isDatas, v.records_data, v.event_data]
      have e4 : Holds M c4 ↔ eventsFit L.count T s' evL :=
        (events_encode chk hshs happ hca senv _ svl hSl _ hhl s' hR.now hR.records hR.machines h12).1
      have hinv' : Step.Inv P s' := hsinv.filterPending _
      have ef : Holds M c4 → (Holds M cf ↔ finishFits L.count T (sh0 :: rest) (Step.applyEvents T { state := s' } evL)) :=
        fun hc4 => (finish_encode chk hshs happ hca hinv hci senv s .accepted
          { state := s' } rfl hinv' hR.now hrem (loop_acc (T := T) chk hshs happ hca senv
            { state := s' } hR.now hSl hhl hR.records hR.machines hR.nextId (q := .int 0) (q0 := 0) rfl hR.fresh h12 hc4) (applyEvents_ok chk.reach _ rfl hinv' _) h12'
          hcfx).1
      constructor
      · rintro ⟨hc4, hcf⟩
        exact ⟨e4.1 hc4, (ef hc4).1 hcf⟩
      · rintro ⟨p4, pf⟩
        have hc4 := e4.2 p4
        exact ⟨hc4, (ef hc4).2 pf⟩
    rw [holds_andT, holds_andT, holds_andT]
    constructor
    · rintro ⟨hc1, hc2, hc3, hc45⟩
      exact ⟨e1.1 hc1, (e2 hc1).1 hc2, hens.1.1 hc3, (e45 hc1 hc2 hc3).1 hc45⟩
    · rintro ⟨p1, p2, p3, p45⟩
      have hc1 := e1.2 p1
      have hc2 := (e2 hc1).2 p2
      have hc3 := hens.1.2 p3
      exact ⟨hc1, hc2, hc3, (e45 hc1 hc2 hc3).2 p45⟩
  · have v.event_data : v.event.isData = true := by
      have := sh.onAnswer.ht; simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at this; exact this.2
    have happ0 := happ
    have hinv0 := hinv
    have happ := v.apply.code_fn (by simp [Ty.isData, Ty.isDatas, v.records_data, v.event_data]) happ hca
    match shs, hk, hR.pending, henc, hshs, senv with
    | sh0 :: rest, hk, ⟨tbl, htbl, hlist⟩, henc, hshs, senv =>
    -- The slot holds the request `to` names, as an entry of the shape `sh`.
    obtain ⟨hhf, hhrest⟩ := (holds_and _ _).1 hhit
    obtain ⟨hheq, hhis⟩ := (holds_and _ _).1 hhrest
    obtain ⟨sv, ys, hS, hl, hw, hperm, hh⟩ := table_view (M := M) htbl h1
    obtain ⟨b, hbsv, hfb⟩ := slot_at hS jn h3'
    have hb : b = true := by simpa [Holds, hfb, Val.toBool] using hhf
    subst hb
    obtain ⟨y, hy, zk, zv, hxs, hzk, hzv⟩ := forall2_mem_right hh _ (by
      simp only [occupied, List.mem_filterMap]; exact ⟨_, hbsv, rfl⟩)
    simp only [Term.denotes, List.cons.injEq, and_true] at hxs
    obtain ⟨htk, hte⟩ := hxs
    have hkey : (y.1 : Nat) = to := by
      have e := Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at hheq; exact hheq)
      change zk = Val.int (Int.ofNat y.1) at hzk
      rw [htk, hzk, hto] at e
      exact Int.ofNat.inj (Val.int.inj e)
    obtain ⟨d', n', hf', hra⟩ := hzv
    have hde := find_det hf' h2
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
    have hstep : step T v s (.answer to ⟨_, value⟩) = match Step.broken ((sh.pending to fx).request.holds value) with
        | r :: rs => ⟨s, .invalid (r :: rs), [], []⟩
        | [] => Step.finish T s (Step.applyEvents T { state := { s with pending := s.pending.filter (·.id != to) } }
            ((sh.pending to fx).request.onAnswer.fn (value, ()))) .accepted := by
      have e : (answerTy sh.output sh.rejection).same
          (answerTy (sh.pending to fx).request.output (sh.pending to fx).request.rejection) = some ⟨rfl⟩ :=
        Ty_same_rfl _
      simp only [step, hfind]
      rw [e]
      rfl
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
    have hc' := (holds_ite _ _ _).1 hc
    have hhitT : (Term.denote M (f.and ((tk.eq toT).and (Term.is de k te)))).toBool = true := hhit
    simp only [hhitT, ite_true] at hc'
    rw [holds_andT, holds_andT, holds_andT] at hc'
    obtain ⟨hc1, hc2, hc3, hc45⟩ := hc'
    have hoa := encode_agrees sh.onAnswer.defs sh.onAnswer.defs.eval (sh.onAnswer.defs.encode L)
      (Defs.encode_agrees M L sh.onAnswer.defs) sh.onAnswer.body σa f3 hσa oa c1 h7 hc1
    have hoa' : Rel M L _ (Ty.up _ sh.onAnswer.ht (sh.onAnswer.fn (Ty.down _ hd3 f3)).fn) oa := by
      rw [Fun.fn, Ty.up_down]
      have e : Ty.up (.tuple sh.answerΓ) sh.onAnswer.hΓ (Ty.down _ hd3 f3) = f3 := Ty.up_down _ hd3 f3
      simp only [Fun.eval, Site.fn]; rw [e]; exact hoa
    have hvc : Smt.Rel M L _ (Ty.up _ hans value) vc := (rel_ofTerm (need_ok.1 h6) _).2 hval
    have hta : (Ty.tuple [answerTy sh.output sh.rejection]).isData = true := by simp [Ty.isData, Ty.isDatas, hans]
    have hargs : Smt.Rels M L [answerTy sh.output sh.rejection]
        (Ty.up (.tuple [answerTy sh.output sh.rejection]) hta (value, ())) (vc, ()) := by
      show Smt.Rel M L _ (Ty.up (.tuple [answerTy sh.output sh.rejection]) hta (value, ())).1 vc ∧ True
      erw [Ty.up_tuple _ _ _ hans rfl]; exact ⟨hvc, trivial⟩
    have hevs := hoa' _ (vc, ()) hargs evs c2 h8 hc2
    have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, v.event_data]
    erw [Ty.up_fn _ _ _ hta hle] at hevs
    -- The query's `ensures` at the captured values, on the input and the answer.
    have hbroken : brokenIn M rules = Step.broken ((sh.pending to (f0, f1, f2, f3, ())).request.holds value) := by
      show brokenIn M rules = Step.broken (RequestV.holds ⟨sh.name, sh.input, sh.output, sh.rejection,
        (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.1,
        ensuresFn sh.ensures (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.1,
        sh.onAnswer.fn (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.2.1⟩ value)
      rw [hY1, hY2]
      unfold ensuresTerms at h9
      obtain ⟨⟨_, _, si, so, sj, ens, _, _, _⟩, _, _, _⟩ := sh
      cases ens with
      | none =>
        cases pure_ok.1 h9
        simp [RequestV.holds, brokenIn, Step.broken, ensuresFn]
      | some es =>
        obtain ⟨Γ, es⟩ := es
        obtain ⟨⟨dn, dnn⟩, g1, h9⟩ := bind_ok.1 h9
        obtain ⟨σe, g2, h9⟩ := bind_ok.1 h9
        obtain ⟨ic, g3, h9⟩ := bind_ok.1 h9
        obtain ⟨⟨oe, ce⟩, g4, h9⟩ := bind_ok.1 h9
        obtain ⟨⟨rs, ce'⟩, g5, h9⟩ := bind_ok.1 h9
        obtain ⟨rl, g6, h9⟩ := bind_ok.1 h9
        cases pure_ok.1 h9
        rw [holds_andT] at hc3
        obtain ⟨dn', nn', vals2, hfe, hv2e, hrel2⟩ := hv2
        obtain rfl := find_det hfe (need_ok.1 g1)
        have hσe : Rels M L Γ f2 σe :=
          tupleCodes_rels Γ [] vals2 f2 σe (by rw [hsel 2 v2 rfl, hv2e]; rfl) hrel2 (need_ok.1 g2)
        have hoe := encode_agrees es.defs es.defs.eval (es.defs.encode L) (Defs.encode_agrees M L es.defs) es.body σe f2
          hσe oe ce g4 hc3.1
        have hoe' : Rel M L _ (Ty.up _ es.ht (es.fn (Ty.down _ hd2 f2)).fn) oe := by
          rw [Fun.fn, Ty.up_down]
          have e : Ty.up (.tuple Γ) es.hΓ (Ty.down _ hd2 f2) = f2 := Ty.up_down _ hd2 f2
          simp only [Fun.eval, Site.fn]; rw [e]; exact hoe
        have hic : Smt.Rel M L si (Ty.up _ hd1 (Ty.down _ hd1 f1)) ic := by
          rw [Ty.up_down]; exact (rel_ofTerm (need_ok.1 g3) _).2 (by rw [hsel 1 v1 rfl]; exact hv1)
        have hte2 : (Ty.tuple [si, answerTy so sj]).isData = true := by
          simp [Ty.isData, Ty.isDatas, hd1, hans]
        have hargs2 : Smt.Rels M L [si, answerTy so sj]
            (Ty.up (.tuple [si, answerTy so sj]) hte2 (Ty.down _ hd1 f1, value, ())) (ic, vc, ()) := by
          show Smt.Rel M L _ (Ty.up (.tuple [si, answerTy so sj]) hte2
            (Ty.down _ hd1 f1, value, ())).1 ic ∧ Smt.Rels M L [answerTy so sj]
              (Ty.up (.tuple [si, answerTy so sj]) hte2 (Ty.down _ hd1 f1, value, ())).2 (vc, ())
          erw [Ty.up_tuple _ _ _ hd1 hta]
          exact ⟨hic, hargs⟩
        have hrs := hoe' _ _ hargs2 rs ce' g5 hc3.2
        erw [Ty.up_fn _ Ty.rules _ hte2 rfl] at hrs
        rw [rules_broken g6 _ hrs]
        rfl
    have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, v.event_data]
    have v.apply.ht : (Ty.fn [v.records, v.event] v.records).isData = true := by simp [Ty.isData, Ty.isDatas, v.records_data, v.event_data]
    -- The table without the request: its slots filtered by key, as `table.remove` does.
    have hrem : PendingRel L (sh0 :: rest) ((slotsTerm d dt (filterSlots (slotsOf d dt n 2 S.pending)
        (keepQs toT (slotsOf d dt n 2 S.pending)))).denote M) (s.pending.filter (·.id != to)) := by
      have ha := keep_aligned (L := L) (k := .dsl .fresh []) (w := pendingEntry (sh0 :: rest)) rfl (to : Nat) toT hto hS hh
      obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
      have hl' : sv'.length = n := by rw [← hl]; simpa using congrArg List.length hsnd
      have hw' : ∀ p ∈ sv', p.2.length = 2 := fun p hp' => by
        have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
        obtain ⟨q, hq, e⟩ := List.mem_map.1 this
        rw [← e]; exact hw q hq
      let Q := fun (e : (Ty.dsl .fresh []).den × (pendingEntry (sh0 :: rest)).den) =>
        !((Ty.dsl .fresh []).deq (to : Nat) e.1 || (Ty.dsl .fresh []).deq e.1 (to : Nat))
      let tbl' : (pendingTable (sh0 :: rest)).den := ⟨tbl.1.filter Q, tbl.2.filter Q⟩
      have hrel := table_mk (x := tbl') h1 hS' hl' hw' (hperm.filter _) hh'
      refine ⟨tbl', hrel, ?_⟩
      rw [← hlist]
      exact filter_pendingList (sh0 :: rest) to tbl.1
    -- The step itself: Invalid on a broken rule, else the events run and the invariants decide.
    have hr : r = _ := hstep
    rw [hr, hbroken]
    cases hb : Step.broken ((sh.pending to (f0, f1, f2, f3, ())).request.holds value) with
    | cons n ns => rfl
    | nil =>
    simp only
    have hall : (allT (rules.map (·.2))).denote M = .bool true := by
      rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil rules).1 (hbroken.trans hb))
    obtain ⟨hc4, hcf⟩ : Holds M c4 ∧ Holds M cf := by
      have := (holds_ite _ _ _).1 hc45; rw [hall] at this
      simpa [Val.toBool, holds_andT] using this
    -- The events of `on_answer`, run through the events loop.
    have hevs' : RelV L (.list v.event) (Ty.up _ hle ((sh.pending to (f0, f1, f2, f3, ())).request.onAnswer.fn (value, ())))
        (evt.denote M) := by
      show RelV L (.list v.event) (Ty.up _ hle ((sh.onAnswer.fn
        (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.2.1).fn (value, ()))) (evt.denote M)
      rw [hY3]; exact (rel_term (need_ok.1 h10) _).1 hevs
    have hlv := (rel_term (need_ok.1 h10) _).2 hevs'
    have hee : evs = evt := Option.some.inj (need_ok.1 h10)
    subst hee
    obtain ⟨svl, hSl, -, -, hhl⟩ := list_view (M := M) hlv h11
    erw [Ty.up_list _ _ v.event_data] at hhl
    let s' : State v := { s with pending := s.pending.filter (·.id != to) }
    have hinv' : Step.Inv P s' := hsinv.filterPending _
    have hdone := loop_acc (T := T) chk hshs happ0 hca senv
      { state := s' } hR.now hSl hhl hR.records hR.machines hR.nextId (q := .int 0) (q0 := 0) rfl hR.fresh h12 hc4
    exact (finish_encode chk hshs happ0 hca hinv0 hci senv s
      .accepted { state := s' } rfl hinv' hR.now hrem hdone (applyEvents_ok chk.reach _ rfl hinv' _) h12' hcfx).2 hcf

end

end Tazuna.Smt
