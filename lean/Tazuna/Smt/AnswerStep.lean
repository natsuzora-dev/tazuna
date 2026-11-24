import Tazuna.Smt.StepEncode

/-! T2 for an answer, on a service without reactions and a state without machine instances. The answer names the
pending request by its wire id `to`; the pending table's slot that holds `to` holds the request as an entry of one
shape, so the step runs that shape's sites at the captured values the entry holds: its query's `ensures` on the
input and the answer, then its `on_answer`, whose events apply in order before the invariants are checked. The
request leaves the table. An answer that names no request of a shape with its type is `Fault.answerUnmatched`.

`answer_step` takes a slot and a shape the script fixes, and `answer_unmatched` the case where no slot holds a request
the answer's type fits, so the statements together cover every answer of a given type. -/

namespace Tazuna.Smt

variable {T : List Ir.TypeDecl}

open Tazuna.Ir


mutual
theorem Ty_same_self : (t : Ty) → (Ty.same t t).isSome = true
  | .int | .str | .date | .id => rfl
  | .param i => by simp [Ty.same]
  | .list a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self a); simp [Ty.same, e]
  | .bag a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self a); simp [Ty.same, e]
  | .tuple a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a); simp [Ty.same, e]
  | .fn a r => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_same_self r)
    simp [Ty.same, e, e']
  | .adt i a v => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_samess_self v)
    simp [Ty.same, e, e']
  | .table k v => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self k)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_same_self v)
    simp [Ty.same, e, e']
  | .dsl k a => by obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self a); simp [Ty.same, e]
theorem Ty_sames_self : (ts : List Ty) → (Ty.sames ts ts).isSome = true
  | [] => rfl
  | t :: ts => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self t)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_sames_self ts)
    simp [Ty.sames, e, e']
theorem Ty_samess_self : (vs : List (List Ty)) → (Ty.samess vs vs).isSome = true
  | [] => rfl
  | ts :: vs => by
    obtain ⟨⟨_⟩, e⟩ := Option.isSome_iff_exists.1 (Ty_sames_self ts)
    obtain ⟨⟨_⟩, e'⟩ := Option.isSome_iff_exists.1 (Ty_samess_self vs)
    simp [Ty.samess, e, e']
end

theorem Ty_same_rfl (t : Ty) : Ty.same t t = some ⟨rfl⟩ := by
  obtain ⟨x, e⟩ := Option.isSome_iff_exists.1 (Ty_same_self t); rw [e]


section
variable (L : Layout)

/-- The codes of a tuple's items, each the selector of its field from `x` of the tuple datatype `d`. -/
def tupleCodes (d : Nat) : (Γ : List Ty) → Term → Nat → Option (Codes Γ)
  | [], _, _ => some ()
  | t :: Γ, x, i => do pure ((← Code.ofTerm? t (.sel d 0 i x)), (← tupleCodes d Γ x (i + 1)))

/-- The code of a site's source over the codes of the values it captured. -/
def _root_.Tazuna.Ir.Site.code {Γ : List Ty} {t : Ty} (s : Site Γ t) (σ : Codes Γ) : Enc (Code t) :=
  encode L (s.defs.encode L) s.body σ

end

section
variable {M : Model} {L : Layout}

theorem tupleCodes_rels {d : Nat} {x : Term} : (Γ : List Ty) → (pre vals : List Val) → (ρ : Ty.dens Γ) →
    (σ : Codes Γ) → x.denote M = .ctor d 0 (pre ++ vals) → RelVs L Γ ρ vals → tupleCodes d Γ x pre.length = some σ →
    Rels M L Γ ρ σ
  | [], _, _, _, _, _, _, _ => trivial
  | t :: Γ, pre, vals, (y, ys), (c, cs), hx, ⟨w, ws, hv, hw, hws⟩, h => by
    subst hv
    cases hc : Code.ofTerm? t (Term.sel d 0 pre.length x) with
    | none => simp [tupleCodes, hc] at h
    | some c' =>
    cases hcs : tupleCodes d Γ x (pre.length + 1) with
    | none => simp [tupleCodes, hc, hcs] at h
    | some cs' =>
    simp only [tupleCodes, hc, hcs, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(rel_ofTerm hc _).2 ?_, tupleCodes_rels Γ (pre ++ [w]) ws ys cs (by simpa using hx) hws (by simpa using hcs)⟩
    rw [sel_ctor _ hx]; simpa using hw

theorem forall2_mem' {α β : Type} {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs → ∀ b ∈ bs,
    ∃ a ∈ as, R a b
  | [], [], _, _, hb => by simp at hb
  | a :: as, b :: bs, ⟨h, hs⟩, b', hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, by simp, h⟩
    · obtain ⟨a', ha', h'⟩ := forall2_mem' hs b' hb; exact ⟨a', by simp [ha'], h'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem slot_at : {S : List Slot} → {sv : List (Bool × List Val)} → SlotsDen M S sv → (j : Nat) → {f : Term} →
    {xs : List Term} → S[j]? = some (f, xs) → ∃ b, (b, Term.denotes M xs) ∈ sv ∧ f.denote M = .bool b
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

/-- The terms of an answer step at one slot: whether the slot holds the request `to` names as an entry of the shape,
the `ensures` rules, the events of `on_answer`, the records after them, the invariants there, and the pending table
without the request. -/
structure AnswerOut where
  hit : Term
  rules : List (Term × Term)
  events : Term
  records : Term
  invariants : List (Term × Term)
  pending : Term

section
variable (L : Layout) {v : ServiceV}

/-- The rules a query's `ensures` keeps for an answer, from the entry's input and captured values, with their
condition; a command's answers keep none. -/
def ensuresTerms {e : Ty} (sh : PendingShape e) (de k : Nat) (entry : Term)
    (vc : Code (answerTy sh.output sh.rejection)) : Except Refusal (List (Term × Term) × Term) :=
  match sh.ensures with
  | none => pure ([], tt)
  | some es => do
    let (dn, _) ← need "a layout without the captures' tuple" (L.find? (.tuple sh.ensuresΓ))
    let σe ← need "captures that have no term" (tupleCodes dn sh.ensuresΓ (.sel de k 2 entry) 0)
    let ic ← need "an input that has no term" (Code.ofTerm? sh.input (.sel de k 1 entry))
    let (oe, c) ← es.code L σe
    let (rs, c') ← oe (ic, vc, ())
    pure (← ruleTerms L rs, andT c c')

/-- An answer step's terms at slot `j` for requests of the shape `sh`, the `k`-th of `shs`, and its condition, from
the codes of the service's `apply` and `invariants` and the terms of the records, the pending table, the wire id the
answer names and the answer. -/
def encodeAnswer (shs : List (PendingShape v.event)) (k : Nat) (sh : PendingShape v.event) (j : Nat)
    (apply : Code (Ty.fn [v.records, v.event] v.records)) (invariants : Code (Ty.fn [v.records] Ty.rules))
    (records pending to value : Term) : Except Refusal (AnswerOut × Term) := do
  let (d, n, dt) ← collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs]
  let (de, _) ← need "a layout without the pending entry" (L.find? (pendingEntry shs))
  let S := slotsOf d dt n 2 pending
  let (f, xs) ← need "a slot past the pending table" S[j]?
  let entry := xs.getD 1 tt
  let hit := Term.and f (.and (.eq (xs.headD tt) to) (.is de k entry))
  let (da, _) ← need "a layout without the captures' tuple" (L.find? (.tuple sh.answerΓ))
  let σa ← need "captures that have no term" (tupleCodes da sh.answerΓ (.sel de k 3 entry) 0)
  let vc ← need "an answer that has no term" (Code.ofTerm? _ value)
  let (oa, c1) ← sh.onAnswer.code L σa
  let (evs, c2) ← oa (vc, ())
  let (rules, c3) ← ensuresTerms L sh de k entry vc
  let evt ← need "events that have no term" (Code.term? _ evs)
  let (dl, nl, dtl) ← collD L (.list v.event) [v.event]
  let (rf, c4) ← applyAll apply records (slotsOf dl dtl nl 1 evt)
  let rfc ← need "records that have no term" (Code.ofTerm? v.records rf)
  let (invs, c5) ← invariants (rfc, ())
  let inv ← ruleTerms L invs
  pure (⟨hit, rules, evt, rf, inv, slotsTerm d dt (filterSlots S (keepQs to S))⟩,
    .ite hit (andT c1 (andT c2 (andT c3 (.ite (allT (rules.map (·.2))) (andT c4 c5) tt)))) tt)

/-- Whether no slot holds the request `to` names as an entry of a shape whose answers have the type `t`. -/
def answerUnmatchedT (shs : List (PendingShape v.event)) (t : Ty) (pending to : Term) : Except Refusal Term := do
  let (d, n, dt) ← collD L (pendingTable shs) [.dsl .fresh [], pendingEntry shs]
  let (de, _) ← need "a layout without the pending entry" (L.find? (pendingEntry shs))
  let typed := (List.range shs.length).filter fun k => match shs[k]? with
    | some sh => (Ty.same (answerTy sh.output sh.rejection) t).isSome
    | none => false
  pure (allT ((slotsOf d dt n 2 pending).map fun (f, xs) =>
    .not (.and f (.and (.eq (xs.headD tt) to) (anyT (typed.map fun k => .is de k (xs.getD 1 tt)))))))

end

section
variable {v : ServiceV}

/-- An answer's step on a service without reactions from a state without machine instances, computed, when the
request it names is `p` and the answer has `p`'s type. -/
theorem step_answer (hx : v.reactions = []) (s : State v) (hs : s.machines = []) (to : Nat) (p : Step.Pending v.event)
    (hp : s.pending.find? (·.id == to) = some p) (value : (answerTy p.request.output p.request.rejection).den0) :
    let evs := p.request.onAnswer.fn (value, ())
    let records := evs.foldl (fun r ev => v.apply.fn (r, ev, ())) s.records
    step T v s (.answer to ⟨_, value⟩) = match Step.broken (p.request.holds value) with
      | r :: rs => ⟨s, .invalid (r :: rs), [], []⟩
      | [] => match Step.broken (v.invariants.fn (records, ())) with
        | n :: _ => ⟨s, .fault (.invariant n), [], []⟩
        | [] => ⟨{ s with records, pending := s.pending.filter (·.id != to) }, .accepted, evs, []⟩ := by
  intro evs records
  simp only [step, hp, Ty_same_rfl]
  cases Step.broken (p.request.holds value) with
  | cons r rs => rfl
  | nil =>
    simp only
    rw [applyEvents_plain hx (p.request.onAnswer.fn (value, ()))
      { state := { s with pending := s.pending.filter (·.id != to) } } hs]
    simp only [Step.finish, Step.Acc.folded, bind, Except.bind, Step.settle, Step.invariants, hs, List.flatMap_nil,
      List.append_nil]
    cases Step.broken (v.invariants.fn (records, ())) <;> rfl

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

/-- T2 for an answer on a service without reactions, from a state without machine instances, at the slot `j` and the
shape `sh`: wherever the condition holds and the slot holds the request the answer names as an entry of `sh`, a
broken `ensures` rule makes the answer Invalid, a broken invariant is the step's fault, and otherwise the step is
accepted with the records, the events and the pending table the terms denote, the request gone. -/
theorem answer_step (hx : v.reactions = []) (s : State v) (hs : s.machines = []) (hrd : v.records.isData = true)
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
    {o : AnswerOut} {cond : Term} (henc : encodeAnswer L shs k sh j apply inv records pending toT valT = .ok (o, cond))
    (hc : Holds M cond) (hhit : Holds M o.hit) :
    let r := step T v s (.answer to ⟨_, value⟩)
    match brokenIn M o.rules with
    | n :: ns => r = ⟨s, .invalid (n :: ns), [], []⟩
    | [] => match brokenIn M o.invariants with
      | n :: _ => r = ⟨s, .fault (.invariant n), [], []⟩
      | [] => r.outcome = .accepted ∧ r.out = [] ∧
          r.state = { s with records := r.state.records, pending := s.pending.filter (·.id != to) } ∧
          RelV L v.records (Ty.up _ hrd r.state.records) (o.records.denote M) ∧
          (∃ he : (Ty.list v.event).isData = true, RelV L (.list v.event) (Ty.up _ he r.events) (o.events.denote M)) ∧
          PendingRel L shs (o.pending.denote M) r.state.pending := by
  intro r
  have hed : v.event.isData = true := by
    have := sh.onAnswer.ht; simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at this; exact this.2
  have happ := v.apply.code_fn (by simp [Ty.isData, Ty.isDatas, hrd, hed]) happ hca
  have hinv := v.invariants.code_fn (by simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hrd]) hinv hci
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
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at hheq hhis h5 h9 hc
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
  have hstep := step_answer (T := T) hx s hs to (sh.pending to fx) hfind value
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
  have hle : (Ty.list v.event).isData = true := by simp [Ty.isData, hed]
  erw [Ty.up_fn _ _ _ hta hle] at hevs
  -- The query's `ensures` at the captured values, on the input and the answer.
  have hbroken : brokenIn M rules = Step.broken ((sh.pending to (f0, f1, f2, f3, ())).request.holds value) := by
    show brokenIn M rules = Step.broken (RequestV.holds ⟨sh.name, sh.input, sh.output, sh.rejection,
      (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.1,
      sh.ensures.map (·.fn (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.1),
      sh.onAnswer.fn (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.2.1⟩ value)
    rw [hY1, hY2]
    unfold ensuresTerms at h9
    cases hens : sh.ensures with
    | none =>
      rw [hens] at h9
      cases pure_ok.1 h9
      simp [RequestV.holds, brokenIn, Step.broken]
    | some es =>
      rw [hens] at h9
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
      have hσe : Rels M L sh.ensuresΓ f2 σe :=
        tupleCodes_rels sh.ensuresΓ [] vals2 f2 σe (by rw [hsel 2 v2 rfl, hv2e]; rfl) hrel2 (need_ok.1 g2)
      have hoe := encode_agrees es.defs es.defs.eval (es.defs.encode L) (Defs.encode_agrees M L es.defs) es.body σe f2
        hσe oe ce g4 hc3.1
      have hoe' : Rel M L _ (Ty.up _ es.ht (es.fn (Ty.down _ hd2 f2)).fn) oe := by
        rw [Fun.fn, Ty.up_down]
        have e : Ty.up (.tuple sh.ensuresΓ) es.hΓ (Ty.down _ hd2 f2) = f2 := Ty.up_down _ hd2 f2
        simp only [Fun.eval, Site.fn]; rw [e]; exact hoe
      have hic : Smt.Rel M L sh.input (Ty.up _ hd1 (Ty.down _ hd1 f1)) ic := by
        rw [Ty.up_down]; exact (rel_ofTerm (need_ok.1 g3) _).2 (by rw [hsel 1 v1 rfl]; exact hv1)
      have hte2 : (Ty.tuple [sh.input, answerTy sh.output sh.rejection]).isData = true := by
        simp [Ty.isData, Ty.isDatas, hd1, hans]
      have hargs2 : Smt.Rels M L [sh.input, answerTy sh.output sh.rejection]
          (Ty.up (.tuple [sh.input, answerTy sh.output sh.rejection]) hte2 (Ty.down _ hd1 f1, value, ())) (ic, vc, ()) := by
        show Smt.Rel M L _ (Ty.up (.tuple [sh.input, answerTy sh.output sh.rejection]) hte2
          (Ty.down _ hd1 f1, value, ())).1 ic ∧ Smt.Rels M L [answerTy sh.output sh.rejection]
            (Ty.up (.tuple [sh.input, answerTy sh.output sh.rejection]) hte2 (Ty.down _ hd1 f1, value, ())).2 (vc, ())
        erw [Ty.up_tuple _ _ _ hd1 hta]
        exact ⟨hic, hargs⟩
      have hrs := hoe' _ _ hargs2 rs ce' g5 hc3.2
      erw [Ty.up_fn _ Ty.rules _ hte2 rfl] at hrs
      rw [rules_broken g6 _ hrs]
      simp [RequestV.holds]
  -- The step itself: Invalid on a broken rule, else the events apply and the invariants decide.
  have hr : r = _ := hstep
  rw [hr, hbroken]
  cases hb : Step.broken ((sh.pending to (f0, f1, f2, f3, ())).request.holds value) with
  | cons n ns => rfl
  | nil =>
  simp only
  have hall : (allT (rules.map (·.2))).denote M = .bool true := by
    rw [allT_denote]; exact congrArg Val.bool ((brokenIn_nil rules).1 (hbroken.trans hb))
  have hc45' : Holds M (andT c4 c5) := by
    have := (holds_ite _ _ _).1 hc45; rw [hall] at this; simpa [Val.toBool] using this
  obtain ⟨hc4, hc5⟩ := (holds_andT _ _).1 hc45'
  -- The events of `on_answer`, folded into the records.
  have hevs' : RelV L (.list v.event) (Ty.up _ hle ((sh.pending to (f0, f1, f2, f3, ())).request.onAnswer.fn (value, ())))
      (evt.denote M) := by
    show RelV L (.list v.event) (Ty.up _ hle ((sh.onAnswer.fn
      (Ty.down (.tuple sh.fields) sh.hdata (f0, f1, f2, f3, ())).2.2.2.1).fn (value, ()))) (evt.denote M)
    rw [hY3]; exact (rel_term (need_ok.1 h10) _).1 hevs
  have hlv := (rel_term (need_ok.1 h10) _).2 hevs'
  have hee : evs = evt := Option.some.inj (need_ok.1 h10)
  subst hee
  obtain ⟨svl, hSl, -, hswl, hhl⟩ := list_view (M := M) hlv h11
  erw [Ty.up_list _ _ hed] at hhl
  have hrf := applyAll_rel happ _ svl hSl hswl _ hhl _ records hrec rf c4 h12 hc4
  erw [← up_foldl hrd hed (by simp [Ty.isData, Ty.isDatas, hrd, hed])] at hrf
  have hrfc : Smt.Rel M L v.records _ rfc := (rel_ofTerm (need_ok.1 h13) _).2 hrf
  have hargs4 : Smt.Rels M L [v.records] (Ty.up (.tuple [v.records]) (by simp [Ty.isData, Ty.isDatas, hrd])
      (((sh.pending to (f0, f1, f2, f3, ())).request.onAnswer.fn (value, ())).foldl
        (fun r ev => v.apply.fn (r, ev, ())) s.records, ())) (rfc, ()) := by
    show Smt.Rel M L _ (Ty.up (.tuple [v.records]) (by simp [Ty.isData, Ty.isDatas, hrd])
      (((sh.pending to (f0, f1, f2, f3, ())).request.onAnswer.fn (value, ())).foldl
        (fun r ev => v.apply.fn (r, ev, ())) s.records, ())).1 rfc ∧ True
    erw [Ty.up_tuple _ _ _ hrd rfl]; exact ⟨hrfc, trivial⟩
  have hiv := hinv _ _ hargs4 invs c5 h14 hc5
  erw [Ty.up_fn _ Ty.rules _ (by simp [Ty.isData, Ty.isDatas, hrd]) rfl] at hiv
  rw [rules_broken h15 _ hiv]
  cases Step.broken (v.invariants.fn ((((sh.pending to (f0, f1, f2, f3, ())).request.onAnswer.fn (value, ())).foldl
      (fun r ev => v.apply.fn (r, ev, ())) s.records), ())) with
  | cons n ns => rfl
  | nil =>
  refine ⟨rfl, rfl, rfl, hrf, ⟨hle, hevs'⟩, ?_⟩
  -- The table without the request: its slots filtered by key, as `table.remove` does.
  have ha := keep_aligned (L := L) (k := .dsl .fresh []) (w := pendingEntry (sh0 :: rest)) rfl (to : Nat) toT hto hS hh
  obtain ⟨sv', hS', hh', hsnd⟩ := filterSlots_den ha
  have hl' : sv'.length = n := by rw [← hl]; simpa using congrArg List.length hsnd
  have hw' : ∀ p ∈ sv', p.2.length = 2 := fun p hp' => by
    have : p.2 ∈ sv.map (·.2) := hsnd ▸ List.mem_map_of_mem hp'
    obtain ⟨q, hq, e⟩ := List.mem_map.1 this
    rw [← e]; exact hw q hq
  let P := fun (e : (Ty.dsl .fresh []).den × (pendingEntry (sh0 :: rest)).den) =>
    !((Ty.dsl .fresh []).deq (to : Nat) e.1 || (Ty.dsl .fresh []).deq e.1 (to : Nat))
  let tbl' : (pendingTable (sh0 :: rest)).den := ⟨tbl.1.filter P, tbl.2.filter P⟩
  have hrel := table_mk (x := tbl') h1 hS' hl' hw' (hperm.filter _) hh'
  refine ⟨tbl', hrel, ?_⟩
  rw [← hlist]
  exact filter_pendingList (sh0 :: rest) to tbl.1

theorem forall2_mem_r {α β : Type} {R : α → β → Prop} : {as : List α} → {bs : List β} → Forall2 R as bs → ∀ a ∈ as,
    ∃ b ∈ bs, R a b
  | [], [], _, _, ha => by simp at ha
  | a :: as, b :: bs, ⟨h, hs⟩, a', ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, by simp, h⟩
    · obtain ⟨b', hb', h'⟩ := forall2_mem_r hs a' ha; exact ⟨b', by simp [hb'], h'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem slot_mem : {S : List Slot} → {sv : List (Bool × List Val)} → SlotsDen M S sv → ∀ p ∈ sv,
    ∃ q ∈ S, q.1.denote M = .bool p.1 ∧ Term.denotes M q.2 = p.2
  | [], [], _, _, hp => by simp at hp
  | (f, xs) :: S, (b, vs) :: sv, ⟨hf, hxs, hS⟩, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨(f, xs), by simp, hf, hxs⟩
    · obtain ⟨q, hq, h⟩ := slot_mem hS p hp; exact ⟨q, by simp [hq], h⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

/-- T2 for an answer that names no request of a shape whose answers have its type: wherever the term holds, the step
is `Fault.answerUnmatched`, whatever the records. -/
theorem answer_unmatched (s : State v) {shs : List (PendingShape v.event)} (to : Nat) (t : Ty) (value : t.den0)
    {pending toT : Term} (hpend : PendingRel L shs (pending.denote M) s.pending)
    (hto : toT.denote M = .int (Int.ofNat to)) {u : Term} (henc : answerUnmatchedT L shs t pending toT = .ok u)
    (hu : Holds M u) :
    step T v s (.answer to ⟨t, value⟩) = ⟨s, .fault (.answerUnmatched (toString to)), [], []⟩ := by
  cases hf : s.pending.find? (·.id == to) with
  | none => simp only [step, hf]
  | some p =>
  match shs, hpend, henc with
  | [], hpend, _ => simp only [PendingRel] at hpend; simp [hpend] at hf
  | sh0 :: rest, ⟨tbl, htbl, hlist⟩, henc =>
  obtain ⟨⟨d, n, dt⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨de, dn⟩, h2, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  -- The request found sits in an occupied slot with its wire id.
  have hp := List.mem_of_find?_eq_some hf
  have hpid : p.id = to := by simpa using List.find?_some hf
  rw [← hlist] at hp
  obtain ⟨⟨y1, y2⟩, hy, rfl⟩ := List.mem_map.1 hp
  obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view (M := M) htbl h1
  obtain ⟨vs, hvs, zk, zv, hxs, hzk, hzv⟩ := forall2_mem_r hh (y1, y2) (hperm.mem_iff.2 hy)
  have hocc : (true, vs) ∈ sv := by
    simp only [occupied, List.mem_filterMap] at hvs
    obtain ⟨⟨b, vs'⟩, hm, he⟩ := hvs
    cases b <;> simp at he
    exact he ▸ hm
  obtain ⟨⟨f, xs⟩, hq, hf1, hxs2⟩ := slot_mem hS _ hocc
  rw [hxs] at hxs2
  obtain ⟨tk, te, rfl⟩ : ∃ tk te, xs = [tk, te] := by
    match xs, hxs2 with
    | [tk, te], _ => exact ⟨tk, te, rfl⟩
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs2
  obtain ⟨htk, hte⟩ := hxs2
  obtain ⟨d', n', hf', hra⟩ := hzv
  have hde := find_det hf' (need_ok.1 h2)
  subst d'
  obtain ⟨j', sh', fx, vals, hj', hzv', -, hpo⟩ := relAlts_pending (L := L) y1 (sh0 :: rest) 0 y2 zv hra
  -- The slot's test is false, so no shape of the answer's type is that entry's.
  have hslot := (holds_allT _).1 hu _ (List.mem_map_of_mem hq)
  simp only [List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at hslot
  have hkey : (y1 : Nat) = to := (pendingOf_id _ _ _).symm.trans hpid
  change zk = Val.int (Int.ofNat y1) at hzk
  simp only [step, hf]
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
        | none => false).map fun k => Term.is de k te)))) := by
      rw [holds_and, holds_and]
      refine ⟨by simp [Holds, hf1, Val.toBool], ?_, ?_⟩
      · simp only [Holds, Term.denote, htk, hzk, hto, hkey, Val.toBool]
        show Val.beq (.int _) (.int _) = true
        simp [Val.beq]
      · simp only [Holds]; rw [anyT_denote]
        rw [Nat.zero_add] at hzv'
        refine List.any_eq_true.2 ⟨Term.is de j' te, List.mem_map_of_mem htyped, ?_⟩
        simp [Term.denote, hte, hzv', Val.toBool]
    have hX' : (Term.denote M _).toBool = true := hX
    have hs' : (Val.bool !(Term.denote M _).toBool).toBool = true := hslot
    rw [hX'] at hs'
    simp [Val.toBool] at hs'

end

end Tazuna.Smt
