import Tazuna.Smt.StepEncode

/-! The pieces of an answer step: reading the pending table's slot that holds the request the answer names (the
captured values of its sites as codes), the rules a query's `ensures` keeps, and the unmatched case: an answer that
names no request of a shape with its type is `Fault.answerUnmatched` (`answer_unmatched`). `Tazuna.Smt.Answer` holds
the matched case, `answer_step`, so the two cover every answer of a given type. -/

namespace Tazuna.Smt

variable {T : List Ir.TypeDecl}

open Tazuna.Ir




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
    step T v s (.answer to ⟨t, value⟩) = ⟨s, .fault .answerUnmatched, [], []⟩ := by
  cases hf : s.pending.find? (·.id == to) with
  | none => simp only [step, hf]
  | some p =>
  match shs, hpend, henc with
  | [], ⟨tbl, _, hlist⟩, _ =>
    match tbl, hlist with
    | ⟨[], _⟩, hlist => simp only [pendingList, List.map_nil] at hlist; simp [← hlist] at hf
    | ⟨(_, x) :: _, _⟩, _ => exact nomatch x
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
  obtain ⟨vs, hvs, zk, zv, hxs, hzk, hzv⟩ := forall2_mem_left hh (y1, y2) (hperm.mem_iff.2 hy)
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
