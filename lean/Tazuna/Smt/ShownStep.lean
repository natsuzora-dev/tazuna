import Tazuna.Smt.Shown

/-! The ids a step's out lines show, as positions of its terms (`StepOut.shownT`): its answer's output or rejection,
its events, the inputs of the requests it sends. Each part is guarded by the condition under which the step reaches
it, so where the terms say what the step's result is and the step does not fault, the positions whose conditions hold
are exactly the ids the result shows (`shown_exact`, against `Result.shownIds`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout) {e : Ty}

/-- The id positions of the input of the request a pending entry holds, one per shape from `k`, each under the
condition that the entry is of that shape. -/
def entryIds (d : Nat) (entry : Term) : List (PendingShape e) → Nat → List (Term × Term)
  | [], _ => []
  | sh :: shs, k => guardIds (.is d k entry) (idsT L sh.input (.sel d k 1 entry)) ++ entryIds d entry shs (k + 1)

/-- The id positions of the inputs of the requests the slots write. -/
def newsIdsT (shs : List (PendingShape e)) (news : List PendingSlot) : List (Term × Term) :=
  match L.find? (pendingEntry shs) with
  | some (d, _) => news.flatMap fun ps => guardIds ps.flag (entryIds L d ps.entry shs 0)
  | none => []

/-- The id positions a step's end shows: its events', then its requests' inputs'. -/
def FinishOut.shownT {v : ServiceV} (shs : List (PendingShape v.event)) (fo : FinishOut v) : List (Term × Term) :=
  fo.events.flatMap (fun sl => guardIds sl.1 (idsT L v.event sl.2[0])) ++ newsIdsT L shs fo.news

/-- The id positions a step's out lines show, each where the step reaches it: a command's rejection or end, a query's
output, the end of an answer, an event or a clock line. -/
def StepOut.shownT {v : ServiceV} {n : Nat} : StepOut v → SymInput v (shapes v) n → List (Term × Term)
  | .command o, .command i _ _ =>
    let admitted := andT o.callerOk (allT (o.rules.map (·.2)))
    guardIds (andT admitted (.not o.decided.ok)) (idsT L (v.commands.get i).rejection o.decided.rejection) ++
      guardIds (andT admitted (andT o.decided.ok (allT (o.decided.ensures.map (·.2))))) (o.finish.shownT L (shapes v))
  | .query o, .query i _ _ =>
    guardIds (andT o.callerOk (allT (o.rules.map (·.2)))) (idsT L (v.queries.get i).output o.output)
  | .answer o, _ => guardIds (allT (o.rules.map (·.2))) (o.finish.shownT L (shapes v))
  | .event o, _ => o.finish.shownT L (shapes v)
  | .clock o, _ => guardIds o.forward (o.finish.shownT L (shapes v))
  | _, _ => []

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {e : Ty}

theorem mem_flatMap_of_forall2 {α β γ : Type} {R : α → β → Prop} {g : β → List γ} {c : γ}
    (hu : ∀ a b b', R a b → R a b' → (c ∈ g b ↔ c ∈ g b')) : {as : List α} → {bs : List β} → Forall2 R as bs →
    (c ∈ bs.flatMap g ↔ ∃ a ∈ as, ∃ b, R a b ∧ c ∈ g b)
  | [], [], _ => by simp
  | a :: as, b :: bs, ⟨h1, h2⟩ => by
    rw [List.flatMap_cons, List.mem_append, mem_flatMap_of_forall2 hu h2]
    constructor
    · rintro (h | ⟨a', ha', b', hr, hc⟩)
      · exact ⟨a, List.mem_cons_self, b, h1, h⟩
      · exact ⟨a', List.mem_cons_of_mem _ ha', b', hr, hc⟩
    · rintro ⟨a', ha', b', hr, hc⟩
      rcases List.mem_cons.1 ha' with rfl | ha'
      · exact .inl ((hu _ _ _ hr h1).1 hc)
      · exact .inr ⟨a', ha', b', hr, hc⟩

theorem writes_one {ds : List (String × DeclaredV)} {x : (Sender × EffectV e) × Nat} {p p' : Step.Pending e}
    (h : Step.Writes ds x p) (h' : Step.Writes ds x p') : p = p' := by
  obtain ⟨r, o, h1, h2, rfl⟩ := h
  obtain ⟨r', o', h1', h2', rfl⟩ := h'
  rw [h1] at h1'
  cases h1'
  rw [h2] at h2'
  cases h2'
  rfl

/-- The ids the requests' lines show. -/
abbrev linesIds (T : List TypeDecl) (ps : List (Step.Pending e)) : List IdV :=
  ps.flatMap fun p => Trace.idsOf T p.request.input p.request.value

theorem down_snd_fst {a b : Ty} {rest : List Ty} (h : (Ty.tuple (a :: b :: rest)).isData = true)
    (hb : b.isData = true) (x : Ty.dens (a :: b :: rest)) : (Ty.down _ h x).2.1 = Ty.down b hb x.2.1 := by
  have ha : a.isData = true := (Bool.and_eq_true _ _ ▸ h).1
  have hbr : (Ty.tuple (b :: rest)).isData = true := (Bool.and_eq_true _ _ ▸ h).2
  have hr : (Ty.tuple rest).isData = true := (Bool.and_eq_true _ _ ▸ hbr).2
  have e1 := congrArg (fun p => p.2.1) (Ty.up_tuple a (b :: rest) h ha hbr (Ty.down _ h x))
  have e2 := congrArg (fun p => p.1) (Ty.up_tuple b rest hbr hb hr (Ty.down _ h x).2)
  have h0 : (Ty.up _ h (Ty.down _ h x)).2.1 = x.2.1 := congrArg (fun p => p.2.1) (Ty.up_down _ h x)
  have h1 : x.2.1 = Ty.up b hb (Ty.down _ h x).2.1 := h0.symm.trans (e1.trans e2)
  exact (Ty.down_up b hb _).symm.trans (congrArg (Ty.down b hb) h1.symm)

/-- The ids of a request's input are the structure-level ids of its fields' input. -/
theorem pending_ids {sh : PendingShape e} (id : Nat) (fx : Ty.dens sh.fields) (i : IdV) :
    i ∈ Trace.idsOf T (sh.pending id fx).request.input (sh.pending id fx).request.value ↔ i ∈ idsV sh.input fx.2.1 := by
  have hr : (Ty.tuple sh.toRequestShape.fields).isData = true := sh.hfields
  have hin : sh.input.isData = true := by
    simp only [RequestShape.fields, Ty.isData, Ty.isDatas, Bool.and_eq_true] at hr; exact hr.1
  show i ∈ Trace.idsOf T sh.input (Ty.down (.tuple (.tuple sh.ks :: sh.input :: [.tuple sh.ensuresΓ,
    .tuple sh.answerΓ])) sh.hdata fx).2.1 ↔ _
  rw [down_snd_fst sh.hdata hin fx]
  exact idsOf_down T hin _ i

/-- A pending entry's positions are exactly the ids of the input of the request it codes. -/
theorem entryIds_exact {d' : Nat} {entry : Term} (id : Nat) :
    (shs : List (PendingShape e)) → (k0 : Nat) → (x : Ty.alts (shs.map PendingShape.fields)) →
    RelAlts L d' k0 (shs.map PendingShape.fields) x (entry.denote M) →
    IdsExact M L (entryIds L d' entry shs k0)
      (Trace.idsOf T (pendingOf shs id x).request.input (pendingOf shs id x).request.value)
  | sh :: shs, k0, .inl fx, ⟨vals, hx, hvs⟩ => by
    obtain ⟨w0, ws0, h0, -, hws⟩ := hvs
    obtain ⟨w1, ws1, h1, hw1, -⟩ := hws
    subst h0 h1
    have hsel : (Term.sel d' k0 1 entry).denote M = w1 := by simp [sel_ctor 1 hx]
    have h := (IdsExact.guard (g := .is d' k0 entry) (by simp [Holds, Term.denote, hx, Val.toBool])
      (ids_exact sh.input _ (hsel ▸ hw1))).append (entryIds_none hx (k0 + 1) (by omega) shs)
    simp only [List.append_nil] at h
    exact h.congr fun i => (pending_ids id fx i).symm
  | sh :: shs, k0, .inr y, hv => by
    obtain ⟨j, _, hx, hj⟩ := relAlts_index d' (k0 + 1) _ y _ hv
    have h := (IdsExact.guard_neg (M := M) (L := L) (g := .is d' k0 entry)
      (by simp [Holds, Term.denote, hx, Val.toBool, show j ≠ k0 by omega]) (idsT L sh.input (.sel d' k0 1 entry))).append
      (entryIds_exact id shs (k0 + 1) y hv)
    simpa [entryIds, pendingOf] using h
where
  entryIds_none {d' j : Nat} {entry : Term} {vals : List Val} (hx : entry.denote M = .ctor d' j vals) :
      (k : Nat) → j < k → (shs : List (PendingShape e)) → IdsExact M L (entryIds L d' entry shs k) []
    | _, _, [] => .nil
    | k, hk, sh :: shs => by
      have h := (IdsExact.guard_neg (M := M) (L := L) (g := .is d' k entry)
        (by simp [Holds, Term.denote, hx, Val.toBool, show j ≠ k by omega])
        (idsT L sh.input (.sel d' k 1 entry))).append (entryIds_none hx (k + 1) (by omega) shs)
      simpa [entryIds] using h

/-- The news slots' positions are exactly the ids of the inputs of the requests the step writes for them. -/
theorem news_exact {shs : List (PendingShape e)} {ds : List (String × DeclaredV)}
    {news : List PendingSlot} {effs : List (Sender × EffectV e)} {n0 : Nat} {written : List (Step.Pending e)}
    (hn : NewsRel M L shs ds news effs n0) (hw : Forall2 (Step.Writes ds) (effs.zipIdx n0) written) :
    IdsExact M L (newsIdsT L shs news) (linesIds T written) := by
  obtain ⟨sv, zs, hS, -, hh, xs, hp, hq⟩ := hn
  let f := fun z : (Ty.dsl .fresh []).den × (pendingEntry shs).den =>
    Trace.idsOf T (pendingOf shs z.1 z.2).request.input (pendingOf shs z.1 z.2).request.value
  have hex : IdsExact M L (newsIdsT L shs news) (zs.flatMap f) := by
    unfold newsIdsT
    split
    · rename_i dP nP hf
      have := slots_ids (M := M) (L := L) (g := fun xs : SlotItems 2 => entryIds L dP xs[1] shs 0)
        (E := ETab L (.dsl .fresh []) (pendingEntry shs)) (f := f)
        (fun xs z ⟨zk, zv, hz, _, hv⟩ => by
          obtain ⟨x0, x1, rfl, -, hx1⟩ := pair_terms hz
          obtain ⟨dP', nP', hf', hra⟩ := hv
          obtain ⟨rfl, -⟩ : dP = dP' ∧ _ := by simpa using hf.symm.trans hf'
          simpa using entryIds_exact z.1 shs 0 z.2 (hx1 ▸ hra)) (news.map PendingSlot.slot) sv hS zs hh
      simpa [List.flatMap_map, PendingSlot.slot] using this
    · rename_i hf
      cases zs with
      | nil => exact .nil
      | cons z zs =>
        exfalso
        unfold Holds2 at hh
        match h : occupied sv, hh with
        | o :: os, ⟨⟨zk, zv, _, _, dP, nP, hf', _⟩, _⟩ => exact absurd (hf.symm.trans hf') (by simp)
  refine hex.congr fun i => ?_
  have hu : ∀ (x : (Sender × EffectV e) × Nat) (p p' : Step.Pending e), Step.Writes ds x p → Step.Writes ds x p' →
      (i ∈ Trace.idsOf T p.request.input p.request.value ↔ i ∈ Trace.idsOf T p'.request.input p'.request.value) :=
    fun x p p' h h' => by rw [writes_one h h']
  rw [mem_flatMap_of_forall2 (R := fun x z => Step.Writes ds x (pendingOf shs z.1 z.2))
      (fun x z z' h h' => hu x _ _ h h') (forall2_imp (fun _ _ h => h.2) hq),
    mem_flatMap_of_forall2 (R := Step.Writes ds) (fun x p p' h h' => hu x p p' h h') hw]
  have hq' := forall2_imp (fun _ _ h => h.2) hq
  constructor
  · rintro ⟨x, hx, z, hz, hi⟩
    obtain ⟨p, -, hpw⟩ := forall2_mem_left hw x (hp.mem_iff.1 hx)
    exact ⟨x, hp.mem_iff.1 hx, p, hpw, (hu x _ _ hz hpw).1 hi⟩
  · rintro ⟨x, hx, p, hpw, hi⟩
    obtain ⟨z, -, hz⟩ := forall2_mem_left hq' x (hp.mem_iff.2 hx)
    exact ⟨x, hp.mem_iff.2 hx, z, hz, (hu x _ _ hpw hz).1 hi⟩

theorem step_query_quiet (T : List TypeDecl) {v : ServiceV} (s : State v) (i : Fin v.queries.length)
    (caller : v.caller.den0) (input : (v.queries.get i).input.den0) :
    (step T v s (.query i caller input)).events = [] ∧ (step T v s (.query i caller input)).out = [] := by
  simp only [step]
  split <;> exact ⟨rfl, rfl⟩

theorem step_rejected_quiet (T : List TypeDecl) {v : ServiceV} {s : State v} {i : Fin v.commands.length}
    {caller : v.caller.den0} {input : (v.commands.get i).input.den0} {y : WireVal}
    (h : (step T v s (.command i caller input)).outcome = .rejected y) :
    (step T v s (.command i caller input)).events = [] ∧ (step T v s (.command i caller input)).out = [] := by
  simp only [step] at h ⊢
  split at h
  · cases h
  · exact ⟨rfl, rfl⟩
  · cases h
  · rename_i a _
    unfold Step.finish at h
    split at h
    · cases h
    · split at h <;> cases h

/-- The event slots' positions are exactly the ids of the events applied. -/
theorem events_exact {v : ServiceV} {S : List (Slot 1)} {evs : List v.event.den0}
    (h : EventsRel M L S evs) :
    IdsExact M L (S.flatMap fun sl => guardIds sl.1 (idsT L v.event sl.2[0])) (evs.flatMap (Trace.idsOf T v.event)) := by
  obtain ⟨sv, hS, hh⟩ := h
  refine (slots_ids (g := fun xs => idsT L v.event xs[0]) (f := idsV v.event) (fun xs y ⟨z, hz, hyz⟩ => by
      obtain ⟨x0, rfl, hx0⟩ := singleton_terms hz
      simp only [SlotItems.getElem_mk, List.getElem_cons_zero]
      exact ids_exact v.event x0 (hx0 ▸ hyz)) S sv hS _ hh).congr fun i => ?_
  exact (mem_flatMap_map (Ty.up v.event v.event_data) (fun y => idsOf_up T v.event v.event_data y i) evs).symm

/-- A step's end that does not fault, from a step in progress that has applied and sent nothing yet: its positions are
exactly the ids its result shows. -/
theorem finish_exact {v : ServiceV} {shs : List (PendingShape v.event)}
    {fo : FinishOut v} {s0 : State v} {a : Step.Acc v} {r : Result v} (hF : Finished M L T shs fo s0 a .accepted r)
    (hnf : ∀ f, r.outcome ≠ .fault f) (ha : a.events = []) (ho : a.out = []) :
    IdsExact M L (fo.shownT L shs) (r.shownIds T) := by
  obtain ⟨-, hF⟩ := hF
  split at hF
  · subst hF; exact absurd rfl (hnf _)
  · split at hF
    · subst hF; exact absurd rfl (hnf _)
    · obtain ⟨e, hE⟩ := hF
      obtain ⟨effs, hn, hw⟩ := hE.news
      rw [hE.result]
      refine ((events_exact (T := T) hE.events).append (news_exact (T := T) hn hw)).congr fun i => ?_
      simp [Result.shownIds, EndVals.result, ha, ho, List.flatMap_map, Step.Pending.line]

/-- T2's terms of a step say exactly which ids it shows: where they say what the step's result is and it does not
fault, the positions of its out lines whose conditions hold are exactly the ids the result shows. -/
theorem shown_exact {v : ServiceV} {n : Nat} {hc : v.caller.isData = true}
    {o : StepOut v} {inp : SymInput v (shapes v) n} {x : Input v} {s : State v}
    (hdec : inp.decode M L hc = some x) (hrel : o.Rel M L T (shapes v) s x (step T v s x))
    (hnf : ∀ f, (step T v s x).outcome ≠ .fault f) :
    IdsExact M L (o.shownT L inp) ((step T v s x).shownIds T) := by
  have neg := fun (g : Term) (h : ¬ Holds M g) (ps : List (Term × Term)) => IdsExact.guard_neg (M := M) (L := L) h ps
  cases inp with
  | command i ci ii =>
    simp only [SymInput.decode] at hdec
    obtain ⟨c, -, hdec⟩ := Option.bind_eq_some_iff.1 hdec
    obtain ⟨xi, -, rfl⟩ := Option.map_eq_some_iff.1 hdec
    cases o <;> simp only [StepOut.Rel] at hrel
    rename_i co
    simp only [StepOut.shownT]
    generalize hr : step T v s (.command i (Ty.down _ hc c) (Ty.down _ (v.commands.get i).input_data xi)) = r at hrel hnf
    split at hrel
    · rename_i hco
      split at hrel
      · rename_i n ns hb
        subst hrel
        have hadm : ¬ Holds M (andT co.callerOk (allT (co.rules.map (·.2)))) := fun h => by
          rw [holds_andT, holds_allT_rules, hb] at h; cases h.2
        exact ((neg _ (fun h => hadm ((holds_andT _ _).1 h).1) _).append
          (neg _ (fun h => hadm ((holds_andT _ _).1 h).1) _)).congr (by simp [Result.shownIds])
      · rename_i hb
        have hadm : Holds M (andT co.callerOk (allT (co.rules.map (·.2)))) :=
          (holds_andT _ _).2 ⟨hco, (holds_allT_rules _).2 hb⟩
        split at hrel
        · rename_i hok
          split at hrel
          · subst hrel; exact absurd rfl (hnf _)
          · rename_i he
            have hg : Holds M (andT (andT co.callerOk (allT (co.rules.map (·.2))))
                (andT co.decided.ok (allT (co.decided.ensures.map (·.2))))) :=
              (holds_andT _ _).2 ⟨hadm, (holds_andT _ _).2 ⟨hok, (holds_allT_rules _).2 he⟩⟩
            exact ((neg _ (fun h => ((holds_not _).1 ((holds_andT _ _).1 h).2) hok) _).append
              ((finish_exact hrel hnf rfl rfl).guard hg)).congr (by simp)
        · rename_i hok
          obtain ⟨-, j, hout, hj⟩ := hrel
          have hq := step_rejected_quiet T (hr ▸ hout)
          rw [hr] at hq
          have hg : Holds M (andT (andT co.callerOk (allT (co.rules.map (·.2)))) (.not co.decided.ok)) :=
            (holds_andT _ _).2 ⟨hadm, (holds_not _).2 (by simpa [Holds] using hok)⟩
          refine (((ids_exact _ _ hj).guard hg).append
            (neg _ (fun h => hok ((holds_andT _ _).1 ((holds_andT _ _).1 h).2).1) _)).congr fun i => ?_
          simp only [Result.shownIds, hout, hq.1, hq.2, List.flatMap_nil, List.append_nil]
          exact (idsOf_up T _ _ j i).symm
    · subst hrel
      have hadm : ¬ Holds M (andT co.callerOk (allT (co.rules.map (·.2)))) := fun h => by
        rename_i hco; exact hco ((holds_andT _ _).1 h).1
      exact ((neg _ (fun h => hadm ((holds_andT _ _).1 h).1) _).append
        (neg _ (fun h => hadm ((holds_andT _ _).1 h).1) _)).congr (by simp [Result.shownIds])
  | query i ci ii =>
    simp only [SymInput.decode] at hdec
    obtain ⟨c, -, hdec⟩ := Option.bind_eq_some_iff.1 hdec
    obtain ⟨xi, -, rfl⟩ := Option.map_eq_some_iff.1 hdec
    cases o <;> simp only [StepOut.Rel] at hrel
    rename_i qo
    simp only [StepOut.shownT]
    have hq := step_query_quiet T s i (Ty.down _ hc c) (Ty.down _ (v.queries.get i).input_data xi)
    obtain ⟨-, hrel⟩ := hrel
    generalize hout : (step T v s _).outcome = out at hrel
    cases out with
    | invalid ns =>
      have hg : ¬ Holds M (andT qo.callerOk (allT (qo.rules.map (·.2)))) := fun h => by
        rw [holds_andT, holds_allT_rules] at h
        simp only [QueryOut.Rel, QueryOut.invalid, show (qo.callerOk.denote M).toBool = true from h.1, h.2,
          ite_true] at hrel
        cases hrel
      exact (neg _ hg _).congr fun i => by simp only [Result.shownIds]; rw [hout, hq.1, hq.2]; simp
    | answered w =>
      obtain ⟨t, y⟩ := w
      obtain ⟨hinv, ht, hy⟩ := hrel
      subst ht
      have hg : Holds M (andT qo.callerOk (allT (qo.rules.map (·.2)))) := by
        simp only [QueryOut.invalid] at hinv
        split at hinv
        · rename_i hco
          split at hinv
          · exact (holds_andT _ _).2 ⟨hco, (holds_allT_rules _).2 (by assumption)⟩
          · cases hinv
        · cases hinv
      refine ((ids_exact _ _ hy).guard hg).congr fun i => ?_
      simp only [Result.shownIds]
      rw [hout, hq.1, hq.2]
      simp only [List.flatMap_nil, List.append_nil]
      exact (idsOf_up T _ _ y i).symm
    | _ => simp [QueryOut.Rel] at hrel
  | answer k j to value | unmatched t to value =>
    simp only [SymInput.decode, decodeAnswer] at hdec
    split at hdec
    · obtain ⟨w, -, hdec⟩ := Option.bind_eq_some_iff.1 hdec
      obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hdec
      cases o <;> simp only [StepOut.Rel] at hrel
      · rename_i ao
        simp only [StepOut.shownT]
        split at hrel
        · rename_i n ns hb
          rw [hrel] at hnf ⊢
          exact (neg _ (by rw [holds_allT_rules, hb]; nofun) _).congr (by simp [Result.shownIds])
        · rename_i hb
          exact (finish_exact hrel hnf rfl rfl).guard ((holds_allT_rules _).2 hb)
      · rw [hrel] at hnf; exact absurd rfl (hnf _)
    · cases hdec
  | event i value =>
    simp only [SymInput.decode] at hdec
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hdec
    cases o <;> simp only [StepOut.Rel] at hrel
    exact finish_exact hrel hnf rfl rfl
  | clock time =>
    simp only [SymInput.decode] at hdec
    obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.1 hdec
    cases o <;> simp only [StepOut.Rel] at hrel
    rename_i co
    simp only [StepOut.shownT]
    split at hrel
    · rename_i hf
      split at hrel
      · rw [hrel] at hnf; exact absurd rfl (hnf _)
      · exact (finish_exact hrel hnf rfl rfl).guard hf
    · rename_i hf
      rw [hrel] at hnf ⊢
      exact (neg _ (by simpa [Holds] using hf) _).congr (by simp [Result.shownIds])

end

end Tazuna.Smt
