import Tazuna.Smt.Verdict
import Tazuna.Smt.CheckedState

/-! The questions cover every step within the slots: a state a run reaches whose values fit its slots and an input
whose values fit theirs are some well-sorted model's, in the case one of the input kind's questions asks about. For
an answer that case is the shape and the slot that hold the request it names; an answer that names no request of its
type is `Fault.answerUnmatched`, and a query never faults. So T4 needs no hypothesis about models: where the solver
answers unsat, no step within the slots of a run from an initial state whose invariants hold faults naming the rule
(`verdict_sound`). -/

namespace Tazuna.Smt

open Tazuna.Ir

theorem isData_of_embeddable : (t : Ty) → t.embeddable = true → t.isData = true
  | .int, _ | .str, _ | .date, _ | .id, _ => rfl
  | .dsl k _, h => by simpa [Ty.embeddable, Ty.isData] using h
  | .adt 0 _ vs, h => by
    unfold Ty.embeddable at h
    unfold boolVs? at h
    split at h
    · simp [Ty.isData, Ty.isDatass, Ty.isDatas]
    · simp at h
  | .adt (_ + 1) _ vs, h => by simpa [Ty.embeddable, Ty.isData] using isDatass_of vs h
  | .tuple ts, h => by simpa [Ty.embeddable, Ty.isData] using isDatas_of ts h
  | .list t, h | .bag t, h => by simpa [Ty.embeddable, Ty.isData] using isData_of_embeddable t h
  | .table k w, h => by
    simp only [Ty.embeddable, Bool.and_eq_true] at h
    simp [Ty.isData, isData_of_embeddable k h.1, isData_of_embeddable w h.2]
  | .fn .., h | .param _, h => by simp [Ty.embeddable] at h
where
  isDatas_of : (ts : List Ty) → Ty.embeddables ts = true → Ty.isDatas ts = true
    | [], _ => rfl
    | t :: ts, h => by
      simp only [Ty.embeddables, Bool.and_eq_true] at h
      simp [Ty.isDatas, isData_of_embeddable t h.1, isDatas_of ts h.2]
  isDatass_of : (vs : List (List Ty)) → Ty.embeddabless vs = true → Ty.isDatass vs = true
    | [], _ => rfl
    | ts :: vs, h => by
      simp only [Ty.embeddabless, Bool.and_eq_true] at h
      simp [Ty.isDatass, isDatas_of ts h.1, isDatass_of vs h.2]

theorem Checked.callerData {P : List AnySite} {E : List AnyEffectSite} {T : List TypeDecl} {v : ServiceV}
    (chk : Checked P E T v) : v.caller.isData = true :=
  isData_of_embeddable _ (stateTys_iff.1 chk.stateTys).2.2.2.2.2.1

section
variable (L : Layout) {v : ServiceV}

/-- The state's values fit the slots: some coding of its pending requests at the shapes embeds with it. -/
def Within (shs : List (PendingShape v.event)) (s : State v) : Prop :=
  ∃ pv : PendingVal shs, pv.list = s.pending ∧ (embedState L s pv).isSome

/-- The values of an input's terms, in the order of `SymInput.tys`, where they fit the slots. A query has no
questions and no terms. An answer of a type with no SMT value is none: it has no wire form. -/
def inputVals (hc : v.caller.isData = true) : Input v → Option (List Val)
  | .command i caller input => (embedV L v.caller (Ty.up _ hc caller)).bind fun c =>
    (embedV L _ (Ty.up _ (v.commands.get i).input_data input)).map fun x => [c, x]
  | .query .. => some []
  | .answer to ⟨t, value⟩ =>
    if h : t.isData = true then (embedV L t (Ty.up _ h value)).map fun w => [.int (Int.ofNat to), w] else none
  | .event i value => (embedV L _ (Ty.up _ (v.subscribes.get i).event_data value)).map fun w => [w]
  | .clock time => some [.int time]

end

-- The model reads only the variables a script declares; the others' value is never asked.
set_option linter.tazuna.silentDefault false in
/-- A model whose variables hold the values `ws` in order. -/
def coverModel (ws : List Val) : Model :=
  { vars := fun n => ws.getD n (.bool false), divZero := fun _ => 0, modZero := fun _ => 0,
    selOther := fun _ _ _ _ => .bool false, defs := fun _ => .bool false }

section
variable {M : Model} {L : Layout} {v : ServiceV}

theorem sorted_of_embed {t : Ty} {x : t.den} {w : Val} (h : embedV L t x = some w) : Sorted L t w :=
  decode_sorted _ _ _ (decode_embed _ _ _ h)

theorem embedMachines_sorted : {ms : List (MachineV v.records v.event)} → (sms : Step.Machines ms) → (ws : List Val) →
    embedMachines L sms = some ws → Forall2 (Sorted L) (ms.map (·.table)) ws
  | _, .nil, _, h => by simp only [embedMachines, Option.some.injEq] at h; subst h; trivial
  | _ :: _, .cons _ sms, _, h => by
    simp only [embedMachines] at h
    split at h
    · obtain ⟨w, hw, h⟩ := bind_some.1 h
      obtain ⟨ws', hws', rfl⟩ := map_some.1 h
      exact ⟨sorted_of_embed hw, embedMachines_sorted sms ws' hws'⟩
    · cases h

theorem embedState_sorted {shs : List (PendingShape v.event)} {s : State v} {pv : PendingVal shs} {vals : List Val}
    (h : embedState L s pv = some vals) : Forall2 (Sorted L) (stateTys v shs) vals := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨p, hp, h⟩ := bind_some.1 h
  obtain ⟨ws, hws, rfl⟩ := map_some.1 h
  exact ⟨sorted_of_embed hrec, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, sorted_of_embed hp, embedMachines_sorted _ ws hws⟩

theorem coverModel_vars {ws : List Val} {j : Nat} {w : Val} (h : ws[j]? = some w) : (coverModel ws).vars j = w := by
  simp [coverModel, h]

theorem forall2_sorted_vars {tys : List Ty} {ws : List Val} (h : Forall2 (Sorted L) tys ws) :
    ∀ j (hj : j < tys.length), Sorted L tys[j] ((coverModel ws).vars j) := by
  intro j hj
  obtain ⟨w, hw, hs⟩ := forall2_getElem? h (List.getElem?_eq_getElem hj)
  rw [coverModel_vars hw]; exact hs

/-- Where a request with the wire id `to` is pending, some shape and slot hold it: the slot is occupied, holds that
wire id, and its entry is the shape's variant, whose answers have the request's types. -/
theorem answer_hit (s : State v) {shs : List (PendingShape v.event)} (to : Nat) {pending toT : Term}
    (hpend : PendingRel L shs (pending.denote M) s.pending) (hto : toT.denote M = .int (Int.ofNat to))
    (senv : StepEnv L shs) {p : Step.Pending v.event} (hf : s.pending.find? (·.id == to) = some p) :
    ∃ (k : Fin shs.length) (j : Fin senv.nT), p.request.output = shs[k].output ∧
      p.request.rejection = shs[k].rejection ∧
      Holds M (Term.and (pendingSlotAt senv.dT senv.dtT j pending).flag
        (.and (.eq (pendingSlotAt senv.dT senv.dtT j pending).id toT)
          (.is senv.dP k (pendingSlotAt senv.dT senv.dtT j pending).entry))) := by
  obtain ⟨tbl, htbl, hlist⟩ := hpend
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
  obtain ⟨sl, hq, rfl⟩ := List.mem_map.1 hq0
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
  rw [hxs] at hxs2
  simp only [PendingSlot.slot, Term.denotes, List.cons.injEq, and_true] at hxs2 hf1
  obtain ⟨htk, hte⟩ := hxs2
  obtain ⟨d', n', hf', hra⟩ := hzv
  have hde := find_det hf' senv.hPE
  subst d'
  obtain ⟨j', sh', fx, vals, hj', hzv', -, hpo⟩ := relAlts_pending (L := L) y1 shs 0 y2 zv hra
  have hlt : j' < shs.length := (List.getElem?_eq_some_iff.1 hj').1
  have hsh : shs[j'] = sh' := (List.getElem?_eq_some_iff.1 hj').2
  have hkey : (y1 : Nat) = to := (pendingOf_id _ _ _).symm.trans hpid
  change zk = Val.int (Int.ofNat y1) at hzk
  refine ⟨⟨j', hlt⟩, ⟨i, by simpa using hi⟩, ?_, ?_, ?_⟩
  · simp only [hpo, Fin.getElem_fin, hsh]; rfl
  · simp only [hpo, Fin.getElem_fin, hsh]; rfl
  · rw [holds_and, holds_and]
    refine ⟨by simp [Holds, hf1, Val.toBool], ?_, ?_⟩
    · simp only [Holds, Term.denote, htk, hzk, hto, hkey, Val.toBool]
      show Val.beq (.int _) (.int _) = true
      simp [Val.beq]
    · rw [Nat.zero_add] at hzv'
      simp [Holds, Term.denote, hte, hzv', Val.toBool]

end


section
variable {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV} {senv : StepEnv L (shapes v P)}
  {S : SymState v}

/-- An answer's script asks about the case that its slot holds the request as an entry of its shape. -/
theorem encodeStep_answer_case {k : Fin (shapes v P).length} {j : Fin senv.nT} {toT valT : Term} {t : EncodedStep v}
    (h : encodeStep L T P v senv S (.answer k j toT valT) = .ok t) :
    t.out.case = Term.and (pendingSlotAt senv.dT senv.dtT j S.pending).flag
      (.and (.eq (pendingSlotAt senv.dT senv.dtT j S.pending).id toT)
        (.is senv.dP k (pendingSlotAt senv.dT senv.dtT j S.pending).entry)) := by
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨⟨o, c, cs⟩, hans, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  unfold encodeAnswer at hans
  repeat (obtain ⟨_, -, hans⟩ := bind_ok.1 hans)
  cases pure_ok.1 hans
  rfl

/-- A command's, query's, event's or clock line's script has one case. -/
theorem encodeStep_case_tt {inp : SymInput v (shapes v P) senv.nT} {t : EncodedStep v}
    (h : encodeStep L T P v senv S inp = .ok t) (ha : ∀ k j to w, inp ≠ .answer k j to w)
    (hu : ∀ ty to w, inp ≠ .unmatched ty to w) : t.out.case = tt := by
  cases inp with
  | answer k j to w => exact absurd rfl (ha k j to w)
  | unmatched ty to w => exact absurd rfl (hu ty to w)
  | _ =>
    simp only [encodeStep] at h
    repeat (obtain ⟨_, -, h⟩ := bind_ok.1 h)
    cases pure_ok.1 h
    rfl

theorem query_no_fault (T : List TypeDecl) (s : State v) (i : Fin v.queries.length) (caller input) (f : Fault) :
    (step T v s (.query i caller input)).outcome ≠ .fault f := by
  simp only [step]
  split <;> simp

/-- The questions cover every step within the slots from a state whose instances are in the step's form: either some
input kind's questions cover the state and the input, or the step faults by nothing but `answerUnmatched` (an answer
that names no request of its type, or a query). -/
theorem covered {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v P)) {s : State v}
    (hkeys : Step.KeysOk T s) (hs : Within L (shapes v P) s) (x : Input v) {ivs : List Val}
    (hx : inputVals L chk.callerData x = some ivs) :
    (∃ inp ∈ stepInputs v (shapes v P) senv.nT (5 + v.machines.length), Covered L T P v senv inp s x) ∨
      ∀ f, f ≠ .answerUnmatched → (step T v s x).outcome ≠ .fault f := by
  obtain ⟨pv, hpv, hsome⟩ := hs
  obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.1 hsome
  have hlen : vals.length = 5 + v.machines.length := by
    obtain ⟨_, -, h⟩ := bind_some.1 hvals
    obtain ⟨_, -, h⟩ := bind_some.1 h
    obtain ⟨ws, hws, rfl⟩ := map_some.1 h
    simp [embedMachines_length _ ws hws]; omega
  let M := coverModel (vals ++ ivs)
  have hst : ∀ j (hj : j < vals.length), M.vars (0 + j) = vals[j] := fun j hj =>
    coverModel_vars (by rw [Nat.zero_add, List.getElem?_append_left hj, List.getElem?_eq_getElem hj])
  have hin : ∀ j (hj : j < ivs.length), M.vars (5 + v.machines.length + j) = ivs[j] := fun j hj =>
    coverModel_vars (by rw [← hlen, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj])
  have hS : (SymState.vars (v := v) 0).decode M L T (shapes v P) = some s :=
    decode_embedState 0 T s pv hpv (fun sm h => (hkeys sm h).2) vals hvals hst
  have hsorted := embedState_sorted hvals
  have hc := chk.callerData
  cases x with
  | command i caller input =>
    obtain ⟨c, hc', h⟩ := bind_some.1 hx
    obtain ⟨w, hw, rfl⟩ := map_some.1 h
    refine .inl ⟨.command i (.var (5 + v.machines.length)) (.var (5 + v.machines.length + 1)),
      by simp [stepInputs], hc, M, forall2_sorted_vars (forall2_append hsorted ⟨sorted_of_embed hc', sorted_of_embed hw, trivial⟩),
      hS, ?_, fun t ht => by rw [encodeStep_case_tt ht (by simp) (by simp)]; exact holds_tt⟩
    have h0 := hin 0 (by simp)
    have h1 := hin 1 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
    simp [SymInput.decode, Term.denote, h0, h1, decode_embed _ _ _ hc', Ty.down_up]
    exact ⟨_, decode_embed _ _ _ hw, Ty.down_up _ _ _⟩
  | query i caller input => exact .inr fun f _ => query_no_fault T s i caller input f
  | event i value =>
    obtain ⟨w, hw, rfl⟩ := map_some.1 hx
    refine .inl ⟨.event i (.var (5 + v.machines.length)), by simp [stepInputs], hc, M,
      forall2_sorted_vars (forall2_append hsorted ⟨sorted_of_embed hw, trivial⟩), hS, ?_,
      fun t ht => by rw [encodeStep_case_tt ht (by simp) (by simp)]; exact holds_tt⟩
    have h0 := hin 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    simp [SymInput.decode, Term.denote, h0]
    exact ⟨_, decode_embed _ _ _ hw, Ty.down_up _ _ _⟩
  | clock time =>
    cases hx
    refine .inl ⟨.clock (.var (5 + v.machines.length)), by simp [stepInputs], hc, M,
      forall2_sorted_vars (forall2_append hsorted ⟨⟨_, rfl⟩, trivial⟩), hS, ?_,
      fun t ht => by rw [encodeStep_case_tt ht (by simp) (by simp)]; exact holds_tt⟩
    have h0 := hin 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h0
    simp [SymInput.decode, Term.denote, h0, intOf]
  | answer to a =>
    obtain ⟨t, value⟩ := a
    simp only [inputVals] at hx
    split at hx
    · rename_i htd
      obtain ⟨w, hw, rfl⟩ := map_some.1 hx
      cases hf : s.pending.find? (·.id == to) with
      | none => exact .inr fun f hf' => by simp only [step, hf]; simpa using hf'.symm
      | some p =>
        cases hsame : Ty.same t (answerTy p.request.output p.request.rejection) with
        | none => exact .inr fun f hf' => by simp only [step, hf, hsame]; simpa using hf'.symm
        | some e =>
          obtain ⟨he⟩ := e
          have h0 := hin 0 (by simp)
          have h1 := hin 1 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
          have hto : (Term.var (5 + v.machines.length)).denote M = .int (Int.ofNat to) := by simp [Term.denote, h0]
          obtain ⟨k, j, hout, hrej, hhit⟩ := answer_hit s to (decode_state hS).pending hto senv hf
          rw [hout, hrej] at he
          subst he
          refine .inl ⟨.answer k j (.var (5 + v.machines.length)) (.var (5 + v.machines.length + 1)),
            by simp [stepInputs], hc, M,
            forall2_sorted_vars (forall2_append hsorted ⟨⟨_, rfl⟩, sorted_of_embed hw, trivial⟩), hS, ?_,
            fun t ht => by rw [encodeStep_answer_case ht]; exact hhit⟩
          simp [SymInput.decode, decodeAnswer, Term.denote, h0, h1, natOf]
          exact ⟨htd, _, decode_embed _ _ _ hw, Ty.down_up _ _ _⟩
    · cases hx

/-- T4: where the solver answers unsat to every input kind's bound question and to its questions about the
invariant rules named `n`, no step of a run from an initial state whose invariants hold faults naming `n`, wherever
the state the run reached and the input fit the slots. -/
theorem verdict_sound {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v P)) (n : String)
    (hinit : Step.invariants (Step.State.init v) = [])
    (hq : ∀ inp ∈ stepInputs v (shapes v P) senv.nT (5 + v.machines.length), ∃ gs qs,
      questions L T P v senv inp = .ok (gs, qs) ∧ ∀ q ∈ qs, (q.target = none ∨ ∃ g, q.target = some g ∧ g.Names n) →
        Unsat L (stateTys v (shapes v P) ++ inp.tys) q.script)
    (is : List (Input v)) (x : Input v) (hs : Within L (shapes v P) (run T v (Step.State.init v) is).1)
    (hx : (inputVals L chk.callerData x).isSome) :
    (step T v (run T v (Step.State.init v) is).1 x).outcome ≠ .fault (.invariant n) := by
  obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  rcases covered chk senv (run_keys T _ (Step.init_keys T hord) is) hs x hivs
    with ⟨inp, hmem, hcov⟩ | h
  · obtain ⟨gs, qs, hqs, hun⟩ := hq inp hmem
    exact verdict_covered chk senv n hinit inp hqs hun is x hcov
  · exact h _ (by simp)

end

end Tazuna.Smt
