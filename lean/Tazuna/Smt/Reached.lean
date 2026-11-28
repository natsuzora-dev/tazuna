import Tazuna.Smt.Cover
import Tazuna.Semantics.Rename

/-! Every state a run reaches is within the slots, where the bound questions have no model, the initial state fits,
and every value an input can carry fits. A step from a state within the slots on an input within them satisfies the
step's condition where its bound question has no model (`bound_cond`), and there its end terms denote the state it
leaves (`step_encode`), which therefore fits too. An answer whose value fits no slot names no pending request of its
type, so it leaves the state as it was. So a step line that reads proved speaks of every run, not only of the runs
within the slots (`proved_sound`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout}

mutual
/-- A value related to an SMT value embeds: the relation holds each collection's items in its slots. -/
theorem embed_of_relV : (t : Ty) → t.embeddable = true → (x : t.den) → (z : Val) → RelV L t x z →
    (embedV L t x).isSome
  | .int, _, _, _, _ | .str, _, _, _, _ | .point _, _, _, _, _ => by simp [embedV]
  | .dsl k a, he, _, _, _ => by
    simp only [Ty.embeddable, beq_iff_eq] at he; subst he; simp [embedV]
  | .id, _, _, _, ⟨d, n, hf, _⟩ => by simp [embedV, hf]
  | .adt 0 a vs, _, _, _, ⟨h, _⟩ => by subst h; simp [embedV]
  | .adt (i + 1) a vs, he, x, z, ⟨d, n, hf, hr⟩ => by
    simp only [embedV, hf]
    exact embedAlts_of_relAlts d 0 vs he x z hr
  | .tuple ts, he, x, _, ⟨d, n, vals, hf, _, hr⟩ => by
    simp only [embedV, hf, Option.isSome_map]
    exact embedVs_of_relVs ts he x vals hr
  | .list t, he, xs, _, ⟨d, n, dt, m, sv, hl, hp, hn, _, _, h2⟩ => by
    simp only [embedV, hl, hp]
    refine (bind_fill_isSome (fun x => (embedV L t x).map ([·])) xs n _ (slotsVal d dt)).2 ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨_, -, z, rfl, hz⟩ := forall2_mem_left h2 x hx
      simpa using embed_of_relV t he x z hz
    · have := forall2_length h2; have := occupied_length_le sv; omega
  | .bag t, he, xs, _, ⟨d, n, dt, m, sv, hl, hp, hn, _, _, ys, hys, h2⟩ => by
    simp only [embedV, hl, hp]
    refine (bind_fill_isSome (fun x => (embedV L t x).map ([·])) xs n _ (slotsVal d dt)).2 ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨_, -, z, rfl, hz⟩ := forall2_mem_left h2 x (hys.mem_iff.2 hx)
      simpa using embed_of_relV t he x z hz
    · have := forall2_length h2; have := occupied_length_le sv; have := hys.length_eq; omega
  | .table k w, he, x, _, ⟨d, n, dt, m, sv, hl, hp, hn, _, _, ys, hys, h2⟩ => by
    simp only [Ty.embeddable, Bool.and_eq_true] at he
    simp only [embedV, hl, hp]
    refine (bind_fill_isSome (fun e => (embedV L k e.1).bind fun a => (embedV L w e.2).map fun b => [a, b]) x.1 n _
      (slotsVal d dt)).2 ⟨fun e hx => ?_, ?_⟩
    · obtain ⟨_, -, zk, zv, rfl, hzk, hzv⟩ := forall2_mem_left h2 e (hys.mem_iff.2 hx)
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (embed_of_relV k he.1 e.1 zk hzk)
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (embed_of_relV w he.2 e.2 zv hzv)
      simp [ha, hb]
    · have := forall2_length h2; have := occupied_length_le sv; have := hys.length_eq; omega
  | .fn .., he, _, _, _ | .param _, he, _, _, _ => by simp [Ty.embeddable] at he
theorem embedVs_of_relVs : (ts : List Ty) → Ty.embeddables ts = true → (x : Ty.dens ts) → (vals : List Val) →
    RelVs L ts x vals → (embedVs L ts x).isSome
  | [], _, _, _, _ => by simp [embedVs]
  | t :: ts, he, (x, xs), _, ⟨w, ws, _, hw, hws⟩ => by
    simp only [Ty.embeddables, Bool.and_eq_true] at he
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (embed_of_relV t he.1 x w hw)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (embedVs_of_relVs ts he.2 xs ws hws)
    simp [embedVs, ha, hb]
theorem embedAlts_of_relAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.embeddabless vs = true →
    (x : Ty.alts vs) → (z : Val) → RelAlts L d k vs x z → (embedAlts L d k vs x).isSome
  | _, [], _, x, _, _ => nomatch x
  | _, fs :: _, he, .inl x, _, ⟨vals, _, hr⟩ => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at he
    simp only [embedAlts, Option.isSome_map]
    exact embedVs_of_relVs fs he.1 x vals hr
  | k, _ :: vs, he, .inr y, z, hr => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at he
    simp only [embedAlts]
    exact embedAlts_of_relAlts d (k + 1) vs he.2 y z hr
end

/-- Whether a table embeds reads its entries as a multiset. -/
theorem embed_table_perm {k w : Ty} {x y : (Ty.table k w).den} (hp : x.1.Perm y.1)
    (h : (embedV L (.table k w) x).isSome) : (embedV L (.table k w) y).isSome := by
  revert h
  simp only [embedV]
  split
  · rw [bind_fill_isSome, bind_fill_isSome]
    exact fun ⟨a, b⟩ => ⟨fun e he => a e (hp.mem_iff.2 he), hp.length_eq ▸ b⟩
  · simp

theorem instEntries_instOf {r e : Ty} (m : MachineV r e) (l : List (m.key.den0 × m.state.den0)) :
    instEntries m (l.map fun (k, x) => instOf m k x) = l := by
  simp only [instEntries, List.map_map]
  exact (List.map_congr_left fun _ _ => rfl).trans (List.map_id l)

theorem embedMachines_of_rel {M : Model} {T : List TypeDecl} {v : ServiceV} :
    {ms : List (MachineV v.records v.event)} → (xs : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) →
    (∀ m ∈ ms, m.table.embeddable = true) → MachinesRel M L T ms xs sms → (embedMachines L sms).isSome
  | [], .nil, .nil, _, _ => rfl
  | m :: _, .cons _ xs, .cons _ sms, he, h => by
    simp only [MachinesRel] at h
    obtain ⟨⟨tbl, hr, rfl⟩, hrest⟩ := h
    have hok := instancesOf_ok (T := T) m tbl
    simp only [embedMachines]
    rw [dite_eq_left_of_eq_true (eq_true hok.2)]
    have e1 : (Ty.up _ m.table_data tbl).1 =
        tbl.1.map fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.state_data p.2) :=
      Ty.up_table m.key m.state m.table_data m.key_data m.state_data tbl
    have e2 : (Ty.up _ m.table_data (m.tableOf (instancesOf T m tbl) hok.2)).1 =
        (m.tableOf (instancesOf T m tbl) hok.2).1.map fun p => (Ty.up _ m.key_data p.1, Ty.up _ m.state_data p.2) :=
      Ty.up_table m.key m.state m.table_data m.key_data m.state_data _
    have h1 : (embedV L m.table (Ty.up _ m.table_data (m.tableOf (instancesOf T m tbl) hok.2))).isSome := by
      refine embed_table_perm (k := m.key) (w := m.state) ?_ (embed_of_relV _ (he m (by simp)) _ _ hr)
      rw [e1, e2]
      refine List.Perm.map _ ?_
      simp only [MachineV.tableOf, instancesOf]
      have := ((List.mergeSort_perm (tbl.1.map fun (k, x) => instOf m k x) (keyLE T m)).map
        fun i => (i.key, i.state)).symm
      have hi := instEntries_instOf m tbl.1
      simp only [instEntries] at hi this ⊢
      exact (List.Perm.of_eq hi.symm).trans this
    have h2 := embedMachines_of_rel xs sms (fun m' h => he m' (by simp [h])) hrest
    revert h1 h2
    cases embedV L m.table (Ty.up _ m.table_data (m.tableOf (instancesOf T m tbl) hok.2)) <;>
      cases embedMachines L sms <;> simp

variable {v : ServiceV} {T : List TypeDecl} {M : Model}

theorem within_congr {shs : List (PendingShape v.event)} {s s' : State v} (h : Within L shs s)
    (hr : s'.records = s.records) (hp : s'.pending = s.pending) (hm : s'.machines = s.machines) : Within L shs s' := by
  obtain ⟨pv, hpv, hsome⟩ := h
  refine ⟨pv, hpv.trans hp.symm, ?_⟩
  revert hsome
  simp only [embedState, hr, hm]
  cases embedV L v.records (Ty.up _ v.records_data s.records) <;> cases embedPending L shs pv <;>
    cases embedMachines L s.machines <;> simp

/-- The types of a state have SMT values: what the step's relations need to embed the states they denote. -/
structure Embeddable (v : ServiceV) (shs : List (PendingShape v.event)) : Prop where
  records : v.records.embeddable = true
  pending : (pendingTable shs).embeddable = true
  machines : ∀ m ∈ v.machines, m.table.embeddable = true

theorem Checked.embeddable {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) :
    Embeddable v (shapes v) := by
  obtain ⟨⟨her, -⟩, hms, hep, -⟩ := stateTys_iff.1 chk.stateTys
  exact ⟨her, embeddable_pending hep, fun m hm => (hms m hm).1⟩

/-- A state whose records, pending requests and instances are related to SMT values is within the slots. -/
theorem within_of_rel {shs : List (PendingShape v.event)} (he : Embeddable v shs) {s : State v} {wr wp : Val}
    {xs : PerMachine (fun _ => Term) v.machines}
    (hr : RelV L v.records (Ty.up _ v.records_data s.records) wr) (hp : PendingRel L shs wp s.pending)
    (hm : MachinesRel M L T v.machines xs s.machines) : Within L shs s := by
  obtain ⟨tbl, htbl, hperm⟩ := hp
  obtain ⟨l', hl', heq⟩ := perm_map_inv hperm.symm (l := tbl.1) rfl
  refine ⟨⟨l', keysUnique_perm hl'.symm tbl.2⟩, heq.symm, ?_⟩
  have h1 := embed_of_relV _ he.records _ _ hr
  have h2 : (embedPending L shs ⟨l', keysUnique_perm hl'.symm tbl.2⟩).isSome :=
    embed_table_perm (k := .dsl .fresh []) (w := pendingEntry shs) hl'.symm (embed_of_relV _ he.pending _ _ htbl)
  have h3 := embedMachines_of_rel xs s.machines he.machines hm
  revert h1 h2 h3
  simp only [embedState]
  cases embedV L v.records (Ty.up _ v.records_data s.records) <;>
    cases embedPending L shs ⟨l', keysUnique_perm hl'.symm tbl.2⟩ <;> cases embedMachines L s.machines <;> simp

theorem within_finished {shs : List (PendingShape v.event)} (he : Embeddable v shs) {fo : FinishOut v} {s0 : State v}
    {a : Step.Acc v} {o : Outcome} {r : Result v} (h : Finished M L T shs fo s0 a o r) (h0 : Within L shs s0) :
    Within L shs r.state := by
  obtain ⟨-, h⟩ := h
  split at h
  · subst h; exact h0
  · split at h
    · subst h; exact h0
    · obtain ⟨e, he'⟩ := h
      rw [he'.result]
      exact within_of_rel he he'.records he'.pending he'.machines

/-- The state a step's terms say it leaves is within the slots, where the state it starts from is. -/
theorem within_stepRel {shs : List (PendingShape v.event)} (he : Embeddable v shs) {out : StepOut v} {s : State v}
    {x : Input v} {r : Result v} (h : out.Rel M L T shs s x r) (hs : Within L shs s) : Within L shs r.state := by
  have hf : ∀ k, Within L shs ({ s with fresh := k } : State v) := fun _ => within_congr hs rfl rfl rfl
  cases out <;> cases x <;> simp only [StepOut.Rel] at h
  · split at h
    · split at h
      · subst h; exact hf _
      · split at h
        · split at h
          · subst h; exact hf _
          · exact within_finished he h (hf _)
        · rw [h.1]; exact hf _
    · subst h; exact hf _
  · rw [h.1]; exact hs
  · split at h
    · subst h; exact hs
    · exact within_finished he h (within_congr hs rfl rfl rfl)
  · subst h; exact hs
  · exact within_finished he h hs
  · split at h
    · split at h
      · subst h; exact hs
      · exact within_finished he h (within_congr hs rfl rfl rfl)
    · subst h; exact hs

theorem pendingOf_shape {e : Ty} : (shs : List (PendingShape e)) → (id : Nat) →
    (y : Ty.alts (shs.map PendingShape.fields)) → ∃ sh ∈ shs,
      (pendingOf shs id y).request.output = sh.output ∧ (pendingOf shs id y).request.rejection = sh.rejection
  | sh :: _, _, .inl _ => ⟨sh, List.mem_cons_self .., rfl, rfl⟩
  | _ :: shs, id, .inr y =>
    let ⟨sh, h, ho, hr⟩ := pendingOf_shape shs id y
    ⟨sh, List.mem_cons_of_mem _ h, ho, hr⟩

/-- A pending request of a state within the slots is of one of the shapes, so an answer to it has a shape's type. -/
theorem pending_shape {shs : List (PendingShape v.event)} {s : State v} (hW : Within L shs s) {p : Step.Pending v.event}
    (hp : p ∈ s.pending) : ∃ sh ∈ shs, p.request.output = sh.output ∧ p.request.rejection = sh.rejection := by
  obtain ⟨pv, hpv, -⟩ := hW
  rw [← hpv] at hp
  obtain ⟨⟨id, y⟩, -, rfl⟩ := List.mem_map.1 hp
  exact pendingOf_shape shs id y

end

/-- The types of what the service's inputs carry into a step's slots, as `inputVals` embeds them: the caller, each
command's input, each answer's value and each event. -/
def inputTys (v : ServiceV) : List Ty :=
  v.caller :: v.commands.map (·.input) ++ (shapes v).map (fun sh => answerTy sh.output sh.rejection) ++
    v.subscribes.map (·.event)

mutual
/-- Whether every value of the type embeds: it holds no list, bag or table, and the layout holds its datatypes. -/
def fitsAll (L : Layout) : Ty → Bool
  | .int | .str | .point _ => true
  | .id => (L.find? .id).isSome
  | .dsl k _ => k == .fresh
  | .adt 0 _ vs => (boolVs? vs).isSome
  | .adt (i + 1) a vs => (L.find? (.adt (i + 1) a vs)).isSome && fitsAllss L vs
  | .tuple ts => (L.find? (.tuple ts)).isSome && fitsAlls L ts
  | .list _ | .bag _ | .table .. | .fn .. | .param _ => false
def fitsAlls (L : Layout) : List Ty → Bool
  | [] => true
  | t :: ts => fitsAll L t && fitsAlls L ts
def fitsAllss (L : Layout) : List (List Ty) → Bool
  | [] => true
  | ts :: vs => fitsAlls L ts && fitsAllss L vs
end

section
variable {L : Layout}

mutual
theorem embed_of_fitsAll : (t : Ty) → fitsAll L t = true → (x : t.den) → (embedV L t x).isSome
  | .int, _, _ | .str, _, _ | .point _, _, _ => by simp [embedV]
  | .id, h, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := Option.isSome_iff_exists.1 h
    simp [embedV, hf]
  | .dsl k a, h, _ => by
    simp only [fitsAll, beq_iff_eq] at h; subst h; simp [embedV]
  | .adt 0 a vs, h, _ => by
    obtain ⟨⟨rfl⟩, -⟩ := Option.isSome_iff_exists.1 h
    simp [embedV]
  | .adt (i + 1) a vs, h, x => by
    simp only [fitsAll, Bool.and_eq_true] at h
    obtain ⟨⟨d, n⟩, hf⟩ := Option.isSome_iff_exists.1 h.1
    simp only [embedV, hf]
    exact embedAlts_of_fitsAll d 0 vs h.2 x
  | .tuple ts, h, x => by
    simp only [fitsAll, Bool.and_eq_true] at h
    obtain ⟨⟨d, n⟩, hf⟩ := Option.isSome_iff_exists.1 h.1
    simp only [embedV, hf, Option.isSome_map]
    exact embedVs_of_fitsAlls ts h.2 x
  | .list _, h, _ | .bag _, h, _ | .table .., h, _ | .fn .., h, _ | .param _, h, _ => by simp [fitsAll] at h
theorem embedVs_of_fitsAlls : (ts : List Ty) → fitsAlls L ts = true → (x : Ty.dens ts) → (embedVs L ts x).isSome
  | [], _, _ => by simp [embedVs]
  | t :: ts, h, (x, xs) => by
    simp only [fitsAlls, Bool.and_eq_true] at h
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (embed_of_fitsAll t h.1 x)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (embedVs_of_fitsAlls ts h.2 xs)
    simp [embedVs, ha, hb]
theorem embedAlts_of_fitsAll (d : Nat) : (k : Nat) → (vs : List (List Ty)) → fitsAllss L vs = true →
    (x : Ty.alts vs) → (embedAlts L d k vs x).isSome
  | _, [], _, x => nomatch x
  | _, fs :: _, h, .inl x => by
    simp only [fitsAllss, Bool.and_eq_true] at h
    simp only [embedAlts, Option.isSome_map]
    exact embedVs_of_fitsAlls fs h.1 x
  | k, _ :: vs, h, .inr y => by
    simp only [fitsAllss, Bool.and_eq_true] at h
    simp only [embedAlts]
    exact embedAlts_of_fitsAll d (k + 1) vs h.2 y
end

end

/-- Whether every value each input carries has data values that embed, so every input fits the slots. -/
def inputsFit (L : Layout) (v : ServiceV) : Bool := (inputTys v).all fun t => t.isData && fitsAll L t

/-- The empty table of pending requests. -/
def noPending {e : Ty} (shs : List (PendingShape e)) : PendingVal shs := ⟨[], List.Pairwise.nil⟩

/-- Whether the initial state fits the slots. -/
def initFits (L : Layout) (v : ServiceV) : Bool := (embedState L (Step.State.init v) (noPending (shapes v))).isSome

section
variable {L : Layout} {v : ServiceV} {T : List TypeDecl} {P : List AnySite}

theorem within_init (h : initFits L v = true) : Within L (shapes v) (Step.State.init v) := ⟨noPending _, rfl, h⟩

/-- Every input fits the slots, or it is an answer that names no pending request of its type and leaves the state as
it was. -/
theorem inputs_fit {E : List AnyEffectSite} (chk : Checked P E T v) (hin : inputsFit L v = true) {s : State v}
    (hW : Within L (shapes v) s) (x : Input v) :
    (inputVals L chk.callerData x).isSome ∨
      ((step T v s x).outcome = .fault .answerUnmatched ∧ (step T v s x).state = s) := by
  have hall : ∀ t ∈ inputTys v, t.isData = true ∧ fitsAll L t = true := fun t ht => by
    simpa only [Bool.and_eq_true] using List.all_eq_true.1 hin t ht
  have hfit : ∀ t ∈ inputTys v, ∀ (h : t.isData = true) (y : t.den0), (embedV L t (Ty.up t h y)).isSome :=
    fun t ht _ _ => embed_of_fitsAll t (hall t ht).2 _
  cases x with
  | command i caller input =>
    left
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hfit v.caller (by simp [inputTys]) chk.callerData caller)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hfit _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_iff_get.2 ⟨i, rfl⟩))))) (v.commands.get i).input_data input)
    simp only [inputVals, hc, Option.bind_some, hw, Option.map_some, Option.isSome_some]
  | query => left; rfl
  | answer to a =>
    obtain ⟨t, value⟩ := a
    cases hf : s.pending.find? (·.id == to) with
    | none => right; simp [step, hf]
    | some p =>
      cases hsame : Ty.same t (answerTy p.request.output p.request.rejection) with
      | none => right; simp [step, hf, hsame]
      | some e =>
        obtain ⟨he⟩ := e
        left
        obtain ⟨sh, hsh, ho, hr⟩ := pending_shape hW (List.mem_of_find?_eq_some hf)
        subst he
        have ht : answerTy p.request.output p.request.rejection ∈ inputTys v := by
          rw [ho, hr]
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hsh))
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hfit _ ht (hall _ ht).1 value)
        simp [inputVals, (hall _ ht).1, hw]
  | event i value =>
    left
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hfit _
      (List.mem_append_right _ (List.mem_map_of_mem (List.mem_iff_get.2 ⟨i, rfl⟩))) (v.subscribes.get i).event_data value)
    simp only [inputVals, hw, Option.map_some, Option.isSome_some]
  | clock => left; rfl

/-- An input kind's bound question is built and has no model: no step of the kind from a state within the slots
leaves them. -/
def BoundUnsat (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (senv : StepEnv L (shapes v))
    (inp : SymInput v (shapes v) senv.nT) : Prop :=
  ∃ gs qs, questions L T P v senv inp = .ok (gs, qs) ∧ ∀ q ∈ qs, q.target = none → Unsat L q.ask

/-- Where every input kind's bound question has no model and every input fits the slots, a step from a state within
the slots, on any input, leaves a state within them. -/
theorem within_step {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))
    (hin : inputsFit L v = true)
    (hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp)
    {s : State v} (hinv : Step.Inv P s) (hsupp : Step.StateSupp s) (hheld : Step.invariants s = [])
    (hkeys : Step.KeysOk T s) (hW : Within L (shapes v) s) (x : Input v) : Within L (shapes v) (step T v s x).state := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  rcases inputs_fit chk hin hW x with hx | ⟨-, h⟩
  · obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
    rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, _, M, hM, hsel, hS, hxd, hcase⟩ | h
    · obtain ⟨gs, qs, hqs, hun⟩ := hb inp hmem
      obtain ⟨t, ht, hcodes, hsites, hcond⟩ := bound_cond chk senv inp hqs hS hinv hsupp hkeys hheld hxd hcase
        fun q hq' hn => (hun q hq' hn).noModel_at (questions_tys L T P v senv hqs q hq') (questions_dts L T P v senv hqs q hq')
          (questions_vars L T P v senv hqs q hq') M
          (fun n h => varSorted_of_sorted (hM n h)) hsel
      have E := (step_encode chk senv (decode_state hS) hinv hxd ht).2 hcodes hsites (hcase t ht)
      exact within_stepRel chk.embeddable (E.2.1 hcond) hW
    · rw [h.2.2.1]; exact hW
  · rw [h]; exact hW

/-- Every state a run on valid inputs reaches from the initial state is within the slots, where the initial state is, every input
fits, and every input kind's bound question has no model. -/
theorem run_within {E : List AnyEffectSite} (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    (hin : inputsFit L v = true)
    (hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp)
    (hinit : Step.invariants (Step.State.init v) = []) (h0 : initFits L v = true) (is : List (Input v))
    (hvalid : Step.ValidRun T (Step.State.init v) is) :
    Within L (shapes v) (run T v (Step.State.init v) is).1 := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  suffices h : ∀ (xs : List (Input v)) (s : State v), Step.Inv P s → Step.StateSupp s → Step.invariants s = [] →
      Step.KeysOk T s → Step.ValidRun T s xs → Within L (shapes v) s → Within L (shapes v) (run T v s xs).1 from
    h is _ Step.init_inv (Step.init_supp he) hinit (Step.init_keys T hord chk.idle) hvalid (within_init h0)
  intro xs
  induction xs with
  | nil => intro s _ _ _ _ _ hW; exact hW
  | cons x xs ih =>
    intro s hinv hsupp hheld hkeys ⟨hx, hxs⟩ hW
    exact ih _ (step_inv T chk.reach s hinv x) (Step.step_supp T he hsupp hinv.below x hx) (step_invariants T s x hheld)
      (step_keys T s hkeys x) hxs (within_step chk senv hin hb hinv hsupp hheld hkeys hW x)

/-- T4 for every run: where every input kind's lines about the fault `f` read proved, the initial state fits the
slots and every value an input can carry fits them, no step of any run on valid inputs from an initial state whose
invariants hold faults with `f`. The bound questions keep every state a run reaches within the slots (`run_within`), where the lines'
questions cover every step. -/
theorem proved_sound {E : List AnyEffectSite} (chk : Checked P E T v) (he : v.Equivariant) (senv : StepEnv L (shapes v))
    (f : Fault) (hf : f ≠ .answerUnmatched) (hinit : Step.invariants (Step.State.init v) = []) (h0 : initFits L v = true)
    (hin : inputsFit L v = true)
    (hq : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), FaultLine L T P v senv f False inp)
    (is : List (Input v)) (hvalid : Step.ValidRun T (Step.State.init v) is) (x : Input v) :
    (step T v (run T v (Step.State.init v) is).1 x).outcome ≠ .fault f := by
  have hord : ∀ m ∈ v.machines, m.key.ordered T = true := fun m hm => (chk.keys m hm).2
  have hb : ∀ inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v), BoundUnsat L T P v senv inp := fun inp hm => by
    obtain ⟨gs, qs, hqs, -, hor⟩ := hq inp hm
    exact ⟨gs, qs, hqs, hor.resolve_right id⟩
  have hW := run_within chk he senv hin hb hinit h0 is hvalid
  have hsupp := Step.run_supp T he chk.reach _ Step.init_inv (Step.init_supp he) is hvalid
  rcases inputs_fit chk hin hW x with hx | ⟨hu, -⟩
  · obtain ⟨ivs, hivs⟩ := Option.isSome_iff_exists.1 hx
    have hkeys := run_keys T _ (Step.init_keys T hord chk.idle) is
    rcases covered chk senv hkeys hW x hivs with ⟨inp, hmem, hcov⟩ | h
    · obtain ⟨gs, qs, hqs, htg, hor⟩ := hq inp hmem
      refine verdict_covered chk senv f hf hinit inp hqs (fun q hq' h => ?_) is hsupp hkeys x hcov
      rcases h with h | h
      · exact hor.resolve_right id q hq' h
      · exact htg q hq' h
    · exact h.1 f hf
  · rw [hu]; exact fun h => hf (Outcome.fault.inj h).symm

end

end Tazuna.Smt
