import Tazuna.Smt.KeysInv
import Tazuna.Semantics.PerMachine

/-! The symbolic state: a service's state between two inputs as terms, so a script can ask about every state at once.
The records are one term of the records' sort, with each table in the slots its layout gives it; the time, the fresh
counter and the next wire id are Ints. The pending requests are one table from wire id to an entry of the service's
pending shapes (`PendingShape`): which sender, which external command or query, which sites its `on_answer` and
`ensures` come from, and the data that varies. A state the terms denote therefore holds only requests of the
program's sites, with distinct wire ids. Each machine's instances are one table from key to state and timer
(`MachineV.table`), decoded in the canonical order of the keys, as the step keeps them. T3 for the state: `decode_state`
reads a model's values as the state they denote, and `decode_embedState` shows that decoding inverts the embedding,
so every state within the slots whose pending requests are of the shapes (`exists_pendingVal`) and whose instances
are in the step's form (`InstancesOk`) is some model's; every state a run reaches is such a state (`decode_run`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The state's data as terms. -/
structure SymState (v : ServiceV) where
  records : Term
  now : Term
  fresh : Term
  nextId : Term
  pending : Term
  machines : PerMachine (fun _ => Term) v.machines

/-- The constants `v<k>`, `v<k + 1>`, ..., one per machine. -/
def machineVars {r e : Ty} : (ms : List (MachineV r e)) → Nat → PerMachine (fun _ => Term) ms
  | [], _ => .nil
  | _ :: ms, k => .cons (.var k) (machineVars ms (k + 1))

/-- The symbolic state held by the constants from `v<b>` on: the pending table at `v<b + 4>` and the machines'
instance tables from `v<b + 5>` on. -/
def SymState.vars {v : ServiceV} (b : Nat) : SymState v :=
  ⟨.var b, .var (b + 1), .var (b + 2), .var (b + 3), .var (b + 4), machineVars v.machines (b + 5)⟩

def intOf : Val → Option Int
  | .int n => some n
  | _ => none

def natOf : Val → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none

section
variable {e : Ty}


/-- The pending requests' value at the shapes. With no shape the entry type has no value, so the table is empty. -/
abbrev PendingVal (shs : List (PendingShape e)) : Type := (pendingTable shs).den

/-- The pending requests a table codes, in its order. -/
def pendingList (shs : List (PendingShape e)) (tbl : (pendingTable shs).den) : List (Step.Pending e) :=
  tbl.1.map fun (id, x) => pendingOf shs id x

abbrev PendingVal.list {shs : List (PendingShape e)} (tbl : PendingVal shs) : List (Step.Pending e) := pendingList shs tbl

end

section
variable (M : Model) (L : Layout) {v : ServiceV}

/-- The pending requests a model's value codes, at the shapes. -/
def decodePending (shs : List (PendingShape v.event)) (w : Val) : Option (List (Step.Pending v.event)) :=
  (decodeV L (pendingTable shs) w).map (pendingList _)

/-- The pending table's well-formedness: the table's (distinct wire ids, each entry well-formed). -/
def wfPending (shs : List (PendingShape v.event)) (x : Term) : Option Term := wfT L (pendingTable shs) x

/-- The pending table's value has its sort's shape, as in every well-sorted model. -/
def PendingSorted (shs : List (PendingShape v.event)) (w : Val) : Prop := Sorted L (pendingTable shs) w

/-- The SMT value of the pending requests' value. -/
def embedPending (shs : List (PendingShape v.event)) (tbl : PendingVal shs) : Option Val := embedV L (pendingTable shs) tbl

/-- The machines' instances the tables' values code, one table per machine. -/
def decodeMachines (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → PerMachine (fun _ => Term) ms →
    Option (Step.Machines ms)
  | [], .nil => some .nil
  | m :: _, .cons x xs => (decodeV L m.table (x.denote M)).bind fun tbl =>
    (decodeMachines T _ xs).map (.cons (instancesOf T m (Ty.down _ m.table_data tbl)))

/-- The instance tables' well-formedness: each table's. -/
def wfMachines : (ms : List (MachineV v.records v.event)) → PerMachine (fun _ => Term) ms → Option Term
  | [], .nil => some tt
  | m :: ms, .cons x xs => (wfT L m.table x).bind fun c => (wfMachines ms xs).map (.and c ·)

/-- The instance tables' values have their sorts' shape, as in every well-sorted model. -/
def MachinesSorted : (ms : List (MachineV v.records v.event)) → PerMachine (fun _ => Term) ms → Prop
  | [], .nil => True
  | m :: ms, .cons x xs => Sorted L m.table (x.denote M) ∧ MachinesSorted ms xs

/-- The SMT values of the machines' instance tables: none when some machine has a key twice. -/
def embedMachines : {ms : List (MachineV v.records v.event)} → Step.Machines ms → Option (List Val)
  | _, .nil => some []
  | m :: _, .cons insts sms =>
    if h : KeysUnique (Ty.semWith Dsl.base m.key).2 (instEntries m insts) then
      (embedV L m.table (Ty.up _ m.table_data (m.tableOf insts h))).bind fun w => (embedMachines sms).map (w :: ·)
    else none

/-- The tables denote the machines' instances: each table's entries, in key order. -/
def MachinesRel (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → PerMachine (fun _ => Term) ms →
    Step.Machines ms → Prop
  | [], .nil, .nil => True
  | m :: ms, .cons x xs, .cons insts sms =>
    (∃ tbl, RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M) ∧ insts = instancesOf T m tbl) ∧
      MachinesRel T ms xs sms

/-- The pending term denotes the pending requests, at the shapes, as a multiset: the table keeps a request in its
slot while the step appends new ones after the others, and no step reads their order (an answer finds its request by
its wire id, which is unique). -/
def PendingRel (shs : List (PendingShape v.event)) (w : Val) (ps : List (Step.Pending v.event)) : Prop :=
  ∃ tbl, RelV L (pendingTable shs) tbl w ∧ (pendingList _ tbl).Perm ps

/-- The terms denote the state: what decoding gives (`decode_state`) and what every step theorem starts from. -/
structure StateRel (T : List TypeDecl) (shs : List (PendingShape v.event)) (S : SymState v) (s : State v) : Prop where
  records : RelV L v.records (Ty.up _ v.records_data s.records) (S.records.denote M)
  now : S.now.denote M = .int s.now
  fresh : S.fresh.denote M = .int (Int.ofNat s.fresh)
  nextId : S.nextId.denote M = .int (Int.ofNat s.nextId)
  pending : PendingRel L shs (S.pending.denote M) s.pending
  machines : MachinesRel M L T v.machines S.machines s.machines

/-- The state whose data a model's values of the symbolic state are, with the pending requests of the shapes `shs`
and the instances in the canonical order of the type table `T`. -/
def SymState.decode (S : SymState v) (T : List TypeDecl) (shs : List (PendingShape v.event)) : Option (State v) :=
  (decodeV L v.records (S.records.denote M)).bind fun r =>
  (intOf (S.now.denote M)).bind fun now =>
  (natOf (S.fresh.denote M)).bind fun fresh =>
  (natOf (S.nextId.denote M)).bind fun nextId =>
  (decodePending L shs (S.pending.denote M)).bind fun pending =>
  (decodeMachines M L T v.machines S.machines).map fun machines =>
  { records := Ty.down _ v.records_data r, machines, pending, now, fresh, nextId }

/-- The well-formedness of the symbolic state, which a script asserts: the records, the pending table and the
instance tables decode and the counters are not negative. -/
def SymState.wf (S : SymState v) (shs : List (PendingShape v.event)) : Option Term :=
  (wfT L v.records S.records).bind fun c => (wfPending L shs S.pending).bind fun cp =>
    (wfMachines L v.machines S.machines).map fun cm =>
    .and c (.and (.and (.le (.int 0) S.fresh) (.le (.int 0) S.nextId)) (.and cp cm))

/-- The values of the state's data, in the order of `SymState.vars`, with the pending requests as `pv`. -/
def embedState {shs : List (PendingShape v.event)} (s : State v) (pv : PendingVal shs) : Option (List Val) :=
  (embedV L v.records (Ty.up _ v.records_data s.records)).bind fun r => (embedPending L shs pv).bind fun p =>
  (embedMachines L s.machines).map fun ms =>
  [r, .int s.now, .int (Int.ofNat s.fresh), .int (Int.ofNat s.nextId), p] ++ ms

/-- An input as terms, at the pending shapes `shs` and a pending table of `slots` slots. Which command, query or
subscription an input names is fixed, so each has its own script; the values it carries are terms. An answer's script
fixes the case it asks about: that the `j`-th pending slot holds the request it names as an entry of the `k`-th
pending shape (`answer`), or that no slot holds it as an entry of a shape whose answers have its type `t`
(`unmatched`). -/
inductive SymInput (v : ServiceV) (shs : List (PendingShape v.event)) (slots : Nat) where
  | command (i : Fin v.commands.length) (caller input : Term)
  | query (i : Fin v.queries.length) (caller input : Term)
  | answer (k : Fin shs.length) (j : Fin slots) (to value : Term)
  | unmatched (t : Ty) (to value : Term)
  | event (i : Fin v.subscribes.length) (value : Term)
  | clock (time : Term)

/-- The answer of the type `t` to the wire id a model's values of the terms denote. -/
def decodeAnswer (t : Ty) (to value : Term) : Option (Input v) :=
  if h : t.isData = true then
    (natOf (to.denote M)).bind fun n => (decodeV L t (value.denote M)).map fun x => .answer n ⟨t, Ty.down _ h x⟩
  else none

/-- The input a model's values of the symbolic input denote. -/
def SymInput.decode {shs : List (PendingShape v.event)} {n : Nat} (hc : v.caller.isData = true) :
    SymInput v shs n → Option (Input v)
  | .answer k _ to value => decodeAnswer M L (answerTy shs[k].output shs[k].rejection) to value
  | .unmatched t to value => decodeAnswer M L t to value
  | .command i caller input =>
    (decodeV L v.caller (caller.denote M)).bind fun c =>
    (decodeV L _ (input.denote M)).map fun x => .command i (Ty.down _ hc c) (Ty.down _ (v.commands.get i).input_data x)
  | .query i caller input =>
    (decodeV L v.caller (caller.denote M)).bind fun c =>
    (decodeV L _ (input.denote M)).map fun x => .query i (Ty.down _ hc c) (Ty.down _ (v.queries.get i).input_data x)
  | .event i value => (decodeV L _ (value.denote M)).map fun x => .event i (Ty.down _ (v.subscribes.get i).event_data x)
  | .clock time => (intOf (time.denote M)).map .clock

end

theorem intOf_eq {w : Val} {n : Int} (h : intOf w = some n) : w = .int n := by
  unfold intOf at h; split at h <;> cases h; rfl

theorem natOf_eq {w : Val} {n : Nat} (h : natOf w = some n) : w = .int (Int.ofNat n) := by
  unfold natOf at h
  split at h
  · rename_i m; split at h
    · rename_i h0; cases h; rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg h0]
    · cases h
  · cases h

section
variable {M : Model} {L : Layout} {v : ServiceV}

/-- T3 for the pending requests: the decoded ones are the ones the value denotes. -/
theorem decode_pending (shs : List (PendingShape v.event)) {w : Val} {ps : List (Step.Pending v.event)}
    (h : decodePending L shs w = some ps) : PendingRel L shs w ps := by
  obtain ⟨tbl, ht, rfl⟩ := map_some.1 h
  exact ⟨tbl, decode_rel _ _ _ ht, .refl _⟩

/-- T3 for the instances: the decoded instances are the ones the tables denote. -/
theorem decode_machines (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) →
    {sms : Step.Machines ms} → decodeMachines M L T ms xs = some sms → MachinesRel M L T ms xs sms
  | [], .nil, _, h => by simp only [decodeMachines, Option.some.injEq] at h; subst h; trivial
  | m :: ms, .cons x xs, _, h => by
    obtain ⟨tbl, ht, h⟩ := bind_some.1 h
    obtain ⟨rest, hrest, rfl⟩ := map_some.1 h
    exact ⟨⟨Ty.down _ m.table_data tbl, by rw [Ty.up_down]; exact decode_rel _ _ _ ht, rfl⟩,
      decode_machines T ms xs hrest⟩

/-- T3 for the state: the decoded state is the one the model's values denote. -/
theorem decode_state {S : SymState v} {T : List TypeDecl} {shs : List (PendingShape v.event)} {s : State v}
    (h : S.decode M L T shs = some s) : StateRel M L T shs S s := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, h⟩ := bind_some.1 h
  obtain ⟨ps, hps, h⟩ := bind_some.1 h
  obtain ⟨sms, hsms, rfl⟩ := map_some.1 h
  refine ⟨?_, intOf_eq hnow, natOf_eq hfr, natOf_eq hni, decode_pending shs hps, decode_machines T _ _ hsms⟩
  simpa [Ty.up_down] using decode_rel _ _ _ hrec

theorem decode_embedPending (shs : List (PendingShape v.event)) (pv : PendingVal shs) (w : Val)
    (h : embedPending L shs pv = some w) : decodePending L shs w = some pv.list := by
  simp only [decodePending, decode_embed _ _ _ h, PendingVal.list]; rfl

theorem embedMachines_length : {ms : List (MachineV v.records v.event)} → (sms : Step.Machines ms) → (ws : List Val) →
    embedMachines L sms = some ws → ws.length = ms.length
  | _, .nil, _, h => by simp only [embedMachines, Option.some.injEq] at h; subst h; rfl
  | _ :: _, .cons _ sms, _, h => by
    simp only [embedMachines] at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_some.1 h
      obtain ⟨ws', hws', rfl⟩ := map_some.1 h
      simp [embedMachines_length sms ws' hws']
    · cases h

/-- T3 for the instances: decoding inverts the embedding of instances in the step's form. -/
theorem decode_embedMachines (T : List TypeDecl) : {ms : List (MachineV v.records v.event)} → (sms : Step.Machines ms) →
    (∀ sm ∈ sms.toSigma, InstancesOk T sm.1 sm.2) → (xs : PerMachine (fun _ => Term) ms) → (ws : List Val) →
    embedMachines L sms = some ws → xs.toList.map (Term.denote M) = ws → decodeMachines M L T ms xs = some sms
  | _, .nil, _, .nil, ws, h, _ => by
    simp only [embedMachines, Option.some.injEq] at h; subst h; rfl
  | m :: _, .cons insts sms, hok, .cons x xs, ws, h, hx => by
    simp only [embedMachines] at h
    split at h
    · rename_i hu
      obtain ⟨w, hw, h⟩ := bind_some.1 h
      obtain ⟨ws', hws', rfl⟩ := map_some.1 h
      simp only [PerMachine.toList_cons, List.map_cons, List.cons.injEq] at hx
      have hrest := decode_embedMachines T sms (fun sm h => hok sm (by simp [h])) xs ws' hws' hx.2
      simp only [decodeMachines, hx.1, decode_embed _ _ _ hw, Option.bind_some, hrest, Option.map_some]
      rw [Ty.down_up]
      have he := instancesOf_entries T m insts ⟨(hok ⟨m, insts⟩ (by simp)).1, hu⟩
      rw [he]
    · cases h

theorem machineVars_toList {r e : Ty} : (ms : List (MachineV r e)) → (k : Nat) →
    (machineVars ms k).toList = (List.range ms.length).map fun j => Term.var (k + j)
  | [], _ => rfl
  | _ :: ms, k => by
    simp only [machineVars, PerMachine.toList_cons, machineVars_toList ms (k + 1), List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, Term.var.injEq]
    omega

/-- T3 for the state: decoding inverts the embedding, in any model whose constants hold the embedded values, for a
state whose instances are in the step's form. -/
theorem decode_embedState (b : Nat) (T : List TypeDecl) {shs : List (PendingShape v.event)} (s : State v)
    (pv : PendingVal shs) (hpv : pv.list = s.pending)
    (hok : ∀ sm ∈ s.machines.toSigma, InstancesOk T sm.1 sm.2) (vals : List Val) (h : embedState L s pv = some vals)
    (hM : ∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) :
    (SymState.vars (v := v) b).decode M L T shs = some s := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨p, hp, h⟩ := bind_some.1 h
  obtain ⟨ws, hws, rfl⟩ := map_some.1 h
  have h0 := hM 0 (by simp)
  have h1 := hM 1 (by simp)
  have h2 := hM 2 (by simp)
  have h3 := hM 3 (by simp)
  have h4 := hM 4 (by simp)
  simp only [List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3 h4
  have hlen : ws.length = v.machines.length := embedMachines_length s.machines ws hws
  have hx : (machineVars v.machines (b + 5)).toList.map (Term.denote M) = ws := by
    rw [machineVars_toList]
    apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    have := hM (5 + j) (by simp at h2 ⊢; omega)
    simp only [List.cons_append] at this
    simp only [List.getElem_map, List.getElem_range, Term.denote]
    rw [show b + 5 + j = b + (5 + j) by omega, this]
    simp [List.getElem_cons_succ, show 5 + j = j + 1 + 1 + 1 + 1 + 1 by omega]
  have hdm := decode_embedMachines (M := M) T s.machines hok (machineVars v.machines (b + 5)) ws hws hx
  simp only [SymState.decode, SymState.vars, Term.denote, h0, h1, h2, h3, h4, decode_embed _ _ _ hrec,
    Option.bind_some, intOf, natOf, Int.ofNat_eq_natCast, Int.natCast_nonneg, ite_true, Int.toNat_natCast,
    decode_embedPending shs pv p hp, hpv, hdm, Option.map_some, Ty.down_up]

/-- Pending requests of the shapes with distinct wire ids are the requests of some value at the shapes, so a state
holding them is some model's when its values fit the slots (`decode_embedState`). -/
theorem exists_pendingVal (shs : List (PendingShape v.event)) : (ps : List (Step.Pending v.event)) →
    (∀ p ∈ ps, AtShapes shs p) → (ps.map (·.id)).Nodup → ∃ pv : PendingVal shs, pv.list = ps := by
  intro ps hps hnd
  induction ps with
  | nil => exact ⟨⟨[], .nil⟩, rfl⟩
  | cons p ps ih =>
    obtain ⟨⟨tbl, hu⟩, htbl⟩ := ih (fun q hq => hps q (by simp [hq])) (List.nodup_cons.1 hnd).2
    obtain ⟨x, hx⟩ := hps p (by simp)
    refine ⟨⟨(p.id, x) :: tbl, List.Pairwise.cons ?_ hu⟩, ?_⟩
    · intro b hb
      have hq : pendingOf shs b.1 b.2 ∈ ps := by
        rw [← htbl]; exact List.mem_map_of_mem (f := fun x => pendingOf shs x.1 x.2) hb
      have hne : (p.id : Nat) ≠ b.1 := fun e =>
        (List.nodup_cons.1 hnd).1 (List.mem_map.2 ⟨_, hq, (pendingOf_id shs b.1 b.2).trans e.symm⟩)
      constructor
      · show (@BEq.beq Nat _ p.id b.1) = false
        exact Bool.eq_false_iff.2 fun h => hne (beq_iff_eq.1 h)
      · show (@BEq.beq Nat _ b.1 p.id) = false
        exact Bool.eq_false_iff.2 fun h => hne (beq_iff_eq.1 h).symm
    · simp only [PendingVal.list, pendingList, List.map_cons] at htbl ⊢
      rw [hx, htbl]

/-- T3 for states that keep the step invariants (`Step.Inv`, `Step.KeysOk`): such a state holds pending requests of
the service's shapes and instances in the step's form, so when its values fit the slots the constants of some model
hold it and the symbolic state decodes to it. -/
theorem decode_reachable (b : Nat) (T : List TypeDecl) {P : List AnySite} (s : State v) (hinv : Step.Inv P s)
    (hkeys : Step.KeysOk T s) :
    ∃ pv : PendingVal (shapes v), pv.list = s.pending ∧ ∀ vals, embedState L s pv = some vals →
      ∀ M : Model, (∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) →
        (SymState.vars (v := v) b).decode M L T (shapes v) = some s := by
  obtain ⟨pv, hpv⟩ := exists_pendingVal (shapes v) s.pending hinv.shaped hinv.nodup
  exact ⟨pv, hpv, fun vals h M hM =>
    decode_embedState b T s pv hpv (fun sm h => (hkeys sm h).2.1) vals h hM⟩

/-- T3 for every state a run reaches from the initial state of a service whose program reaches only `P` and whose
machine keys are ordered (what check requires): no assumption about the state is left. -/
theorem decode_run (b : Nat) (T : List TypeDecl) {P : List AnySite} {E : List AnyEffectSite} (hv : v.Reach P E)
    (hord : ∀ m ∈ v.machines, m.key.ordered T = true)
    (hidle : ∀ m ∈ v.machines, m.instances.fn (v.init, ()) = []) (is : List (Input v)) :
    ∃ pv : PendingVal (shapes v), pv.list = (run T v (Step.State.init v) is).1.pending ∧
      ∀ vals, embedState L (run T v (Step.State.init v) is).1 pv = some vals →
      ∀ M : Model, (∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) →
        (SymState.vars (v := v) b).decode M L T (shapes v) = some (run T v (Step.State.init v) is).1 :=
  decode_reachable b T _ (run_inv T hv _ Step.init_inv is) (run_keys T _ (Step.init_keys T hord hidle) is)

/-- The instance tables' well-formedness holds exactly when they decode. -/
theorem wfMachines_iff (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) →
    {c : Term} → wfMachines L ms xs = some c → MachinesSorted M L ms xs →
    (Holds M c ↔ (decodeMachines M L T ms xs).isSome = true)
  | [], .nil, _, hc, _ => by
    simp only [wfMachines, Option.some.injEq] at hc; subst hc
    simp [Holds, tt, Term.denote, Val.toBool, decodeMachines]
  | m :: ms, .cons x xs, _, hc, hs => by
    obtain ⟨c1, hc1, hc⟩ := bind_some.1 hc
    obtain ⟨c2, hc2, rfl⟩ := map_some.1 hc
    rw [holds_and, wf_iff _ _ _ hc1 hs.1, wfMachines_iff T ms xs hc2 hs.2]
    simp only [decodeMachines]
    cases decodeV L m.table (x.denote M) <;> cases decodeMachines M L T ms xs <;> simp

/-- The symbolic state's well-formedness characterizes the states it decodes to: for values of the state's sorts it
holds exactly when they decode, so a model of a script that asserts it is a real state, and no state is lost. -/
theorem wf_decode {S : SymState v} {T : List TypeDecl} {shs : List (PendingShape v.event)} {c : Term}
    (hc : S.wf L shs = some c)
    (hs : Sorted L v.records (S.records.denote M)) (hp : PendingSorted L shs (S.pending.denote M))
    (hm : MachinesSorted M L v.machines S.machines)
    (hnow : ∃ n, S.now.denote M = .int n)
    (hfr : ∃ n, S.fresh.denote M = .int n) (hni : ∃ n, S.nextId.denote M = .int n) :
    Holds M c ↔ (S.decode M L T shs).isSome = true := by
  obtain ⟨cr, hcr, h⟩ := bind_some.1 hc
  obtain ⟨cp, hcp, h⟩ := bind_some.1 h
  obtain ⟨cm, hcm, rfl⟩ := map_some.1 h
  obtain ⟨now, hnow⟩ := hnow
  obtain ⟨fr, hfr⟩ := hfr
  obtain ⟨ni, hni⟩ := hni
  have hw := wf_iff (M := M) v.records S.records cr hcr hs
  have hwp : Holds M cp ↔ (decodePending L shs (S.pending.denote M)).isSome = true := by
    rw [wf_iff _ _ _ hcp hp]; simp only [decodePending, Option.isSome_map]
  have hwm := wfMachines_iff T v.machines S.machines hcm hm
  rw [holds_and, holds_and, holds_and, holds_and, hw, hwp, hwm]
  simp only [Holds, Term.denote, hfr, hni, Val.toInt, Val.toBool, decide_eq_true_eq]
  simp only [SymState.decode, hnow, hfr, hni, intOf, natOf, Option.bind_some]
  cases decodeV L v.records (S.records.denote M) <;> cases decodePending L shs (S.pending.denote M) <;>
    cases decodeMachines M L T v.machines S.machines <;> simp
  all_goals by_cases h1 : 0 ≤ fr <;> by_cases h2 : 0 ≤ ni <;> simp [h1, h2]

theorem sorted_of_decodePending (shs : List (PendingShape v.event)) {w : Val} {ps : List (Step.Pending v.event)}
    (h : decodePending L shs w = some ps) : PendingSorted L shs w := by
  obtain ⟨tbl, ht, -⟩ := map_some.1 h; exact decode_sorted _ _ tbl ht

theorem sorted_of_decodeMachines (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) →
    (xs : PerMachine (fun _ => Term) ms) → {sms : Step.Machines ms} →
    decodeMachines M L T ms xs = some sms → MachinesSorted M L ms xs
  | [], .nil, _, _ => trivial
  | _ :: ms, .cons _ xs, _, h => by
    obtain ⟨tbl, ht, h⟩ := bind_some.1 h
    obtain ⟨_, hrest, -⟩ := map_some.1 h
    exact ⟨decode_sorted _ _ tbl ht, sorted_of_decodeMachines T ms xs hrest⟩

/-- Every state a model decodes to satisfies the well-formedness, embedded states among them. -/
theorem wf_of_decodeState {S : SymState v} {T : List TypeDecl} {shs : List (PendingShape v.event)} {c : Term}
    (hc : S.wf L shs = some c) {s : State v} (h : S.decode M L T shs = some s) : Holds M c := by
  have h' := h
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, h⟩ := bind_some.1 h
  obtain ⟨ps, hps, h⟩ := bind_some.1 h
  obtain ⟨sms, hsms, _⟩ := map_some.1 h
  exact (wf_decode (T := T) hc (decode_sorted _ _ r hrec) (sorted_of_decodePending shs hps)
    (sorted_of_decodeMachines T _ _ hsms) ⟨now, intOf_eq hnow⟩ ⟨_, natOf_eq hfr⟩ ⟨_, natOf_eq hni⟩).2
    (by rw [h']; rfl)

/-- T3 for a query's input: the decoded caller and input are the values the model's values code. -/
theorem decode_query {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true}
    {i : Fin v.queries.length} {sc si : Term} {x : Input v}
    (h : (SymInput.query (shs := shs) (slots := n) i sc si).decode M L hc = some x) :
    ∃ caller input, x = .query i caller input ∧ RelV L v.caller (Ty.up _ hc caller) (sc.denote M) ∧
      RelV L (v.queries.get i).input (Ty.up _ (v.queries.get i).input_data input) (si.denote M) := by
  obtain ⟨c, h1, h⟩ := bind_some.1 h
  obtain ⟨y, h2, rfl⟩ := map_some.1 h
  exact ⟨_, _, rfl, by simpa [Ty.up_down] using decode_rel _ _ _ h1, by simpa [Ty.up_down] using decode_rel _ _ _ h2⟩

/-- T3 for a command's input. -/
theorem decode_command {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true}
    {i : Fin v.commands.length} {sc si : Term} {x : Input v}
    (h : (SymInput.command (shs := shs) (slots := n) i sc si).decode M L hc = some x) :
    ∃ caller input, x = .command i caller input ∧ RelV L v.caller (Ty.up _ hc caller) (sc.denote M) ∧
      RelV L (v.commands.get i).input (Ty.up _ (v.commands.get i).input_data input) (si.denote M) := by
  obtain ⟨c, h1, h⟩ := bind_some.1 h
  obtain ⟨y, h2, rfl⟩ := map_some.1 h
  exact ⟨_, _, rfl, by simpa [Ty.up_down] using decode_rel _ _ _ h1, by simpa [Ty.up_down] using decode_rel _ _ _ h2⟩

/-- T3 for an event's input. -/
theorem decode_event {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true}
    {i : Fin v.subscribes.length} {sv : Term} {x : Input v}
    (h : (SymInput.event (shs := shs) (slots := n) i sv).decode M L hc = some x) :
    ∃ value, x = .event i value ∧ RelV L (v.subscribes.get i).event (Ty.up _ (v.subscribes.get i).event_data value) (sv.denote M) := by
  obtain ⟨y, h1, rfl⟩ := map_some.1 h
  exact ⟨_, rfl, by simpa [Ty.up_down] using decode_rel _ _ _ h1⟩

/-- T3 for a clock line's input. -/
theorem decode_clock {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true} {st : Term}
    {x : Input v} (h : (SymInput.clock (shs := shs) (slots := n) st).decode M L hc = some x) :
    ∃ time, x = .clock time ∧ st.denote M = .int time := by
  obtain ⟨n, h1, rfl⟩ := map_some.1 h
  exact ⟨n, rfl, intOf_eq h1⟩

/-- T3 for an answer of the type `t`. -/
theorem decode_answer {t : Ty} {toT valT : Term} {x : Input v} (h : decodeAnswer M L t toT valT = some x) :
    ∃ (ht : t.isData = true) (to : Nat) (value : t.den0), x = .answer to ⟨t, value⟩ ∧
      toT.denote M = .int (Int.ofNat to) ∧ RelV L t (Ty.up _ ht value) (valT.denote M) := by
  unfold decodeAnswer at h
  split at h
  · rename_i ht
    obtain ⟨n, h1, h⟩ := bind_some.1 h
    obtain ⟨y, h2, rfl⟩ := map_some.1 h
    exact ⟨ht, n, _, rfl, natOf_eq h1, by simpa [Ty.up_down] using decode_rel _ _ _ h2⟩
  · cases h

end

section
variable (L : Layout) {v : ServiceV}

/-- The input's terms are well formed, as a state's are (`SymState.wf`): each value's slots and ids, and an answer's
wire id not negative. Every script whose models are read as inputs asserts it, so a model's values decode to an
input; every input a model decodes to satisfies it (`SymInput.wf_of_decode`), so no input is lost. -/
def SymInput.wf {shs : List (PendingShape v.event)} {n : Nat} : SymInput v shs n → Option Term
  | .command i caller input => (wfT L v.caller caller).bind fun c => (wfT L (v.commands.get i).input input).map (andT c)
  | .query i caller input => (wfT L v.caller caller).bind fun c => (wfT L (v.queries.get i).input input).map (andT c)
  | .answer k _ to value => (wfT L (answerTy shs[k].output shs[k].rejection) value).map (andT (.le (.int 0) to))
  | .unmatched t to value => (wfT L t value).map (andT (.le (.int 0) to))
  | .event i value => wfT L (v.subscribes.get i).event value
  | .clock _ => some tt

end

section
variable {M : Model} {L : Layout} {v : ServiceV}

theorem wfT_of_decodeV {t : Ty} {x : Term} {c : Term} {y : t.den} (hc : wfT L t x = some c)
    (h : decodeV L t (x.denote M) = some y) : Holds M c :=
  (wf_iff t x c hc (decode_sorted t _ y h)).2 (by rw [h]; rfl)

theorem natOf_holds {to : Term} {k : Nat} (h : natOf (to.denote M) = some k) : Holds M (.le (.int 0) to) := by
  simp [Holds, Term.denote, natOf_eq h, Val.toBool, Val.toInt]

theorem answer_wf_of_decode {t : Ty} {to value c : Term} {x : Input v} (hc : (wfT L t value).map (andT (.le (.int 0) to)) = some c)
    (h : decodeAnswer M L t to value = some x) : Holds M c := by
  obtain ⟨cv, hcv, rfl⟩ := map_some.1 hc
  unfold decodeAnswer at h
  split at h
  · obtain ⟨k, h1, h⟩ := bind_some.1 h
    obtain ⟨y, h2, -⟩ := map_some.1 h
    exact (holds_andT _ _).2 ⟨natOf_holds h1, wfT_of_decodeV hcv h2⟩
  · cases h

/-- Every input a model decodes to satisfies the input's well-formedness. -/
theorem SymInput.wf_of_decode {shs : List (PendingShape v.event)} {n : Nat} {hc : v.caller.isData = true}
    {inp : SymInput v shs n} {c : Term} (hw : inp.wf L = some c) {x : Input v} (h : inp.decode M L hc = some x) :
    Holds M c := by
  cases inp with
  | command i caller input | query i caller input =>
    obtain ⟨c1, hc1, hw⟩ := bind_some.1 hw
    obtain ⟨c2, hc2, rfl⟩ := map_some.1 hw
    obtain ⟨y1, h1, h⟩ := bind_some.1 h
    obtain ⟨y2, h2, -⟩ := map_some.1 h
    exact (holds_andT _ _).2 ⟨wfT_of_decodeV hc1 h1, wfT_of_decodeV hc2 h2⟩
  | answer k j to value => exact answer_wf_of_decode hw h
  | unmatched t to value => exact answer_wf_of_decode hw h
  | event i value =>
    obtain ⟨y, h1, -⟩ := map_some.1 h
    exact wfT_of_decodeV hw h1
  | clock time => cases hw; exact holds_tt

end

end Tazuna.Smt
