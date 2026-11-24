import Tazuna.Smt.KeysInv

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
structure SymState where
  records : Term
  now : Term
  fresh : Term
  nextId : Term
  pending : Term
  /-- One instance table per machine, in the order of the service's machines. -/
  machines : List Term

/-- The symbolic state held by the constants `v<b>` to `v<b + 4 + n>`: the pending table at `v<b + 4>`, and `n`
machines' instance tables from `v<b + 5>` on. -/
def SymState.vars (b : Nat) (n : Nat := 0) : SymState :=
  ⟨.var b, .var (b + 1), .var (b + 2), .var (b + 3), .var (b + 4), (List.range n).map fun j => .var (b + 5 + j)⟩

def intOf : Val → Option Int
  | .int n => some n
  | _ => none

def natOf : Val → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none

section
variable {e : Ty}

/-- The table type that codes pending requests of the shapes: wire ids to entries. Wire ids are naturals, as the
fresh counter's values are, so the keys have the counter's type. -/
def pendingTable (shs : List (PendingShape e)) : Ty := .table (.dsl .fresh []) (pendingEntry shs)

/-- The pending requests' value at the shapes. With no shape the entry type has no value, so the table is empty. -/
abbrev PendingVal (shs : List (PendingShape e)) : Type := (pendingTable shs).den

/-- The pending requests a table codes, in its order. -/
def pendingList (shs : List (PendingShape e)) (tbl : (pendingTable shs).den) : List (Step.Pending e) :=
  tbl.1.map fun (id, x) => pendingOf shs id x

abbrev PendingVal.list {shs : List (PendingShape e)} (tbl : PendingVal shs) : List (Step.Pending e) := pendingList shs tbl

end

section
variable (M : Model) (L : Layout) {v : ServiceV} (hr : v.records.isData = true)

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
def decodeMachines (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → List Term →
    Option (List (Step.MachineState v.records v.event))
  | [], [] => some []
  | m :: ms, x :: xs => (decodeV L m.table (x.denote M)).bind fun tbl =>
    (decodeMachines T ms xs).map fun rest => ⟨m, instancesOf T m (Ty.down _ m.table_data tbl)⟩ :: rest
  | _, _ => none

/-- The instance tables' well-formedness: each table's. -/
def wfMachines : (ms : List (MachineV v.records v.event)) → List Term → Option Term
  | [], [] => some tt
  | m :: ms, x :: xs => (wfT L m.table x).bind fun c => (wfMachines ms xs).map (.and c ·)
  | _, _ => none

/-- The instance tables' values have their sorts' shape, as in every well-sorted model. -/
def MachinesSorted : (ms : List (MachineV v.records v.event)) → List Term → Prop
  | [], [] => True
  | m :: ms, x :: xs => Sorted L m.table (x.denote M) ∧ MachinesSorted ms xs
  | _, _ => False

/-- The SMT values of the machines' instance tables: none when some machine has a key twice. -/
def embedMachines : List (Step.MachineState v.records v.event) → Option (List Val)
  | [] => some []
  | ⟨m, insts⟩ :: sms =>
    if h : KeysUnique (Ty.semWith Dsl.base m.key).2 (instEntries m insts) then
      (embedV L m.table (Ty.up _ m.table_data (m.tableOf insts h))).bind fun w => (embedMachines sms).map (w :: ·)
    else none

/-- The tables denote the machines' instances: each table's entries, in key order. -/
def MachinesRel (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → List Term →
    List (Step.MachineState v.records v.event) → Prop
  | [], [], [] => True
  | m :: ms, x :: xs, sm :: sms =>
    (∃ tbl, RelV L m.table (Ty.up _ m.table_data tbl) (x.denote M) ∧ sm = ⟨m, instancesOf T m tbl⟩) ∧
      MachinesRel T ms xs sms
  | _, _, _ => False

/-- The terms denote the state's data. -/
def StateRel (S : SymState) (s : State v) : Prop :=
  RelV L v.records (Ty.up _ hr s.records) (S.records.denote M) ∧ S.now.denote M = .int s.now ∧
    S.fresh.denote M = .int (Int.ofNat s.fresh) ∧ S.nextId.denote M = .int (Int.ofNat s.nextId)

/-- The pending term denotes the pending requests, at the shapes. -/
def PendingRel (shs : List (PendingShape v.event)) (w : Val) (ps : List (Step.Pending v.event)) : Prop :=
  ∃ tbl, RelV L (pendingTable shs) tbl w ∧ pendingList _ tbl = ps

/-- The state whose data a model's values of the symbolic state are, with the pending requests of the shapes `shs`
and the instances in the canonical order of the type table `T`. -/
def SymState.decode (S : SymState) (T : List TypeDecl) (shs : List (PendingShape v.event)) : Option (State v) :=
  (decodeV L v.records (S.records.denote M)).bind fun r =>
  (intOf (S.now.denote M)).bind fun now =>
  (natOf (S.fresh.denote M)).bind fun fresh =>
  (natOf (S.nextId.denote M)).bind fun nextId =>
  (decodePending L shs (S.pending.denote M)).bind fun pending =>
  (decodeMachines M L T v.machines S.machines).map fun machines =>
  { records := Ty.down _ hr r, machines, pending, now, fresh, nextId }

/-- The well-formedness of the symbolic state, which a script asserts: the records, the pending table and the
instance tables decode and the counters are not negative. -/
def SymState.wf (S : SymState) (shs : List (PendingShape v.event)) : Option Term :=
  (wfT L v.records S.records).bind fun c => (wfPending L shs S.pending).bind fun cp =>
    (wfMachines L v.machines S.machines).map fun cm =>
    .and c (.and (.and (.le (.int 0) S.fresh) (.le (.int 0) S.nextId)) (.and cp cm))

/-- The values of the state's data, in the order of `SymState.vars`, with the pending requests as `pv`. -/
def embedState {shs : List (PendingShape v.event)} (s : State v) (pv : PendingVal shs) : Option (List Val) :=
  (embedV L v.records (Ty.up _ hr s.records)).bind fun r => (embedPending L shs pv).bind fun p =>
  (embedMachines L s.machines).map fun ms =>
  [r, .int s.now, .int (Int.ofNat s.fresh), .int (Int.ofNat s.nextId), p] ++ ms

/-- An input as terms. Which command, query or subscription an input names is fixed, so each has its own script; the
values it carries are terms. An answer is not symbolic yet: its type is the type of the pending request it answers. -/
inductive SymInput (v : ServiceV) where
  | command (i : Fin v.commands.length) (caller input : Term)
  | query (i : Fin v.queries.length) (caller input : Term)
  | event (i : Fin v.subscribes.length) (value : Term)
  | clock (time : Term)

/-- The input a model's values of the symbolic input denote. -/
def SymInput.decode (hc : v.caller.isData = true) (hin : ∀ i : Fin v.commands.length, (v.commands.get i).input.isData = true)
    (hq : ∀ i : Fin v.queries.length, (v.queries.get i).input.isData = true)
    (he : ∀ i : Fin v.subscribes.length, (v.subscribes.get i).event.isData = true) : SymInput v → Option (Input v)
  | .command i caller input =>
    (decodeV L v.caller (caller.denote M)).bind fun c =>
    (decodeV L _ (input.denote M)).map fun x => .command i (Ty.down _ hc c) (Ty.down _ (hin i) x)
  | .query i caller input =>
    (decodeV L v.caller (caller.denote M)).bind fun c =>
    (decodeV L _ (input.denote M)).map fun x => .query i (Ty.down _ hc c) (Ty.down _ (hq i) x)
  | .event i value => (decodeV L _ (value.denote M)).map fun x => .event i (Ty.down _ (he i) x)
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
variable {M : Model} {L : Layout} {v : ServiceV} {hr : v.records.isData = true}

/-- T3 for the pending requests: the decoded ones are the ones the value denotes. -/
theorem decode_pending (shs : List (PendingShape v.event)) {w : Val} {ps : List (Step.Pending v.event)}
    (h : decodePending L shs w = some ps) : PendingRel L shs w ps := by
  obtain ⟨tbl, ht, rfl⟩ := map_some.1 h
  exact ⟨tbl, decode_rel _ _ _ ht, rfl⟩

/-- T3 for the instances: the decoded instances are the ones the tables denote. -/
theorem decode_machines (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → (xs : List Term) →
    {sms : List (Step.MachineState v.records v.event)} → decodeMachines M L T ms xs = some sms → MachinesRel M L T ms xs sms
  | [], [], _, h => by simp only [decodeMachines, Option.some.injEq] at h; subst h; trivial
  | m :: ms, x :: xs, _, h => by
    obtain ⟨tbl, ht, h⟩ := bind_some.1 h
    obtain ⟨rest, hrest, rfl⟩ := map_some.1 h
    exact ⟨⟨Ty.down _ m.table_data tbl, by rw [Ty.up_down]; exact decode_rel _ _ _ ht, rfl⟩,
      decode_machines T ms xs hrest⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [decodeMachines] at h

/-- T3 for the state: the decoded state is the one the model's values denote. -/
theorem decode_state {S : SymState} {T : List TypeDecl} {shs : List (PendingShape v.event)} {s : State v}
    (h : S.decode M L hr T shs = some s) :
    StateRel M L hr S s ∧ PendingRel L shs (S.pending.denote M) s.pending ∧
      MachinesRel M L T v.machines S.machines s.machines := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, h⟩ := bind_some.1 h
  obtain ⟨ps, hps, h⟩ := bind_some.1 h
  obtain ⟨sms, hsms, rfl⟩ := map_some.1 h
  refine ⟨⟨?_, intOf_eq hnow, natOf_eq hfr, natOf_eq hni⟩, decode_pending shs hps, decode_machines T _ _ hsms⟩
  simpa [Ty.up_down] using decode_rel _ _ _ hrec

theorem decode_embedPending (shs : List (PendingShape v.event)) (pv : PendingVal shs) (w : Val)
    (h : embedPending L shs pv = some w) : decodePending L shs w = some pv.list := by
  simp only [decodePending, decode_embed _ _ _ h, PendingVal.list]; rfl

theorem embedMachines_length : (sms : List (Step.MachineState v.records v.event)) → (ws : List Val) →
    embedMachines L sms = some ws → ws.length = sms.length
  | [], _, h => by simp only [embedMachines, Option.some.injEq] at h; subst h; rfl
  | ⟨_, _⟩ :: sms, _, h => by
    simp only [embedMachines] at h
    split at h
    · obtain ⟨_, _, h⟩ := bind_some.1 h
      obtain ⟨ws', hws', rfl⟩ := map_some.1 h
      simp [embedMachines_length sms ws' hws']
    · cases h

/-- T3 for the instances: decoding inverts the embedding of instances in the step's form. -/
theorem decode_embedMachines (T : List TypeDecl) : (sms : List (Step.MachineState v.records v.event)) →
    (∀ sm ∈ sms, InstancesOk T sm.1 sm.2) → (xs : List Term) → (ws : List Val) → embedMachines L sms = some ws →
    xs.map (Term.denote M) = ws → decodeMachines M L T (sms.map (·.1)) xs = some sms
  | [], _, xs, ws, h, hx => by
    simp only [embedMachines, Option.some.injEq] at h; subst h
    rw [List.map_eq_nil_iff.1 hx]; rfl
  | ⟨m, insts⟩ :: sms, hok, xs, ws, h, hx => by
    simp only [embedMachines] at h
    split at h
    · rename_i hu
      obtain ⟨w, hw, h⟩ := bind_some.1 h
      obtain ⟨ws', hws', rfl⟩ := map_some.1 h
      match xs, hx with
      | x :: xs, hx =>
        simp only [List.map_cons, List.cons.injEq] at hx
        have hrest := decode_embedMachines T sms (fun sm h => hok sm (by simp [h])) xs ws' hws' hx.2
        simp only [List.map_cons, decodeMachines, hx.1, decode_embed _ _ _ hw, Option.bind_some, hrest, Option.map_some]
        rw [Ty.down_up]
        have he := instancesOf_entries T m insts ⟨(hok ⟨m, insts⟩ (by simp)).1, hu⟩
        rw [he]
    · cases h

/-- T3 for the state: decoding inverts the embedding, in any model whose constants hold the embedded values, for a
state whose machines are the service's with their instances in the step's form. -/
theorem decode_embedState (b : Nat) (T : List TypeDecl) {shs : List (PendingShape v.event)} (s : State v)
    (pv : PendingVal shs) (hpv : pv.list = s.pending) (hms : s.machines.map (·.1) = v.machines)
    (hok : ∀ sm ∈ s.machines, InstancesOk T sm.1 sm.2) (vals : List Val) (h : embedState L hr s pv = some vals)
    (hM : ∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) :
    (SymState.vars b v.machines.length).decode M L hr T shs = some s := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨p, hp, h⟩ := bind_some.1 h
  obtain ⟨ws, hws, rfl⟩ := map_some.1 h
  have h0 := hM 0 (by simp)
  have h1 := hM 1 (by simp)
  have h2 := hM 2 (by simp)
  have h3 := hM 3 (by simp)
  have h4 := hM 4 (by simp)
  simp only [List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3 h4
  have hlen : ws.length = v.machines.length := by
    rw [← hms, List.length_map]
    exact embedMachines_length s.machines ws hws
  have hx : ((List.range v.machines.length).map fun j => Term.var (b + 5 + j)).map (Term.denote M) = ws := by
    apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    have := hM (5 + j) (by simp at h2 ⊢; omega)
    simp only [List.cons_append] at this
    simp only [List.getElem_map, List.getElem_range, Term.denote]
    rw [show b + 5 + j = b + (5 + j) by omega, this]
    simp [List.getElem_cons_succ, show 5 + j = j + 1 + 1 + 1 + 1 + 1 by omega]
  have hdm := decode_embedMachines (M := M) T s.machines hok _ ws hws hx
  rw [hms] at hdm
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
    ∃ pv : PendingVal (shapes v P), pv.list = s.pending ∧ ∀ vals, embedState L hr s pv = some vals →
      ∀ M : Model, (∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) →
        (SymState.vars b v.machines.length).decode M L hr T (shapes v P) = some s := by
  obtain ⟨pv, hpv⟩ := exists_pendingVal (shapes v P) s.pending hinv.shaped hinv.nodup
  exact ⟨pv, hpv, fun vals h M hM =>
    decode_embedState b T s pv hpv hinv.machinesOf (fun sm h => (hkeys sm h).2) vals h hM⟩

/-- T3 for every state a run reaches from the initial state of a service whose program reaches only `P` and whose
machine keys are ordered (what check requires): no assumption about the state is left. -/
theorem decode_run (b : Nat) (T : List TypeDecl) {P : List AnySite} (hv : v.Reach P)
    (hord : ∀ m ∈ v.machines, m.key.ordered T = true) (is : List (Input v)) :
    ∃ pv : PendingVal (shapes v P), pv.list = (run T v (Step.State.init v) is).1.pending ∧
      ∀ vals, embedState L hr (run T v (Step.State.init v) is).1 pv = some vals →
      ∀ M : Model, (∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) →
        (SymState.vars b v.machines.length).decode M L hr T (shapes v P) = some (run T v (Step.State.init v) is).1 :=
  decode_reachable b T _ (run_inv T hv _ (Step.init_inv hv) is) (run_keys T _ (Step.init_keys T hord) is)

/-- The instance tables' well-formedness holds exactly when they decode. -/
theorem wfMachines_iff (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → (xs : List Term) → {c : Term} →
    wfMachines L ms xs = some c → MachinesSorted M L ms xs →
    (Holds M c ↔ (decodeMachines M L T ms xs).isSome = true)
  | [], [], _, hc, _ => by
    simp only [wfMachines, Option.some.injEq] at hc; subst hc
    simp [Holds, tt, Term.denote, Val.toBool, decodeMachines]
  | m :: ms, x :: xs, _, hc, hs => by
    obtain ⟨c1, hc1, hc⟩ := bind_some.1 hc
    obtain ⟨c2, hc2, rfl⟩ := map_some.1 hc
    rw [holds_and, wf_iff _ _ _ hc1 hs.1, wfMachines_iff T ms xs hc2 hs.2]
    simp only [decodeMachines]
    cases decodeV L m.table (x.denote M) <;> cases decodeMachines M L T ms xs <;> simp
  | [], _ :: _, _, hc, _ | _ :: _, [], _, hc, _ => by simp [wfMachines] at hc

/-- The symbolic state's well-formedness characterizes the states it decodes to: for values of the state's sorts it
holds exactly when they decode, so a model of a script that asserts it is a real state, and no state is lost. -/
theorem wf_decode {S : SymState} {T : List TypeDecl} {shs : List (PendingShape v.event)} {c : Term}
    (hc : S.wf L shs = some c)
    (hs : Sorted L v.records (S.records.denote M)) (hp : PendingSorted L shs (S.pending.denote M))
    (hm : MachinesSorted M L v.machines S.machines)
    (hnow : ∃ n, S.now.denote M = .int n)
    (hfr : ∃ n, S.fresh.denote M = .int n) (hni : ∃ n, S.nextId.denote M = .int n) :
    Holds M c ↔ (S.decode M L hr T shs).isSome = true := by
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

theorem sorted_of_decodeMachines (T : List TypeDecl) : (ms : List (MachineV v.records v.event)) → (xs : List Term) →
    {sms : List (Step.MachineState v.records v.event)} → decodeMachines M L T ms xs = some sms → MachinesSorted M L ms xs
  | [], [], _, _ => trivial
  | _ :: ms, _ :: xs, _, h => by
    obtain ⟨tbl, ht, h⟩ := bind_some.1 h
    obtain ⟨_, hrest, -⟩ := map_some.1 h
    exact ⟨decode_sorted _ _ tbl ht, sorted_of_decodeMachines T ms xs hrest⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [decodeMachines] at h

/-- Every state a model decodes to satisfies the well-formedness, embedded states among them. -/
theorem wf_of_decodeState {S : SymState} {T : List TypeDecl} {shs : List (PendingShape v.event)} {c : Term}
    (hc : S.wf L shs = some c) {s : State v} (h : S.decode M L hr T shs = some s) : Holds M c := by
  have h' := h
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, h⟩ := bind_some.1 h
  obtain ⟨ps, hps, h⟩ := bind_some.1 h
  obtain ⟨sms, hsms, _⟩ := map_some.1 h
  exact (wf_decode (hr := hr) hc (decode_sorted _ _ r hrec) (sorted_of_decodePending shs hps)
    (sorted_of_decodeMachines T _ _ hsms) ⟨now, intOf_eq hnow⟩ ⟨_, natOf_eq hfr⟩ ⟨_, natOf_eq hni⟩).2
    (by rw [h']; rfl)

/-- T3 for a query's input: the decoded caller and input are the values the model's values code. -/
theorem decode_query {hc : v.caller.isData = true} {hin hq he} {i : Fin v.queries.length} {sc si : Term}
    {x : Input v} (h : (SymInput.query i sc si).decode M L hc hin hq he = some x) :
    ∃ caller input, x = .query i caller input ∧ RelV L v.caller (Ty.up _ hc caller) (sc.denote M) ∧
      RelV L (v.queries.get i).input (Ty.up _ (hq i) input) (si.denote M) := by
  obtain ⟨c, h1, h⟩ := bind_some.1 h
  obtain ⟨y, h2, rfl⟩ := map_some.1 h
  exact ⟨_, _, rfl, by simpa [Ty.up_down] using decode_rel _ _ _ h1, by simpa [Ty.up_down] using decode_rel _ _ _ h2⟩

end

end Tazuna.Smt
