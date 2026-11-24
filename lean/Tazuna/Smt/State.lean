import Tazuna.Smt.Wf
import Tazuna.Semantics.Sites

/-! The symbolic state: a service's state between two inputs as terms, so a script can ask about every state at once.
The records are one term of the records' sort, with each table in the slots its layout gives it; the time, the fresh
counter and the next wire id are Ints. The pending requests are one table from wire id to an entry of the service's
pending shapes (`PendingShape`): which sender, which external command or query, which sites its `on_answer` and
`ensures` come from, and the data that varies. A state the terms denote therefore holds only requests of the
program's sites, with distinct wire ids. Machine instances are not symbolic yet. T3 for the state: `decode_state`
reads a model's values as the state they denote, and `decode_embedState` shows that decoding inverts the embedding,
so every state within the slots whose pending requests are of the shapes (`exists_pendingVal`) is some model's. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The state's data as terms. -/
structure SymState where
  records : Term
  now : Term
  fresh : Term
  nextId : Term
  pending : Term

/-- The symbolic state held by the constants `v<b>` to `v<b + 4>`; the pending table at `v<b + 4>` is read only when
the service has pending shapes, so a script for a service without them may use that constant for something else. -/
def SymState.vars (b : Nat) : SymState := ⟨.var b, .var (b + 1), .var (b + 2), .var (b + 3), .var (b + 4)⟩

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

/-- The pending requests' value at the shapes: none when there is no shape, so nothing can be pending; else a table. -/
def PendingVal : List (PendingShape e) → Type
  | [] => Unit
  | sh :: shs => (pendingTable (sh :: shs)).den

/-- The pending requests a table codes, in its order. -/
def pendingList (shs : List (PendingShape e)) (tbl : (pendingTable shs).den) : List (Step.Pending e) :=
  tbl.1.map fun (id, x) => pendingOf shs id x

def PendingVal.list : {shs : List (PendingShape e)} → PendingVal shs → List (Step.Pending e)
  | [], () => []
  | _ :: _, tbl => pendingList _ tbl

end

section
variable (M : Model) (L : Layout) {v : ServiceV} (hr : v.records.isData = true)

/-- The pending requests a model's value codes, at the shapes. -/
def decodePending : (shs : List (PendingShape v.event)) → Val → Option (List (Step.Pending v.event))
  | [], _ => some []
  | sh :: shs, w => (decodeV L (pendingTable (sh :: shs)) w).map (pendingList _)

/-- The pending table's well-formedness: the table's (distinct wire ids, each entry well-formed). -/
def wfPending : List (PendingShape v.event) → Term → Option Term
  | [], _ => some tt
  | sh :: shs, x => wfT L (pendingTable (sh :: shs)) x

/-- The pending table's value has its sort's shape, as in every well-sorted model. -/
def PendingSorted : List (PendingShape v.event) → Val → Prop
  | [], _ => True
  | sh :: shs, w => Sorted L (pendingTable (sh :: shs)) w

/-- The SMT value of the pending requests' value. -/
def embedPending : (shs : List (PendingShape v.event)) → PendingVal shs → Option Val
  | [], () => some (.int 0)
  | sh :: shs, tbl => embedV L (pendingTable (sh :: shs)) tbl

/-- The terms denote the state's data. -/
def StateRel (S : SymState) (s : State v) : Prop :=
  RelV L v.records (Ty.up _ hr s.records) (S.records.denote M) ∧ S.now.denote M = .int s.now ∧
    S.fresh.denote M = .int (Int.ofNat s.fresh) ∧ S.nextId.denote M = .int (Int.ofNat s.nextId)

/-- The pending term denotes the pending requests, at the shapes. -/
def PendingRel : (shs : List (PendingShape v.event)) → Val → List (Step.Pending v.event) → Prop
  | [], _, ps => ps = []
  | sh :: shs, w, ps => ∃ tbl, RelV L (pendingTable (sh :: shs)) tbl w ∧ pendingList _ tbl = ps

/-- The state whose data a model's values of the symbolic state are, with the machine instances given and the
pending requests of the shapes `shs`. -/
def SymState.decode (S : SymState) (machines : List (Step.MachineState v.records v.event))
    (shs : List (PendingShape v.event)) : Option (State v) :=
  (decodeV L v.records (S.records.denote M)).bind fun r =>
  (intOf (S.now.denote M)).bind fun now =>
  (natOf (S.fresh.denote M)).bind fun fresh =>
  (natOf (S.nextId.denote M)).bind fun nextId =>
  (decodePending L shs (S.pending.denote M)).map fun pending =>
  { records := Ty.down _ hr r, machines, pending, now, fresh, nextId }

/-- The well-formedness of the symbolic state, which a script asserts: the records and the pending table decode and
the counters are not negative. -/
def SymState.wf (S : SymState) (shs : List (PendingShape v.event)) : Option Term :=
  (wfT L v.records S.records).bind fun c => (wfPending L shs S.pending).map fun cp =>
    .and c (.and (.and (.le (.int 0) S.fresh) (.le (.int 0) S.nextId)) cp)

/-- The values of the state's data, in the order of `SymState.vars`, with the pending requests as `pv`. -/
def embedState {shs : List (PendingShape v.event)} (s : State v) (pv : PendingVal shs) : Option (List Val) :=
  (embedV L v.records (Ty.up _ hr s.records)).bind fun r => (embedPending L shs pv).map fun p =>
  [r, .int s.now, .int (Int.ofNat s.fresh), .int (Int.ofNat s.nextId), p]

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
theorem decode_pending : (shs : List (PendingShape v.event)) → {w : Val} → {ps : List (Step.Pending v.event)} →
    decodePending L shs w = some ps → PendingRel L shs w ps
  | [], _, _, h => by simp only [decodePending, Option.some.injEq] at h; exact h.symm
  | _ :: _, _, _, h => by
    obtain ⟨tbl, ht, rfl⟩ := map_some.1 h
    exact ⟨tbl, decode_rel _ _ _ ht, rfl⟩

/-- T3 for the state: the decoded state is the one the model's values denote. -/
theorem decode_state {S : SymState} {ms : List (Step.MachineState v.records v.event)} {shs : List (PendingShape v.event)}
    {s : State v} (h : S.decode M L hr ms shs = some s) :
    StateRel M L hr S s ∧ PendingRel L shs (S.pending.denote M) s.pending ∧ s.machines = ms := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, h⟩ := bind_some.1 h
  obtain ⟨ps, hps, rfl⟩ := map_some.1 h
  refine ⟨⟨?_, intOf_eq hnow, natOf_eq hfr, natOf_eq hni⟩, decode_pending shs hps, rfl⟩
  simpa [Ty.up_down] using decode_rel _ _ _ hrec

theorem decode_embedPending : (shs : List (PendingShape v.event)) → (pv : PendingVal shs) → (w : Val) →
    embedPending L shs pv = some w → decodePending L shs w = some pv.list
  | [], (), _, _ => rfl
  | _ :: _, tbl, _, h => by
    simp only [decodePending, decode_embed _ _ _ h, PendingVal.list]; rfl

/-- T3 for the state: decoding inverts the embedding, in any model whose constants hold the embedded values. -/
theorem decode_embedState (b : Nat) {shs : List (PendingShape v.event)} (s : State v) (pv : PendingVal shs)
    (hpv : pv.list = s.pending) (vals : List Val) (h : embedState L hr s pv = some vals)
    (hM : ∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) :
    (SymState.vars b).decode M L hr s.machines shs = some s := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨p, hp, rfl⟩ := map_some.1 h
  have h0 := hM 0 (by simp)
  have h1 := hM 1 (by simp)
  have h2 := hM 2 (by simp)
  have h3 := hM 3 (by simp)
  have h4 := hM 4 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3 h4
  simp only [SymState.decode, SymState.vars, Term.denote, h0, h1, h2, h3, h4, decode_embed _ _ _ hrec, Option.bind_some,
    intOf, natOf, Int.ofNat_eq_natCast, Int.natCast_nonneg, ite_true, Int.toNat_natCast, Option.map_some, Ty.down_up,
    decode_embedPending shs pv p hp, hpv]

/-- Pending requests of the shapes with distinct wire ids are the requests of some value at the shapes, so a state
holding them is some model's when its values fit the slots (`decode_embedState`). -/
theorem exists_pendingVal (shs : List (PendingShape v.event)) : (ps : List (Step.Pending v.event)) →
    (∀ p ∈ ps, AtShapes shs p) → (ps.map (·.id)).Nodup → ∃ pv : PendingVal shs, pv.list = ps := by
  match shs with
  | [] =>
    intro ps hps _
    cases ps with
    | nil => exact ⟨(), rfl⟩
    | cons p _ => obtain ⟨x, _⟩ := hps p (by simp); exact x.elim
  | sh :: shs =>
    intro ps hps hnd
    induction ps with
    | nil => exact ⟨⟨[], .nil⟩, rfl⟩
    | cons p ps ih =>
      obtain ⟨⟨tbl, hu⟩, htbl⟩ := ih (fun q hq => hps q (by simp [hq])) (List.nodup_cons.1 hnd).2
      obtain ⟨x, hx⟩ := hps p (by simp)
      refine ⟨⟨(p.id, x) :: tbl, List.Pairwise.cons ?_ hu⟩, ?_⟩
      · intro b hb
        have hq : pendingOf (sh :: shs) b.1 b.2 ∈ ps := by
          rw [← htbl]; exact List.mem_map_of_mem (f := fun x => pendingOf (sh :: shs) x.1 x.2) hb
        have hne : (p.id : Nat) ≠ b.1 := fun e =>
          (List.nodup_cons.1 hnd).1 (List.mem_map.2 ⟨_, hq, (pendingOf_id (sh :: shs) b.1 b.2).trans e.symm⟩)
        constructor
        · show (@BEq.beq Nat _ p.id b.1) = false
          exact Bool.eq_false_iff.2 fun h => hne (beq_iff_eq.1 h)
        · show (@BEq.beq Nat _ b.1 p.id) = false
          exact Bool.eq_false_iff.2 fun h => hne (beq_iff_eq.1 h).symm
      · simp only [PendingVal.list, pendingList, List.map_cons] at htbl ⊢
        rw [hx, htbl]

/-- The symbolic state's well-formedness characterizes the states it decodes to: for values of the state's sorts it
holds exactly when they decode, so a model of a script that asserts it is a real state, and no state is lost. -/
theorem wf_decode {S : SymState} {shs : List (PendingShape v.event)} {c : Term} (hc : S.wf L shs = some c)
    (hs : Sorted L v.records (S.records.denote M)) (hp : PendingSorted L shs (S.pending.denote M))
    (hnow : ∃ n, S.now.denote M = .int n)
    (hfr : ∃ n, S.fresh.denote M = .int n) (hni : ∃ n, S.nextId.denote M = .int n)
    (ms : List (Step.MachineState v.records v.event)) :
    Holds M c ↔ (S.decode M L hr ms shs).isSome = true := by
  obtain ⟨cr, hcr, h⟩ := bind_some.1 hc
  obtain ⟨cp, hcp, rfl⟩ := map_some.1 h
  obtain ⟨now, hnow⟩ := hnow
  obtain ⟨fr, hfr⟩ := hfr
  obtain ⟨ni, hni⟩ := hni
  have hw := wf_iff (M := M) v.records S.records cr hcr hs
  have hwp : Holds M cp ↔ (decodePending L shs (S.pending.denote M)).isSome = true := by
    match shs, hcp, hp with
    | [], hcp, _ =>
      simp only [wfPending, Option.some.injEq] at hcp; subst hcp
      simp [Holds, tt, Term.denote, Val.toBool, decodePending]
    | _ :: _, hcp, hp =>
      rw [wf_iff _ _ _ hcp hp]; simp only [decodePending, Option.isSome_map]
  rw [holds_and, holds_and, holds_and, hw, hwp]
  simp only [Holds, Term.denote, hfr, hni, Val.toInt, Val.toBool, decide_eq_true_eq]
  simp only [SymState.decode, hnow, hfr, hni, intOf, natOf, Option.bind_some]
  cases decodeV L v.records (S.records.denote M) <;> simp
  by_cases h1 : 0 ≤ fr <;> by_cases h2 : 0 ≤ ni <;> simp [h1, h2]

theorem sorted_of_decodePending : (shs : List (PendingShape v.event)) → {w : Val} → {ps : List (Step.Pending v.event)} →
    decodePending L shs w = some ps → PendingSorted L shs w
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => by obtain ⟨tbl, ht, -⟩ := map_some.1 h; exact decode_sorted _ _ tbl ht

/-- Every state a model decodes to satisfies the well-formedness, embedded states among them. -/
theorem wf_of_decodeState {S : SymState} {shs : List (PendingShape v.event)} {c : Term} (hc : S.wf L shs = some c)
    {ms : List (Step.MachineState v.records v.event)} {s : State v}
    (h : S.decode M L hr ms shs = some s) : Holds M c := by
  have h' := h
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, h⟩ := bind_some.1 h
  obtain ⟨ps, hps, _⟩ := map_some.1 h
  exact (wf_decode (hr := hr) hc (decode_sorted _ _ r hrec) (sorted_of_decodePending shs hps) ⟨now, intOf_eq hnow⟩
    ⟨_, natOf_eq hfr⟩ ⟨_, natOf_eq hni⟩ ms).2 (by rw [h']; rfl)

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
