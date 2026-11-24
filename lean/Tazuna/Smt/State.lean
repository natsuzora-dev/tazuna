import Tazuna.Smt.Decode
import Tazuna.Semantics.Step

/-! The symbolic state: a service's state between two inputs as terms, so a script can ask about every state at once.
The records are one term of the records' sort, with each table in the slots its layout gives it; the time, the fresh
counter and the next wire id are Ints. Machine instances and pending requests are not symbolic yet: a pending
request holds the function its answer runs, which has no term. T3 for the state: `decode_state` reads a model's
values as the state they denote, and `decode_embedState` shows that decoding inverts the embedding, so every state
within the slots is some model's. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The state's data as terms. -/
structure SymState where
  records : Term
  now : Term
  fresh : Term
  nextId : Term

/-- The symbolic state held by the constants `v<b>` to `v<b + 3>`. -/
def SymState.vars (b : Nat) : SymState := ⟨.var b, .var (b + 1), .var (b + 2), .var (b + 3)⟩

def intOf : Val → Option Int
  | .int n => some n
  | _ => none

def natOf : Val → Option Nat
  | .int n => if 0 ≤ n then some n.toNat else none
  | _ => none

section
variable (M : Model) (L : Layout) {v : ServiceV} (hr : v.records.isData = true)

/-- The terms denote the state's data. -/
def StateRel (S : SymState) (s : State v) : Prop :=
  RelV L v.records (Ty.up _ hr s.records) (S.records.denote M) ∧ S.now.denote M = .int s.now ∧
    S.fresh.denote M = .int (Int.ofNat s.fresh) ∧ S.nextId.denote M = .int (Int.ofNat s.nextId)

/-- The state whose data a model's values of the symbolic state are, with the machine instances and pending requests
given. -/
def SymState.decode (S : SymState) (machines : List (Step.MachineState v.records v.event))
    (pending : Step.Bag (Step.Pending v.event)) : Option (State v) :=
  (decodeV L v.records (S.records.denote M)).bind fun r =>
  (intOf (S.now.denote M)).bind fun now =>
  (natOf (S.fresh.denote M)).bind fun fresh =>
  (natOf (S.nextId.denote M)).map fun nextId =>
  { records := Ty.down _ hr r, machines, pending, now, fresh, nextId }

/-- The values of the state's data, in the order of `SymState.vars`. -/
def embedState (s : State v) : Option (List Val) :=
  (embedV L v.records (Ty.up _ hr s.records)).map fun r =>
  [r, .int s.now, .int (Int.ofNat s.fresh), .int (Int.ofNat s.nextId)]

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

/-- T3 for the state: the decoded state is the one the model's values denote. -/
theorem decode_state {S : SymState} {ms : List (Step.MachineState v.records v.event)} {ps : Step.Bag (Step.Pending v.event)}
    {s : State v} (h : S.decode M L hr ms ps = some s) : StateRel M L hr S s ∧ s.machines = ms ∧ s.pending = ps := by
  obtain ⟨r, hrec, h⟩ := bind_some.1 h
  obtain ⟨now, hnow, h⟩ := bind_some.1 h
  obtain ⟨fr, hfr, h⟩ := bind_some.1 h
  obtain ⟨ni, hni, rfl⟩ := map_some.1 h
  refine ⟨⟨?_, intOf_eq hnow, natOf_eq hfr, natOf_eq hni⟩, rfl, rfl⟩
  simpa [Ty.up_down] using decode_rel _ _ _ hrec

/-- T3 for the state: decoding inverts the embedding, in any model whose constants hold the embedded values. -/
theorem decode_embedState (b : Nat) (s : State v) (vals : List Val) (h : embedState L hr s = some vals)
    (hM : ∀ j (hj : j < vals.length), M.vars (b + j) = vals[j]) :
    (SymState.vars b).decode M L hr s.machines s.pending = some s := by
  obtain ⟨r, hrec, rfl⟩ := map_some.1 h
  have h0 := hM 0 (by simp)
  have h1 := hM 1 (by simp)
  have h2 := hM 2 (by simp)
  have h3 := hM 3 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3
  simp only [SymState.decode, SymState.vars, Term.denote, h0, h1, h2, h3, decode_embed _ _ _ hrec, Option.bind_some,
    intOf, natOf, Int.ofNat_eq_natCast, Int.natCast_nonneg, ite_true, Int.toNat_natCast, Option.map_some, Ty.down_up]

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
