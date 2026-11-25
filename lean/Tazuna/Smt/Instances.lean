import Tazuna.Smt.Wf
import Tazuna.Semantics.Step

/-! A machine's live instances as data: a table from each key to its entry, the state and the timer (the deadline and
the state it enters). The step keeps instances in the canonical order of their keys with no key twice, and a table
has no order, so the instances a table holds are its entries sorted by key (`instancesOf`), and every list of
instances in that form is some table's (`instancesOf_entries`). -/

namespace Tazuna.Ir

section
variable {r e : Ty}

/-- What a key maps to: the instance's state and its timer, as the deadline and the state it enters. -/
def instEntry (st : Ty) : Ty := .tuple [st, Ty.option (.tuple [.int, st])]

/-- The table a machine's instances are: key to entry. -/
def MachineV.table (m : MachineV r e) : Ty := .table m.key (instEntry m.state)

theorem MachineV.key_data (m : MachineV r e) : m.key.isData = true := by
  have h := m.on.ht
  simp only [Ty.machineCtx, Ty.isData, Ty.isDatas, Ty.isDatass, Bool.and_eq_true] at h
  exact h.1.1.1.1
theorem MachineV.state_data (m : MachineV r e) : m.state.isData = true := by
  have h := m.on.ht
  simp only [Ty.machineCtx, Ty.isData, Ty.isDatas, Ty.isDatass, Bool.and_eq_true] at h
  exact h.1.1.1.2.1
theorem MachineV.records_data (m : MachineV r e) : r.isData = true := by
  have h := m.on.ht
  simp only [Ty.machineCtx, Ty.isData, Ty.isDatas, Ty.isDatass, Bool.and_eq_true] at h
  exact h.1.1.1.2.2.1
theorem MachineV.table_data (m : MachineV r e) : m.table.isData = true := by
  simp [MachineV.table, instEntry, Ty.option, Ty.isData, Ty.isDatas, Ty.isDatass, m.key_data, m.state_data]

theorem ServiceV.records_data (v : ServiceV) : v.records.isData = true := by
  have h := v.apply.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.2
theorem ServiceV.event_data (v : ServiceV) : v.event.isData = true := by
  have h := v.apply.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.1.2.1
theorem CommandV.input_data {r e c : Ty} (x : CommandV r e c) : x.input.isData = true := by
  have h := x.accepts.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.1.1
theorem QueryV.input_data {r c : Ty} (q : QueryV r c) : q.input.isData = true := by
  have h := q.accepts.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.1.1
theorem SubscriptionV.event_data {e : Ty} (x : SubscriptionV e) : x.event.isData = true := by
  have h := x.wrap.ht
  simp only [Ty.isData, Ty.isDatas, Bool.and_eq_true] at h
  exact h.1.1

/-- A timer as an entry holds it. -/
def timerOf {st : Ty} : (Ty.option (.tuple [.int, st])).den0 → Option (Int × st.den0)
  | .inl ((d, s, ()), ()) => some (d, s)
  | .inr _ => none

def timerVal {st : Ty} : Option (Int × st.den0) → (Ty.option (.tuple [.int, st])).den0
  | some (d, s) => .inl ((d, s, ()), ())
  | none => .inr (.inl ())

theorem timerOf_val {st : Ty} : (t : Option (Int × st.den0)) → timerOf (timerVal t) = t
  | some _ => rfl
  | none => rfl

/-- The instance an entry codes. -/
def instOf (m : MachineV r e) (k : m.key.den0) (x : (instEntry m.state).den0) : Step.Instance m :=
  ⟨k, x.1, timerOf x.2.1⟩

/-- The instances' entries, in their order. -/
def instEntries (m : MachineV r e) (insts : List (Step.Instance m)) : List (m.key.den0 × (instEntry m.state).den0) :=
  insts.map fun i => (i.key, (i.state, timerVal i.timer, ()))

/-- The table of instances with no key twice. -/
def MachineV.tableOf (m : MachineV r e) (insts : List (Step.Instance m))
    (h : KeysUnique (Ty.semWith Dsl.base m.key).2 (instEntries m insts)) : m.table.den0 :=
  ⟨instEntries m insts, h⟩

variable (T : List TypeDecl)

/-- Whether `a`'s key comes no later than `b`'s in the canonical order. -/
def keyLE (m : MachineV r e) (a b : Step.Instance m) : Bool := (Ty.cmp T m.key a.key b.key).isLE

/-- The instances a table holds, in the canonical order of their keys. -/
def instancesOf (m : MachineV r e) (tbl : m.table.den0) : List (Step.Instance m) :=
  (tbl.1.map fun (k, x) => instOf m k x).mergeSort (keyLE T m)

/-- The form the step keeps instances in: in key order, with no key twice. -/
def InstancesOk (m : MachineV r e) (insts : List (Step.Instance m)) : Prop :=
  insts.Pairwise (fun a b => keyLE T m a b = true) ∧ KeysUnique (Ty.semWith Dsl.base m.key).2 (instEntries m insts)

theorem instOf_entries (m : MachineV r e) (insts : List (Step.Instance m)) :
    (instEntries m insts).map (fun (k, x) => instOf m k x) = insts := by
  induction insts with
  | nil => rfl
  | cons i is ih =>
    simp only [instEntries, List.map_cons] at ih ⊢
    rw [ih]; simp only [instOf, timerOf_val]

/-- Instances in the step's form are the instances of the table of their entries. -/
theorem instancesOf_entries (m : MachineV r e) (insts : List (Step.Instance m)) (h : InstancesOk T m insts) :
    instancesOf T m (m.tableOf insts h.2) = insts := by
  simp only [instancesOf, MachineV.tableOf]
  rw [instOf_entries]
  exact List.mergeSort_of_pairwise h.1

end

end Tazuna.Ir
