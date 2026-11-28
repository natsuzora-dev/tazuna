import Tazuna.Semantics.StepRen

/-! The step does not read the order a bag or table is stored in, nor where time starts: `step_ren` with the renaming
that keeps every name and moves every instant by `d` (`Ren.shifted d`), which keeps the counters' order. Two states
are the same up to that order and the shift when they relate under it with the same counter and next wire id
(`StateShift`); stepping such states on such inputs gives such results (`step_shift`), and with no shift that is
`step_same`, which verify's replay rests on. -/

namespace Tazuna.Ir

/-- The renaming that keeps every counter and moves every instant by `d` milliseconds, or keeps them when `d` is
none. -/
def PBij.shifted (d : Option Int) : PBij := { PBij.refl with shift := d }

theorem PBij.shifted_rel {d : Option Int} {a b : Nat} (h : (PBij.shifted d).rel a b) : a = b := h

/-- The renaming that keeps every counter and every wire id and moves every instant by `d`. -/
def Ren.shifted (d : Option Int) : Ren := ⟨PBij.shifted d, PBij.refl⟩

/-- The renaming that keeps every counter, every wire id and every instant. -/
abbrev Ren.refl : Ren := Ren.shifted none

/-- Values the same up to the order their bags and tables are stored in. -/
abbrev Ty.Same (t : Ty) : t.den0 → t.den0 → Prop := Ty.rel0 PBij.refl t

theorem Ty.same_of_deq {t : Ty} (hc : t.comparable = true) {x y : t.den0} (h : t.deq0 x y = true) : Ty.Same t x y :=
  Ty.rel0_deq_right hc (Ty.rel0_refl t hc x) h

namespace Step

section Machine
variable {r e : Ty}

/-- Instances the same up to order and a time shift, item by item. -/
abbrev Insts.Shift (d : Option Int) {m : MachineV r e} : List (Instance m) → List (Instance m) → Prop :=
  Insts.Ren (PBij.shifted d)

abbrev Machines.Shift (d : Option Int) {ms : List (MachineV r e)} : Machines ms → Machines ms → Prop :=
  Machines.Ren (PBij.shifted d)

/-- Instances the same up to order, item by item. -/
abbrev Machines.Same {ms : List (MachineV r e)} : Machines ms → Machines ms → Prop := Machines.Shift none

end Machine

variable {v : ServiceV} {d : Option Int} {T : List TypeDecl}

/-- States the same up to the order their bags and tables are stored in and the time shift `d`. -/
def StateShift (d : Option Int) (s s' : State v) : Prop :=
  Ty.rel0 (PBij.shifted d) v.records s.records s'.records ∧ Machines.Shift d s.machines s'.machines ∧
    Forall2 (Pending.Rel (Ren.shifted d)) s.pending s'.pending ∧ (PBij.shifted d).point .ms s.now s'.now ∧
    s.fresh = s'.fresh ∧ s.nextId = s'.nextId

/-- States the same up to the order their bags and tables are stored in. -/
abbrev StateSame (s s' : State v) : Prop := StateShift none s s'

/-- Outcomes the same up to order and a time shift: a fault on both sides, or the same outcome with related values. -/
abbrev Outcome.Shift (d : Option Int) : Outcome → Outcome → Prop := Outcome.Ren (Ren.shifted d)

/-- Outcomes the same up to order. -/
abbrev Outcome.Same : Outcome → Outcome → Prop := Outcome.Shift none

/-- Results the same up to order and a time shift. -/
def ResultShift (d : Option Int) (r r' : Result v) : Prop :=
  StateShift d r.state r'.state ∧ Outcome.Shift d r.outcome r'.outcome ∧
    Forall2 (Ty.rel0 (PBij.shifted d) v.event) r.events r'.events ∧ Forall2 (OutLine.Rel (Ren.shifted d)) r.out r'.out

/-- Results the same up to order. -/
abbrev ResultSame (r r' : Result v) : Prop := ResultShift none r r'

/-- Inputs the same up to the order of their values' bags and tables and the time shift `d`. -/
inductive Input.Shift (d : Option Int) : Input v → Input v → Prop
  | command (i : Fin v.commands.length) {c c' : v.caller.den0} {x x' : (v.commands.get i).input.den0} :
      Ty.rel0 (PBij.shifted d) v.caller c c' → Ty.rel0 (PBij.shifted d) _ x x' →
      Input.Shift d (.command i c x) (.command i c' x')
  | query (i : Fin v.queries.length) {c c' : v.caller.den0} {x x' : (v.queries.get i).input.den0} :
      Ty.rel0 (PBij.shifted d) v.caller c c' → Ty.rel0 (PBij.shifted d) _ x x' →
      Input.Shift d (.query i c x) (.query i c' x')
  | answer (to : Nat) {w w' : WireVal} : WireVal.Rel (PBij.shifted d) w w' →
      Input.Shift d (.answer to w) (.answer to w')
  | event (i : Fin v.subscribes.length) {x x' : (v.subscribes.get i).event.den0} :
      Ty.rel0 (PBij.shifted d) _ x x' → Input.Shift d (.event i x) (.event i x')
  | clock {t t' : Int} : (PBij.shifted d).point .ms t t' → Input.Shift d (.clock t) (.clock t')

/-- Inputs the same up to the order of their values' bags and tables. -/
abbrev Input.Same : Input v → Input v → Prop := Input.Shift none

theorem StateShift.ren {s s' : State v} (h : StateShift d s s') : StateRen (Ren.shifted d) s s' := by
  obtain ⟨hrec, hmach, hpend, hnow, hf, hn⟩ := h
  exact ⟨hrec, hmach, hpend, hnow, fun k => show _ = _ by rw [hf], fun k => show _ = _ by rw [hn]⟩

theorem StateRen.shift {s s' : State v} (h : StateRen (Ren.shifted d) s s') : StateShift d s s' := by
  obtain ⟨hrec, hmach, hpend, hnow, hf, hn⟩ := h
  exact ⟨hrec, hmach, hpend, hnow, hf 0, hn 0⟩

theorem Input.Shift.ren {x x' : Input v} : Input.Shift d x x' → Input.Ren (Ren.shifted d) x x'
  | .command i hc hx => .command i hc hx
  | .query i hc hx => .query i hc hx
  | .answer _ hw => .answer rfl hw
  | .event i hx => .event i hx
  | .clock ht => .clock ht

/-- The step reads no bag's or table's order and no origin of time: from states the same up to that order and the
time shift `d`, on inputs the same up to them, it steps to results the same up to them, item by item. -/
theorem step_shift (ho : Ordered T v) {s s' : State v} (hs : StateShift d s s') {x x' : Input v}
    (hx : Input.Shift d x x') : ResultShift d (step T v s x) (step T v s' x') := by
  obtain ⟨hst, hout, hev, hol⟩ := step_ren ho (PBij.mono_of_eq PBij.shifted_rel) hs.ren hx.ren
  exact ⟨hst.shift, hout, hev, hol⟩

/-- The step reads no bag's or table's order: from states the same up to that order, on inputs the same up to it, it
steps to results the same up to it, item by item. -/
theorem step_same (ho : Ordered T v) {s s' : State v} (hs : StateSame s s') {x x' : Input v} (hx : Input.Same x x') :
    ResultSame (step T v s x) (step T v s' x') :=
  step_shift ho hs hx

end Step

end Tazuna.Ir
