import Tazuna.Semantics.Sim.Order
import Tazuna.Thm.Semantics.Value.Basic
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Sim.Order

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Sim
open Tazuna.Thm.Semantics.Value.Basic

variable {s : Service.State}

/-- Only lines on one channel are ordered: lines on different channels, or on none, keep no order. -/
@[guarantee] theorem ordered_same_channel (a b : Nat) (la lb : Line) (ha : s.lines[a]? = some la) (hb : s.lines[b]? = some lb)
    (h : ordered s a b = true) : (channelOf la).isSome ∧ channelOf la = channelOf lb := by
  unfold ordered at h
  rw [ha, hb] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- Two lines of one group of a decide's emits, written at one time, are unordered. -/
@[guarantee] theorem group_lines_unordered (a b : Nat) (t : Time) (ia ib : LineId) (ea eb : Ir.Ref) (pa pb : Value)
    (ra rb : Option LineId) (w : EmittedBy) (ha : s.lines[a]? = some ⟨t, .out, ia, .event ea pa ra, w, (), ()⟩)
    (hb : s.lines[b]? = some ⟨t, .out, ib, .event eb pb rb, w, (), ()⟩) : ordered s a b = false := by
  unfold ordered
  simp [ha, hb]

/--
Two event lines at one time whose steps differ and that no cause chain links are unordered, even on one channel:
independent senders impose no order.
-/
@[guarantee] theorem independent_unordered (a b : Nat) (t : Time) (ia ib : LineId) (ea eb : Ir.Ref) (pa pb : Value)
    (ra rb : Option LineId) (wa wb : EmittedBy) (ha : s.lines[a]? = some ⟨t, .out, ia, .event ea pa ra, wa, (), ()⟩)
    (hb : s.lines[b]? = some ⟨t, .out, ib, .event eb pb rb, wb, (), ()⟩) (hstep : wa.step ≠ wb.step)
    (hcause : causedBy s wa.step wb.step = false) : ordered s a b = false := by
  unfold ordered
  simp [ha, hb, hstep, hcause]

end Tazuna.Thm.Semantics.Sim.Order
