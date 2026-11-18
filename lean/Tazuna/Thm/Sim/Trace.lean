import Tazuna.Sim.Trace
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Sim.Trace

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Data.Basic

variable {s : State}

/-- Only lines on one channel are ordered: lines on different channels, or on none, keep no order. -/
theorem ordered_same_channel (a b : Nat) (la lb : Line) (ha : s.lines[a]? = some la) (hb : s.lines[b]? = some lb)
    (h : ordered s a b = true) : (channelOf la).isSome ∧ channelOf la = channelOf lb := by
  unfold ordered at h
  rw [ha, hb] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- Two lines of one group of a decide's emits are unordered. -/
theorem group_lines_unordered (a b : Nat) (la lb : Line) (w : EmittedBy) (ha : s.lines[a]? = some la)
    (hb : s.lines[b]? = some lb) (hwa : la.emitted = some w) (hwb : lb.emitted = some w) : ordered s a b = false := by
  unfold ordered
  simp [ha, hb, hwa, hwb]

/--
Two event lines whose steps differ and that no cause chain links are unordered, even on one channel: independent
senders impose no order.
-/
theorem independent_unordered (a b : Nat) (la lb : Line) (wa wb : EmittedBy) (ha : s.lines[a]? = some la)
    (hb : s.lines[b]? = some lb) (hwa : la.emitted = some wa) (hwb : lb.emitted = some wb) (hstep : wa.step ≠ wb.step)
    (hcause : causedBy s wa.step wb.step = false) : ordered s a b = false := by
  unfold ordered
  simp [ha, hb, hwa, hwb, hstep, hcause]

end Tazuna.Thm.Sim.Trace
