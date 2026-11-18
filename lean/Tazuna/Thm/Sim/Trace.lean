import Tazuna.Sim.Trace
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Sim.Trace

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Data.Basic

variable {s : State}

/-- Only lines on one channel are ordered: lines on different channels, or on none, keep no order. -/
theorem ordered_same_channel (lineSteps : Array (Option (Nat × Nat))) (a b : Nat) (la lb : Line)
    (ha : s.lines[a]? = some la) (hb : s.lines[b]? = some lb) (h : ordered s lineSteps a b = true) :
    (channelOf la).isSome ∧ channelOf la = channelOf lb := by
  unfold ordered at h
  rw [ha, hb] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- Two lines of one group of a decide's emits are unordered. -/
theorem group_lines_unordered (lineSteps : Array (Option (Nat × Nat))) (a b sa sb g : Nat)
    (hla : lineSteps[a]? = some (some (sa, g))) (hlb : lineSteps[b]? = some (some (sb, g))) :
    ordered s lineSteps a b = false := by
  unfold ordered
  split
  · rw [hla, hlb]; simp
  · rfl

end Tazuna.Thm.Sim.Trace
