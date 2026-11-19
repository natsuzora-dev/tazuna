import Tazuna.Service.Queue
import Tazuna.Thm.Service.Screen.Subscription
import Tazuna.Thm.Service.Query
import Tazuna.Thm.Service.Clock

namespace Tazuna.Thm.Service.Queue

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock

variable {st : Service} {fs : Functions Id} {s : State}

@[simp] theorem endMessage_id : endMessage st fs s = afterMessage st fs s := rfl

theorem checkInvariants_fixed : (checkInvariants st fs s).fixed = s.fixed := reportAll_fixed _

theorem checkInvariants_lines : (checkInvariants st fs s).lines = s.lines := reportAll_lines _

theorem afterMessage_fixed : (afterMessage st fs s).fixed = s.fixed := by
  simp only [afterMessage, id_bind]
  split
  · exact checkInvariants_fixed
  · exact publish_fixed.trans checkInvariants_fixed

theorem afterMessage_grows : Grows s (afterMessage st fs s) := by
  simp only [afterMessage, id_bind]
  split
  · exact Grows.of_lines checkInvariants_lines
  · exact (Grows.of_lines checkInvariants_lines).trans (congrArg Fixed.now checkInvariants_fixed) publish_grows

theorem afterMessage_records : (afterMessage st fs s).records = s.records := congrArg Fixed.records afterMessage_fixed

theorem afterMessage_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (afterMessage st fs s).records := by
  rw [afterMessage_records]
  exact h

theorem fireDue_keysDistinct (to : Time) (fuel : Nat) (tie : Option Time) (h : KeysDistinct s.records) :
    KeysDistinct (fireDue st fs to fuel tie s).records := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> exact h
  | succ fuel ih =>
    rw [fireDue]
    split
    · exact h
    · split
      · exact h
      · dsimp only
        split
        · simpa using h
        · rename_i hc
          obtain ⟨_, rfl⟩ := chooseDeadline_orders hc
          try simp only [id_bind, endMessage_id]
          exact ih _ (afterMessage_keysDistinct (drain_keysDistinct _ _ (by rw [(keeps_settled _ _ (keeps_fire _ _)).records]; exact h)))

theorem message_keysDistinct (q : Queue) (h : KeysDistinct s.records) : KeysDistinct (message st fs s q).records := by
  simp only [message, finish, id_bind, endMessage_id]
  exact fireDue_keysDistinct _ _ _ (afterMessage_keysDistinct (drain_keysDistinct _ _ h))

theorem deadline_message_at_its_time (to : Time) (fuel : Nat) (tie : Option Time) (e t : Deadline) (s' : State)
    (hh : s.halted = none) (he : earliestDeadline s.deadlines to = some e)
    (hc : chooseDeadline s e (s.deadlines.filter (·.time == e.time))
      (1 < (s.deadlines.filter (·.time == e.time)).length || tie == e.time) = .ok (t, s')) :
    ∃ s₁ q tie', fireDue st fs to (fuel + 1) tie s =
        fireDue st fs to fuel tie' (afterMessage st fs (drain st fs Limit.messageWork.max s₁ q)) ∧
      s₁.now = max s'.now t.time := by
  refine ⟨_, _, _, by simp only [fireDue, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, he, hc, Tazuna.Thm.Service.Note.note_id,
      id_pure, endMessage_id, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, id_bind]; rfl, ?_⟩
  exact (keeps_settled _ _ (keeps_fire _ t)).now _

theorem message_outputs_at_its_time (n : Nat) (q : Queue) :
    ∃ new, (afterMessage st fs (drain st fs n s q)).lines = s.lines ++ new ∧ ∀ l ∈ new, l.time = s.now :=
  (drain_grows n q).trans (drain_keeps_now n q) afterMessage_grows

end Tazuna.Thm.Service.Queue
