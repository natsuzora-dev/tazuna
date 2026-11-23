import Tazuna.Semantics.Service.Queue
import Tazuna.Thm.Semantics.Service.Screen.Subscription
import Tazuna.Thm.Semantics.Service.Query
import Tazuna.Thm.Semantics.Service.Clock
import Tazuna.Thm.Guarantee
import Tazuna.Thm.Semantics.Service.Response

namespace Tazuna.Thm.Semantics.Service.Queue

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.Chart.Always Tazuna.Thm.Semantics.Service.Chart.Deadline Tazuna.Thm.Semantics.Service.Chart.Done Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Macrostep Tazuna.Thm.Semantics.Service.Chart.Map Tazuna.Thm.Semantics.Service.Chart.Microstep Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.Chart.Request Tazuna.Thm.Semantics.Service.Functions Tazuna.Thm.Semantics.Service.Screen.Subscription Tazuna.Thm.Semantics.Service.Automation Tazuna.Thm.Semantics.Service.Command Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.Service.Query Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic Tazuna.Thm.Semantics.Service.Clock Tazuna.Thm.Semantics.Service.Response

variable {st : Service} {fs : Functions Id} {s : Service.State}

@[simp] theorem endMessage_id : endMessage st fs s = observeResponses st fs (afterMessage st fs s) := rfl

theorem afterMessage_fixed : (afterMessage st fs s).fixed = s.fixed := by
  simp only [afterMessage]
  split
  · rfl
  · exact publish_fixed

theorem afterMessage_grows : Grows s (afterMessage st fs s) := by
  simp only [afterMessage]
  split
  · exact Grows.refl _
  · exact publish_grows

theorem afterMessage_records : (afterMessage st fs s).records = s.records := congrArg Fixed.records afterMessage_fixed

theorem afterMessage_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (afterMessage st fs s).records := by
  rw [afterMessage_records]
  exact h

theorem fireDue_keysDistinct (to : Time) (fuel : Nat) (h : KeysDistinct s.records) :
    KeysDistinct (fireDue st fs to fuel s).records := by
  induction fuel generalizing s with
  | zero => simp only [fireDue]; split <;> exact h
  | succ fuel ih =>
    rw [fireDue]
    split
    · exact h
    · split
      · exact h
      · dsimp only
        try simp only [id_bind, endMessage_id]
        refine ih ?_
        rw [observeResponses_records]
        exact afterMessage_keysDistinct (drain_keysDistinct _ _ (by
          rw [(keeps_settled _ _ (keeps_fire _ _)).records]; simpa using h))

@[guarantee] theorem message_keysDistinct (q : Queue) (h : KeysDistinct s.records) : KeysDistinct (message st fs s q).records := by
  simp only [message, finish, id_bind, endMessage_id]
  exact fireDue_keysDistinct _ _ (by rw [observeResponses_records]; exact afterMessage_keysDistinct (drain_keysDistinct _ _ h))

@[guarantee] theorem deadline_message_at_its_time (to : Time) (fuel : Nat) (t : Service.Deadline)
    (hh : s.halted = none) (he : earliestDeadline s.deadlines to = some t) :
    ∃ s₁ q, fireDue st fs to (fuel + 1) s =
        fireDue st fs to fuel (observeResponses st fs (afterMessage st fs (drain st fs Limit.messageWork.max s₁ q))) ∧
      s₁.now = max s.now t.time := by
  refine ⟨_, _, by simp only [fireDue, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, he,
      endMessage_id, id_bind]; rfl, ?_⟩
  rw [(keeps_settled _ _ (keeps_fire _ t)).now _]
  simp

@[guarantee] theorem message_outputs_at_its_time (n : Nat) (q : Queue) :
    ∃ new, (afterMessage st fs (drain st fs n s q)).lines = s.lines ++ new ∧ ∀ l ∈ new, l.time = s.now :=
  ((drain_grows n q).trans (drain_keeps_now n q) afterMessage_grows).1


/-- A clock advance that still has a deadline due after Limit.dueDeadlines deadlines halts with exceededDueDeadlines. -/
@[guarantee] theorem due_deadlines_limit_halts (to : Time) (hs : s.halted = none)
    (hd : (earliestDeadline s.deadlines to).isSome = true) :
    (fireDue st fs to 0 s).halted = some (.fault (.exceededDueDeadlines Limit.dueDeadlines.max)) := by
  simp only [fireDue, hs, Option.isNone_none, hd, Bool.and_self, ite_true]
  exact report_halted _ rfl

end Tazuna.Thm.Semantics.Service.Queue
