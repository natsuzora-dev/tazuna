import Tazuna.Service.Restart
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Note
import Tazuna.Thm.Service.Queue

/-!
Only a clock advance moves a service's current time, the time that every line it writes carries: each other input keeps
it, since the deadlines that the input lets fire are due by then and fire at the current time.
-/

namespace Tazuna.Thm.Service.Now

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Note Tazuna.Thm.Service.State Tazuna.Thm.Service.Chart.Queue
open Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Queue
open Tazuna.Thm.Service.Clock

variable {st : Service} {fs : Functions Id}

theorem earliestDeadline_le {ds : List Deadline} {to : Time} {e : Deadline} (h : earliestDeadline ds to = some e) :
    e.time ≤ to := by
  unfold earliestDeadline at h
  suffices ∀ (init : Option Deadline), (∀ b, init = some b → b.time ≤ to) → ∀ e,
      ds.foldl (fun best t => if t.time > to then best else match best with
        | none => some t
        | some b => if t.time < b.time then some t else some b) init = some e → e.time ≤ to from
    this none (by simp) e h
  clear h
  induction ds with
  | nil => intro init hi e he; exact hi e he
  | cons d ds ih =>
    intro init hi e he
    refine ih _ (fun b hb => ?_) e he
    by_cases hd : d.time > to
    · simp only [hd, ite_true] at hb; exact hi b hb
    · simp only [hd, ite_false] at hb
      have hd : d.time ≤ to := Int.not_lt.mp hd
      split at hb
      · cases hb; exact hd
      · split at hb <;> cases hb
        · exact hd
        · exact hi _ rfl

theorem chooseDeadline_due {s s' : State} {tied : Bool} {first t : Deadline} {due : List Deadline}
    (h : chooseDeadline s first due tied = .ok (t, s')) : t = first ∨ t ∈ due := by
  unfold chooseDeadline at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h)
  all_goals (try obtain ⟨rfl, -⟩ := h)
  all_goals first | exact .inl rfl | (right; exact List.mem_of_find?_eq_some ‹_›)

theorem afterMessage_now (s : State) : (afterMessage st fs s).now = s.now := congrArg Fixed.now afterMessage_fixed

/-- Firing the deadlines due by a time no later than the current time keeps the current time. -/
theorem fireDue_now (to : Time) (fuel : Nat) (tie : Option Time) (s : State) (h : to ≤ s.now) :
    (fireDue st fs to fuel tie s).now = s.now := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> simp
  | succ fuel ih =>
    rw [fireDue]
    split
    · rfl
    · split
      · rfl
      · rename_i e he
        dsimp only
        split
        · simp
        · rename_i t s' hc
          have ht : t.time ≤ s.now := by
            rcases chooseDeadline_due hc with rfl | hm
            · exact Int.le_trans (earliestDeadline_le he) h
            · have := (List.mem_filter.mp hm).2
              simp only [beq_iff_eq] at this
              rw [this]; exact Int.le_trans (earliestDeadline_le he) h
          obtain ⟨_, rfl⟩ := Tazuna.Thm.Service.Clock.chooseDeadline_orders hc
          simp only [id_bind, note_id, endMessage_id]
          rw [ih]
          all_goals rw [Tazuna.Thm.Service.Response.observeResponses_now, afterMessage_now, drain_keeps_now,
            (keeps_settled _ _ (keeps_fire _ _)).now]
          all_goals simp only [newStep_now, newMessage_now, Tazuna.Thm.Service.Response.passTime_now, Int.max_eq_left ht]
          all_goals first | rfl | exact h

/-- A message keeps the current time: its work does, and the deadlines it lets fire are due by then. -/
theorem message_now (s : State) (q : Queue) : (message st fs s q).now = s.now := by
  simp only [message, finish, id_bind, endMessage_id]
  rw [fireDue_now _ _ _ _ (Int.le_refl _), Tazuna.Thm.Service.Response.observeResponses_now, afterMessage_now,
    drain_keeps_now]

theorem processCommand_now (name : String) (raw : Value) (caller : Caller) (id : Option LineId) (n : Nat) (s : State) :
    (processCommand st fs s name raw caller id n).1.now = s.now :=
  congrArg Prod.snd (Tazuna.Thm.Service.Command.processCommand_clock name raw caller id n)

theorem keeps_deliverAnswer (step : Nat) (p : Pending) (answer : Answer) : Keeps (deliverAnswer fs st step p answer) := by
  intro r
  unfold deliverAnswer
  dsimp only
  split
  · exact (keeps_answerTo _ _ _ _ _).trans (by simp [State.answered]; split <;> rfl)
  · show (r.state.answered p).1.fixed = r.state.fixed
    simp [State.answered]; split <;> rfl

/-- Closes `(f s).now = s.now` where `f` changes fields other than the current time, then may run a message. -/
macro "now_leaf" : tactic => `(tactic| ((try rw [message_now]) <;>
  (try rw [(keeps_settled _ _ (keeps_deliverAnswer _ _ _)).now]) <;>
  (try rw [(keeps_settled _ _ (keeps_dispatch _ _ _ _)).now]) <;>
  simp [State.answer, State.write, State.newStep, State.newMessage, processCommand_now, apply_ite State.now] <;> (repeat' split) <;> simp [State.report] <;> (repeat' split) <;> rfl))

theorem send_now (name : Spec.Ref) (id : Option LineId) (raw : Value) (caller : Caller) (s : State) :
    (send st fs s name id raw caller).now = s.now := by
  simp only [send, id_bind]; repeat' split
  all_goals now_leaf

theorem call_now (name : Spec.Ref) (id : Option LineId) (raw : Value) (caller : Caller) (s : State) :
    (call st fs s name id raw caller).now = s.now := by
  simp only [call, id_bind]; repeat' split
  all_goals now_leaf

theorem subscribe_now (name : Spec.Ref) (id : Option LineId) (raw : Value) (caller : Caller) (s : State) :
    (subscribe st fs s name id raw caller).now = s.now := by
  simp only [subscribe]; repeat' split
  all_goals now_leaf

theorem endSubscription_now (id : LineId) (s : State) : (endSubscription st fs s id).now = s.now := by
  simp only [endSubscription]; now_leaf

theorem receive_now (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId) (s : State) :
    (receive st fs s name id raw resultOf).now = s.now := by
  simp only [receive, redeliver, deliver, id_bind]; repeat' split
  all_goals now_leaf

theorem answerRequest_now (id : Option LineId) (p : Pending) (answer : Answer) (s : State) :
    (answerRequest st fs s id p answer).now = s.now := by
  simp only [answerRequest, id_bind]; repeat' split
  all_goals now_leaf

theorem begin_now (s : State) : (begin st fs s).now = s.now := by
  simp only [begin, id_bind]
  split
  · rfl
  · rw [message_now]
    have hr : ∀ t : State, (startRecords st fs t).now = t.now := fun t => by
      simp only [startRecords]; rw [foldlM_id]
      exact foldl_keeps (fun x : State => x.now = t.now) _ (fun x e hx => by split <;> simp [hx]) _ _ rfl
    have hi : ∀ t : State, (startInstances st fs t).now = t.now := fun t => by
      simp only [startInstances]; rw [foldlM_id]
      exact foldl_keeps (fun x : State => x.now = t.now) _ (fun x c hx => by
        simp only [startInstance, id_bind]; (repeat' split) <;> simp [hx]) _ _ rfl
    rw [hi, hr]; rfl

theorem operate_now (screen : InstanceId) (control : String) (payload : Value) (s : State) :
    (operate st fs s screen control payload).now = s.now := by
  simp only [operate, id_bind]; repeat' split
  all_goals now_leaf

theorem restart_now (s : State) : (restart st fs s).now = s.now := by
  simp only [restart, begin_now]; simp [State.stop]

end Tazuna.Thm.Service.Now
