import Tazuna.Service.Input
import Tazuna.Thm.Service.Queue
import Tazuna.Thm.Spec.Structure

namespace Tazuna.Thm.Service.Input

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock Tazuna.Thm.Service.Queue

open Tazuna.Thm.Spec.Structure (resultOfMismatch_eq_none_iff resultOfMismatch_unaccepted)

variable {st : Service} {fs : Functions Id} {s : State}

theorem send_keysDistinct (name : String) (id : Option String) (raw : Value) (h : KeysDistinct s.records) :
    KeysDistinct (send st fs s name id raw).records := by
  unfold send
  split
  · simp only [id_bind]
    split
    · exact message_keysDistinct _ (by rw [answer_records]; exact h)
    · exact message_keysDistinct _ (processCommand_keysDistinct _ _ _ _ h)
  · exact h

/--
A spec service's invalid-input answer to another spec service's request is the sender's fault: only the receiver parses
a message, so the sender wrote an input that the receiver's schema does not take.
-/
theorem invalid_input_answer_faults_sender (p : Pending) (reason : Option String)
    (ha : st.«structure».isAssumed p.activity.ref = false) :
    checkAnswer st fs p (.rejected { kind := .invalidInput, reason }) =
      .ok { decoded := .error (.fault (p.requester.inputFault st p.activity.ref)) } := by
  simp [checkAnswer, specAnswer, Requester.rejectedInput?, ha]

theorem resent_command_gets_first_answer (name id : String) (raw : Value)
    (known : Request × Answer) (hc : name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 = { name, input := raw }) :
    send st fs s name (some id) raw =
      let s' := (sent s name id raw).1
      message st fs (s'.answer (some id) known.2) {} := by
  simp [send, hc, hk, answerAgain, hr, sent]

theorem reused_id_rejected (name id : String) (raw : Value)
    (known : Request × Answer) (hc : name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 ≠ { name, input := raw }) :
    send st fs s name (some id) raw =
      let s' := (sent s name id raw).1
      message st fs (s'.answer (some id) (.rejected { kind := .reusedId })) {} := by
  simp [send, hc, hk, answerAgain, hr, sent]

theorem redelivered_event_not_processed (name id : String) (raw : Value) (hh : s.halted = none)
    (hd : id ∈ s.deliveries) :
    receive st fs s name (some id) raw none = message st fs (delivered s name id raw).newMessage {} := by
  simp [receive, redeliver, withResultOf, hh, hd, delivered, State.lineId]

theorem send_is_one_message (name : String) (id : Option String) (raw : Value) (hc : name ∈ st.commands) :
    ∃ s' q, send st fs s name id raw = message st fs s' q := by
  simp only [send, hc, ↓reduceIte, id_bind]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

end Tazuna.Thm.Service.Input
