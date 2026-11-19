import Tazuna.Service.Input
import Tazuna.Thm.Service.Queue
import Tazuna.Thm.Spec.Structure

namespace Tazuna.Thm.Service.Input

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock Tazuna.Thm.Service.Queue

open Tazuna.Thm.Spec.Structure (resultOfMismatch_eq_none_iff resultOfMismatch_unaccepted)

variable {st : Service} {fs : Functions Id} {s : State}

theorem send_keysDistinct (name : Spec.Ref) (id : Option LineId) (raw : Value) (h : KeysDistinct s.records) :
    KeysDistinct (send st fs s name id raw).records := by
  unfold send
  split
  · simp only [id_bind]
    split
    · exact message_keysDistinct _ (by rw [answer_records]; exact h)
    · exact message_keysDistinct _ (processCommand_keysDistinct _ _ _ _ h)
  · exact h
theorem resent_command_gets_first_answer (name : Spec.Ref) (id : LineId) (raw : Value)
    (known : Request × Answer) (hs : name.service = st.service) (hc : name.name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1.same { name := name.name, input := raw }) :
    send st fs s name (some id) raw =
      let s' := (sent s name id raw).1
      message st fs (s'.answer (some id) name known.2) {} := by
  simp [send, hs, hc, hk, answerAgain, hr, sent]

theorem reused_id_rejected (name : Spec.Ref) (id : LineId) (raw : Value)
    (known : Request × Answer) (hs : name.service = st.service) (hc : name.name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1.same { name := name.name, input := raw } = false) :
    send st fs s name (some id) raw =
      let s' := (sent s name id raw).1
      message st fs (s'.answer (some id) name (.rejected { kind := .reusedId })) {} := by
  simp [send, hs, hc, hk, answerAgain, hr, sent]

theorem redelivered_event_not_processed (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId)
    (hd : id ∈ s.deliveries) :
    receive st fs s name id raw resultOf =
      message st fs (s.write .in (some id) (.event name raw resultOf)).1.newMessage {} := by
  simp [receive, redeliver, hd]
end Tazuna.Thm.Service.Input
