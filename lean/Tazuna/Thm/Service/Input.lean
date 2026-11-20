import Tazuna.Service.Input
import Tazuna.Thm.Service.Queue
import Tazuna.Thm.Spec.Structure
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Service.Input

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock Tazuna.Thm.Service.Queue

open Tazuna.Thm.Spec.Structure (resultOfMismatch_eq_none_iff resultOfMismatch_unaccepted)

variable {st : Service} {fs : Functions Id} {s : State}

@[guarantee] theorem send_keysDistinct (name : Spec.Ref) (id : Option LineId) (raw : Value) (h : KeysDistinct s.records) :
    KeysDistinct (send st fs s name id raw).records := by
  unfold send
  split
  · simp only [id_bind]
    split
    · exact message_keysDistinct _ (by rw [answer_records]; exact h)
    · exact message_keysDistinct _ (processCommand_keysDistinct _ _ _ _ h)
  · exact h
@[guarantee] theorem resent_command_gets_first_answer (name : Spec.Ref) (id : LineId) (raw : Value)
    (known : Request × Answer) (hs : name.service = st.service) (hc : name.name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1.same { name := name.name, input := raw }) :
    send st fs s name (some id) raw =
      let s' := (sent s name id raw).1
      message st fs (s'.answer (some id) name known.2) {} := by
  simp [send, hs, hc, hk, answerAgain, hr, sent]

@[guarantee] theorem reused_id_rejected (name : Spec.Ref) (id : LineId) (raw : Value)
    (known : Request × Answer) (hs : name.service = st.service) (hc : name.name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1.same { name := name.name, input := raw } = false) :
    send st fs s name (some id) raw =
      let s' := (sent s name id raw).1
      message st fs (s'.answer (some id) name (.rejected { kind := .reusedId })) {} := by
  simp [send, hs, hc, hk, answerAgain, hr, sent]

@[guarantee] theorem redelivered_event_not_processed (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId)
    (hd : id ∈ s.deliveries) :
    receive st fs s name id raw resultOf =
      message st fs (s.write .in (some id) (.event name raw resultOf)).1.newMessage {} := by
  simp [receive, redeliver, hd]

/-- A command is one message: the service processes it, and the work that it causes, in one `message`. -/
@[guarantee] theorem command_one_message (target : Spec.Ref) (id : Option LineId) (raw : Value)
    (hs : target.service = st.service) (hc : target.name ∈ st.commands) :
    ∃ s' q, send st fs s target id raw = message st fs s' q := by
  simp only [send, hs, hc, and_self, ite_true, id_bind]
  split <;> exact ⟨_, _, rfl⟩

/-- A query has no identity: the service resolves and answers every query, one with the id of an earlier query too. -/
@[guarantee] theorem query_answered_again (target : Spec.Ref) (givenId : Option LineId) (raw : Value) (a : Answer)
    (vs : List Fault) (hs : target.service = st.service) (hq : target.name ∈ st.queries)
    (hr : resolveChecked st fs (s.write .in givenId (.query target raw)).1.newMessage target.name raw =
      .answered a vs) :
    call st fs s target givenId raw =
      message st fs (((s.write .in givenId (.query target raw)).1.newMessage.reportAll vs).answer
        (some (s.write .in givenId (.query target raw)).2) target a) {} := by
  simp [call, hs, hq, hr]

/--
A spec service's `invalid-input` answer to another spec service is the sender's Fault, since the sender wrote the input
as it is and only the receiver parsed it.
-/
@[guarantee] theorem invalid_input_answer_blames_sender (p : Pending) (reason : Option String)
    (hp : st.«structure».isAssumed p.activity.ref = false) :
    checkAnswer st fs p (.rejected { kind := .invalidInput, reason }) =
      .ok (.error (.fault (.inputSchema (st.ref p.requester.sender) p.activity.ref))) := by
  simp [checkAnswer, hp, rejectedInput?]

end Tazuna.Thm.Service.Input
