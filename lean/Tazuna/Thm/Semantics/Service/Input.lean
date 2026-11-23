import Tazuna.Semantics.Service.Input
import Tazuna.Thm.Semantics.Service.Queue
import Tazuna.Thm.Ir.Structure
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Service.Input

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.Chart.Always Tazuna.Thm.Semantics.Service.Chart.Deadline Tazuna.Thm.Semantics.Service.Chart.Done Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Macrostep Tazuna.Thm.Semantics.Service.Chart.Map Tazuna.Thm.Semantics.Service.Chart.Microstep Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.Chart.Request Tazuna.Thm.Semantics.Service.Functions Tazuna.Thm.Semantics.Service.Screen.Subscription Tazuna.Thm.Semantics.Service.Automation Tazuna.Thm.Semantics.Service.Command Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.Service.Query Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic Tazuna.Thm.Semantics.Service.Clock Tazuna.Thm.Semantics.Service.Queue

open Tazuna.Thm.Ir.Structure (resultOfMismatch_eq_none_iff resultOfMismatch_unaccepted)

variable {st : Service} {fs : Functions Id} {s : Service.State}

@[guarantee] theorem send_keysDistinct (name : Ir.Ref) (id : Option LineId) (raw : Value) (caller : Caller) (h : KeysDistinct s.records) :
    KeysDistinct (send st fs s name id raw caller).records := by
  unfold send
  split
  · simp only [id_bind]
    split
    · exact message_keysDistinct _ (by rw [answer_records]; exact h)
    · exact message_keysDistinct _ (processCommand_keysDistinct _ _ _ _ _ h)
  · exact h
@[guarantee] theorem resent_command_gets_first_answer (name : Ir.Ref) (id : LineId) (raw : Value) (caller : Caller)
    (known : Request × Answer) (hs : name.service = st.service) (hc : name.name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1.same { name := name.name, input := raw, caller }) :
    send st fs s name (some id) raw caller =
      let s' := (sent s name id raw caller).1
      message st fs (s'.answer (some id) name known.2) {} := by
  simp [send, hs, hc, hk, answerAgain, hr, sent]

@[guarantee] theorem reused_id_rejected (name : Ir.Ref) (id : LineId) (raw : Value) (caller : Caller)
    (known : Request × Answer) (hs : name.service = st.service) (hc : name.name ∈ st.commands)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1.same { name := name.name, input := raw, caller } = false) :
    send st fs s name (some id) raw caller =
      let s' := (sent s name id raw caller).1
      message st fs (s'.answer (some id) name (.rejected { kind := .reusedId })) {} := by
  simp [send, hs, hc, hk, answerAgain, hr, sent]

@[guarantee] theorem redelivered_event_not_processed (name : Ir.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId)
    (hd : id ∈ s.deliveries) :
    receive st fs s name id raw resultOf =
      message st fs (s.write .in (some id) (.event name raw resultOf)).1.newMessage {} := by
  simp [receive, redeliver, hd]

/-- A command is one message: the service processes it, and the work that it causes, in one `message`. -/
@[guarantee] theorem command_one_message (target : Ir.Ref) (id : Option LineId) (raw : Value) (caller : Caller)
    (hs : target.service = st.service) (hc : target.name ∈ st.commands) :
    ∃ s' q, send st fs s target id raw caller = message st fs s' q := by
  simp only [send, hs, hc, and_self, ite_true, id_bind]
  split <;> exact ⟨_, _, rfl⟩

/-- A query has no identity: the service resolves and answers every query, one with the id of an earlier query too. -/
@[guarantee] theorem query_answered_again (target : Ir.Ref) (givenId : Option LineId) (raw : Value) (caller : Caller) (a : Answer)
    (vs : List Fault) (hs : target.service = st.service) (hq : target.name ∈ st.queries)
    (hr : resolveChecked st fs (s.write .in givenId (.query target raw caller)).1.newMessage target.name raw caller =
      .answered a vs) :
    call st fs s target givenId raw caller =
      message st fs (((s.write .in givenId (.query target raw caller)).1.newMessage.reportAll vs).answer
        (some (s.write .in givenId (.query target raw caller)).2) target a) {} := by
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

end Tazuna.Thm.Semantics.Service.Input
