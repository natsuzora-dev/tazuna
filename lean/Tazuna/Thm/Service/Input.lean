import Tazuna.Service.Input
import Tazuna.Thm.Service.Queue
import Tazuna.Thm.Syntax.Structure

namespace Tazuna.Thm.Service.Input

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock Tazuna.Thm.Service.Queue

open Tazuna.Thm.Syntax.Structure (resultOfMismatch_eq_none_iff resultOfMismatch_unaccepted)

variable {st : Service} {fs : Functions Id} {s : State}

theorem addResult_records (id : String) (e : Emit) : (addResult st fs s id e).records = s.records := by
  unfold addResult
  simp only [id_bind]
  split
  · rfl
  · split <;> simp

theorem resultRequest_records (name k : String) : (resultRequest st s name k).1.records = s.records := by
  unfold resultRequest
  repeat' split
  all_goals first | rfl | simp

theorem startRecords_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (startRecords st fs s).records := by
  unfold startRecords
  rw [foldlM_id]
  refine foldl_keeps (fun t : State => KeysDistinct t.records) _ (fun t e ht => ?_) _ _ h
  simp only [id_bind]
  split
  · exact ht
  · rename_i hc
    show KeysDistinct (t.records ++ [_])
    unfold KeysDistinct at ht ⊢
    rw [List.map_append, List.nodup_append]
    refine ⟨ht, by simp, fun a ha b hb he => ?_⟩
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    subst he
    obtain ⟨r, hr, hre⟩ := List.mem_map.mp ha
    exact hc (List.any_eq_true.mpr ⟨r, hr, by simp [(Prod.mk.inj hre).1]⟩)

theorem begin_keysDistinct (h : KeysDistinct s.records) : KeysDistinct (begin st fs s).records := by
  unfold begin
  split
  · exact h
  · simp only [id_bind]
    apply message_keysDistinct
    unfold startInstances
    rw [foldlM_id]
    rw [foldl_records]
    · exact startRecords_keysDistinct h
    · intro t c
      unfold startInstance
      split
      · rfl
      · simp only [id_bind]
        split <;> simp

@[simp] theorem checkDeadlineOrder_records : s.checkDeadlineOrder.records = s.records := by
  unfold State.checkDeadlineOrder; split <;> simp

@[simp] theorem checkDeadlineOrder_started : s.checkDeadlineOrder.started = s.started := by
  unfold State.checkDeadlineOrder; split <;> simp

@[simp] theorem checkDeadlineOrder_lines : s.checkDeadlineOrder.lines = s.lines := by
  unfold State.checkDeadlineOrder; split <;> simp

@[simp] theorem checkDeadlineOrder_commandAnswers : s.checkDeadlineOrder.commandAnswers = s.commandAnswers := by
  unfold State.checkDeadlineOrder; split <;> simp

theorem send_keysDistinct (name : String) (id : Option String) (raw : Value) (h : KeysDistinct s.records) :
    KeysDistinct (send st fs s name id raw).records := by
  unfold send
  split
  · simp only [id_bind]
    split
    · simpa using h
    · split
      · exact message_keysDistinct _ (by rw [answer_records]; exact h)
      · exact message_keysDistinct _ (processCommand_keysDistinct _ _ _ _ h)
  · exact h

theorem call_keysDistinct (name : String) (id : Option String) (raw : Value) (h : KeysDistinct s.records) :
    KeysDistinct (call st fs s name id raw).records := by
  unfold call
  split
  · simp only [id_bind]
    split
    · simpa using h
    · generalize resolveChecked st fs _ name raw = x
      rcases x with ⟨a, vs⟩ | f
      · exact message_keysDistinct _ (by rw [answer_records, reportAll_records]; exact h)
      · simpa using h
  · exact h

theorem subscribe_keysDistinct (name : String) (id : Option String) (raw : Value)
    (h : KeysDistinct s.records) : KeysDistinct (subscribe st fs s name id raw).records := by
  unfold subscribe
  split
  · simp only [id_bind]
    split
    · simpa using h
    · apply message_keysDistinct
      split
      · simpa using h
      · exact h
  · exact h

theorem endSubscription_keysDistinct (id : String) (h : KeysDistinct s.records) :
    KeysDistinct (endSubscription st fs s id).records := by
  unfold endSubscription
  apply message_keysDistinct
  split <;> exact h

theorem deliver_keysDistinct (name : String) (id : Option String) (payload : Value) (request : Option Pending)
    (h : KeysDistinct s.records) : KeysDistinct (deliver st fs s name id payload request).records := by
  unfold deliver
  simp only [id_bind]
  split
  · apply message_keysDistinct
    show KeysDistinct (State.newStep (State.newMessage (addResult st fs _ _ _)) none).1.records
    rw [show ∀ t : State, t.newMessage.newStep none |>.1.records = t.records from fun _ => rfl, addResult_records]
    exact h
  · exact message_keysDistinct _ h

theorem withResultOf_records (name : String) (k : Option String) :
    (withResultOf st s name k).1.records = s.records := by
  cases k
  · rfl
  · exact resultRequest_records _ _

theorem redeliver_records_before_message (name : String) (id : Option String) (raw : Value) (resultOf : Option String) :
    ∃ s', s'.records = s.records ∧
      (redeliver st fs s name id raw resultOf = message st fs s' {} ∨ redeliver st fs s name id raw resultOf = s') := by
  unfold redeliver
  simp only [id_bind]
  split
  · exact ⟨_, report_records .., Or.inr rfl⟩
  · refine ⟨_, ?_, Or.inl rfl⟩
    simp only [State.newMessage]; exact withResultOf_records _ _

theorem receive_keysDistinct (name : String) (id : Option String) (raw : Value) (resultOf : Option String)
    (h : KeysDistinct s.records) : KeysDistinct (receive st fs s name id raw resultOf).records := by
  unfold receive
  split
  · obtain ⟨s', hr, e | e⟩ := redeliver_records_before_message (st := st) (fs := fs) (s := s) name id raw resultOf
    · rw [e]
      exact message_keysDistinct _ (hr ▸ h)
    · rw [e]
      exact hr ▸ h
  · simp only [id_bind]
    split
    · simpa using h
    · exact h
    · exact deliver_keysDistinct _ _ _ _ ((withResultOf_records (st := st) (s := s) _ _).symm ▸ h)

theorem operate_keysDistinct (screen control : String) (payload : Value)
    (h : KeysDistinct s.records) : KeysDistinct (operate st fs s screen control payload).records := by
  unfold operate
  simp only [id_bind]
  repeat' split
  all_goals first
    | exact h
    | simpa using h
    | (apply message_keysDistinct
       first
        | exact h
        | (rw [(keeps_settled _ _ (keeps_dispatch _ _ _ _)).records]; exact h))

theorem result_is_event_of_emits (name k : String) (s' : State) (p : Pending)
    (h : resultRequest st s name k = (s', some p)) :
    (∃ d ∈ st.«structure».definitions.find? (·.ref == p.activity.ref), match d.body with
      | .command _ _ _ emits .. => some (st.refOf name) ∈ emits
      | _ => False) ∧
      ∃ o, s.takenAnswers.lookup k = some (p, .accepted o) := by
  unfold resultRequest at h
  split at h
  · rename_i q a hk
    cases a with
    | accepted o =>
      cases hm : st.«structure».resultOfMismatch q.activity.ref true (st.refOf name) with
      | some m => simp [hm] at h
      | none =>
        simp only [hm, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨((resultOfMismatch_eq_none_iff _ _ _ _).mp hm).2, o, hk⟩
    | fulfilled o =>
      cases hm : st.«structure».resultOfMismatch q.activity.ref false (st.refOf name) with
      | none => exact absurd hm (resultOfMismatch_unaccepted _ _ _)
      | some m => simp [hm] at h
    | rejected r =>
      cases hm : st.«structure».resultOfMismatch q.activity.ref false (st.refOf name) with
      | none => exact absurd hm (resultOfMismatch_unaccepted _ _ _)
      | some m => simp [hm] at h
  · simp at h

theorem startInstance_halted (t : State) (c : Chart) (h : t.halted.isSome = true) : startInstance st fs t c = t := by
  simp [startInstance, h]

theorem foldl_startInstance_halted (cs : List Chart) (t : State) (h : t.halted.isSome = true) :
    cs.foldl (startInstance st fs) t = t := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.foldl_cons, startInstance_halted t c h, ih]

theorem startInstances_one_per_definition (h : (startInstances st fs s).halted = none) :
    ∃ new, (startInstances st fs s).machines = s.machines ++ new ∧ new.map (·.chart) = st.starting ∧
      ∀ i ∈ new, i.resource = i.chart.name ∧ i.opener = none ∧ i.copyOf = none := by
  unfold startInstances at h ⊢
  rw [foldlM_id] at h ⊢
  generalize st.starting = cs at h ⊢
  induction cs generalizing s with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons c cs ih =>
    simp only [List.foldl_cons] at h ⊢
    by_cases hs : s.halted.isSome = true
    · rw [startInstance_halted s c hs, foldl_startInstance_halted cs s hs] at h
      simp [h] at hs
    · cases hc : initialContextOf fs st c.name (.obj []) with
      | error v =>
        have hv := initialContextOf_error_halts c.name (.obj []) v hc
        have e : startInstance st fs s c = s.report (.fault v) := by simp [startInstance, hs, hc]
        rw [e, foldl_startInstance_halted cs _ (by simp [report_halted (.fault _) hv])] at h
        simp [report_halted (.fault _) hv] at h
      | ok context =>
        simp only [startInstance, hs, Bool.false_eq_true, ↓reduceIte, hc, id_bind, id_pure] at h ⊢
        obtain ⟨new, h₁, h₂, h₃⟩ := ih h
        refine ⟨_ :: new, by rw [h₁, List.append_assoc]; rfl, by simp only [List.map_cons, h₂], fun i hi => ?_⟩
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨rfl, rfl, rfl⟩
        · exact h₃ i hi

theorem begin_starts_each (h : s.started = false) :
    begin st fs s = message st fs (startInstances st fs (startRecords st fs { s with started := true }.newMessage))
      { tasks := st.starting.map (.start ·.name none) } := by
  simp [begin, h]

theorem begin_starts_starting_without_parent (h : s.started = false) :
    ∃ t, begin st fs s = message st fs t { tasks := st.starting.map (.start ·.name none) } ∧
      (t.halted = none → ∃ new, t.machines = (startRecords st fs { s with started := true }.newMessage).machines ++ new ∧
        new.map (·.chart) = st.starting ∧ ∀ i ∈ new, i.opener = none) :=
  ⟨_, begin_starts_each h, fun hh => (startInstances_one_per_definition hh).imp fun _ ⟨h₁, h₂, h₃⟩ =>
    ⟨h₁, h₂, fun i hi => (h₃ i hi).2.1⟩⟩

theorem resultRequest_lines (name k : String) : (resultRequest st s name k).1.lines = s.lines := by
  unfold resultRequest
  repeat' split
  all_goals first | rfl | simp

theorem addResult_lines (id : String) (e : Emit) : (addResult st fs s id e).lines = s.lines := by
  unfold addResult
  simp only [id_bind]
  split
  · rfl
  · split
    · simp
    · rfl
    · rfl

theorem resultRequest_now (name k : String) : (resultRequest st s name k).1.now = s.now := by
  unfold resultRequest
  repeat' split
  all_goals first | rfl | simp

theorem resultOfFinding_halts (event : Syntax.Ref) (requestId : String) (target : Syntax.Ref)
    (m : Syntax.ResultOfMismatch) : (resultOfFinding event requestId target m).halts = false := by
  cases m <;> rfl

theorem brokenAssumption_finding (requestId : String) (target : Syntax.Ref) (answer : Answer)
    (failedRequires failedEnsures : Option String) (r : Finding)
    (h : brokenAssumption requestId target answer failedRequires failedEnsures = some r) :
    r.halts = false ∧ ∃ m, r = assumptionFinding requestId target m := by
  obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨by cases m <;> rfl, m, rfl⟩

theorem checkAnswer_findings (p : Pending) (answer : Answer) (checked : AnswerCheck)
    (h : checkAnswer st fs p answer = .ok checked) :
    (∀ r, checked.assumption = some r → r.halts = false ∧ ∃ m, r = assumptionFinding p.id p.activity.ref m) ∧
      ∀ r, checked.written = .error r → r.halts = true ∧
        ((∃ rejection, r = .invalidInput (.unlistedRejectionKind p.id p.activity.ref rejection)) ∨
          (∃ rejection, r = .invalidInput (.unlistedRejectionReason p.id p.activity.ref rejection)) ∨
          r = .invalidInput (.answerOutputSchema p.id p.activity.ref)) := by
  unfold checkAnswer at h
  simp only [id_bind, id_pure] at h
  repeat' split at h
  all_goals (try simp only [reduceCtorEq, id_ok_inj] at h)
  all_goals (try subst h)
  all_goals refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  all_goals first
    | (simp at hr; done)
    | exact brokenAssumption_finding _ _ _ _ _ _ (by simpa using hr)
    | (simp only [Except.error.injEq] at hr; subst hr; exact ⟨rfl, by simp⟩)

theorem unmatched_result_violates (name k : String) (s₁ : State) (q : Pending) (a : Answer)
    (hp : s.takenAnswers.lookup k = some (q, a)) (hq : resultRequest st s name k = (s₁, none)) :
    ∃ event requestId target m, s₁ = s.violate (resultOfFinding event requestId target m).toViolation := by
  unfold resultRequest at hq
  split at hq
  · repeat' split at hq
    all_goals first
      | (simp at hq; done)
      | (simp only [Prod.mk.injEq, State.report, resultOfFinding_halts, Bool.false_eq_true, ↓reduceIte] at hq
         exact ⟨_, _, _, _, hq.1.symm⟩)
  · rename_i hn
    exact (hn q a hp).elim

theorem refused_operation_reported (screen control : String) (payload : Value) (c : Chart)
    (ctl : Control) (decoded : Value) (r : Refusal) (hc : st.chart? screen = some c)
    (hctl : c.controls.find? (·.name == control) = some ctl)
    (hp : fs.parse (.control screen control) payload = .ok (some decoded))
    (ha : acceptsOperation fs st (s.write .in none (.operation s!"{screen}.{control}"
      (if ctl.hasPayload then some payload else none))).1 screen control decoded = .ok (.error r)) :
    let s₁ :=
      (s.write .in none (.operation s!"{screen}.{control}" (if ctl.hasPayload then some payload else none))).1
    operate st fs s screen control payload = s₁.halt (r.finding st screen control decoded).toViolation := by
  simp only [operate, hc, hctl, id_bind, hp, ha]
  cases r <;> simp [State.report, Finding.halts, InvalidInput.halts, Refusal.finding]

theorem resent_command_gets_first_answer (name id : String) (raw input : Value)
    (known : Request × Answer) (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 = { name, input }) :
    send st fs s name (some id) raw =
      let s' := (sent s name id input).1
      message st fs (s'.answer (some id) known.2) {} := by
  simp [send, hc, hi, hk, answerAgain, hr, sent]

/-- The theorem is restricted to the state before `message` because `message` may call decide and react: it takes always
transitions of screens whose `shown` changed, and handles due deadlines. -/
theorem resent_command_ignores_decide (name id : String) (raw input : Value)
    (known : Request × Answer)
    (decide : String → Value → Records → Time → Id (Except Issue (List (List Emit))))
    (react : String → Value → Records → Time → Keys → Id (Except Issue (Option Value × List String)))
    (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 = { name, input }) :
    ∃ s', send st fs s name (some id) raw = message st fs s' {} ∧
      send st { fs with decide, react } s name (some id) raw =
        message st { fs with decide, react } s' {} := by
  refine ⟨_, resent_command_gets_first_answer name id raw input known hc hi hk hr, ?_⟩
  exact resent_command_gets_first_answer (fs := { fs with decide, react }) name id raw input known hc hi hk hr

theorem reused_id_rejected (name id : String) (raw input : Value)
    (known : Request × Answer) (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 ≠ { name, input }) :
    send st fs s name (some id) raw =
      let s' := (sent s name id input).1
      message st fs (s'.answer (some id) (.rejected { kind := .reusedId })) {} := by
  simp [send, hc, hi, hk, answerAgain, hr, sent]

theorem invalid_input_not_kept (name id : String) (raw input : Value)
    (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input) (hk : s.commandAnswers.find? id = none)
    (hp : fs.parse (.input name) raw = .ok none) :
    send st fs s name (some id) raw =
      let s' := (sent s name id input).1
      message st fs (s'.answer (some id) (.rejected { kind := .invalidInput })) {} := by
  rcases s with ⟨⟩
  simp only at hk
  simp only [send, hc, hi, ↓reduceIte, newStep_commandAnswers, newMessage_commandAnswers, write_commandAnswers,
      write_id, hk, processCommand, evaluate, hp, id_pure, newStep_records, newMessage_records, write_records,
      newStep_now, newMessage_now, write_now, id_bind, newStep_eventDeliveries, newStep_halted, newMessage_halted,
      write_halted, Tazuna.Thm.Service.Note.note_id, CommandAnswers.keep, keepsAnswer, answer_now, Bool.false_eq_true,
      answer_commandAnswers, answer_halted, sent]
  rfl

theorem unanswered_command_processed (name id : String) (raw input : Value)
    (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input) (hk : s.commandAnswers.find? id = none) :
    (send st fs s name (some id) raw).commandAnswers =
      s.commandAnswers.keep id { name, input } (evaluate st fs s.records s.now name raw).answer := by
  simp [send, hc, hi, hk, message_commandAnswers, processCommand_commandAnswers, processCommand_answer]

theorem corrected_input_processed (name id : String) (raw₁ raw₂ input₁ input₂ : Value)
    (hc : name ∈ st.commands) (hk : s.commandAnswers.find? id = none)
    (hi₁ : fs.canonical (.input name) raw₁ = .ok input₁) (hi₂ : fs.canonical (.input name) raw₂ = .ok input₂)
    (hp : fs.parse (.input name) raw₁ = .ok none) (s₁ s₂ : State)
    (h₁ : send st fs s name (some id) raw₁ = s₁)
    (h₂ : s₂.commandAnswers = s₁.commandAnswers) :
    (send st fs s₂ name (some id) raw₂).commandAnswers =
      s.commandAnswers.keep id { name, input := input₂ } (evaluate st fs s₂.records s₂.now name raw₂).answer := by
  have hk₁ : s₁.commandAnswers = s.commandAnswers := by
    rw [← h₁, invalid_input_not_kept name id raw₁ input₁ hc hi₁ hk hp]
    simp [sent, message_commandAnswers]
  rw [unanswered_command_processed name id raw₂ input₂ hc hi₂ (by rw [h₂, hk₁]; exact hk), h₂, hk₁]

theorem redelivered_event_not_processed (name id : String) (raw payload : Value)
    (hd : id ∈ s.eventDeliveries) (hc : fs.canonical (.payload name) raw = .ok payload) :
    receive st fs s name (some id) raw none = message st fs (delivered s name id payload).newMessage {} := by
  simp [receive, redeliver, withResultOf, hd, hc, delivered, State.lineId]

/-- The theorem is restricted to the state before `message` for the same reason as resent_command_ignores_decide. -/
theorem redelivered_event_keeps_records (name id : String) (raw payload : Value)
    (hd : id ∈ s.eventDeliveries)
    (hc : fs.canonical (.payload name) raw = .ok payload)
    (parse : Schema → Value → Id (Except Issue (Option Value)))
    (decide : String → Value → Records → Time → Id (Except Issue (List (List Emit))))
    (react : String → Value → Records → Time → Keys → Id (Except Issue (Option Value × List String))) :
    ∃ s', s'.records = s.records ∧
      receive st fs s name (some id) raw none = message st fs s' {} ∧
      receive st { fs with parse, decide, react } s name (some id) raw none =
        message st { fs with parse, decide, react } s' {} := by
  refine ⟨_, ?_, redelivered_event_not_processed name id raw payload hd hc,
    redelivered_event_not_processed (fs := { fs with parse, decide, react }) name id raw payload hd hc⟩
  rfl

theorem query_processed_again (name id : String) (raw input : Value) (hq : name ∈ st.queries)
    (hi : fs.canonical (.input name) raw = .ok input) :
    call st fs s name (some id) raw =
      let s₁ := (s.write .in (some id) (.query name input)).1.newMessage
      match resolveChecked st fs s₁ name raw with
      | .answered a vs => message st fs ((s₁.reportAll vs).answer (some id) a) {}
      | .halted f => s₁.report (.fault f) := by
  simp only [call, hq, hi, id_bind]
  rfl

theorem send_is_one_message (name : String) (id : Option String) (raw input : Value) (hc : name ∈ st.commands)
    (hi : fs.canonical (.input name) raw = .ok input) :
    ∃ s' q, send st fs s name id raw = message st fs s' q := by
  simp only [send, hc, hi, ↓reduceIte, id_bind]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem line_names_accepted_request (name : String) (id : Option String) (raw payload : Value) (k : String)
    (s₁ : State) (p : Pending)
    (hd : s.eventDeliveries.contains (s.lineId id name) = false)
    (hp : fs.parse (.payload name) raw = .ok (some payload)) (hq : resultRequest st s name k = (s₁, some p)) :
    (receive st fs s name id raw (some k)).lines[s.lines.size]? =
      some { time := s.now, dir := .in, id := (s₁.write .in id (.event name payload (some p.id))).2,
             body := .event name payload (some p.id) } := by
  simp only [State.lineId] at hd
  have hl : s₁.lines = s.lines := by rw [← resultRequest_lines (st := st) (s := s) name k, hq]
  have hn : s₁.now = s.now := by rw [← resultRequest_now (st := st) (s := s) name k, hq]
  simp only [receive, hd, id_bind, hp, withResultOf, hq, id_pure, State.lineId]
  unfold deliver
  simp only [id_bind, Option.map_some]
  have hw : (s₁.write .in id (.event name payload (some p.id))).1.lines[s.lines.size]? =
      some { time := s.now, dir := .in, id := (s₁.write .in id (.event name payload (some p.id))).2,
             body := .event name payload (some p.id) } := by
    simp [State.write, hl, hn]
  refine (message_extends _).getElem? ?_
  simp only [State.newStep, State.newMessage]
  rw [addResult_lines]
  exact hw

end Tazuna.Thm.Service.Input
