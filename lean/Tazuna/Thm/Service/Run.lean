import Tazuna.Service.Run
import Tazuna.Thm.Service.Restart

namespace Tazuna.Thm.Service.Run

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Query Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Clock Tazuna.Thm.Service.Input Tazuna.Thm.Service.Queue Tazuna.Thm.Service.Restart

variable {st : Service} {fs : Functions Id} {s : State} {time : DateTime} {order : Option (List DeadlineId)}
  {stepOrder : Option (List StepName)} {keys advanceKeys : Option (List (String × List String))}

theorem arrive_keysDistinct (input : Step) (h : KeysDistinct s.records) :
    KeysDistinct (arrive st fs s input).records := by
  unfold arrive
  split
  · exact h
  · exact restart_keysDistinct h
  · exact send_keysDistinct _ _ _ h
  · exact call_keysDistinct _ _ _ h
  · exact subscribe_keysDistinct _ _ _ _ h
  · exact endSubscription_keysDistinct _ h
  · exact receive_keysDistinct _ _ _ _ h
  · exact operate_keysDistinct _ _ _ _ h
  · exact operate_keysDistinct _ _ _ _ h
  · exact mock_keysDistinct _ _ _ _ _ h
  · exact answerById_keysDistinct _ _ _ h

theorem step_keysDistinct (input : Step) (h : KeysDistinct s.records) :
    KeysDistinct (step st fs s input).records := by
  unfold step
  split
  · exact h
  · simp only [id_bind, id_pure]
    have ha := advance_keysDistinct (st := st) (fs := fs)
      (s := { s with deadlineOrder := input.deadlineOrder.getD [], inputDeadlineOrder := input.deadlineOrder.getD [], stepOrder := input.stepOrder.getD [], keyNames := input.advanceKeys.getD [] }) input h
    split
    · rw [checkOrderUsed_records, takeKeys_records]; exact ha
    · split <;> rw [checkOrderUsed_records]
      · simpa using ha
      · exact arrive_keysDistinct _ (by rw [takeKeys_records]; exact ha)

theorem run_keys_distinct (inputs : List Step) : KeysDistinct (run st fs inputs).records := by
  have : ∀ (inputs : List Step) (s : State), KeysDistinct s.records →
      KeysDistinct (runFrom (step st fs) s inputs).records := by
    intro inputs
    induction inputs with
    | nil => intro s h; exact h
    | cons i rest ih =>
      intro s h
      simp only [runFrom, id_bind]
      split
      · exact step_keysDistinct _ h
      · exact ih _ (step_keysDistinct _ h)
  exact this _ _ List.nodup_nil

theorem resent_command_gets_first_answer (name id : String) (raw input : Value)
    (known : Request × Answer) (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 = { name, input }) :
    arrive st fs s ⟨time, .command (some id) name raw, order, stepOrder, keys, advanceKeys⟩ =
      let s' := (sent s name id input).1
      message st fs (s'.answer (some id) known.2) {} := by
  simp [arrive, send, hc, hi, hk, answerAgain, hr, sent]

/-- The theorem is restricted to the state before `message` because `message` may call decide and react: it takes always
transitions of screens whose `shown` changed, and handles due deadlines. -/
theorem resent_command_ignores_decide (name id : String) (raw input : Value)
    (known : Request × Answer)
    (decide : String → Value → Records → Time → Id (Except Issue (List (List Emit))))
    (react : String → Value → Records → Time → List (String × NextKeys) → Id (Except Issue (Option Value × List String)))
    (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 = { name, input }) :
    ∃ s', arrive st fs s ⟨time, .command (some id) name raw, order, stepOrder, keys, advanceKeys⟩ = message st fs s' {} ∧
      arrive st { fs with decide, react } s ⟨time, .command (some id) name raw, order, stepOrder, keys, advanceKeys⟩ =
        message st { fs with decide, react } s' {} := by
  refine ⟨_, resent_command_gets_first_answer name id raw input known hc hi hk hr, ?_⟩
  exact resent_command_gets_first_answer (fs := { fs with decide, react }) name id raw input known hc hi hk hr

theorem reused_id_rejected (name id : String) (raw input : Value)
    (known : Request × Answer) (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input)
    (hk : s.commandAnswers.find? id = some known) (hr : known.1 ≠ { name, input }) :
    arrive st fs s ⟨time, .command (some id) name raw, order, stepOrder, keys, advanceKeys⟩ =
      let s' := (sent s name id input).1
      message st fs (s'.answer (some id) (.rejected { kind := .reusedId })) {} := by
  simp [arrive, send, hc, hi, hk, answerAgain, hr, sent]

theorem invalid_input_not_kept (name id : String) (raw input : Value)
    (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input) (hk : s.commandAnswers.find? id = none)
    (hp : fs.parse (.input name) raw = .ok none) :
    arrive st fs s ⟨time, .command (some id) name raw, order, stepOrder, keys, advanceKeys⟩ =
      let s' := (sent s name id input).1
      message st fs (s'.answer (some id) (.rejected { kind := .invalidInput })) {} := by
  rcases s with ⟨⟩
  simp only at hk
  simp only [arrive, send, hc, hi, ↓reduceIte, newStep_commandAnswers, newMessage_commandAnswers, writeInput_commandAnswers,
      writeInput_id, hk, processCommand, evaluate, hp, id_pure, newStep_records, newMessage_records, writeInput_records,
      newStep_now, newMessage_now, writeInput_now, id_bind, newStep_eventDeliveries, newStep_halted, newMessage_halted,
      writeInput_halted, Tazuna.Thm.Service.Note.note_id, CommandAnswers.keep, keepsAnswer, answer_now, Bool.false_eq_true,
      answer_commandAnswers, answer_halted, sent]
  rfl

theorem unanswered_command_processed (name id : String) (raw input : Value)
    (hc : name ∈ st.commands) (hi : fs.canonical (.input name) raw = .ok input) (hk : s.commandAnswers.find? id = none) :
    (arrive st fs s ⟨time, .command (some id) name raw, order, stepOrder, keys, advanceKeys⟩).commandAnswers =
      s.commandAnswers.keep id { name, input } (evaluate st fs s.records s.now name raw).answer := by
  simp [arrive, send, hc, hi, hk, message_commandAnswers, processCommand_commandAnswers, processCommand_answer]

theorem corrected_input_processed (name id : String) (raw₁ raw₂ input₁ input₂ : Value)
    (hc : name ∈ st.commands) (hk : s.commandAnswers.find? id = none)
    (hi₁ : fs.canonical (.input name) raw₁ = .ok input₁) (hi₂ : fs.canonical (.input name) raw₂ = .ok input₂)
    (hp : fs.parse (.input name) raw₁ = .ok none) (s₁ s₂ : State)
    (h₁ : arrive st fs s ⟨time, .command (some id) name raw₁, order, stepOrder, keys, advanceKeys⟩ = s₁)
    (h₂ : s₂.commandAnswers = s₁.commandAnswers) :
    (arrive st fs s₂ ⟨time, .command (some id) name raw₂, order, stepOrder, keys, advanceKeys⟩).commandAnswers =
      s.commandAnswers.keep id { name, input := input₂ } (evaluate st fs s₂.records s₂.now name raw₂).answer := by
  have hk₁ : s₁.commandAnswers = s.commandAnswers := by
    rw [← h₁, invalid_input_not_kept name id raw₁ input₁ hc hi₁ hk hp]
    simp [sent, message_commandAnswers]
  rw [unanswered_command_processed name id raw₂ input₂ hc hi₂ (by rw [h₂, hk₁]; exact hk), h₂, hk₁]

theorem malformedRedelivery_continues (id : String) (first d : Delivery) : (malformedRedelivery id first d).halts = false := by
  unfold malformedRedelivery; split <;> rfl

theorem redelivered_event_not_processed (name id : String) (raw payload : Value) (first : Delivery)
    (hr : name ∈ st.received) (hd : s.eventDeliveries.find? id = some first)
    (hc : fs.canonical (.payload name) raw = .ok payload) :
    arrive st fs s ⟨time, .event (some id) name raw none, order, stepOrder, keys, advanceKeys⟩ =
      let d : Delivery := { event := st.refOf name, payload }
      let s' := delivered s name id d.payload
      message st fs (if first = d then s' else s'.violate (Finding.invalidInput (malformedRedelivery id first d)).toViolation).newMessage {} := by
  simp [arrive, receive, redeliver, withResultOf, hr, hd, hc, delivered, State.lineId, State.report, Finding.halts,
    malformedRedelivery_continues]

theorem redelivery_reports_reused_id_iff_differs (name id : String) (raw payload : Value)
    (first : Delivery) (hr : name ∈ st.received) (hd : s.eventDeliveries.find? id = some first)
    (hc : fs.canonical (.payload name) raw = .ok payload) :
    let d : Delivery := { event := st.refOf name, payload }
    ∃ s', arrive st fs s ⟨time, .event (some id) name raw none, order, stepOrder, keys, advanceKeys⟩ = message st fs s' {} ∧
      s'.records = s.records ∧
      (s'.violations = s.violations ++ [(Finding.invalidInput (malformedRedelivery id first d)).toViolation] ↔ first ≠ d) ∧
      (first = d → s'.violations = s.violations) := by
  intro d
  refine ⟨_, redelivered_event_not_processed name id raw payload first hr hd hc, ?_, ?_, ?_⟩
  · simp only [delivered]
    split <;> rfl
  · by_cases he : first = d
    · simp only [d] at he
      simp only [State.newMessage, he, ↓reduceIte, delivered, State.writeInput, List.self_eq_append_right,
          List.cons_ne_self, ne_eq, false_iff, Decidable.not_not]
      rfl
    · simp only [d] at he
      simp [he, delivered, State.writeInput, State.newMessage, State.violate, d]
  · intro he
    simp only [d] at he
    simp [he, delivered, State.writeInput, State.newMessage]

/-- The theorem is restricted to the state before `message` for the same reason as resent_command_ignores_decide. -/
theorem redelivered_event_keeps_records (name id : String) (raw payload : Value) (first : Delivery)
    (hr : name ∈ st.received) (hd : s.eventDeliveries.find? id = some first)
    (hc : fs.canonical (.payload name) raw = .ok payload)
    (parse : Schema → Value → Id (Except Issue (Option Value)))
    (decide : String → Value → Records → Time → Id (Except Issue (List (List Emit))))
    (react : String → Value → Records → Time → List (String × NextKeys) → Id (Except Issue (Option Value × List String))) :
    ∃ s', s'.records = s.records ∧
      arrive st fs s ⟨time, .event (some id) name raw none, order, stepOrder, keys, advanceKeys⟩ = message st fs s' {} ∧
      arrive st { fs with parse, decide, react } s ⟨time, .event (some id) name raw none, order, stepOrder, keys, advanceKeys⟩ =
        message st { fs with parse, decide, react } s' {} := by
  refine ⟨_, ?_, redelivered_event_not_processed name id raw payload first hr hd hc,
    redelivered_event_not_processed (fs := { fs with parse, decide, react }) name id raw payload first hr hd hc⟩
  simp only [delivered]
  split <;> rfl

theorem query_processed_again (name id : String) (raw input : Value) (hq : name ∈ st.queries)
    (hi : fs.canonical (.input name) raw = .ok input) :
    arrive st fs s ⟨time, .query (some id) name raw, order, stepOrder, keys, advanceKeys⟩ =
      let s₁ := (s.writeInput (some id) (.query name input)).1.newMessage
      match resolveChecked st fs s₁ name raw with
      | .answered a vs => message st fs ((s₁.reportAll vs).answer (some id) a) {}
      | .halted f => s₁.report (.fault f) := by
  simp only [arrive, call, hq, hi, id_bind]
  rfl

theorem send_is_one_message (name : String) (id : Option String) (raw input : Value) (hc : name ∈ st.commands)
    (hi : fs.canonical (.input name) raw = .ok input) :
    ∃ s' q, arrive st fs s ⟨time, .command id name raw, order, stepOrder, keys, advanceKeys⟩ = message st fs s' q := by
  simp only [arrive, send, hc, hi, ↓reduceIte, id_bind]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem keys_never_duplicate (inputs : List Step) :
    ((run st fs inputs).records.map fun r => (r.entity, r.key)).Nodup :=
  run_keys_distinct inputs

theorem line_names_accepted_request (name : String) (id : Option String) (raw payload : Value) (k : String)
    (s₁ : State) (p : Pending) (hr : name ∈ st.received)
    (hd : s.eventDeliveries.find? (s.lineId id name) = none)
    (hp : fs.parse (.payload name) raw = .ok (some payload)) (hq : resultRequest st s name k = (s₁, some p)) :
    (arrive st fs s ⟨time, .event id name raw (some k), order, stepOrder, keys, advanceKeys⟩).lines[s.lines.size]? =
      some { time := s.now, dir := .in, id := (s₁.writeInput id (.event name payload (some p.id))).2,
             body := .event name payload (some p.id), deadlineOrder := s.inputDeadlineOrder } := by
  simp only [State.lineId] at hd
  have hl : s₁.lines = s.lines := by rw [← resultRequest_lines (st := st) (s := s) name k, hq]
  have hn : s₁.now = s.now := by rw [← resultRequest_now (st := st) (s := s) name k, hq]
  have ho : s₁.inputDeadlineOrder = s.inputDeadlineOrder := by rw [← resultRequest_inputDeadlineOrder (st := st) (s := s) name k, hq]
  simp only [arrive, receive, hr, hd, id_bind, hp, withResultOf, hq, id_pure, State.lineId]
  unfold deliver
  simp only [id_bind, Option.map_some]
  have hw : (s₁.writeInput id (.event name payload (some p.id))).1.lines[s.lines.size]? =
      some { time := s.now, dir := .in, id := (s₁.writeInput id (.event name payload (some p.id))).2,
             body := .event name payload (some p.id), deadlineOrder := s.inputDeadlineOrder } := by
    simp [State.writeInput, hl, hn, ho]
  refine (message_extends _).getElem? ?_
  simp only [State.newStep, State.newMessage]
  rw [addResult_lines]
  exact hw

/--
When an input without an uncreated key halts on arrival after an advance that did not halt, the run stops there and
skips `rest`.
-/
theorem halting_arrival_stops_run (i : Step) (rest : List Step) (v : Violation) (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := i.deadlineOrder.getD [], inputDeadlineOrder := i.deadlineOrder.getD [], stepOrder := i.stepOrder.getD [], keyNames := i.advanceKeys.getD [] } i).takeKeys (i.keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := i.deadlineOrder.getD [], inputDeadlineOrder := i.deadlineOrder.getD [], stepOrder := i.stepOrder.getD [], keyNames := i.advanceKeys.getD [] } i).takeKeys (i.keys.getD [])).uncreatedKey st i.body = none)
    (hv : let s₁ := (advance st fs { s with deadlineOrder := i.deadlineOrder.getD [], inputDeadlineOrder := i.deadlineOrder.getD [], stepOrder := i.stepOrder.getD [], keyNames := i.advanceKeys.getD [] } i).takeKeys (i.keys.getD [])
      arrive st fs s₁ i = s₁.halt v) :
    runFrom (step st fs) s (i :: rest) =
      (((advance st fs { s with deadlineOrder := i.deadlineOrder.getD [], inputDeadlineOrder := i.deadlineOrder.getD [], stepOrder := i.stepOrder.getD [], keyNames := i.advanceKeys.getD [] } i).takeKeys (i.keys.getD [])).halt
          v).checkOrderUsed := by
  have hs : step st fs s i =
      (((advance st fs { s with deadlineOrder := i.deadlineOrder.getD [], inputDeadlineOrder := i.deadlineOrder.getD [], stepOrder := i.stepOrder.getD [], keyNames := i.advanceKeys.getD [] } i).takeKeys (i.keys.getD [])).halt
          v).checkOrderUsed := by
    rw [step]
    simp only [show s.halted.isSome = false by simp [hh], id_bind, id_pure, ha, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, hk]
    rw [hv]
  simp only [runFrom, id_bind, hs]
  simp [State.checkOrderUsed, State.takeKeys, State.halt]

theorem other_service_screen_stops_run (screen control : String) (payload : Value) (body : Step.Body)
    (hb : body = .operation screen control payload ∨ body = .unacceptedOperation screen control payload)
    (rest : List Step) (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, body, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, body, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).uncreatedKey st body = none)
    (hc : st.chart? screen = none) :
    runFrom (step st fs) s (⟨time, body, order, stepOrder, keys, advanceKeys⟩ :: rest) =
      (((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, body, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halt
          (Finding.invalidInput (.unownedTarget (st.refOf screen))).toViolation).checkOrderUsed := by
  rcases hb with rfl | rfl <;>
  exact halting_arrival_stops_run _ rest _ hh ha hk
    (by simp [arrive, operate, hc, State.halt, State.report, Finding.halts, InvalidInput.halts])

theorem unknown_control_stops_run (screen control : String) (payload : Value) (body : Step.Body)
    (hb : body = .operation screen control payload ∨ body = .unacceptedOperation screen control payload)
    (rest : List Step) (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, body, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, body, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).uncreatedKey st body = none)
    (c : Chart) (hc : st.chart? screen = some c) (hn : c.controls.find? (·.name == control) = none) :
    runFrom (step st fs) s (⟨time, body, order, stepOrder, keys, advanceKeys⟩ :: rest) =
      (((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, body, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halt
          (Finding.invalidInput (.unknownControl (st.ref screen) control)).toViolation).checkOrderUsed := by
  rcases hb with rfl | rfl <;>
  exact halting_arrival_stops_run _ rest _ hh ha hk
    (by simp [arrive, operate, hc, hn, State.halt, State.report, Finding.halts, InvalidInput.halts])

theorem other_service_command_stops_run (name : String) (id : Option String) (raw : Value) (rest : List Step)
    (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .command id name raw, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .command id name raw, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).uncreatedKey st (.command id name raw) = none)
    (hc : name ∉ st.commands) :
    runFrom (step st fs) s (⟨time, .command id name raw, order, stepOrder, keys, advanceKeys⟩ :: rest) =
      (((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .command id name raw, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halt
          (Finding.invalidInput (.unownedTarget (st.refOf name))).toViolation).checkOrderUsed :=
  halting_arrival_stops_run _ rest _ hh ha hk
    (by simp [arrive, send, hc, State.halt, State.report, Finding.halts, InvalidInput.halts])

theorem other_service_query_stops_run (name : String) (id : Option String) (raw : Value) (rest : List Step)
    (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .query id name raw, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .query id name raw, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).uncreatedKey st (.query id name raw) = none)
    (hq : name ∉ st.queries) :
    runFrom (step st fs) s (⟨time, .query id name raw, order, stepOrder, keys, advanceKeys⟩ :: rest) =
      (((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .query id name raw, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halt
          (Finding.invalidInput (.unownedTarget (st.refOf name))).toViolation).checkOrderUsed :=
  halting_arrival_stops_run _ rest _ hh ha hk
    (by simp [arrive, call, hq, State.halt, State.report, Finding.halts, InvalidInput.halts])

theorem other_service_subscription_stops_run (name : String) (id : Option String) (raw : Value) (handle : Option String)
    (rest : List Step)
    (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .subscribe id name raw handle, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .subscribe id name raw handle, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).uncreatedKey st (.subscribe id name raw handle) = none)
    (hq : name ∉ st.queries) :
    runFrom (step st fs) s (⟨time, .subscribe id name raw handle, order, stepOrder, keys, advanceKeys⟩ :: rest) =
      (((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .subscribe id name raw handle, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halt
          (Finding.invalidInput (.unownedTarget (st.refOf name))).toViolation).checkOrderUsed :=
  halting_arrival_stops_run _ rest _ hh ha hk
    (by simp [arrive, subscribe, hq, State.halt, State.report, Finding.halts, InvalidInput.halts])

theorem uncontracted_event_stops_run (name : String) (id : Option String) (raw : Value) (resultOf : Option String)
    (rest : List Step) (hh : s.halted = none)
    (ha : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .event id name raw resultOf, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halted = none)
    (hk : ((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .event id name raw resultOf, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).uncreatedKey st (.event id name raw resultOf) = none)
    (hr : name ∉ st.received) :
    runFrom (step st fs) s (⟨time, .event id name raw resultOf, order, stepOrder, keys, advanceKeys⟩ :: rest) =
      (((advance st fs { s with deadlineOrder := order.getD [], inputDeadlineOrder := order.getD [], stepOrder := stepOrder.getD [], keyNames := advanceKeys.getD [] } ⟨time, .event id name raw resultOf, order, stepOrder, keys, advanceKeys⟩).takeKeys (keys.getD [])).halt
          (Finding.invalidInput (.unlistedEvent (st.refOf name))).toViolation).checkOrderUsed :=
  halting_arrival_stops_run _ rest _ hh ha hk
    (by simp [arrive, receive, hr, State.halt, State.report, Finding.halts, InvalidInput.halts])

end Tazuna.Thm.Service.Run
