import Tazuna.Semantics.System.Input
import Tazuna.Thm.Semantics.System.Queue
import Tazuna.Thm.Syntax.Structure

namespace Tazuna.Thm.Semantics.System.Input

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.Chart.Always Tazuna.Thm.Semantics.Chart.Deadline Tazuna.Thm.Semantics.Chart.Done Tazuna.Thm.Semantics.Chart.Exit Tazuna.Thm.Semantics.Chart.Macrostep Tazuna.Thm.Semantics.Chart.Map Tazuna.Thm.Semantics.Chart.Microstep Tazuna.Thm.Semantics.Chart.Queue Tazuna.Thm.Semantics.Chart.Request Tazuna.Thm.Semantics.Functions Tazuna.Thm.Semantics.Screen.Subscription Tazuna.Thm.Semantics.Service.Automation Tazuna.Thm.Semantics.Service.Command Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.Service.Query Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic Tazuna.Thm.Semantics.System.Clock Tazuna.Thm.Semantics.System.Queue

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

@[simp] theorem checkOrderUsed_records : s.checkOrderUsed.records = s.records := by
  unfold State.checkOrderUsed; split <;> simp

@[simp] theorem checkOrderUsed_started : s.checkOrderUsed.started = s.started := by
  unfold State.checkOrderUsed; split <;> simp

@[simp] theorem checkOrderUsed_lines : s.checkOrderUsed.lines = s.lines := by
  unfold State.checkOrderUsed; split <;> simp

@[simp] theorem checkOrderUsed_commandAnswers : s.checkOrderUsed.commandAnswers = s.commandAnswers := by
  unfold State.checkOrderUsed; split <;> simp

theorem advance_keysDistinct (input : Step) (h : KeysDistinct s.records) :
    KeysDistinct (advance st fs s input).records := by
  unfold advance
  dsimp only
  split
  · exact h
  · simp only [id_bind]
    have hf := fireDue_keysDistinct (st := st) (fs := fs) input.time.time Limit.dueDeadlines.max none h
    generalize fireDue st fs input.time.time Limit.dueDeadlines.max none s = X at hf ⊢
    split
    · exact hf
    · split
      · exact hf
      · exact begin_keysDistinct (st := st) (fs := fs) (s := { X with now := max X.now input.time.time }) hf

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

theorem subscribe_keysDistinct (name : String) (id : Option String) (raw : Value) (handle : Option String)
    (h : KeysDistinct s.records) : KeysDistinct (subscribe st fs s name id raw handle).records := by
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

theorem endOpened_keysDistinct (id : String) (h : KeysDistinct s.records) :
    KeysDistinct (endOpened st fs s id).records := by
  unfold endOpened
  apply message_keysDistinct
  split <;> exact h

theorem endSubscription_keysDistinct (subscription : Ended) (h : KeysDistinct s.records) :
    KeysDistinct (endSubscription st fs s subscription).records := by
  unfold endSubscription
  split
  · exact endOpened_keysDistinct _ h
  · split
    · exact endOpened_keysDistinct _ h
    · exact h

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

theorem redeliver_records_before_message (name : String) (id : Option String) (raw : Value) (resultOf : Option String)
    (first : Delivery) :
    ∃ s', s'.records = s.records ∧
      (redeliver st fs s name id raw resultOf first = message st fs s' {} ∨ redeliver st fs s name id raw resultOf first = s') := by
  unfold redeliver
  simp only [id_bind]
  split
  · exact ⟨_, report_records .., Or.inr rfl⟩
  · refine ⟨_, ?_, Or.inl rfl⟩
    split
    · exact withResultOf_records _ _
    · simp only [State.newMessage, report_records]; exact withResultOf_records _ _

theorem receive_keysDistinct (name : String) (id : Option String) (raw : Value) (resultOf : Option String)
    (h : KeysDistinct s.records) : KeysDistinct (receive st fs s name id raw resultOf).records := by
  unfold receive
  split
  · split
    · rename_i first _
      obtain ⟨s', hr, e | e⟩ := redeliver_records_before_message (st := st) (fs := fs) (s := s) name id raw resultOf first
      · rw [e]
        exact message_keysDistinct _ (hr ▸ h)
      · rw [e]
        exact hr ▸ h
    · simp only [id_bind]
      split
      · simpa using h
      · exact h
      · exact deliver_keysDistinct _ _ _ _ ((withResultOf_records (st := st) (s := s) _ _).symm ▸ h)
  · exact h

theorem mock_keysDistinct (sender name : String) (answer : Answer) (choice : Option Choice) (handle : Option String)
    (h : KeysDistinct s.records) : KeysDistinct (mock st fs s sender name answer choice handle).records := by
  unfold mock answerRequest
  simp only [id_bind]
  split
  · simpa using h
  · split
    · simpa using h
    · split
      · split <;> simpa using h
      · apply message_keysDistinct
        rw [(keeps_settled _ _ (keeps_deliverAnswer _ _ _)).records]
        simp only [State.newStep, State.newMessage, State.writeInput]
        repeat' split
        all_goals simpa using h

theorem operate_keysDistinct (screen control : String) (payload : Value) (accepted : Bool)
    (h : KeysDistinct s.records) : KeysDistinct (operate st fs s screen control payload accepted).records := by
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
      ∃ o, s.mocks.lookup k = some (p, .accepted o) := by
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

theorem subscription_answer_is_own_message (sender name : String) (answer : Answer) (choice : Option Choice)
    (handle : Option String) (p : Pending) (checked : AnswerCheck) (written : Answer)
    (hf : s.answering st fs sender name choice = .ok p) (ha : checkAnswer st fs p answer = .ok checked)
    (hw : checked.written = .ok written) :
    ∃ t : State, t.lines = (s.writeInput none (.answer p.id written)).1.lines ∧
      mock st fs s sender name answer choice handle =
        let started := t.newMessage.newStep none
        let r := settled fs st started.2 p.requester.machine? (deliverAnswer fs st started.2 p written) ⟨started.1, {}⟩
        message st fs r.state r.queue := by
  unfold mock answerRequest
  simp only [id_bind, id_pure]
  rw [hf]
  simp only [ha, hw]
  refine ⟨_, ?_, rfl⟩
  cases checked.assumption <;> split <;> simp [State.writeInput, State.lineId]

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

theorem earliestTurn_spec (ps : List Pending) (p : Pending) (h : earliestTurn ps = some p) :
    p ∈ ps ∧ ∀ q ∈ ps, p.turn ≤ q.turn := by
  obtain ⟨hm, _, hq⟩ := foldl_earliest ps none p h
  rcases hm with hm | hm
  · cases hm
  · exact ⟨hm, hq⟩

theorem mock_answers_longest_waiting (ps : List Pending) (p : Pending) (h : earliestTurn ps = some p) :
    p ∈ ps ∧ ∀ q ∈ ps, p.turn ≤ q.turn :=
  earliestTurn_spec ps p h

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

theorem resultRequest_inputDeadlineOrder (name k : String) :
    (resultRequest st s name k).1.inputDeadlineOrder = s.inputDeadlineOrder := by
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
    (hp : s.mocks.lookup k = some (q, a)) (hq : resultRequest st s name k = (s₁, none)) :
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

theorem earlier_at_reported (input : Step) :
    advance st fs s input =
      let time := input.time.time
      if time < s.now then s.halt (Finding.invalidInput (.earlierAt time s.now)).toViolation else
      let s₁ := fireDue st fs time Limit.dueDeadlines.max none s
      if s₁.halted.isSome then s₁ else
      match input.body with
      | .restart => { s₁ with now := max s₁.now time }
      | _ => begin st fs { s₁ with now := max s₁.now time } := by
  simp only [advance, State.report, Finding.halts, InvalidInput.halts, id_bind]
  rfl

theorem acceptance_mismatch_reported (screen control : String) (payload : Value) (accepted : Bool) (c : Chart)
    (ctl : Control) (decoded : Value) (top : Except Refusal Instance) (hc : st.chart? screen = some c)
    (hctl : c.controls.find? (·.name == control) = some ctl)
    (hp : fs.parse (.control screen control) payload = .ok (some decoded))
    (ha : acceptsOperation fs st (s.writeInput none (.operation s!"{screen}.{control}"
      (if ctl.hasPayload then some payload else none) accepted)).1 screen control decoded = .ok top) :
    let s₁ :=
      (s.writeInput none (.operation s!"{screen}.{control}" (if ctl.hasPayload then some payload else none) accepted)).1
    operate st fs s screen control payload accepted =
      match accepted, top with
      | true, .error r => s₁.halt (r.finding st screen control decoded).toViolation
      | false, .ok _ => s₁.halt (Finding.invalidInput (.unexpectedlyAccepted (st.ref screen) control)).toViolation
      | false, .error _ => message st fs s₁.newMessage {}
      | true, .ok i =>
        let started := s₁.newMessage.newStep none
        let r := settled fs st started.2 (some i.resource) (dispatch fs st started.2 i.resource control decoded) ⟨started.1, {}⟩
        message st fs r.state r.queue := by
  cases accepted <;> cases top
  all_goals simp only [operate, hc, hctl, id_bind, hp, ha]
  · simp [State.report, Finding.halts, InvalidInput.halts]
  · rename_i r
    cases r <;> simp [State.report, Finding.halts, InvalidInput.halts, Refusal.finding]

theorem earliestTurn_eq_none (ps : List Pending) : earliestTurn ps = none ↔ ps = [] := by
  unfold earliestTurn
  cases ps with
  | nil => simp
  | cons p ps =>
    simp only [List.foldl_cons, reduceCtorEq, iff_false]
    suffices ∀ (l : List Pending) (b : Pending), l.foldl (fun best p => match best with
        | some b => if p.turn < b.turn then some p else some b
        | none => some p) (some b) ≠ none from this ps p
    intro l
    induction l with
    | nil => intro b; simp
    | cons q qs ih => intro b; simp only [List.foldl_cons]; split <;> exact ih _

theorem mock_without_waiting_request_reported (sender name : String) (choice : Option Choice)
    (hc : s.answerable st fs sender name choice = .ok []) :
    s.answering st fs sender name choice =
      .error (.invalidInput ((if choosesStale choice then InvalidInput.missingStaleRequest else .missingWaitingRequest)
        (st.refOf sender) (st.refOf name))) := by
  simp [State.answering, hc, earliestTurn]

theorem ambiguous_mock_reported (sender name : String) (choice : Option Choice) (ps : List Pending)
    (hc : s.answerable st fs sender name choice = .ok ps) (ha : 1 < (ps.map (·.input)).eraseDups.length) :
    s.answering st fs sender name choice =
      .error (.invalidInput (.ambiguousMock (st.refOf sender) (st.refOf name) (ps.map (·.input)).eraseDups)) := by
  simp [State.answering, hc, ha]

theorem mock_reports_unanswered (sender name : String) (answer : Answer) (choice : Option Choice)
    (handle : Option String) (f : Finding) (hf : s.answering st fs sender name choice = .error f) :
    mock st fs s sender name answer choice handle = s.report f := by
  simp [mock, hf]

end Tazuna.Thm.Semantics.System.Input
