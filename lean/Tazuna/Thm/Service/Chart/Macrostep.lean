import Tazuna.Service.Chart.Macrostep
import Tazuna.Thm.Service.Chart.Always
import Tazuna.Thm.Service.Screen.Subscription
import Tazuna.Thm.Service.Automation
import Tazuna.Thm.Service.Command

namespace Tazuna.Thm.Service.Chart.Macrostep

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem settled_some (step : Nat) (name : InstanceId) (f : Processing → Id Processing) (r : Processing) :
    settled fs st step (some name) f r = settleAround fs st step (name.owner) f r := rfl

theorem records_change_settles (s : State) (groups : List (List Emit)) (cause : Nat) (i : Instance)
    (hm : i ∈ s.machines) (hc : i.closed = false) :
    ∃ received, Work.receive i.id received cause ∈ reactions st s groups true cause := by
  refine ⟨(groups.map fun g => g.flatMap fun e =>
      (i.chart.receives.filter (·.2 == e.event)).map fun r => { key := r.1, payload := e.payload : Received }).filter (!·.isEmpty),
    List.mem_append_left _ (List.mem_filterMap.mpr ⟨i, hm, ?_⟩)⟩
  simp [machineWork, hc]

theorem keeps_settle (step : Nat) (name : InstanceId) : Keeps (settle fs st step name) :=
  fun r => settleFrom_fixed step _ _ r

theorem keeps_settleAround (step : Nat) (owner : InstanceId) {f : Processing → Id Processing} (hf : Keeps f) :
    Keeps (settleAround fs st step owner f) := by
  intro r
  simp only [settleAround, id_bind]
  rw [settleFrom_fixed, keeps_unlessHalted hf, settleFrom_fixed]

theorem keeps_settled (step : Nat) (name : Option InstanceId) {f : Processing → Id Processing} (hf : Keeps f) :
    Keeps (settled fs st step name f) := by
  intro r
  cases name with
  | none => exact hf r
  | some n => rw [settled_some]; exact keeps_settleAround step _ hf r

theorem keeps_applyCompletion (step : Nat) (name : InstanceId) (ts : List Transition) (extra : Extra) :
    Keeps (applyCompletion fs st step name ts extra) := by
  unfold applyCompletion
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report]
  · rfl
  · exact keeps_microstep step name _ _ r

theorem keeps_handle (step : Nat) (name : InstanceId) (state : String) (a : Activity) (answer : Answer) :
    Keeps (handle fs st step name state a answer) := by
  unfold handle
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · split <;> exact keeps_applyCompletion _ _ _ _ r

theorem keeps_dispatch (step : Nat) (name : InstanceId) (key : String) (payload : Value) :
    Keeps (dispatch fs st step name key payload) := by
  intro r
  unfold dispatch
  split
  · rfl
  · split
    · rfl
    · try simp only [id_bind]
      split
      · simp [Processing.report]
      · split
        · simp [Processing.report]
        · rfl
        · exact keeps_microstep step name _ _ r

theorem keeps_receiveWork (step : Nat) (name : InstanceId) (groups : List (List Received)) :
    Keeps (receiveWork fs st step name groups) := by
  intro r
  unfold receiveWork
  split
  · exact (keeps_dispatch step name _ _ _).trans (keeps_settle step name r)
  · rfl

theorem keeps_done (step : Nat) (name : InstanceId) (n : String) : Keeps (done fs st step name n) := by
  unfold done
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · exact keeps_applyCompletion _ _ _ _ r

theorem keeps_doneWork (step : Nat) (name : InstanceId) (fuel : Nat) : Keeps (doneWork fs st step name fuel) := by
  induction fuel with
  | zero => intro r; rw [doneWork]; repeat' split
            all_goals rfl
  | succ fuel ih =>
    intro r
    rw [doneWork]
    split
    · rfl
    · split
      · rfl
      · split
        · try simp only [id_bind]
          rw [ih, keeps_done, keeps_settle]
          rfl
        · rfl

theorem keeps_startWork (step : Nat) (name : InstanceId) : Keeps (startWork fs st step name) := by
  unfold startWork
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  rw [keeps_unlessHalted (keeps_settle step name), keeps_enter]

theorem showAnswer_fixed (name : InstanceId) (slot : String) (answer : Answer) (r : Processing) :
    (showAnswer st name slot answer r).state.fixed = r.state.fixed := by
  unfold showAnswer
  repeat' split
  all_goals rfl

theorem keeps_answerTo (step : Nat) (a : Activity) (answer : Answer) (requester : Requester) :
    Keeps (answerTo fs st step a answer requester) := by
  intro r
  cases requester with
  | state name state => exact keeps_handle _ _ _ _ _ _
  | slot name slot =>
    simp only [answerTo]
    repeat' split
    all_goals exact showAnswer_fixed _ _ _ _
  | automation n => exact automationAnswer_fixed _ _ _

theorem keeps_deliverAnswer (step : Nat) (p : Pending) (answer : Answer) :
    Keeps (deliverAnswer fs st step p answer) := by
  intro r
  have ha := answered_fixed (s := r.state) p
  unfold deliverAnswer
  rcases h : r.state.answered p with ⟨s', live⟩
  rw [h] at ha
  cases live
  · exact ha
  · exact (keeps_answerTo _ _ _ _ _).trans ha

theorem growsBy_settle (step : Nat) (name : InstanceId) : GrowsBy (settle fs st step name) :=
  fun r => settleFrom_grows step _ _ r

theorem growsBy_settleAround (step : Nat) (owner : InstanceId) {f : Processing → Id Processing} (hf : GrowsBy f)
    (hk : Keeps f) : GrowsBy (settleAround fs st step owner f) := by
  intro r
  simp only [settleAround, id_bind]
  exact (settleFrom_grows step owner _ r).trans (congrArg Fixed.now (settleFrom_fixed step owner _ r))
    ((growsBy_unlessHalted hf _).trans ((keeps_unlessHalted hk).now _) (settleFrom_grows step owner _ _))

theorem growsBy_settled (step : Nat) (name : Option InstanceId) {f : Processing → Id Processing} (hf : GrowsBy f)
    (hk : Keeps f) : GrowsBy (settled fs st step name f) := by
  intro r
  cases name with
  | none => exact hf r
  | some n => rw [settled_some]; exact growsBy_settleAround step _ hf hk r

theorem growsBy_applyCompletion (step : Nat) (name : InstanceId) (ts : List Transition) (extra : Extra) :
    GrowsBy (applyCompletion fs st step name ts extra) := by
  unfold applyCompletion
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  split
  · exact Grows.of_lines (report_lines ..)
  · exact Grows.refl _
  · exact growsBy_microstep step name _ _ r

theorem growsBy_handle (step : Nat) (name : InstanceId) (state : String) (a : Activity) (answer : Answer) :
    GrowsBy (handle fs st step name state a answer) := by
  unfold handle
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · split <;> exact growsBy_applyCompletion _ _ _ _ r

theorem growsBy_dispatch (step : Nat) (name : InstanceId) (key : String) (payload : Value) :
    GrowsBy (dispatch fs st step name key payload) := by
  intro r
  unfold dispatch
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · try simp only [id_bind]
      split
      · exact Grows.of_lines (report_lines ..)
      · split
        · exact Grows.of_lines (report_lines ..)
        · exact Grows.refl _
        · exact growsBy_microstep step name _ _ r

theorem growsBy_receiveWork (step : Nat) (name : InstanceId) (groups : List (List Received)) :
    GrowsBy (receiveWork fs st step name groups) := by
  intro r
  unfold receiveWork
  split
  · exact Grows.comp (growsBy_settle step name) (keeps_settle step name) (growsBy_dispatch step name _ _) r
  · exact Grows.refl _

theorem growsBy_done (step : Nat) (name : InstanceId) (n : String) : GrowsBy (done fs st step name n) := by
  unfold done
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · exact growsBy_applyCompletion _ _ _ _ r

theorem growsBy_doneWork (step : Nat) (name : InstanceId) (fuel : Nat) : GrowsBy (doneWork fs st step name fuel) := by
  induction fuel with
  | zero => intro r; rw [doneWork]; repeat' split
            all_goals exact Grows.of_lines rfl
  | succ fuel ih =>
    intro r
    rw [doneWork]
    split
    · exact Grows.refl _
    · split
      · exact Grows.refl _
      · split
        · try simp only [id_bind]
          exact Grows.after (f := fun r => doneWork fs st step name fuel (done fs st step name _ (settle fs st step name r)))
            (fun r => (Grows.comp (growsBy_settle step name) (keeps_settle step name) (growsBy_done step name _) r).trans
              ((keeps_done step name _).now _ |>.trans ((keeps_settle step name).now r)) (ih _)) rfl rfl
        · exact Grows.refl _

theorem growsBy_startWork (step : Nat) (name : InstanceId) : GrowsBy (startWork fs st step name) := by
  unfold startWork
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  exact (growsBy_enter step name _ r).trans ((keeps_enter step name _).now r)
    (growsBy_unlessHalted (growsBy_settle step name) _)

theorem showAnswer_grows (name : InstanceId) (slot : String) (answer : Answer) (r : Processing) :
    Grows r.state (showAnswer st name slot answer r).state := by
  refine Grows.of_lines ?_
  unfold showAnswer
  repeat' split
  all_goals rfl

theorem growsBy_answerTo (step : Nat) (a : Activity) (answer : Answer) (requester : Requester) :
    GrowsBy (answerTo fs st step a answer requester) := by
  intro r
  cases requester with
  | state name state => exact growsBy_handle _ _ _ _ _ _
  | slot name slot =>
    simp only [answerTo]
    repeat' split
    all_goals exact showAnswer_grows _ _ _ _
  | automation n => exact Grows.of_lines (automationAnswer_lines _ _ _)

theorem stopped_machine_takes_no_event (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) (hc : i.closed = true) :
    dispatch fs st step name key payload r = r := by
  simp [dispatch, hi, hc]

theorem dispatch_takes_one_microstep (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) (i : Instance)
    (leaves : List (InstanceId × Option String)) (chosen : List (InstanceId × Transition)) (hh : r.state.halted = none)
    (hi : r.state.machine? name = some i) (hc : i.closed = false) (hl : eventLeaves fs st r.state i payload = .ok leaves)
    (hs : select fs st r.state i (.on key) (.payload payload) leaves = .ok chosen) (hn : chosen ≠ []) :
    dispatch fs st step name key payload r = microstep fs st step name chosen (.payload payload) r := by
  unfold dispatch
  cases chosen with
  | nil => exact absurd rfl hn
  | cons t ts =>
    simp only [hi, Processing.halted, hh, hc, Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte, id_bind]
    rw [hl]
    simp only
    rw [hs]

theorem answer_after_exit_ignored (step : Nat) (name : InstanceId) (state : String) (a : Activity) (answer : Answer) (r : Processing)
    (i : Instance) (hi : r.state.machine? name = some i) (hn : i.isIn state = false) :
    handle fs st step name state a answer r = r := by
  unfold handle withMachine
  split
  · rfl
  · simp [hi, hn]

theorem untaken_operation_changes_nothing (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) (i : Instance)
    (leaves : List (InstanceId × Option String)) (hh : r.state.halted = none) (hi : r.state.machine? name = some i)
    (hl : eventLeaves fs st r.state i payload = .ok leaves)
    (hs : select fs st r.state i (.on key) (.payload payload) leaves = .ok []) :
    dispatch fs st step name key payload r = r := by
  unfold dispatch
  simp only [hi, Processing.halted, hh, Option.isSome_none, Bool.false_or]
  split
  · rfl
  · simp only [id_bind]; rw [hl]; simp only; rw [hs]; rfl

theorem stale_answer_ignored (step : Nat) (p : Pending) (answer : Answer) (r : Processing) (waiting : Pending)
    (hw : r.state.pending.find? (·.id == p.id) = some waiting) (hs : waiting.stale = true) :
    deliverAnswer fs st step p answer r = ⟨(r.state.answered p).1, r.queue⟩ := by
  simp [deliverAnswer, State.answered, hw, hs]

theorem keeps_workBody (step : Nat) (w : Work) : Keeps (workBody st fs step w) := by
  intro r
  obtain ⟨s, q⟩ := r
  cases w with
  | reaction a gs c =>
    rcases gs with _ | ⟨_ | ⟨e, g⟩, gs⟩
    · rfl
    · rfl
    simp only [workBody, id_bind]
    repeat' split
    all_goals first | rfl | exact (await_fixed ..).trans rfl | simp [State.fixed, report_eq]
  | answered c answer cause =>
    simp only [workBody]
    repeat' split
    all_goals first | exact keeps_answerTo _ _ _ _ _ | rfl | simp [State.fixed, State.takeQueued, report_eq]
  | start name c => exact keeps_startWork _ _ _
  | receive name received c => exact keeps_receiveWork _ _ _ _
  | onDone name c => exact keeps_doneWork _ _ _ _
  | opensDone name state key output serial c =>
    simp only [workBody]
    split
    · rfl
    · exact keeps_withMachine (fun i r => keeps_applyCompletion _ _ _ _ r) _

theorem growsBy_workBody (step : Nat) (w : Work) : GrowsBy (workBody st fs step w) := by
  intro r
  obtain ⟨s, q⟩ := r
  cases w with
  | reaction a gs c =>
    rcases gs with _ | ⟨_ | ⟨e, g⟩, gs⟩
    · exact Grows.of_lines rfl
    · exact Grows.of_lines rfl
    simp only [workBody, id_bind]
    repeat' split
    all_goals first
      | exact Grows.of_lines rfl
      | exact ⟨#[_], Array.push_eq_append, by simp [State.createKeys]⟩
      | (apply Grows.of_lines; simp)
  | answered c answer cause =>
    simp only [workBody]
    repeat' split
    all_goals first | exact growsBy_answerTo _ _ _ _ _ | exact Grows.of_lines rfl | exact Grows.of_lines (report_lines ..)
  | start name c => exact growsBy_startWork _ _ _
  | receive name received c => exact growsBy_receiveWork _ _ _ _
  | onDone name c => exact growsBy_doneWork _ _ _ _
  | opensDone name state key output serial c =>
    simp only [workBody]
    split
    · exact Grows.of_lines rfl
    · exact growsBy_withMachine (fun i r => growsBy_applyCompletion _ _ _ _ r) _

theorem runWork_fixed (q : Queue) (step : Nat) (w : Work) : (runWork st fs s q step w).1.fixed = s.fixed :=
  keeps_settled step _ (keeps_workBody step w) ⟨s, q⟩

theorem keeps_settleScreen (name : InstanceId) : Keeps (settleScreen st fs name) := by
  intro r
  unfold settleScreen
  split
  · rfl
  · exact keeps_settle _ name _

theorem growsBy_settleScreen (name : InstanceId) : GrowsBy (settleScreen st fs name) := by
  intro r
  unfold settleScreen
  split
  · exact Grows.refl _
  · exact Grows.after (growsBy_settle _ name) rfl rfl

theorem settleScreens_fixed (screens : List InstanceId) (q : Queue) :
    (screens.foldlM (fun r name => settleScreen st fs name r) (⟨refreshScreens st fs s, q⟩ : Processing)).1.fixed =
      s.fixed :=
  (foldlM_keeps (fun n => keeps_settleScreen n) _ _).trans refreshScreens_fixed

theorem settleScreens_grows (screens : List InstanceId) (q : Queue) :
    Grows s (screens.foldlM (fun r name => settleScreen st fs name r) (⟨refreshScreens st fs s, q⟩ : Processing)).1 :=
  refreshScreens_grows.trans (congrArg Fixed.now refreshScreens_fixed)
    (foldlM_grows (fun n => growsBy_settleScreen n) (fun n => keeps_settleScreen n) _ _)

theorem drain_clock (n : Nat) (q : Queue) : (drain st fs n s q).clock = s.clock := by
  induction n generalizing s q with
  | zero =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first | rfl | exact congrArg (fun f : Fixed => (f.commandAnswers, f.now)) (refreshScreens_fixed (fs := fs))
  | succ n ih =>
    have hc : ∀ {t : State}, t.fixed = s.fixed → t.clock = s.clock := fun h =>
      congrArg (fun f : Fixed => (f.commandAnswers, f.now)) h
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | rfl
      | exact hc refreshScreens_fixed
      | exact hc ((report_fixed _).trans rfl)
      | (rw [ih]; first
          | exact hc (runWork_fixed _ _ _)
          | exact hc (keeps_sendEntered _)
          | exact hc (settleScreens_fixed _ _)
          | (rw [processCommand_clock]; rfl))

theorem drain_commandAnswers (n : Nat) (q : Queue) : (drain st fs n s q).commandAnswers = s.commandAnswers :=
  congrArg Prod.fst (drain_clock n q)

theorem runWork_grows (q : Queue) (step : Nat) (w : Work) : Grows s (runWork st fs s q step w).1 :=
  growsBy_settled step _ (growsBy_workBody step w) (keeps_workBody step w) ⟨s, q⟩

theorem drain_grows (n : Nat) (q : Queue) : Grows s (drain st fs n s q) := by
  induction n generalizing s q with
  | zero =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | exact Grows.of_lines rfl
      | exact refreshScreens_grows
  | succ n ih =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | exact Grows.refl _
      | exact Grows.of_lines ((report_lines _).trans rfl)
      | exact refreshScreens_grows
      | exact (growsBy_sendEntered _).trans (congrArg Fixed.now (keeps_sendEntered _)) (ih _)
      | exact (settleScreens_grows _ _).trans (congrArg Fixed.now (settleScreens_fixed _ _)) (ih _)
      | (refine Grows.trans ?_ ?_ (ih _)
         exact (Grows.of_lines rfl).trans rfl (runWork_grows _ _ _)
         exact congrArg Fixed.now (runWork_fixed _ _ _))
      | (refine Grows.trans ?_ ?_ (ih _)
         exact (Grows.of_lines rfl).trans rfl (processCommand_grows _ _ _ _)
         exact congrArg Prod.snd (processCommand_clock _ _ _ _))

theorem drain_keysDistinct (n : Nat) (q : Queue) (h : KeysDistinct s.records) :
    KeysDistinct (drain st fs n s q).records := by
  induction n generalizing s q with
  | zero =>
    have hr : ∀ {t : State}, t.fixed = s.fixed → KeysDistinct t.records := fun {t} e => by
      show KeysDistinct t.fixed.records
      rw [e]
      exact h
    simp only [drain, id_bind]
    repeat' split
    all_goals first | exact h | exact hr (refreshScreens_fixed (fs := fs))
  | succ n ih =>
    have hr : ∀ {t : State}, t.fixed = s.fixed → KeysDistinct t.records := fun {t} e => by
      show KeysDistinct t.fixed.records
      rw [e]
      exact h
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | exact h
      | exact hr refreshScreens_fixed
      | exact hr ((report_fixed _).trans rfl)
      | exact ih _ (hr (runWork_fixed _ _ _))
      | exact ih _ (hr (keeps_sendEntered _))
      | exact ih _ (hr (settleScreens_fixed _ _))
      | exact ih _ (processCommand_keysDistinct _ _ _ _ h)

/-- An answer to a stale own-service command only ends the wait for it, unless it rejects the input (Requester.inputFault). -/
theorem stale_command_answer_ignored (s : State) (q : Queue) (step : Nat) (c : Sent) (serial cause : Nat)
    (answer : Answer) (sent : Queued) (hc : c.serial = some serial) (hq : s.queued.find? (·.serial == serial) = some sent)
    (hs : sent.stale = true) (ha : ∀ reason, answer ≠ .rejected { kind := .invalidInput, reason }) :
    workBody st fs step (.answered c answer cause) ⟨s, q⟩ = ⟨(s.takeQueued serial).1, q⟩ := by
  rcases answer with _ | _ | ⟨kind, reason⟩
  · simp [workBody, State.takeQueued, Requester.rejectedInput?, hc, hq, hs]
  · simp [workBody, State.takeQueued, Requester.rejectedInput?, hc, hq, hs]
  · cases kind
    · exact absurd rfl (ha reason)
    all_goals simp [workBody, State.takeQueued, Requester.rejectedInput?, hc, hq, hs]

/-- A spec service's invalid-input answer to an own-service command is the sender's fault (Requester.inputFault). -/
theorem invalid_input_command_answer_faults_sender (s : State) (q : Queue) (step : Nat) (c : Sent) (cause : Nat)
    (reason : Option String) :
    workBody st fs step (.answered c (.rejected { kind := .invalidInput, reason }) cause) ⟨s, q⟩ =
      let t := match c.serial with
        | some serial => (s.takeQueued serial).1
        | none => s
      ⟨t.report (.fault (c.requester.inputFault st c.activity.ref)), q⟩ := by
  cases h : c.serial <;> simp [workBody, Requester.rejectedInput?, h]

theorem groups_choices_cons {α : Type} (gs : List (List α)) : ∃ cs, Groups.choices gs = gs :: cs := by
  unfold Groups.choices
  split <;> exact ⟨_, rfl⟩

theorem choices_cons (w : Work) : ∃ cs, w.choices = w :: cs := by
  cases w with
  | receive machine gs cause =>
    obtain ⟨cs, h⟩ := groups_choices_cons gs
    exact ⟨cs.map (.receive machine · cause), by simp [Work.choices, h]⟩
  | reaction a gs cause =>
    obtain ⟨cs, h⟩ := groups_choices_cons gs
    exact ⟨cs.map (.reaction a · cause), by simp [Work.choices, h]⟩
  | _ => exact ⟨_, rfl⟩

/-- Without `stepOrder` entries, the queue takes its first task and puts back what the step leaves of it. -/
theorem drain_runs_task_first (fuel : Nat) (q : Queue) (w : Work) (ws : List Work) (hh : s.halted = none)
    (ho : s.stepOrder = []) (hq : q.tasks = w :: ws) :
    drain st fs (fuel + 1) s q =
      let (s₁, step) := s.newStep w.cause
      let r := runWork st fs s₁ ({ q with tasks := ws }.putBack 0 (w.rest step)) step w
      drain st fs fuel r.state r.queue := by
  obtain ⟨cs, hc⟩ := choices_cons w
  cases s; subst ho
  simp_all [drain, Queue.take, Queue.entries, Queue.without]

/-- Without `stepOrder` entries or tasks, the queue takes the first command, with the round joined. -/
theorem drain_processes_command_with_current_records (fuel : Nat) (q : Queue) (c : Sent) (cs : List Sent)
    (hh : s.halted = none) (ho : s.stepOrder = []) (ht : q.tasks = []) (hc : q.commands ++ sortSent q.round = c :: cs)
    (hr : (s.newCommandStep c.cause (st.ref c.requester.sender)).2 = none) :
    drain st fs (fuel + 1) s q =
      let (s₁, step) := (s.newCommandStep c.cause (st.ref c.requester.sender)).1
      let r := processCommand st fs s₁ (st.traceNameOf c.activity.ref) c.input none step
      drain st fs fuel r.1
        { tasks := commandWork st r.1 r.2.2 step ++ [.answered c r.2.1 step], round := [], commands := cs,
          entered := q.entered } := by
  cases s; subst ho
  simp_all [drain, Queue.take, Queue.entries, Queue.without, Ready.name]

/-- A ready work or command that the next `stepOrder` entry names runs before the others, whatever their order. -/
theorem take_named (q : Queue) (name : Ready → StepName) (named : StepName) (rest : List StepName) (r : Ready) (i : Nat)
    (h : q.entries.find? (name ·.1 == named) = some (r, i)) :
    q.take name (named :: rest) = .ok (some (r, i, q.without i, rest)) := by
  simp only [Queue.take]
  generalize q.entries = entries at h ⊢
  cases entries with
  | nil => simp at h
  | cons x xs => dsimp only; rw [h]

theorem take_unnamed (q : Queue) (name : Ready → StepName) (named : StepName) (rest : List StepName) (e : Ready × Nat)
    (es : List (Ready × Nat)) (hr : q.entries = e :: es) (h : q.entries.find? (name ·.1 == named) = none)
    (hd : named.isDeadline = false) :
    q.take name (named :: rest) = .error (.unreadyStep named (q.entries.map (name ·.1))) := by
  simp only [Queue.take]
  rw [hr] at h ⊢
  dsimp only
  rw [h]
  simp [hd]

/-- An entry that names a deadline waits for its tie: the queue takes its first ready entry and keeps the entry. -/
theorem take_deadline (q : Queue) (name : Ready → StepName) (named : StepName) (rest : List StepName) (r : Ready)
    (i : Nat) (es : List (Ready × Nat)) (hr : q.entries = (r, i) :: es) (h : q.entries.find? (name ·.1 == named) = none)
    (hd : named.isDeadline = true) :
    q.take name (named :: rest) = .ok (some (r, i, q.without i, named :: rest)) := by
  simp only [Queue.take]
  rw [hr] at h ⊢
  dsimp only
  rw [h]
  simp [hd]

theorem find_distinct_name {α : Type} (key : α → StepName) :
    ∀ (l : List α) (x : α), l.Pairwise (key · ≠ key ·) → x ∈ l → l.find? (key · == key x) = some x
  | [], _, _, hx => by simp at hx
  | y :: ys, x, hp, hx => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne : key y ≠ key x := hp.1 x hx
      simp [hne, find_distinct_name key ys x hp.2 hx]

/-- When the ready entries have distinct names, naming an entry takes exactly that entry. -/
theorem take_reaches (q : Queue) (name : Ready → StepName) (rest : List StepName) (r : Ready) (i : Nat)
    (hd : q.entries.Pairwise (name ·.1 ≠ name ·.1)) (hx : (r, i) ∈ q.entries) :
    q.take name (name r :: rest) = .ok (some (r, i, q.without i, rest)) :=
  take_named q name _ rest r i (find_distinct_name (name ·.1) q.entries (r, i) hd hx)

theorem newCommandStep_exceeded_halts (cause : Nat) (sender : Spec.Ref) (exceeded : Fault)
    (h : (s.newCommandStep cause sender).2 = some exceeded) : exceeded.halts = true := by
  unfold State.newCommandStep at h
  dsimp only at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

theorem drain_halts_on_command_runaway (fuel : Nat) (q : Queue) (c : Sent) (cs : List Sent) (exceeded : Fault)
    (hh : s.halted = none) (ho : s.stepOrder = []) (ht : q.tasks = []) (hc : q.commands ++ sortSent q.round = c :: cs)
    (hr : (s.newCommandStep c.cause (st.ref c.requester.sender)).2 = some exceeded) :
    drain st fs (fuel + 1) s q =
      (s.newCommandStep c.cause (st.ref c.requester.sender)).1.1.halt (Finding.fault exceeded) := by
  have hx := newCommandStep_exceeded_halts _ _ _ hr
  cases s; subst ho
  simp_all [drain, Queue.take, Queue.entries, Queue.without, State.report]

theorem drain_at_work_limit (q : Queue) (hh : s.halted = none) :
    drain st fs 0 s q =
      if !q.isEmpty then s.halt (Finding.fault (.exceededMessageWork Limit.messageWork.max)) else
      let s₁ := refreshScreens st fs s
      if s₁.halted.isNone && !(shownChanged s s₁).isEmpty then s₁.halt (Finding.fault (.exceededMessageWork Limit.messageWork.max)) else s₁ := by
  simp only [drain, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind, State.report]
  rfl

theorem doneWork_at_selection_limit (step : Nat) (name : InstanceId) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) :
    doneWork fs st step name 0 r =
      match i.awaitingOnDone with
      | some (_ :: _) => ⟨r.state.halt (Finding.fault (.exceededOnDoneSelections (st.ref i.chart.name) Limit.onDoneSelections.max)), r.queue⟩
      | _ => ⟨r.state.setMachine name fun i => { i with awaitingOnDone := none }, r.queue⟩ := by
  simp only [doneWork, hi]
  rcases h : i.awaitingOnDone with _ | _ | ⟨_, _⟩ <;> simp [Processing.report, State.report, Fault.halts]

theorem shows_rejection_reported (name : InstanceId) (slot : String) (answer : Answer) (r : Processing) :
    (showAnswer st name slot answer r).state.violations = r.state.violations ++
      (match answer with
       | .rejected rj =>
         if RejectionKind.byCaller rj.kind then [(Finding.fault (.rejectedShows (st.ref name.chart) slot rj))]
         else []
       | _ => []) ∧
      (showAnswer st name slot answer r).state.halted = r.state.halted := by
  cases answer with
  | rejected rj => cases h : RejectionKind.byCaller rj.kind <;> simp [showAnswer, h, State.report, State.violate, Fault.halts]
  | _ => simp [showAnswer, State.setShown, State.setMachine]

theorem queued_work_keeps_records (q : Queue) (step : Nat) (w : Work) :
    (runWork st fs s q step w).state.records = s.records :=
  congrArg Fixed.records (runWork_fixed q step w)

theorem reaction_reads_current_records (q : Queue) (step : Nat) (a : Automation) (e : Emit) (g : List Emit)
    (gs : List (List Emit)) (cause : Nat) :
    ∃ k : Except Issue (Option Value × List String) → Processing,
      runWork st fs s q step (.reaction a ((e :: g) :: gs) cause) =
        k (fs.react a.name e.payload s.records s.now s.nextKeys) :=
  ⟨fun x => runWork st { fs with react := fun _ _ _ _ _ => x } s q step (.reaction a ((e :: g) :: gs) cause), by
    simp only [runWork, Work.settledMachine?, settled, workBody, id_bind]⟩

theorem drain_keeps_now (n : Nat) (q : Queue) : (drain st fs n s q).now = s.now :=
  congrArg Prod.snd (drain_clock n q)

theorem drain_answers (n : Nat) (q : Queue) : (drain st fs n s q).answers = s.answers := by
  induction n generalizing s q with
  | zero =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first | rfl | exact congrArg Fixed.answers (refreshScreens_fixed (fs := fs))
  | succ n ih =>
    have hm : ∀ {t : State}, t.fixed = s.fixed → t.answers = s.answers := fun e => congrArg Fixed.answers e
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | rfl
      | exact hm refreshScreens_fixed
      | exact hm ((report_fixed _).trans rfl)
      | (rw [ih]; first
          | exact hm (runWork_fixed _ _ _)
          | exact hm (keeps_sendEntered _)
          | exact hm (settleScreens_fixed _ _)
          | (rw [processCommand_answers]; rfl))

end Tazuna.Thm.Service.Chart.Macrostep
