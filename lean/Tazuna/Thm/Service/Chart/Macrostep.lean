import Tazuna.Service.Chart.Macrostep
import Tazuna.Thm.Service.Chart.Always
import Tazuna.Thm.Service.Screen.Subscription
import Tazuna.Thm.Service.Automation
import Tazuna.Thm.Service.Command
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Service.Chart.Macrostep

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Always Tazuna.Thm.Service.Chart.Deadline Tazuna.Thm.Service.Chart.Done Tazuna.Thm.Service.Chart.Exit Tazuna.Thm.Service.Chart.Map Tazuna.Thm.Service.Chart.Microstep Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Chart.Request Tazuna.Thm.Service.Functions Tazuna.Thm.Service.Screen.Subscription Tazuna.Thm.Service.Automation Tazuna.Thm.Service.Command Tazuna.Thm.Service.Integrity Tazuna.Thm.Service.Records Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem settled_some (step : Nat) (name : InstanceId) (f : Processing → Id Processing) (r : Processing) :
    settled fs st step (some name) f r = settleAround fs st step (name.owner) f r := rfl

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
  rfl

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
  let r' : Processing := ⟨r.state.setMachine name ({ · with startStep := some step }), r.queue⟩
  exact (Grows.of_lines (s' := r'.state) rfl).trans rfl ((growsBy_enter step name _ r').trans
    ((keeps_enter step name _).now r') (growsBy_unlessHalted (growsBy_settle step name) _))

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

@[guarantee] theorem stopped_machine_takes_no_event (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) (hc : i.closed = true) :
    dispatch fs st step name key payload r = r := by
  simp [dispatch, hi, hc]

@[guarantee] theorem untaken_operation_changes_nothing (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) (i : Instance)
    (leaves : List (InstanceId × Option String)) (hh : r.state.halted = none) (hi : r.state.machine? name = some i)
    (hl : eventLeaves fs st r.state i payload = .ok leaves)
    (hs : select fs st r.state i (.on key) (.payload payload) leaves = .ok []) :
    dispatch fs st step name key payload r = r := by
  unfold dispatch
  simp only [hi, Processing.halted, hh, Option.isSome_none, Bool.false_or]
  split
  · rfl
  · simp only [id_bind]; rw [hl]; simp only; rw [hs]; rfl

@[guarantee] theorem stale_answer_ignored (step : Nat) (p : Pending) (answer : Answer) (r : Processing) (waiting : Pending)
    (hw : r.state.pending.find? (·.id == p.id) = some waiting) (hs : waiting.stale = true) :
    deliverAnswer fs st step p answer r = ⟨(r.state.answered p).1, r.queue⟩ := by
  simp [deliverAnswer, State.answered, hw, hs]

theorem keeps_workBody (step : Nat) (w : Work) : Keeps (workBody st fs step w) := by
  intro r
  obtain ⟨s, q⟩ := r
  cases w with
  | reaction a gs d c =>
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
  | receive name received d c => exact keeps_receiveWork _ _ _ _
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
  | reaction a gs d c =>
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
  | receive name received d c => exact growsBy_receiveWork _ _ _ _
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

/-- An answer to a stale own-service command only ends the wait for it, unless it rejects the input (rejectedInput?). -/
@[guarantee] theorem stale_command_answer_ignored (s : State) (q : Queue) (step : Nat) (c : Sent) (serial cause : Nat)
    (answer : Answer) (sent : Queued) (hc : c.serial = some serial) (hq : s.queued.find? (·.serial == serial) = some sent)
    (hs : sent.stale = true) (ha : ∀ reason, answer ≠ .rejected { kind := .invalidInput, reason }) :
    workBody st fs step (.answered c answer cause) ⟨s, q⟩ = ⟨(s.takeQueued serial).1, q⟩ := by
  rcases answer with _ | _ | ⟨kind, reason⟩
  · simp [workBody, State.takeQueued, rejectedInput?, hc, hq, hs]; split <;> rfl
  · simp [workBody, State.takeQueued, rejectedInput?, hc, hq, hs]; split <;> rfl
  · cases kind
    · exact absurd rfl (ha reason)
    all_goals simp [workBody, State.takeQueued, rejectedInput?, hc, hq, hs]; split <;> rfl
@[guarantee] theorem drain_keeps_now (n : Nat) (q : Queue) : (drain st fs n s q).now = s.now :=
  congrArg Prod.snd (drain_clock n q)


/-- A message whose work is still queued after Limit.messageWork steps halts with exceededMessageWork. -/
@[guarantee] theorem message_work_limit_halts (q : Queue) (hs : s.halted = none) (hq : q.isEmpty = false) :
    (drain st fs 0 s q).halted = some (.fault (.exceededMessageWork Limit.messageWork.max)) := by
  simp only [drain, hs, Option.isSome_none, Bool.false_eq_true, ite_false, hq, Bool.not_false, ite_true]
  exact report_halted _ rfl

theorem newCommandStep_halts (cause : Nat) (sender : Spec.Ref) (f : Fault)
    (h : (s.newCommandStep cause sender).2 = some f) : f.halts = true := by
  simp only [State.newCommandStep] at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/--
A command whose chain of own-service commands is deeper than Limit.commandDepth, or that is one too many of its message
(Limit.messageCommands), halts with the Fault of that limit.
-/
@[guarantee] theorem command_limit_halts (n : Nat) (q rest : Queue) (c : Sent) (i : Nat) (order : List StepName)
    (f : Fault) (hs : s.halted = none) (ht : q.take Ready.name s.stepOrder = .ok (some (.command c, i, rest, order)))
    (hf : ({ s with stepOrder := order }.newCommandStep c.cause (st.ref c.requester.sender)).2 = some f) :
    (drain st fs (n + 1) s q).halted = some (.fault f) := by
  have hh := newCommandStep_halts _ _ f hf
  simp only [hs] at hf
  simp only [drain, hs, Option.isSome_none, Bool.false_eq_true, ite_false, ht, hf]
  exact report_halted _ hh

/-- An onDone work that still has selections after Limit.onDoneSelections halts with exceededOnDoneSelections. -/
@[guarantee] theorem done_selections_limit_halts (step : Nat) (name : InstanceId) (r : Processing) (i : Instance)
    (n : String) (rest : List String) (hi : r.state.machine? name = some i) (ha : i.awaitingOnDone = some (n :: rest)) :
    (doneWork fs st step name 0 r).state.halted =
      some (.fault (.exceededOnDoneSelections (st.ref i.chart.name) Limit.onDoneSelections.max)) := by
  simp only [doneWork, hi, ha, Processing.report]
  exact report_halted _ rfl

end Tazuna.Thm.Service.Chart.Macrostep
