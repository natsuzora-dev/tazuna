import Tazuna.Semantics.Chart.Macrostep
import Tazuna.Thm.Semantics.Chart.Always
import Tazuna.Thm.Semantics.Screen.Subscription
import Tazuna.Thm.Semantics.Service.Automation
import Tazuna.Thm.Semantics.Service.Command

namespace Tazuna.Thm.Semantics.Chart.Macrostep

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic Tazuna.Thm.Semantics.Chart.Always Tazuna.Thm.Semantics.Chart.Deadline Tazuna.Thm.Semantics.Chart.Done Tazuna.Thm.Semantics.Chart.Exit Tazuna.Thm.Semantics.Chart.Map Tazuna.Thm.Semantics.Chart.Microstep Tazuna.Thm.Semantics.Chart.Queue Tazuna.Thm.Semantics.Chart.Request Tazuna.Thm.Semantics.Functions Tazuna.Thm.Semantics.Screen.Subscription Tazuna.Thm.Semantics.Service.Automation Tazuna.Thm.Semantics.Service.Command Tazuna.Thm.Semantics.Service.Integrity Tazuna.Thm.Semantics.Service.Records Tazuna.Thm.Semantics.State Tazuna.Thm.Syntax.Shape Tazuna.Thm.Semantics.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem settled_some (step : Nat) (name : String) (f : Processing → Id Processing) (r : Processing) :
    settled fs st step (some name) f r = settleAround fs st step (r.state.ownerOf name) f r := rfl

theorem runWork_settles_around (q : Queue) (step : Nat) (w : Work) (name : String) (hw : w.settledMachine? = some name) :
    runWork st fs s q step w = settleAround fs st step (s.ownerOf name) (workBody st fs step w) ⟨s, q⟩ := by
  rw [runWork, hw, settled_some]

theorem receive_settles (q : Queue) (step : Nat) (name : String) (cause : Nat) :
    runWork st fs s q step (.receive name [] cause) =
      settleFrom fs st step (s.ownerOf name) Limit.alwaysRounds.max ⟨s, q⟩ := by
  have hw : workBody st fs step (.receive name [] cause) = pure := funext fun _ => rfl
  rw [runWork_settles_around q step _ name rfl, hw]
  simp only [settleAround, id_bind]
  rw [unlessHalted_pure, settleFrom_idem]

theorem receive_settles_before_each_event (step : Nat) (name key : String) (payload : Value)
    (rest : List (String × Value)) (r : Processing) :
    receiveWork fs st step name ((key, payload) :: rest) r =
      receiveWork fs st step name rest (dispatch fs st step name key payload (settle fs st step name r)) := rfl

theorem records_change_settles (s : State) (emits : List Emit) (cause : Nat) (i : Instance) (hm : i ∈ s.machines)
    (hc : i.closed = false) :
    ∃ received, Work.receive i.resource received cause ∈ reactions st s emits true cause := by
  refine ⟨emits.flatMap fun e => (i.chart.receives.filter (·.2 == e.event)).map fun r => (r.1, e.payload),
    List.mem_append_left _ (List.mem_filterMap.mpr ⟨i, hm, ?_⟩)⟩
  simp [machineWork, hc]


theorem keeps_settle (step : Nat) (name : String) : Keeps (settle fs st step name) :=
  fun r => settleFrom_fixed step _ _ r

theorem keeps_settleAround (step : Nat) (owner : String) {f : Processing → Id Processing} (hf : Keeps f) :
    Keeps (settleAround fs st step owner f) := by
  intro r
  simp only [settleAround, id_bind]
  rw [settleFrom_fixed, keeps_unlessHalted hf, settleFrom_fixed]

theorem keeps_settled (step : Nat) (name : Option String) {f : Processing → Id Processing} (hf : Keeps f) :
    Keeps (settled fs st step name f) := by
  intro r
  cases name with
  | none => exact hf r
  | some n => rw [settled_some]; exact keeps_settleAround step _ hf r

theorem keeps_applyCompletion (step : Nat) (name : String) (ts : List Transition) (extra : Extra) :
    Keeps (applyCompletion fs st step name ts extra) := by
  unfold applyCompletion
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report]
  · rfl
  · exact keeps_microstep step name _ _ r

theorem keeps_handle (step : Nat) (name state : String) (a : Activity) (answer : Answer) :
    Keeps (handle fs st step name state a answer) := by
  unfold handle
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · split <;> exact keeps_applyCompletion _ _ _ _ r

theorem keeps_dispatch (step : Nat) (name key : String) (payload : Value) :
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

theorem keeps_receiveWork (step : Nat) (name : String) (received : List (String × Value)) :
    Keeps (receiveWork fs st step name received) :=
  foldlM_keeps (g := fun (x : String × Value) r => dispatch fs st step name x.1 x.2 (settle fs st step name r))
    (fun x r => (keeps_dispatch step name x.1 x.2 _).trans (keeps_settle step name r)) received

theorem keeps_done (step : Nat) (name n : String) : Keeps (done fs st step name n) := by
  unfold done
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · exact keeps_applyCompletion _ _ _ _ r

theorem keeps_doneWork (step : Nat) (name : String) (fuel : Nat) : Keeps (doneWork fs st step name fuel) := by
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

theorem keeps_startWork (step : Nat) (name : String) : Keeps (startWork fs st step name) := by
  unfold startWork
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  rw [keeps_unlessHalted (keeps_settle step name), keeps_enter]

theorem showAnswer_fixed (name slot : String) (answer : Answer) (r : Processing) :
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

theorem growsBy_settle (step : Nat) (name : String) : GrowsBy (settle fs st step name) :=
  fun r => settleFrom_grows step _ _ r

theorem growsBy_settleAround (step : Nat) (owner : String) {f : Processing → Id Processing} (hf : GrowsBy f)
    (hk : Keeps f) : GrowsBy (settleAround fs st step owner f) := by
  intro r
  simp only [settleAround, id_bind]
  exact (settleFrom_grows step owner _ r).trans (congrArg Fixed.now (settleFrom_fixed step owner _ r))
    ((growsBy_unlessHalted hf _).trans ((keeps_unlessHalted hk).now _) (settleFrom_grows step owner _ _))

theorem growsBy_settled (step : Nat) (name : Option String) {f : Processing → Id Processing} (hf : GrowsBy f)
    (hk : Keeps f) : GrowsBy (settled fs st step name f) := by
  intro r
  cases name with
  | none => exact hf r
  | some n => rw [settled_some]; exact growsBy_settleAround step _ hf hk r

theorem growsBy_applyCompletion (step : Nat) (name : String) (ts : List Transition) (extra : Extra) :
    GrowsBy (applyCompletion fs st step name ts extra) := by
  unfold applyCompletion
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  split
  · exact Grows.of_lines (report_lines ..)
  · exact Grows.refl _
  · exact growsBy_microstep step name _ _ r

theorem growsBy_handle (step : Nat) (name state : String) (a : Activity) (answer : Answer) :
    GrowsBy (handle fs st step name state a answer) := by
  unfold handle
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · split <;> exact growsBy_applyCompletion _ _ _ _ r

theorem growsBy_dispatch (step : Nat) (name key : String) (payload : Value) :
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

theorem growsBy_receiveWork (step : Nat) (name : String) (received : List (String × Value)) :
    GrowsBy (receiveWork fs st step name received) :=
  foldlM_grows (g := fun (x : String × Value) r => dispatch fs st step name x.1 x.2 (settle fs st step name r))
    (fun x r => Grows.comp (growsBy_settle step name) (keeps_settle step name) (growsBy_dispatch step name x.1 x.2) r)
    (fun x r => (keeps_dispatch step name x.1 x.2 _).trans (keeps_settle step name r)) received

theorem growsBy_done (step : Nat) (name n : String) : GrowsBy (done fs st step name n) := by
  unfold done
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · exact growsBy_applyCompletion _ _ _ _ r

theorem growsBy_doneWork (step : Nat) (name : String) (fuel : Nat) : GrowsBy (doneWork fs st step name fuel) := by
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

theorem growsBy_startWork (step : Nat) (name : String) : GrowsBy (startWork fs st step name) := by
  unfold startWork
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  exact (growsBy_enter step name _ r).trans ((keeps_enter step name _).now r)
    (growsBy_unlessHalted (growsBy_settle step name) _)

theorem showAnswer_grows (name slot : String) (answer : Answer) (r : Processing) :
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

theorem growsBy_deliverAnswer (step : Nat) (p : Pending) (answer : Answer) :
    GrowsBy (deliverAnswer fs st step p answer) := by
  intro r
  have hl := answered_lines (s := r.state) p
  have hn := congrArg Fixed.now (answered_fixed (s := r.state) p)
  unfold deliverAnswer
  rcases h : r.state.answered p with ⟨s', live⟩
  rw [h] at hl hn
  cases live
  · exact Grows.of_lines hl
  · exact (Grows.of_lines hl).trans hn (growsBy_answerTo _ _ _ _ _)

theorem start_settles (step : Nat) (name : String) (r : Processing) (i : Instance) (hh : r.state.halted = none)
    (hi : r.state.machine? name = some i) :
    startWork fs st step name r = unlessHalted (settle fs st step name) (enter fs st step name [i.chart.initial] r) := by
  simp [startWork, withMachine, Processing.halted, hh, hi]

theorem completion_microstep (step : Nat) (name : String) (ts : List Transition) (extra : Extra) (r : Processing)
    (i : Instance) (t : Transition) (hh : r.state.halted = none) (hi : r.state.machine? name = some i)
    (ht : choose fs st r.state i extra ts = .ok (some t)) :
    applyCompletion fs st step name ts extra r = microstep fs st step name [(name, t)] extra r := by
  simp [applyCompletion, withMachine, Processing.halted, hh, hi, ht]

theorem subscription_answer_reaches_screen (step : Nat) (p : Pending) (name slot : String) (answer : Answer)
    (r : Processing) (waiting : Pending) (hw : r.state.pending.find? (·.id == p.id) = some waiting)
    (hs : waiting.stale = false) (hp : p.requester = .slot name slot) :
    deliverAnswer fs st step p answer r = showAnswer st name slot answer ⟨(r.state.answered p).1, r.queue⟩ := by
  simp [deliverAnswer, answerTo, State.answered, hw, hs, hp]

theorem done_work_takes_first (step : Nat) (name n : String) (rest : List String) (fuel : Nat) (r : Processing)
    (i : Instance) (hh : r.state.halted = none) (hi : r.state.machine? name = some i)
    (hw : i.awaitingOnDone = some (n :: rest)) :
    doneWork fs st step name (fuel + 1) r =
      doneWork fs st step name fuel (done fs st step name n
        (settle fs st step name ⟨r.state.setMachine name fun i => { i with awaitingOnDone := some rest }, r.queue⟩)) := by
  simp [doneWork, Processing.halted, hh, hi, hw]

theorem stopped_machine_takes_no_event (step : Nat) (name key : String) (payload : Value) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) (hc : i.closed = true) :
    dispatch fs st step name key payload r = r := by
  simp [dispatch, hi, hc]

theorem dispatch_takes_one_microstep (step : Nat) (name key : String) (payload : Value) (r : Processing) (i : Instance)
    (leaves : List (String × Option String)) (chosen : List (String × Transition)) (hh : r.state.halted = none)
    (hi : r.state.machine? name = some i) (hc : i.closed = false) (hl : eventLeaves fs st r.state i payload = .ok leaves)
    (hs : select fs st r.state i ["on", key] (.payload payload) leaves = .ok chosen) (hn : chosen ≠ []) :
    dispatch fs st step name key payload r = microstep fs st step name chosen (.payload payload) r := by
  unfold dispatch
  cases chosen with
  | nil => exact absurd rfl hn
  | cons t ts =>
    simp only [hi, Processing.halted, hh, hc, Option.isSome_none, Bool.or_false, Bool.false_eq_true, ↓reduceIte, id_bind]
    rw [hl]
    simp only
    rw [hs]

theorem answer_after_exit_ignored (step : Nat) (name state : String) (a : Activity) (answer : Answer) (r : Processing)
    (i : Instance) (hi : r.state.machine? name = some i) (hn : i.isIn state = false) :
    handle fs st step name state a answer r = r := by
  unfold handle withMachine
  split
  · rfl
  · simp [hi, hn]

theorem accepted_output_reaches_onAccepted (step : Nat) (name state : String) (a : Activity) (o : Value) (r : Processing)
    (i : Instance) (hh : r.state.halted = none) (hi : r.state.machine? name = some i) (hc : i.closed = false)
    (hin : i.isIn state = true) :
    handle fs st step name state a (.accepted (some o)) r =
      applyCompletion fs st step name (i.chart.transitionsAt (some state) [a.keyword, a.key, successAnswer a]) (.output o)
        r := by
  simp [handle, withMachine, Processing.halted, hh, hi, hc, hin]

theorem rejection_kind_reaches_guard (step : Nat) (name state : String) (a : Activity) (r : Rejection) (run : Processing)
    (i : Instance) (hh : run.state.halted = none) (hi : run.state.machine? name = some i) (hc : i.closed = false)
    (hin : i.isIn state = true) :
    handle fs st step name state a (.rejected r) run =
      applyCompletion fs st step name (i.chart.transitionsAt (some state) [a.keyword, a.key, "onRejected"]) (.rejection r)
        run := by
  simp [handle, withMachine, Processing.halted, hh, hi, hc, hin]

theorem untaken_operation_changes_nothing (step : Nat) (name key : String) (payload : Value) (r : Processing) (i : Instance)
    (leaves : List (String × Option String)) (hh : r.state.halted = none) (hi : r.state.machine? name = some i)
    (hl : eventLeaves fs st r.state i payload = .ok leaves)
    (hs : select fs st r.state i ["on", key] (.payload payload) leaves = .ok []) :
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

theorem opens_done_ignored_when_stale (q : Queue) (step : Nat) (name state key : String) (output : Value)
    (serial cause : Nat) (waiting : Queued) (hq : s.queued.find? (·.serial == serial) = some waiting)
    (hs : waiting.stale = true) :
    workBody st fs step (.opensDone name state key output serial cause) ⟨s, q⟩ = ⟨(s.takeQueued serial).1, q⟩ := by
  simp [workBody, State.takeQueued, hq, hs]

theorem opens_done_taken_when_live (q : Queue) (step : Nat) (name state key : String) (output : Value)
    (serial cause : Nat) (waiting : Queued) (hq : s.queued.find? (·.serial == serial) = some waiting)
    (hs : waiting.stale = false) :
    workBody st fs step (.opensDone name state key output serial cause) ⟨s, q⟩ =
      withMachine name (fun i r =>
        applyCompletion fs st step name (i.chart.transitionsAt (some state) ["opens", key, "onDone"]) (.output output) r)
        ⟨(s.takeQueued serial).1, q⟩ := by
  simp [workBody, State.takeQueued, hq, hs]

theorem keeps_workBody (step : Nat) (w : Work) : Keeps (workBody st fs step w) := by
  intro r
  obtain ⟨s, q⟩ := r
  cases w with
  | reaction a e c =>
    simp only [workBody, id_bind]
    repeat' split
    all_goals first | rfl | simp [State.createKeys, State.fixed, report_eq]
  | answered c answer cause =>
    simp only [workBody]
    split
    all_goals split
    all_goals first | exact keeps_answerTo _ _ _ _ _ | rfl
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
  | reaction a e c =>
    simp only [workBody, id_bind]
    repeat' split
    all_goals first
      | exact Grows.of_lines rfl
      | exact ⟨#[_], Array.push_eq_append, by simp [State.createKeys]⟩
      | (apply Grows.of_lines; simp [State.createKeys])
  | answered c answer cause =>
    simp only [workBody]
    split
    all_goals split
    all_goals first | exact growsBy_answerTo _ _ _ _ _ | exact Grows.of_lines rfl
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

theorem runWork_commandAnswers (q : Queue) (step : Nat) (w : Work) :
    (runWork st fs s q step w).1.commandAnswers = s.commandAnswers := congrArg Fixed.commandAnswers (runWork_fixed q step w)

theorem keeps_settleScreen (name : String) : Keeps (settleScreen st fs name) := by
  intro r
  unfold settleScreen
  split
  · rfl
  · exact keeps_settle _ name _

theorem growsBy_settleScreen (name : String) : GrowsBy (settleScreen st fs name) := by
  intro r
  unfold settleScreen
  split
  · exact Grows.refl _
  · exact Grows.after (growsBy_settle _ name) rfl rfl

theorem settleScreens_fixed (screens : List String) (q : Queue) :
    (screens.foldlM (fun r name => settleScreen st fs name r) (⟨refreshScreens st fs s, q⟩ : Processing)).1.fixed =
      s.fixed :=
  (foldlM_keeps (fun n => keeps_settleScreen n) _ _).trans refreshScreens_fixed

theorem settleScreens_grows (screens : List String) (q : Queue) :
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

theorem runWork_records (q : Queue) (step : Nat) (w : Work) : (runWork st fs s q step w).state.records = s.records :=
  congrArg Fixed.records (runWork_fixed q step w)

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

theorem stale_command_answer_ignored (s : State) (q : Queue) (step : Nat) (c : Sent) (serial cause : Nat)
    (answer : Answer) (sent : Queued) (hc : c.serial = some serial) (hq : s.queued.find? (·.serial == serial) = some sent)
    (hs : sent.stale = true) :
    workBody st fs step (.answered c answer cause) ⟨s, q⟩ = ⟨(s.takeQueued serial).1, q⟩ := by
  simp [workBody, State.takeQueued, hc, hq, hs]

theorem automation_command_queued (q : Queue) (step : Nat) (a : Automation) (e : Emit) (cause : Nat) (raw input : Value)
    (keys : List String) (hr : fs.react a.name e.payload s.records s.now s.keyCounts = .ok (some raw, keys))
    (hn : fs.normalize (.input a.sends.target) (st.sorted (.input a.sends.target) raw) = .ok (some input))
    (ho : a.sends.own = true) :
    runWork st fs s q step (.reaction a e cause) =
      ⟨s.createKeys keys,
        { q with round := q.round ++ [{ order := a.order, requester := .automation a.name, activity := a.sends,
                                        serial := none, input, cause := step }] }⟩ := by
  simp only [runWork, Work.settledMachine?, settled, workBody, id_bind]
  rw [hr]
  simp only [hn, ho]
  rfl

theorem automation_request_sent (q : Queue) (step : Nat) (a : Automation) (e : Emit) (cause : Nat) (raw input : Value)
    (keys : List String) (hr : fs.react a.name e.payload s.records s.now s.keyCounts = .ok (some raw, keys))
    (hn : fs.normalize (.input a.sends.target) (st.sorted (.input a.sends.target) raw) = .ok (some input))
    (ho : a.sends.own = false) :
    runWork st fs s q step (.reaction a e cause) =
      ⟨(s.createKeys keys).await (.command a.sends.target input) (.automation a.name) a.sends input, q⟩ := by
  simp only [runWork, Work.settledMachine?, settled, workBody, id_bind]
  rw [hr]
  simp only [hn, ho]
  rfl

theorem automation_answer_delivered (step : Nat) (p : Pending) (a : String) (answer : Answer) (r : Processing)
    (waiting : Pending) (hw : r.state.pending.find? (·.id == p.id) = some waiting) (hs : waiting.stale = false)
    (ha : p.requester = .automation a) :
    deliverAnswer fs st step p answer r = ⟨automationAnswer st a answer (r.state.answered p).1, r.queue⟩ := by
  simp [deliverAnswer, answerTo, State.answered, hw, hs, ha]

/-- Without `stepOrder` entries, the queue takes its first task. -/
theorem drain_runs_task_first (fuel : Nat) (q : Queue) (w : Work) (ws : List Work) (hh : s.halted = none)
    (ho : s.stepOrder = []) (hq : q.tasks = w :: ws) :
    drain st fs (fuel + 1) s q =
      let (s₁, step) := s.newStep w.cause
      let r := runWork st fs s₁ { q with tasks := ws } step w
      drain st fs fuel r.state r.queue := by
  cases s; subst ho
  simp_all [drain, Queue.take]

/-- Without `stepOrder` entries or tasks, the queue takes the first command, with the round joined. -/
theorem drain_processes_command_with_current_records (fuel : Nat) (q : Queue) (c : Sent) (cs : List Sent)
    (hh : s.halted = none) (ho : s.stepOrder = []) (ht : q.tasks = []) (hc : q.commands ++ sortSent q.round = c :: cs)
    (hr : (s.newCommandStep c.cause (st.ref (s.senderOf c.requester))).2 = none) :
    drain st fs (fuel + 1) s q =
      let (s₁, step) := (s.newCommandStep c.cause (st.ref (s.senderOf c.requester))).1
      let r := processCommand st fs s₁ c.activity.target c.input none step
      drain st fs fuel r.1
        { tasks := commandWork st r.1 r.2.2 step ++ [.answered c r.2.1 step], round := [], commands := cs,
          entered := q.entered } := by
  cases s; subst ho
  simp_all [drain, Queue.take, State.readyName]

theorem drain_sends_entered_when_idle (fuel : Nat) (q : Queue) (hh : s.halted = none) (ht : q.tasks = [])
    (hc : q.commands ++ sortSent q.round = []) (he : q.entered.isEmpty = false) :
    drain st fs (fuel + 1) s q = drain st fs fuel (sendEntered fs st ⟨s, q⟩).state (sendEntered fs st ⟨s, q⟩).queue := by
  cases ho : s.stepOrder <;> simp [drain, hh, Queue.take, Queue.ready, ht, hc, he, ho]

theorem drain_refreshes_when_idle (fuel : Nat) (q : Queue) (hh : s.halted = none) (ht : q.tasks = [])
    (hc : q.commands ++ sortSent q.round = []) (he : q.entered.isEmpty = true) :
    drain st fs (fuel + 1) s q =
      let s₁ := refreshScreens st fs s
      if (shownChanged s s₁).isEmpty then s₁ else
      let r := (shownChanged s s₁).foldlM (m := Id) (fun r name => settleScreen st fs name r) ⟨s₁, q⟩
      drain st fs fuel r.state r.queue := by
  cases ho : s.stepOrder <;> simp [drain, hh, Queue.take, Queue.ready, ht, hc, he, ho]

/-- A ready work or command that the next `stepOrder` entry names runs before the others, whatever their order. -/
theorem take_named (q : Queue) (name : Ready → StepName) (named : StepName) (rest : List StepName) (r : Ready) (i : Nat)
    (h : q.ready.zipIdx.find? (name ·.1 == named) = some (r, i)) :
    q.take name (named :: rest) = .ok (some (r, q.without i, rest)) := by
  simp only [Queue.take]
  generalize q.ready = ready at h ⊢
  cases ready with
  | nil => simp at h
  | cons x xs => dsimp only; rw [h]

theorem take_unnamed (q : Queue) (name : Ready → StepName) (named : StepName) (rest : List StepName) (r : Ready)
    (rs : List Ready) (hr : q.ready = r :: rs) (h : q.ready.zipIdx.find? (name ·.1 == named) = none) :
    q.take name (named :: rest) = .error (.stepNotNext named (q.ready.map name)) := by
  simp only [Queue.take]
  rw [hr] at h ⊢
  dsimp only
  rw [h]

theorem settleScreen_settles (name : String) (r : Processing) (hh : r.state.halted = none) :
    settleScreen st fs name r =
      let (s₁, step) := r.state.newStep none (barrier := true)
      settle fs st step name ⟨s₁, r.queue⟩ := by
  simp [settleScreen, Processing.halted, hh]

theorem newCommandStep_exceeded_halts (cause : Nat) (sender : Syntax.Ref) (exceeded : Fault)
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
    (hr : (s.newCommandStep c.cause (st.ref (s.senderOf c.requester))).2 = some exceeded) :
    drain st fs (fuel + 1) s q =
      (s.newCommandStep c.cause (st.ref (s.senderOf c.requester))).1.1.halt (Finding.fault exceeded).toViolation := by
  have hx := newCommandStep_exceeded_halts _ _ _ hr
  cases s; subst ho
  simp_all [drain, Queue.take, State.report]

theorem drain_at_work_limit (q : Queue) (hh : s.halted = none) :
    drain st fs 0 s q =
      if !q.isEmpty then s.halt (Finding.fault .messageWork).toViolation else
      let s₁ := refreshScreens st fs s
      if s₁.halted.isNone && !(shownChanged s s₁).isEmpty then s₁.halt (Finding.fault .messageWork).toViolation else s₁ := by
  simp only [drain, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind, State.report]
  rfl

theorem doneWork_at_selection_limit (step : Nat) (name : String) (r : Processing) (i : Instance)
    (hi : r.state.machine? name = some i) :
    doneWork fs st step name 0 r =
      match i.awaitingOnDone with
      | some (_ :: _) => ⟨r.state.halt (Finding.fault (.onDoneSelections (st.ref i.chart.name))).toViolation, r.queue⟩
      | _ => ⟨r.state.setMachine name fun i => { i with awaitingOnDone := none }, r.queue⟩ := by
  simp only [doneWork, hi]
  rcases h : i.awaitingOnDone with _ | _ | ⟨_, _⟩ <;> simp [Processing.report, State.report, Fault.halts]

theorem shows_rejection_reported (name slot : String) (answer : Answer) (r : Processing) :
    (showAnswer st name slot answer r).state.violations = r.state.violations ++
      (match answer with
       | .rejected rj =>
         if RejectionKind.byCaller rj.kind then [(Finding.fault (.rejectedShows (st.ref (r.state.chartName name)) slot rj)).toViolation]
         else []
       | _ => []) ∧
      (showAnswer st name slot answer r).state.halted = r.state.halted := by
  cases answer with
  | rejected rj => cases h : RejectionKind.byCaller rj.kind <;> simp [showAnswer, h, State.report, State.violate, Fault.halts]
  | _ => simp [showAnswer, State.setShown, State.setMachine]

theorem queued_work_keeps_records (q : Queue) (step : Nat) (w : Work) :
    (runWork st fs s q step w).state.records = s.records :=
  congrArg Fixed.records (runWork_fixed q step w)

theorem reaction_reads_current_records (q : Queue) (step : Nat) (a : Automation) (e : Emit) (cause : Nat) :
    ∃ k : Except Issue (Option Value × List String) → Processing,
      runWork st fs s q step (.reaction a e cause) = k (fs.react a.name e.payload s.records s.now s.keyCounts) :=
  ⟨fun x => runWork st { fs with react := fun _ _ _ _ _ => x } s q step (.reaction a e cause), by
    simp only [runWork, Work.settledMachine?, settled, workBody, id_bind]⟩

theorem drain_keeps_now (n : Nat) (q : Queue) : (drain st fs n s q).now = s.now :=
  congrArg Prod.snd (drain_clock n q)

theorem drain_started (n : Nat) (q : Queue) : (drain st fs n s q).started = s.started := by
  induction n generalizing s q with
  | zero =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first | rfl | exact congrArg Fixed.started (refreshScreens_fixed (fs := fs))
  | succ n ih =>
    have hs : ∀ {t : State}, t.fixed = s.fixed → t.started = s.started := fun e => congrArg Fixed.started e
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | rfl
      | exact hs refreshScreens_fixed
      | exact hs ((report_fixed _).trans rfl)
      | (rw [ih]; first
          | exact hs (runWork_fixed _ _ _)
          | exact hs (keeps_sendEntered _)
          | exact hs (settleScreens_fixed _ _)
          | (rw [processCommand_started]; rfl))

theorem drain_mocks (n : Nat) (q : Queue) : (drain st fs n s q).mocks = s.mocks := by
  induction n generalizing s q with
  | zero =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first | rfl | exact congrArg Fixed.mocks (refreshScreens_fixed (fs := fs))
  | succ n ih =>
    have hm : ∀ {t : State}, t.fixed = s.fixed → t.mocks = s.mocks := fun e => congrArg Fixed.mocks e
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
          | (rw [processCommand_mocks]; rfl))

end Tazuna.Thm.Semantics.Chart.Macrostep
