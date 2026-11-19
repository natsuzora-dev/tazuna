import Tazuna.Service.Restart
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Note
import Tazuna.Thm.Service.Clock

/-!
Processing never drops a createKey value: every input keeps the owner that qualifies the values and the entities that
createKey was called for, and may only add to them.
-/

namespace Tazuna.Thm.Service.KeyGrowth

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Note

variable {st : Service} {fs : Functions Id}

/-- `t` keeps the createKey values of `s`: the same owner, and the entities of `s` first. -/
def KeepsKeys (s t : State) : Prop := t.service = s.service ∧ s.createdEntities <+: t.createdEntities

theorem KeepsKeys.refl (s : State) : KeepsKeys s s := ⟨rfl, List.prefix_refl _⟩

theorem KeepsKeys.trans {a b c : State} (h₁ : KeepsKeys a b) (h₂ : KeepsKeys b c) : KeepsKeys a c :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem keeps_foldl {α : Type} (f : State → α → State) (h : ∀ t x, KeepsKeys t (f t x)) (xs : List α) (s : State) :
    KeepsKeys s (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact .refl _
  | cons x xs ih => exact (h s x).trans (ih _)

theorem keeps_foldlM {α : Type} (f : State → α → Id State) (h : ∀ t x, KeepsKeys t (f t x)) (xs : List α)
    (s : State) : KeepsKeys s (xs.foldlM f s) := by
  rw [foldlM_id]; exact keeps_foldl _ h xs s

@[simp] theorem report_service (s : State) (f : Finding) : (s.report f).service = s.service := by
  unfold State.report; split <;> rfl

@[simp] theorem report_createdEntities (s : State) (f : Finding) : (s.report f).createdEntities = s.createdEntities := by
  unfold State.report; split <;> rfl

/-- Closes `KeepsKeys s t` where `t` is `s` with fields other than the keys changed, or with keys created. -/
macro "keys_leaf" : tactic => `(tactic| (refine ⟨?_, ?_⟩ <;> simp [State.halt, State.violate,
  State.write, State.newStep, State.newMessage, State.await, State.setMachine, State.setShown, State.removeFromStack,
  State.startQueued, State.takeQueued, State.answered, State.createKeys, State.endSubscription, State.leaveState,
  State.takeDeadline, State.answer, State.newCommandStep, Processing.report, State.stop,
  apply_ite State.toDurable, apply_ite Durable.service, apply_ite Durable.createdEntities]
  <;> (repeat' split) <;> (try simp)) <;> done)

/-- Closes `KeepsKeys a t` from `h : KeepsKeys a b`, where `t` is `b` with fields other than the keys changed. -/
macro "keys_close " h:term : tactic => `(tactic| (obtain ⟨hk1, hk2⟩ := $h; (try simp at hk1 hk2); refine ⟨?_, ?_⟩ <;> simp [State.halt,
  State.violate, State.write, State.newStep, State.newMessage, State.await, State.setMachine, State.setShown,
  State.removeFromStack, State.startQueued, State.takeQueued, State.answered, State.createKeys,
  State.leaveState, State.takeDeadline, State.answer, State.newCommandStep, Processing.report,
  State.stop, apply_ite State.toDurable, apply_ite Durable.service, apply_ite Durable.createdEntities, hk1] <;> (try split) <;> (try simp [hk1]) <;> (try exact hk2) <;> exact hk2.trans (List.prefix_append _ _)))

theorem keeps_reportAll (s : State) (fs : List Fault) : KeepsKeys s (s.reportAll fs) :=
  keeps_foldl _ (fun t x => by split <;> keys_leaf) _ _

@[simp] theorem reportAll_service (s : State) (fs : List Fault) : (s.reportAll fs).service = s.service :=
  (keeps_reportAll s fs).1

@[simp] theorem reportAll_createdEntities (s : State) (fs : List Fault) :
    (s.reportAll fs).createdEntities = s.createdEntities := by
  unfold State.reportAll
  induction fs generalizing s with
  | nil => rfl
  | cons f fs ih => simp only [List.foldl_cons]; rw [ih]; split <;> simp

theorem keeps_emitAll (s : State) (r : Option LineId) (es : List (Emit × EmittedBy)) : KeepsKeys s (s.emitAll r es) :=
  keeps_foldl _ (fun t x => by keys_leaf) _ _

@[simp] theorem emitAll_createdEntities (s : State) (r : Option LineId) (es : List (Emit × EmittedBy)) :
    (s.emitAll r es).createdEntities = s.createdEntities := by
  unfold State.emitAll
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons]; rw [ih]; rfl

@[simp] theorem emitAll_service (s : State) (r : Option LineId) (es : List (Emit × EmittedBy)) :
    (s.emitAll r es).service = s.service := (keeps_emitAll s r es).1

theorem keeps_addDeadlines (step : Nat) (name : InstanceId) (n : String) (ds : List String) (s : State) :
    KeepsKeys s (addDeadlines st fs step name n ds s) := by
  unfold addDeadlines
  split
  · exact .refl _
  · refine keeps_foldlM _ (fun t d => ?_) _ _
    dsimp only
    split
    · exact .refl _
    · generalize fs.deadlineTime _ _ _ = r
      rcases r with e | t <;> simp only [Functor.map] <;> keys_leaf

/-- Processing `f` keeps the createKey values. -/
def KeysBy (f : Processing → Id Processing) : Prop := ∀ r, KeepsKeys r.state (f r).1

theorem keysBy_foldlM {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, KeysBy (g x)) (xs : List α)
    (r : Processing) : KeepsKeys r.state (xs.foldlM (fun r x => g x r) r).1 :=
  Tazuna.Thm.Service.Chart.Queue.By.foldlM (R := KeepsKeys) KeepsKeys.refl (fun _ _ _ h₁ h₂ => h₁.trans h₂) h xs r

theorem keysBy_unlessHalted {f : Processing → Id Processing} (h : KeysBy f) : KeysBy (unlessHalted f) :=
  Tazuna.Thm.Service.Chart.Queue.By.unlessHalted (R := KeepsKeys) KeepsKeys.refl h

theorem keysBy_withMachine {name : InstanceId} {f : Instance → Processing → Id Processing} (h : ∀ i, KeysBy (f i)) :
    KeysBy (withMachine name f) :=
  Tazuna.Thm.Service.Chart.Queue.By.withMachine (R := KeepsKeys) KeepsKeys.refl h

theorem keysBy_runAssign (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) : KeysBy (runAssign fs st name a scope extra held) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  repeat' split
  all_goals keys_leaf

theorem keeps_endSubscriptions (s : State) (ps : List Pending) :
    KeepsKeys s (ps.foldl (fun s p => s.endSubscription p) s) :=
  keeps_foldl _ (fun t p => by keys_leaf) _ _

@[simp] theorem endSubscriptions_service (s : State) (ps : List Pending) :
    (ps.foldl (fun s p => s.endSubscription p) s).service = s.service := (keeps_endSubscriptions s ps).1

@[simp] theorem endSubscriptions_createdEntities (s : State) (ps : List Pending) :
    (ps.foldl (fun s p => s.endSubscription p) s).createdEntities = s.createdEntities := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih => simp only [List.foldl_cons, ih]; simp [State.endSubscription, State.write]

theorem keysBy_endWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, KeysBy (exit c n))
    (c : InstanceId) : KeysBy (endWith exit c) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  have h1 := keysBy_foldlM (fun n => keysBy_unlessHalted (h c n)) (i.chart.tree.exitOrder i.active) r
  split
  · exact h1
  · keys_close h1

theorem keysBy_leaveWith {exit : InstanceId → String → Processing → Id Processing} (h : ∀ c n, KeysBy (exit c n))
    (name : InstanceId) (n : String) : KeysBy (leaveWith fs st exit name n) := by
  intro r
  simp only [leaveWith, id_bind, note_id]
  have h1 := keysBy_runAssign (fs := fs) (st := st) name (.exit n) (some n) .none none r
  split
  · exact h1
  · refine KeepsKeys.trans ?_ (keysBy_foldlM (fun c => keysBy_unlessHalted (keysBy_endWith h c)) _ _)
    keys_close h1

theorem keysBy_exitOne (fuel : Nat) (name : InstanceId) (n : String) : KeysBy (exitOne fs st fuel name n) := by
  induction fuel generalizing name n with
  | zero => intro r; simp only [exitOne]; keys_leaf
  | succ fuel ih =>
    intro r
    simp only [exitOne]
    apply keysBy_withMachine (f := fun i r => _)
    intro i r
    simp only [id_bind]
    have h1 := keysBy_foldlM (fun k => keysBy_unlessHalted (keysBy_endWith (fun c n => ih c n)
      (InstanceId.copy i.id n k))) (i.copyKeysOf n).reverse r
    split
    · exact h1
    · refine KeepsKeys.trans ?_ (keysBy_leaveWith (fun c n => ih c n) _ _ _)
      keys_close h1

theorem keysBy_enterFinal (step : Nat) (name : InstanceId) (parent : String) : KeysBy (fun r => pure (enterFinal step name parent r)) := by
  intro r
  simp only [enterFinal]
  repeat' split
  all_goals keys_leaf

theorem keysBy_closeFinal (step : Nat) (name : InstanceId) : KeysBy (closeFinal fs st step name) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  split
  · keys_leaf
  · rename_i output failed _
    have h := (keeps_reportAll r.state (failed.toList.map (st.failedEnsures i.chart.name))).trans
      (keysBy_endWith (fun c n => keysBy_exitOne (fs := fs) (st := st) st.exitFuel c n) name
        ⟨r.state.reportAll (failed.toList.map (st.failedEnsures i.chart.name)), r.queue⟩)
    split
    · exact h
    · split
      · keys_close h
      · exact h

theorem keysBy_fillHeld (name : InstanceId) (n : String) (edge : Edge) (scope : Option String)
    (held : Option Value) (extra : Extra) : KeysBy (fillHeld fs st name n edge scope held extra) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  repeat' split
  all_goals keys_leaf

theorem keysBy_fillByTransition (c : InstanceId × Transition) (entered : List (InstanceId × String)) (held : Value)
    (extra : Extra) : KeysBy (fillByTransition fs st c entered held extra) := by
  apply keysBy_withMachine
  intro i r
  repeat' (first | split | dsimp only)
  all_goals first | exact .refl _ | exact keysBy_fillHeld _ _ _ _ _ _ r

theorem keysBy_fillByInitial (filled : Bool) (name : InstanceId) (n : String) :
    KeysBy (fillByInitial fs st filled name n) := by
  apply keysBy_withMachine
  intro i r
  repeat' split
  all_goals first | exact .refl _ | exact keysBy_fillHeld _ _ _ _ _ _ r

theorem keysBy_transitionContent (extra : Extra) (sourceHeld : List Value) (entries : List (List (InstanceId × String)))
    (ck : (InstanceId × Transition) × Nat) : KeysBy (fun r => transitionContent fs st extra sourceHeld entries r ck) := by
  intro r
  simp only [transitionContent, id_bind, note_id]
  exact (keysBy_unlessHalted (keysBy_fillByTransition _ _ _ _) r).trans (keysBy_unlessHalted (keysBy_runAssign _ _ _ _ _) _)

theorem keysBy_enterOne (step : Nat) (filled : Bool) (name : InstanceId) (n : String) :
    KeysBy (enterOne fs st step filled name n) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind, note_id]
  have h0 : KeepsKeys r.state (r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now })
    := by keys_leaf
  have hF := h0.trans (keysBy_fillByInitial (fs := fs) (st := st) filled name n
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩)
  generalize fillByInitial fs st filled name n
    ⟨r.state.setMachine name fun i => { i with entered := setEntered i.entered n r.state.now }, r.queue⟩ = F at hF ⊢
  have h := hF.trans (keysBy_runAssign (fs := fs) (st := st) name (.entry n) (some n) .none none F)
  repeat' split
  all_goals first
    | exact hF
    | exact h
    | exact h.trans (keysBy_closeFinal _ _ _)
    | exact h.trans (keysBy_endWith (fun c n => keysBy_exitOne _ c n) _ _)
    | exact h.trans (keysBy_enterFinal _ _ _ _)
    | exact h.trans (keeps_addDeadlines _ _ _ _ _)

theorem keysBy_enter (step : Nat) (name : InstanceId) (targets : List String) : KeysBy (enter fs st step name targets) := by
  apply keysBy_withMachine
  intro i r
  exact keysBy_foldlM (fun n => keysBy_unlessHalted (keysBy_enterOne step false name n)) _ r

theorem keysBy_microstep (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) :
    KeysBy (microstep fs st step name chosen extra) := by
  apply keysBy_withMachine
  intro i r
  split
  · exact .refl _
  · simp only [id_bind, note_id, id_pure]
    refine KeepsKeys.trans ?_ (keysBy_foldlM (fun e => keysBy_unlessHalted (keysBy_enterOne step _ _ _)) _ _)
    refine KeepsKeys.trans ?_ (keysBy_foldlM (fun c => keysBy_transitionContent extra _ _ c) _ _)
    refine KeepsKeys.trans ?_ (keysBy_foldlM (fun e => keysBy_unlessHalted (keysBy_exitOne _ _ _)) _ _)
    exact keeps_foldl _ (fun t h => by keys_leaf) _ _

theorem keysBy_request (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    KeysBy (request fs st step name state a) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  repeat' split
  all_goals keys_leaf

theorem keysBy_openScreen (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    KeysBy (openScreen fs st step name state a) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  repeat' split
  all_goals keys_leaf

theorem keysBy_activate (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    KeysBy (activate fs st step name state a) := by
  unfold activate
  split
  · exact keysBy_openScreen _ _ _ _
  · intro r; exact .refl _
  · exact keysBy_request _ _ _ _
  · exact keysBy_request _ _ _ _

theorem keysBy_activateEntered (e : InstanceId × String × Nat) : KeysBy (activateEntered fs st e) := by
  apply keysBy_withMachine
  intro i r
  repeat' split
  all_goals first
    | exact .refl _
    | (simp only [id_bind, note_id, id_pure]
       refine KeepsKeys.trans ?_ (keysBy_foldlM (fun a => keysBy_unlessHalted (keysBy_activate _ _ _ a)) _ _)
       keys_leaf)

theorem keysBy_sendEntered : KeysBy (sendEntered fs st) := by
  intro r
  refine KeepsKeys.trans ?_ (keysBy_foldlM (fun e => keysBy_activateEntered e) _ _)
  exact .refl _

theorem keysBy_startCopy (step : Nat) (owner : InstanceId) (map : String) (key encodedKey : Value) :
    KeysBy (startCopy fs st step owner map key encodedKey) := by
  apply keysBy_withMachine
  intro o r
  simp only [id_bind, note_id, id_pure]
  split
  · refine KeepsKeys.trans ?_ (keysBy_enter _ _ _ _)
    keys_leaf
  · keys_leaf

theorem keysBy_exitLeftCopy (owner : InstanceId) (map : String) (itemKeys : List Value) (k : Value) :
    KeysBy (fun r => exitLeftCopy fs st owner map itemKeys r k) := by
  intro r
  unfold exitLeftCopy
  split
  · exact .refl _
  · exact keysBy_unlessHalted (keysBy_endWith (fun c n => keysBy_exitOne _ c n) _) r

theorem keeps_setMachine (s : State) (name : InstanceId) (f : Instance → Instance) : KeepsKeys s (s.setMachine name f) := by
  keys_leaf

theorem keys_exitLeftCopies (owner : InstanceId) (map : String) (itemKeys xs : List Value) (r : Processing) :
    KeepsKeys r.state (xs.foldlM (fun r k => exitLeftCopy fs st owner map itemKeys r k) r).state :=
  keysBy_foldlM (g := fun k r => exitLeftCopy fs st owner map itemKeys r k)
    (fun k => keysBy_exitLeftCopy owner map itemKeys k) xs r

theorem keys_startCopies (step : Nat) (owner : InstanceId) (map : String) (xs : List (Value × Value)) (r : Processing) :
    KeepsKeys r.state (xs.foldlM (fun (r : Processing) (k : Value × Value) =>
      unlessHalted (startCopy fs st step owner map k.1 k.2) r) r).state :=
  keysBy_foldlM (g := fun (k : Value × Value) => unlessHalted (startCopy fs st step owner map k.1 k.2))
    (fun k => keysBy_unlessHalted (keysBy_startCopy step owner map k.1 k.2)) xs r

theorem keys_syncMap (step : Nat) (owner : InstanceId) (r : Processing) (map : String) :
    KeepsKeys r.state (syncMap fs st step owner r map).1.state := by
  simp only [syncMap, id_bind, note_id, id_pure]
  repeat' split
  · exact .refl _
  · exact .refl _
  · keys_leaf
  · keys_leaf
  · exact .refl _
  · refine KeepsKeys.trans ?_ (keeps_setMachine _ _ _)
    refine KeepsKeys.trans ?_ (keys_startCopies _ _ _ _ _)
    exact keys_exitLeftCopies _ _ _ _ _

theorem keys_syncCopies (step : Nat) (owner : InstanceId) (r : Processing) :
    KeepsKeys r.state (syncCopies fs st step owner r).1.state := by
  simp only [syncCopies]
  split
  · exact .refl _
  · rw [foldlM_id]
    suffices ∀ (xs : List String) (acc : Processing × Bool), KeepsKeys r.state acc.1.state →
        KeepsKeys r.state (xs.foldl (fun acc map => ((syncMap fs st step owner acc.1 map).1,
          acc.2 || (syncMap fs st step owner acc.1 map).2)) acc).1.state from this _ _ (.refl _)
    intro xs
    induction xs with
    | nil => intro acc h; exact h
    | cons x xs ih => intro acc h; exact ih _ (h.trans (keys_syncMap _ _ _ _))

theorem keys_alwaysRound (step : Nat) (owner : InstanceId)
    {next : Instance → List (InstanceId × Transition) → Processing → Id Processing} (h : ∀ o c, KeysBy (next o c)) :
    KeysBy (alwaysRound fs st step owner next) := by
  intro r
  simp only [alwaysRound, id_bind]
  have h1 := keys_syncCopies (fs := fs) (st := st) step owner r
  repeat' split
  all_goals first
    | exact .refl _
    | exact h1
    | exact h1.trans (h _ _ _)
    | keys_close h1

theorem keysBy_settleFrom (step : Nat) (owner : InstanceId) (rounds : Nat) : KeysBy (settleFrom fs st step owner rounds) := by
  induction rounds with
  | zero => exact keys_alwaysRound step owner (fun o c r => by keys_leaf)
  | succ n ih =>
    refine keys_alwaysRound step owner (fun o c r => ?_)
    simp only [id_bind]
    split
    · exact ih _
    · exact (keysBy_microstep _ _ _ _ r).trans (ih _)

theorem keysBy_settle (step : Nat) (name : InstanceId) : KeysBy (settle fs st step name) :=
  fun r => keysBy_settleFrom _ _ _ r

theorem keysBy_settled (step : Nat) (name : Option InstanceId) {f : Processing → Id Processing} (hf : KeysBy f) :
    KeysBy (settled fs st step name f) := by
  intro r
  cases name with
  | none => exact hf r
  | some n =>
    simp only [settled, settleAround, id_bind, note_id]
    exact (keysBy_settleFrom _ _ _ r).trans ((keysBy_unlessHalted hf _).trans (keysBy_settleFrom _ _ _ _))

theorem keeps_syncShows (s : State) (owner : InstanceId) (wanted : List Wanted) :
    KeepsKeys s (s.syncShows owner wanted) := by
  unfold State.syncShows
  refine KeepsKeys.trans (keeps_foldl _ (fun t p => ?_) _ s) (keeps_foldl _ (fun t w => ?_) _ _)
  · unfold State.endShowStep; repeat' split
    all_goals keys_leaf
  · unfold State.subscribeStep; split
    all_goals keys_leaf

theorem keeps_refresh (s : State) (owner : InstanceId) : KeepsKeys s (refresh st fs s owner) := by
  simp only [refresh, id_bind]
  repeat' split
  all_goals first | exact .refl _ | exact keeps_syncShows _ _ _ | keys_leaf

theorem keeps_refreshScreens (s : State) : KeepsKeys s (refreshScreens st fs s) :=
  keeps_foldlM _ (fun t i => by split; exact .refl _; exact keeps_refresh _ _) _ _

theorem keeps_automationAnswer (a : String) (answer : Answer) (s : State) :
    KeepsKeys s (automationAnswer st a answer s) := by
  unfold automationAnswer; repeat' split
  all_goals keys_leaf

theorem keeps_processCommand (name : String) (raw : Value) (id : Option LineId) (step : Nat) (s : State) :
    KeepsKeys s (processCommand st fs s name raw id step).1 := by
  simp only [processCommand, id_bind]
  split
  · keys_leaf
  · rename_i records groups violations _
    refine KeepsKeys.trans ?_ (keeps_emitAll _ _ _)
    keys_leaf
  · exact keeps_reportAll _ _

theorem keeps_publish (s : State) : KeepsKeys s (publish st fs s) :=
  keeps_foldlM _ (fun t sub => by
    simp only [publishOne, id_bind]
    repeat' split
    all_goals first
      | exact .refl _
      | keys_leaf) _ _

theorem keysBy_applyCompletion (step : Nat) (name : InstanceId) (ts : List Transition) (extra : Extra) :
    KeysBy (applyCompletion fs st step name ts extra) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  split
  · keys_leaf
  · exact .refl _
  · exact keysBy_microstep _ _ _ _ r

theorem keysBy_handle (step : Nat) (name : InstanceId) (state : String) (a : Activity) (answer : Answer) :
    KeysBy (handle fs st step name state a answer) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind, note_id]
  repeat' split
  all_goals first | exact .refl _ | exact keysBy_applyCompletion _ _ _ _ r

theorem keysBy_dispatch (step : Nat) (name : InstanceId) (key : String) (payload : Value) :
    KeysBy (dispatch fs st step name key payload) := by
  intro r
  simp only [dispatch, id_bind, note_id]
  repeat' split
  all_goals first | exact .refl _ | exact keysBy_microstep _ _ _ _ r | keys_leaf

theorem keysBy_receiveWork (step : Nat) (name : InstanceId) (groups : List (List Received)) :
    KeysBy (receiveWork fs st step name groups) := by
  intro r
  unfold receiveWork
  split
  · exact (keysBy_settle step name r).trans (keysBy_dispatch step name _ _ _)
  · exact .refl _

theorem keysBy_done (step : Nat) (name : InstanceId) (n : String) : KeysBy (done fs st step name n) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind, note_id]
  split
  · exact .refl _
  · exact keysBy_applyCompletion _ _ _ _ r

theorem keysBy_doneWork (step : Nat) (name : InstanceId) (fuel : Nat) : KeysBy (doneWork fs st step name fuel) := by
  induction fuel with
  | zero => intro r; simp only [doneWork]; repeat' split
            all_goals exact .refl _
  | succ fuel ih =>
    intro r
    simp only [doneWork, id_bind]
    repeat' split
    all_goals first
      | exact .refl _
      | keys_leaf
      | (refine KeepsKeys.trans ?_ (ih _)
         refine KeepsKeys.trans ?_ (keysBy_done _ _ _ _)
         refine KeepsKeys.trans ?_ (keysBy_settle _ _ _)
         keys_leaf)

theorem keysBy_startWork (step : Nat) (name : InstanceId) : KeysBy (startWork fs st step name) := by
  apply keysBy_withMachine
  intro i r
  simp only [id_bind]
  let r' : Processing := ⟨r.state.setMachine name ({ · with startStep := some step }), r.queue⟩
  exact (KeepsKeys.refl r.state : KeepsKeys r.state r'.state).trans
    ((keysBy_enter step name _ r').trans (keysBy_unlessHalted (keysBy_settle step name) _))

theorem keysBy_answerTo (step : Nat) (a : Activity) (answer : Answer) (requester : Requester) :
    KeysBy (answerTo fs st step a answer requester) := by
  intro r
  cases requester with
  | state name state => exact keysBy_handle _ _ _ _ _ r
  | slot name slot =>
    simp only [answerTo, showAnswer, id_bind, note_id]
    repeat' split
    all_goals keys_leaf
  | automation n => exact keeps_automationAnswer _ _ _

theorem keysBy_deliverAnswer (step : Nat) (p : Pending) (answer : Answer) :
    KeysBy (deliverAnswer fs st step p answer) := by
  intro r
  simp only [deliverAnswer]
  split
  · refine KeepsKeys.trans ?_ (keysBy_answerTo _ _ _ _ _)
    keys_leaf
  · keys_leaf

theorem keysBy_workBody (step : Nat) (w : Work) : KeysBy (workBody st fs step w) := by
  intro r
  obtain ⟨s, q⟩ := r
  cases w with
  | reaction a gs d c =>
    rcases gs with _ | ⟨_ | ⟨e, g⟩, gs⟩
    · exact ⟨rfl, List.prefix_refl _⟩
    · exact ⟨rfl, List.prefix_refl _⟩
    simp only [workBody, id_bind]
    repeat' split
    all_goals keys_leaf
  | answered c answer cause =>
    simp only [workBody]
    repeat' split
    all_goals first
      | (refine KeepsKeys.trans ?_ (keysBy_answerTo _ _ _ _ _); keys_leaf)
      | keys_leaf
  | start name c => exact keysBy_startWork _ _ _
  | receive name received d c => exact keysBy_receiveWork _ _ _ _
  | onDone name c => exact keysBy_doneWork _ _ _ _
  | opensDone name state key output serial c =>
    simp only [workBody, id_bind, note_id]
    split
    · keys_leaf
    · refine KeepsKeys.trans ?_ (keysBy_withMachine (fun i r => keysBy_applyCompletion _ _ _ _ r) _)
      keys_leaf

theorem keysBy_settleScreen (name : InstanceId) : KeysBy (settleScreen st fs name) := by
  intro r
  simp only [settleScreen, id_bind, note_id]
  split
  · exact .refl _
  · refine KeepsKeys.trans ?_ (keysBy_settle _ _ _)
    keys_leaf

theorem keeps_drain (n : Nat) (s : State) (q : Queue) : KeepsKeys s (drain st fs n s q) := by
  induction n generalizing s q with
  | zero =>
    simp only [drain, id_bind]
    repeat' split
    all_goals first
      | exact .refl _
      | exact keeps_refreshScreens _
  | succ n ih =>
    simp only [drain, id_bind, note_id]
    repeat' split
    all_goals first
      | exact .refl _
      | keys_leaf
      | exact keeps_refreshScreens _
      | (refine KeepsKeys.trans ?_ (ih _ _)
         refine KeepsKeys.trans ?_ (keysBy_settled _ _ (keysBy_workBody _ _) _)
         keys_leaf)
      | (refine KeepsKeys.trans ?_ (ih _ _)
         refine KeepsKeys.trans ?_ (keeps_processCommand _ _ _ _ _)
         keys_leaf)
      | (refine KeepsKeys.trans ?_ (ih _ _)
         exact keysBy_sendEntered _)
      | (refine KeepsKeys.trans ?_ (ih _ _)
         refine KeepsKeys.trans (keeps_refreshScreens (st := st) (fs := fs) s) ?_
         exact keysBy_foldlM (g := fun (name : InstanceId) r => settleScreen st fs name r)
           (fun name => keysBy_settleScreen name) _ _)

theorem keysBy_fire (step : Nat) (t : Deadline) : KeysBy (fire fs st step t) := by
  intro r
  simp only [fire, id_bind, note_id]
  split
  · keys_leaf
  · refine KeepsKeys.trans ?_ (keysBy_withMachine (fun i r => by
      split
      · exact .refl _
      · exact keysBy_applyCompletion _ _ _ _ r) _)
    keys_leaf

theorem keeps_afterMessage (s : State) : KeepsKeys s (afterMessage st fs s) := by
  simp only [afterMessage, checkInvariants, id_bind]
  split
  · exact keeps_reportAll _ _
  · exact (keeps_reportAll _ _).trans (keeps_publish _)

theorem keeps_fireDue (to : Time) (fuel : Nat) (tie : Option Time) (s : State) :
    KeepsKeys s (fireDue st fs to fuel tie s) := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> keys_leaf
  | succ fuel ih =>
    rw [fireDue]
    split
    · exact .refl _
    · split
      · exact .refl _
      · dsimp only
        split
        · keys_leaf
        · rename_i hc
          obtain ⟨_, rfl⟩ := Tazuna.Thm.Service.Clock.chooseDeadline_orders hc
          simp only [id_bind, note_id]
          refine KeepsKeys.trans ?_ (ih _ _)
          refine KeepsKeys.trans ?_ (keeps_afterMessage _)
          refine KeepsKeys.trans ?_ (keeps_drain _ _ _)
          refine KeepsKeys.trans ?_ (keysBy_settled _ _ (keysBy_fire _ _) _)
          keys_leaf

theorem keeps_message (s : State) (q : Queue) : KeepsKeys s (message st fs s q) := by
  simp only [message, finish, id_bind]
  exact (keeps_drain _ _ _).trans ((keeps_afterMessage _).trans (keeps_fireDue _ _ _ _))

/-- Closes an equation between the keys of `t` and of `s`, where `t` is `s` with fields other than the keys changed. -/
macro "keys_same" : tactic => `(tactic| ((repeat' split) <;> simp [State.halt, State.violate,
  State.write, State.newStep, State.newMessage, State.answer, apply_ite State.toDurable,
  apply_ite Durable.service, apply_ite Durable.createdEntities] <;> (repeat' split) <;> (try simp)) <;> done)

@[simp] theorem processCommand_service (name : String) (raw : Value) (id : Option LineId) (step : Nat) (s : State) :
    (processCommand st fs s name raw id step).1.service = s.service := (keeps_processCommand _ _ _ _ _).1

@[simp] theorem processCommand_createdEntities (name : String) (raw : Value) (id : Option LineId) (step : Nat)
    (s : State) : (processCommand st fs s name raw id step).1.createdEntities = s.createdEntities := by
  simp only [processCommand, id_bind]
  split <;> keys_same

theorem keeps_send (name : Spec.Ref) (id : Option LineId) (raw : Value) (s : State) :
    KeepsKeys s (send st fs s name id raw) := by
  simp only [send, id_bind]
  repeat' split
  all_goals first
    | keys_leaf
    | (refine KeepsKeys.trans ?_ (keeps_message _ _); keys_leaf)

theorem keeps_call (name : Spec.Ref) (id : Option LineId) (raw : Value) (s : State) :
    KeepsKeys s (call st fs s name id raw) := by
  simp only [call, id_bind]
  repeat' split
  all_goals first
    | keys_leaf
    | (refine KeepsKeys.trans ?_ (keeps_message _ _); keys_leaf)

theorem keeps_subscribe (name : Spec.Ref) (id : Option LineId) (raw : Value) (s : State) :
    KeepsKeys s (subscribe st fs s name id raw) := by
  simp only [subscribe]
  repeat' split
  all_goals first
    | keys_leaf
    | (refine KeepsKeys.trans ?_ (keeps_message _ _); keys_leaf)

theorem keeps_endSubscription (id : LineId) (s : State) : KeepsKeys s (endSubscription st fs s id) := by
  simp only [endSubscription]
  refine KeepsKeys.trans ?_ (keeps_message _ _)
  keys_leaf

theorem keeps_receive (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId) (s : State) :
    KeepsKeys s (receive st fs s name id raw resultOf) := by
  simp only [receive, redeliver, id_bind]
  repeat' split
  all_goals first
    | keys_leaf
    | (refine KeepsKeys.trans ?_ (keeps_message _ _); keys_leaf)

theorem keeps_answerRequest (id : Option LineId) (p : Pending) (answer : Answer) (s : State) :
    KeepsKeys s (answerRequest st fs s id p answer) := by
  simp only [answerRequest, id_bind]
  repeat' split
  all_goals first
    | keys_leaf
    | (refine KeepsKeys.trans ?_ (keeps_message _ _)
       refine KeepsKeys.trans ?_ (keysBy_settled _ _ (keysBy_deliverAnswer _ _ _) _)
       keys_leaf)

theorem keeps_begin (s : State) : KeepsKeys s (begin st fs s) := by
  simp only [begin, id_bind]
  split
  · exact .refl _
  · refine KeepsKeys.trans ?_ (keeps_message _ _)
    refine KeepsKeys.trans ?_ (keeps_foldlM _ (fun t c => by
      simp only [startInstance, id_bind]; repeat' split
      all_goals first | exact .refl _ | keys_leaf) _ _)
    refine KeepsKeys.trans ?_ (keeps_foldlM _ (fun t e => by
      simp only [id_bind]; repeat' split
      all_goals exact .refl _) _ _)
    keys_leaf

theorem keeps_operate (screen : InstanceId) (control : String) (payload : Value) (s : State) :
    KeepsKeys s (operate st fs s screen control payload) := by
  simp only [operate, id_bind]
  repeat' split
  all_goals first
    | keys_leaf
    | (refine KeepsKeys.trans ?_ (keeps_message _ _)
       refine KeepsKeys.trans ?_ (keysBy_settled _ _ (keysBy_dispatch _ _ _ _) _)
       keys_leaf)

theorem keeps_restart (s : State) : KeepsKeys s (restart st fs s) := by
  simp only [restart]
  refine KeepsKeys.trans ?_ (keeps_begin _)
  keys_leaf

end Tazuna.Thm.Service.KeyGrowth
