import Tazuna.Explore.Instrument
import Tazuna.Thm.Data.List

/-!
Service definitions are generic in `m`, so instrumented functions that agree with the plain ones (FunctionsAgree) make
every instrumented definition agree with its plain one.
-/

namespace Tazuna.Thm.Explore.Instrument

open Tazuna.Data Tazuna.Service Tazuna.Explore Tazuna.Sim Tazuna.Thm.Data.List

variable {C : Type}

/-- Whether `x` returns `a` from every starting state. -/
@[irreducible] def Agrees {α : Type} (x : StateT C Id α) (a : α) : Prop := ∀ c, (x.run c).1 = a

theorem Agrees.pure {α : Type} (a : α) : Agrees (C := C) (Pure.pure a) a := by
  unfold Agrees; exact fun _ => rfl

theorem Agrees.bind {α β : Type} {x : StateT C Id α} {a : Id α} {f : α → StateT C Id β} {g : α → Id β}
    (hx : Agrees x a) (hf : ∀ b, Agrees (f b) (g b)) : Agrees (x >>= f) (a >>= g) := by
  unfold Agrees at *
  intro c
  show ((f (x.run c).1).run (x.run c).2).1 = g a
  rw [hf _ _, hx c]

theorem Agrees.map {α β : Type} {x : StateT C Id α} {a : Id α} (f : α → β) (hx : Agrees x a) :
    Agrees (f <$> x) (f <$> a) := by
  unfold Agrees at *
  intro c
  show f (x.run c).1 = f a
  rw [hx c]

theorem Agrees.unit {β : Type} {x : StateT C Id PUnit} {f : PUnit → StateT C Id β} {a : β}
    (hf : ∀ u, Agrees (f u) a) : Agrees (x >>= f) a := by
  unfold Agrees at *
  intro c
  exact hf _ _

theorem Agrees.foldlM {α β : Type} {f : β → α → StateT C Id β} {g : β → α → Id β}
    (hf : ∀ b a, Agrees (f b a) (g b a)) (xs : List α) (init : β) :
    Agrees (xs.foldlM f init) (xs.foldlM g init) := by
  induction xs generalizing init with
  | nil => exact Agrees.pure _
  | cons x xs ih => exact Agrees.bind (hf init x) (fun b => ih b)

theorem Agrees.filterMapM {α β : Type} {f : α → StateT C Id (Option β)} {g : α → Id (Option β)}
    (hf : ∀ a, Agrees (f a) (g a)) (xs : List α) : Agrees (xs.filterMapM f) (xs.filterMapM g) := by
  unfold List.filterMapM
  suffices ∀ (ys : List α) (acc : List β), Agrees (List.filterMapM.loop f ys acc) (List.filterMapM.loop g ys acc) from
    this xs []
  intro ys
  induction ys with
  | nil => intro acc; exact Agrees.pure _
  | cons y ys ih =>
    intro acc
    simp only [List.filterMapM.loop]
    exact Agrees.bind (hf y) (fun b => by cases b <;> exact ih _)

theorem Agrees.mapM {α β : Type} {f : α → StateT C Id β} {g : α → Id β} (hf : ∀ a, Agrees (f a) (g a))
    (xs : List α) : Agrees (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => exact Agrees.pure _
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact Agrees.bind (hf x) fun b => Agrees.bind ih fun bs => Agrees.pure _

structure FunctionsAgree (fsI : Functions (StateT C Id)) (fs : Functions Id) : Prop where
  parse : ∀ a b, Agrees (fsI.parse a b) (fs.parse a b)
  unordered : ∀ a b, Agrees (fsI.unordered a b) (fs.unordered a b)
  normalize : ∀ a b, Agrees (fsI.normalize a b) (fs.normalize a b)
  binding : ∀ a b c d e, Agrees (fsI.binding a b c d e) (fs.binding a b c d e)
  requirement : ∀ a b c d e, Agrees (fsI.requirement a b c d e) (fs.requirement a b c d e)
  inputRequirement : ∀ a b c, Agrees (fsI.inputRequirement a b c) (fs.inputRequirement a b c)
  decide : ∀ a b c d, Agrees (fsI.decide a b c d) (fs.decide a b c d)
  ensures : ∀ a b c d e, Agrees (fsI.ensures a b c d e) (fs.ensures a b c d e)
  queryEnsures : ∀ a b c d, Agrees (fsI.queryEnsures a b c d) (fs.queryEnsures a b c d)
  resultEnsures : ∀ a b c d e, Agrees (fsI.resultEnsures a b c d e) (fs.resultEnsures a b c d e)
  invariant : ∀ a b, Agrees (fsI.invariant a b) (fs.invariant a b)
  serviceInvariant : ∀ a, Agrees (fsI.serviceInvariant a) (fs.serviceInvariant a)
  chartInvariant : ∀ a b, Agrees (fsI.chartInvariant a b) (fs.chartInvariant a b)
  resolve : ∀ a b c d, Agrees (fsI.resolve a b c d) (fs.resolve a b c d)
  automationBinding : ∀ a b c d e, Agrees (fsI.automationBinding a b c d e) (fs.automationBinding a b c d e)
  automationGuard : ∀ a b c d e, Agrees (fsI.automationGuard a b c d e) (fs.automationGuard a b c d e)
  react : ∀ a b c d e, Agrees (fsI.react a b c d e) (fs.react a b c d e)
  comparable : ∀ a b, Agrees (fsI.comparable a b) (fs.comparable a b)
  initialContext : ∀ a b, Agrees (fsI.initialContext a b) (fs.initialContext a b)
  guard : ∀ a b c d e, Agrees (fsI.guard a b c d e) (fs.guard a b c d e)
  assign : ∀ a b c d e, Agrees (fsI.assign a b c d e) (fs.assign a b c d e)
  input : ∀ a b c d, Agrees (fsI.input a b c d) (fs.input a b c d)
  held : ∀ a b c d e, Agrees (fsI.held a b c d e) (fs.held a b c d e)
  deadlineAt : ∀ a b c, Agrees (fsI.deadlineAt a b c) (fs.deadlineAt a b c)
  offers : ∀ a b c, Agrees (fsI.offers a b c) (fs.offers a b c)
  showInput : ∀ a b c, Agrees (fsI.showInput a b c) (fs.showInput a b c)
  items : ∀ a b, Agrees (fsI.items a b) (fs.items a b)
  defaults : ∀ a, Agrees (fsI.defaults a) (fs.defaults a)
  close : ∀ a b, Agrees (fsI.close a b) (fs.close a b)

theorem note_agrees [MonadNote (StateT C Id)] (n : Note) :
    Agrees (MonadNote.note n : StateT C Id Unit) (MonadNote.note n : Id Unit) := by
  unfold Agrees; intro _; rfl

theorem expectFound_agrees [MonadNote (StateT C Id)] {α : Type} [Inhabited α] (what : String) (found : Option α) :
    Agrees (expectFound what found : StateT C Id α) (expectFound what found : Id α) := by
  cases found
  · exact Agrees.unit fun _ => Agrees.pure _
  · exact Agrees.pure _

syntax "agree" "[" term,* "]" : tactic
macro_rules
  | `(tactic| agree [$ts,*]) => do
    let mut given ← `(tactic| fail "no lemma applies")
    for t in ts.getElems do
      given ← `(tactic| first | with_reducible apply $t | $given:tactic)
    `(tactic| repeat' (first
      | $given:tactic
      | exact Agrees.pure _
      | refine Agrees.bind ?_ (fun _ => ?_)
      | refine Agrees.map _ ?_
      | refine Agrees.foldlM (fun _ _ => ?_) _ _
      | refine Agrees.filterMapM (fun _ => ?_) _
      | with_reducible exact note_agrees _
      | with_reducible exact expectFound_agrees _ _
      | split
      | (dsimp only)
      | intro _))

variable {fsI : Functions (StateT C Id)} {fs : Functions Id} {st : Service} [MonadNote (StateT C Id)]

omit [MonadNote (StateT C Id)] in
theorem firstFalse_agrees {test : String → StateT C Id (Except Issue Bool)} {test' : String → Id (Except Issue Bool)}
    (ht : ∀ n, Agrees (test n) (test' n)) (ns : List String) : Agrees (firstFalse test ns) (firstFalse test' ns) := by
  induction ns with
  | nil => exact Agrees.pure _
  | cons n ns ih => simp only [firstFalse]; agree [ht, ih]

omit [MonadNote (StateT C Id)] in
theorem unlessHalted_agrees {f : Processing → StateT C Id Processing} {g : Processing → Id Processing}
    (hf : ∀ r, Agrees (f r) (g r)) (r : Processing) : Agrees (unlessHalted f r) (unlessHalted g r) := by
  unfold unlessHalted; agree [hf]

omit [MonadNote (StateT C Id)] in
theorem withMachine_agrees {name : InstanceId} {f : Instance → Processing → StateT C Id Processing}
    {g : Instance → Processing → Id Processing} (hf : ∀ i r, Agrees (f i r) (g i r)) (r : Processing) :
    Agrees (withMachine name f r) (withMachine name g r) := by
  unfold withMachine; agree [hf]

omit [MonadNote (StateT C Id)] in
theorem endWith_agrees {e : InstanceId → String → Processing → StateT C Id Processing}
    {e' : InstanceId → String → Processing → Id Processing} (he : ∀ c n r, Agrees (e c n r) (e' c n r))
    (c : InstanceId) (r : Processing) : Agrees (endWith e c r) (endWith e' c r) := by
  unfold endWith; refine withMachine_agrees (fun i r => ?_) r; agree [unlessHalted_agrees, he]

theorem sorted_agrees (schema : Schema) (v : Value) :
    Agrees (st.sorted schema v : StateT C Id Value) (st.sorted schema v : Id Value) := by
  unfold Service.sorted; agree [expectFound_agrees]

section
variable (h : FunctionsAgree fsI fs)
include h

omit [MonadNote (StateT C Id)] in
theorem runAssign_agrees (name : InstanceId) (a : Assignment) (scope : Option String) (extra : Extra)
    (held : Option Value) (r : Processing) :
    Agrees (runAssign fsI st name a scope extra held r) (runAssign fs st name a scope extra held r) := by
  unfold runAssign; refine withMachine_agrees (fun i r => ?_) r; agree [h.assign]

theorem leaveWith_agrees {e : InstanceId → String → Processing → StateT C Id Processing}
    {e' : InstanceId → String → Processing → Id Processing} (he : ∀ c n r, Agrees (e c n r) (e' c n r))
    (name : InstanceId) (n : String) (r : Processing) :
    Agrees (leaveWith fsI st e name n r) (leaveWith fs st e' name n r) := by
  unfold leaveWith; agree [runAssign_agrees h, unlessHalted_agrees, endWith_agrees he]

theorem exitOne_agrees (fuel : Nat) (name : InstanceId) (n : String) (r : Processing) :
    Agrees (exitOne fsI st fuel name n r) (exitOne fs st fuel name n r) := by
  induction fuel generalizing name n r with
  | zero => exact Agrees.unit fun _ => Agrees.pure _
  | succ fuel ih =>
    unfold exitOne; refine withMachine_agrees (fun i r => ?_) r
    agree [unlessHalted_agrees, endWith_agrees ih, leaveWith_agrees h ih]

theorem closeFinal_agrees (step : Nat) (name : InstanceId) (r : Processing) :
    Agrees (closeFinal fsI st step name r) (closeFinal fs st step name r) := by
  unfold closeFinal; refine withMachine_agrees (fun i r => ?_) r
  agree [h.close, endWith_agrees (exitOne_agrees h _)]

omit [MonadNote (StateT C Id)] in
theorem request_agrees (step : Nat) (name : InstanceId) (state : String) (a : Activity) (r : Processing) :
    Agrees (request fsI st step name state a r) (request fs st step name state a r) := by
  unfold request; refine withMachine_agrees (fun i r => ?_) r; agree [h.input]

omit [MonadNote (StateT C Id)] in
theorem initialContextOf_agrees (chart : String) (input : Value) :
    Agrees (initialContextOf fsI st chart input) (initialContextOf fs st chart input) := by
  unfold initialContextOf; agree [h.initialContext, h.defaults, h.normalize]

theorem openScreen_agrees (step : Nat) (name : InstanceId) (state : String) (a : Activity) (r : Processing) :
    Agrees (openScreen fsI st step name state a r) (openScreen fs st step name state a r) := by
  unfold openScreen; refine withMachine_agrees (fun i r => ?_) r; agree [h.input, h.parse, firstFalse_agrees (fun _ => h.inputRequirement _ _ _), initialContextOf_agrees h]

theorem activate_agrees (step : Nat) (name : InstanceId) (state : String) (a : Activity) (r : Processing) :
    Agrees (activate fsI st step name state a r) (activate fs st step name state a r) := by
  unfold activate; agree [openScreen_agrees h, request_agrees h]

theorem activateEntered_agrees (e : InstanceId × String × Nat) (r : Processing) :
    Agrees (activateEntered fsI st e r) (activateEntered fs st e r) := by
  unfold activateEntered; refine withMachine_agrees (fun i r => ?_) r; agree [unlessHalted_agrees, activate_agrees h]

theorem sendEntered_agrees (r : Processing) : Agrees (sendEntered fsI st r) (sendEntered fs st r) := by
  unfold sendEntered; agree [activateEntered_agrees h]

theorem addDeadlines_agrees (step : Nat) (name : InstanceId) (n : String) (ds : List Spec.Deadline)
    (s : State) : Agrees (addDeadlines st fsI step name n ds s) (addDeadlines st fs step name n ds s) := by
  unfold addDeadlines; agree [h.deadlineAt]

omit [MonadNote (StateT C Id)] in
theorem fillHeld_agrees (name : InstanceId) (n : String) (edge : Edge) (scope : Option String) (held : Option Value)
    (extra : Extra) (r : Processing) :
    Agrees (fillHeld fsI st name n edge scope held extra r) (fillHeld fs st name n edge scope held extra r) := by
  unfold fillHeld; refine withMachine_agrees (fun i r => ?_) r; agree [h.held]

omit [MonadNote (StateT C Id)] in
theorem fillByTransition_agrees (c : InstanceId × Transition) (entered : List (InstanceId × String)) (held : Value)
    (extra : Extra) (r : Processing) :
    Agrees (fillByTransition fsI st c entered held extra r) (fillByTransition fs st c entered held extra r) := by
  unfold fillByTransition; refine withMachine_agrees (fun i r => ?_) r; agree [fillHeld_agrees h]

omit [MonadNote (StateT C Id)] in
theorem fillByInitial_agrees (filled : Bool) (name : InstanceId) (n : String) (r : Processing) :
    Agrees (fillByInitial fsI st filled name n r) (fillByInitial fs st filled name n r) := by
  unfold fillByInitial; refine withMachine_agrees (fun i r => ?_) r; agree [fillHeld_agrees h]

theorem transitionContent_agrees (extra : Extra) (sourceHeld : List Value) (entries : List (List (InstanceId × String)))
    (r : Processing) (ck : (InstanceId × Transition) × Nat) :
    Agrees (transitionContent fsI st extra sourceHeld entries r ck) (transitionContent fs st extra sourceHeld entries r ck) := by
  unfold transitionContent
  agree [note_agrees, fillByTransition_agrees h, runAssign_agrees h, unlessHalted_agrees]

theorem enterOne_agrees (step : Nat) (filled : Bool) (name : InstanceId) (n : String) (r : Processing) :
    Agrees (enterOne fsI st step filled name n r) (enterOne fs st step filled name n r) := by
  unfold enterOne; refine withMachine_agrees (fun i r => ?_) r
  agree [fillByInitial_agrees h, runAssign_agrees h, closeFinal_agrees h, endWith_agrees (exitOne_agrees h _),
    addDeadlines_agrees h]

theorem enter_agrees (step : Nat) (name : InstanceId) (targets : List String) (r : Processing) :
    Agrees (enter fsI st step name targets r) (enter fs st step name targets r) := by
  unfold enter; refine withMachine_agrees (fun i r => ?_) r; agree [unlessHalted_agrees, enterOne_agrees h]

theorem microstep_agrees (step : Nat) (name : InstanceId) (chosen : List (InstanceId × Transition)) (extra : Extra) (r : Processing) :
    Agrees (microstep fsI st step name chosen extra r) (microstep fs st step name chosen extra r) := by
  unfold microstep; refine withMachine_agrees (fun i r => ?_) r
  agree [note_agrees, transitionContent_agrees h, unlessHalted_agrees, exitOne_agrees h, enterOne_agrees h]

omit [MonadNote (StateT C Id)] in
theorem choose_agrees (s : State) (i : Instance) (extra : Extra) (ts : List Transition) :
    Agrees (choose fsI st s i extra ts) (choose fs st s i extra ts) := by
  induction ts with
  | nil => exact Agrees.pure _
  | cons t rest ih => unfold choose; agree [firstFalse_agrees (fun _ => h.guard _ _ _ _ _), ih]

theorem firstLevel_agrees (s : State) (extra : Extra) (levels : List (Instance × List Transition)) :
    Agrees (firstLevel fsI st s extra levels) (firstLevel fs st s extra levels) := by
  induction levels with
  | nil => exact Agrees.pure _
  | cons l rest ih => unfold firstLevel; agree [choose_agrees h, ih]

theorem reaches_agrees (c : Instance) (payload : Value) : Agrees (reaches fsI st c payload) (reaches fs st c payload) := by
  unfold reaches copyKey; agree [h.normalize]

theorem reachedCopies_agrees (s : State) (top : Instance) (payload : Value) :
    Agrees (reachedCopies fsI st s top payload) (reachedCopies fs st s top payload) := by
  unfold reachedCopies; agree [reaches_agrees h]

theorem eventLeaves_agrees (s : State) (top : Instance) (payload : Value) :
    Agrees (eventLeaves fsI st s top payload) (eventLeaves fs st s top payload) := by
  unfold eventLeaves; agree [reachedCopies_agrees h]

theorem pick_agrees (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra) (l : InstanceId × Option String) :
    Agrees (pick fsI st s top trigger extra l) (pick fs st s top trigger extra l) := by
  unfold pick; agree [firstLevel_agrees h]

theorem select_agrees (s : State) (top : Instance) (trigger : Spec.Trigger) (extra : Extra)
    (leaves : List (InstanceId × Option String)) :
    Agrees (select fsI st s top trigger extra leaves) (select fs st s top trigger extra leaves) := by
  unfold select; agree [pick_agrees h]

theorem startCopy_agrees (step : Nat) (owner : InstanceId) (map : String) (key encodedKey : Value) (r : Processing) :
    Agrees (startCopy fsI st step owner map key encodedKey r) (startCopy fs st step owner map key encodedKey r) := by
  unfold startCopy; refine withMachine_agrees (fun i r => ?_) r; agree [h.defaults, enter_agrees h]

theorem exitLeftCopy_agrees (owner : InstanceId) (map : String) (itemKeys : List Value) (r : Processing) (k : Value) :
    Agrees (exitLeftCopy fsI st owner map itemKeys r k) (exitLeftCopy fs st owner map itemKeys r k) := by
  unfold exitLeftCopy; agree [unlessHalted_agrees, endWith_agrees (exitOne_agrees h _)]

theorem syncMap_agrees (step : Nat) (owner : InstanceId) (r : Processing) (map : String) :
    Agrees (syncMap fsI st step owner r map) (syncMap fs st step owner r map) := by
  unfold syncMap; agree [h.items, exitLeftCopy_agrees h, unlessHalted_agrees, startCopy_agrees h]

theorem syncCopies_agrees (step : Nat) (owner : InstanceId) (r : Processing) :
    Agrees (syncCopies fsI st step owner r) (syncCopies fs st step owner r) := by
  unfold syncCopies; agree [syncMap_agrees h]

theorem alwaysRound_agrees (step : Nat) (owner : InstanceId)
    {k : Instance → List (InstanceId × Transition) → Processing → StateT C Id Processing}
    {k' : Instance → List (InstanceId × Transition) → Processing → Id Processing} (hk : ∀ o c r, Agrees (k o c r) (k' o c r))
    (r : Processing) : Agrees (alwaysRound fsI st step owner k r) (alwaysRound fs st step owner k' r) := by
  unfold alwaysRound; agree [syncCopies_agrees h, select_agrees h, hk]

theorem settleFrom_agrees (step : Nat) (owner : InstanceId) (roundsLeft : Nat) (r : Processing) :
    Agrees (settleFrom fsI st step owner roundsLeft r) (settleFrom fs st step owner roundsLeft r) := by
  induction roundsLeft generalizing r with
  | zero => unfold settleFrom; exact alwaysRound_agrees h step owner (fun _ _ _ => Agrees.pure _) r
  | succ n ih =>
    unfold settleFrom
    exact alwaysRound_agrees h step owner (fun _ _ r => by agree [microstep_agrees h, ih]) r

theorem settle_agrees (step : Nat) (name : InstanceId) (r : Processing) :
    Agrees (settle fsI st step name r) (settle fs st step name r) := by
  unfold settle; exact settleFrom_agrees h step _ _ r

theorem settleAround_agrees (step : Nat) (owner : InstanceId) {f : Processing → StateT C Id Processing}
    {g : Processing → Id Processing} (hf : ∀ r, Agrees (f r) (g r)) (r : Processing) :
    Agrees (settleAround fsI st step owner f r) (settleAround fs st step owner g r) := by
  unfold settleAround; agree [settleFrom_agrees h, unlessHalted_agrees hf]

theorem settled_agrees (step : Nat) (name : Option InstanceId) {f : Processing → StateT C Id Processing}
    {g : Processing → Id Processing} (hf : ∀ r, Agrees (f r) (g r)) (r : Processing) :
    Agrees (settled fsI st step name f r) (settled fs st step name g r) := by
  cases name with
  | none => exact hf r
  | some n => unfold settled; agree [note_agrees, settleAround_agrees h step _ hf]

theorem applyCompletion_agrees (step : Nat) (name : InstanceId) (ts : List Transition) (extra : Extra) (r : Processing) :
    Agrees (applyCompletion fsI st step name ts extra r) (applyCompletion fs st step name ts extra r) := by
  unfold applyCompletion; refine withMachine_agrees (fun i r => ?_) r
  agree [choose_agrees h, microstep_agrees h]

theorem handle_agrees (step : Nat) (name : InstanceId) (state : String) (a : Activity) (answer : Answer) (r : Processing) :
    Agrees (handle fsI st step name state a answer r) (handle fs st step name state a answer r) := by
  unfold handle; refine withMachine_agrees (fun i r => ?_) r; agree [applyCompletion_agrees h]

theorem dispatch_agrees (step : Nat) (name : InstanceId) (key : String) (payload : Value) (r : Processing) :
    Agrees (dispatch fsI st step name key payload r) (dispatch fs st step name key payload r) := by
  unfold dispatch
  agree [eventLeaves_agrees h, select_agrees h, microstep_agrees h]

theorem receiveWork_agrees (step : Nat) (name : InstanceId) (groups : List (List Received)) (r : Processing) :
    Agrees (receiveWork fsI st step name groups r) (receiveWork fs st step name groups r) := by
  unfold receiveWork; split <;> agree [dispatch_agrees h, settle_agrees h]

theorem done_agrees (step : Nat) (name : InstanceId) (n : String) (r : Processing) :
    Agrees (done fsI st step name n r) (done fs st step name n r) := by
  unfold done; refine withMachine_agrees (fun i r => ?_) r; agree [applyCompletion_agrees h]

theorem doneWork_agrees (step : Nat) (name : InstanceId) (fuel : Nat) (r : Processing) :
    Agrees (doneWork fsI st step name fuel r) (doneWork fs st step name fuel r) := by
  induction fuel generalizing r with
  | zero => unfold doneWork; agree []
  | succ fuel ih => unfold doneWork; agree [settle_agrees h, done_agrees h, ih]

theorem startWork_agrees (step : Nat) (name : InstanceId) (r : Processing) :
    Agrees (startWork fsI st step name r) (startWork fs st step name r) := by
  unfold startWork; refine withMachine_agrees (fun i r => ?_) r; agree [enter_agrees h, unlessHalted_agrees, settle_agrees h]

theorem answerTo_agrees (step : Nat) (a : Activity) (answer : Answer) (requester : Requester) (r : Processing) :
    Agrees (answerTo fsI st step a answer requester r) (answerTo fs st step a answer requester r) := by
  cases requester <;> unfold answerTo <;> agree [handle_agrees h]

theorem deliverAnswer_agrees (step : Nat) (p : Pending) (answer : Answer) (r : Processing) :
    Agrees (deliverAnswer fsI st step p answer r) (deliverAnswer fs st step p answer r) := by
  unfold deliverAnswer; agree [answerTo_agrees h]

theorem normalizeEmits_agrees (name : String) (emits : List Emit) :
    Agrees (normalizeEmits st fsI name emits) (normalizeEmits st fs name emits) := by
  unfold normalizeEmits; agree [h.normalize, sorted_agrees]

theorem runWork_agrees (s : State) (q : Queue) (step : Nat) (w : Work) :
    Agrees (runWork st fsI s q step w) (runWork st fs s q step w) := by
  unfold runWork
  refine settled_agrees h step _ (fun r => ?_) _
  obtain ⟨s, q⟩ := r
  cases w <;> unfold workBody <;>
    agree [firstFalse_agrees (fun _ => h.automationBinding _ _ _ _ _),
      firstFalse_agrees (fun _ => h.automationGuard _ _ _ _ _), h.react, h.normalize, answerTo_agrees h, startWork_agrees h, receiveWork_agrees h, doneWork_agrees h,
      withMachine_agrees, applyCompletion_agrees h]

theorem resolveChecked_agrees (s : State) (name : String) (raw : Value) :
    Agrees (resolveChecked st fsI s name raw) (resolveChecked st fs s name raw) := by
  unfold resolveChecked normalizeOutput; agree [h.parse, firstFalse_agrees (fun _ => h.inputRequirement _ _ _), h.resolve, h.normalize,
    h.queryEnsures, sorted_agrees]

theorem publishOne_agrees (s : State) (sub : Subscription) :
    Agrees (publishOne st fsI s sub) (publishOne st fs s sub) := by
  unfold publishOne; agree [resolveChecked_agrees h, h.comparable]

theorem publish_agrees (s : State) : Agrees (publish st fsI s) (publish st fs s) := by
  unfold publish; agree [publishOne_agrees h]

omit [MonadNote (StateT C Id)] in
theorem wantedShows_agrees (s : State) (i : Instance) : Agrees (wantedShows st fsI s i) (wantedShows st fs s i) := by
  unfold wantedShows; agree [h.showInput]

omit [MonadNote (StateT C Id)] in
theorem refresh_agrees (s : State) (owner : InstanceId) : Agrees (refresh st fsI s owner) (refresh st fs s owner) := by
  unfold refresh; agree [wantedShows_agrees h]

omit [MonadNote (StateT C Id)] in
theorem refreshScreens_agrees (s : State) : Agrees (refreshScreens st fsI s) (refreshScreens st fs s) := by
  unfold refreshScreens; agree [refresh_agrees h]

theorem offeringStates_agrees (s : State) (top : Instance) (control : String) (payload : Value) :
    Agrees (offeringStates fsI st s top control payload) (offeringStates fs st s top control payload) := by
  unfold offeringStates; agree [reachedCopies_agrees h]

theorem offered_agrees (s : State) (top : Instance) (control : String) (payload : Value) :
    Agrees (offered fsI st s top control payload) (offered fs st s top control payload) := by
  unfold offered; agree [offeringStates_agrees h, h.offers]

theorem acceptsOperation_agrees (s : State) (screen : InstanceId) (control : String) (payload : Value) :
    Agrees (acceptsOperation fsI st s screen control payload) (acceptsOperation fs st s screen control payload) := by
  unfold acceptsOperation; agree [offered_agrees h]

theorem fire_agrees (step : Nat) (t : Deadline) (r : Processing) :
    Agrees (fire fsI st step t r) (fire fs st step t r) := by
  unfold fire; agree [withMachine_agrees, applyCompletion_agrees h]

omit [MonadNote (StateT C Id)] in
theorem invariantViolations_agrees (s : State) :
    Agrees (invariantViolations st fsI s) (invariantViolations st fs s) := by
  unfold invariantViolations
  exact Agrees.bind (Agrees.mapM (fun _ => Agrees.bind (h.chartInvariant _ _) fun r => by
    cases r <;> exact Agrees.pure _) _) fun _ => Agrees.pure _

omit [MonadNote (StateT C Id)] in
theorem checkInvariants_agrees (s : State) : Agrees (checkInvariants st fsI s) (checkInvariants st fs s) := by
  unfold checkInvariants; exact Agrees.bind (invariantViolations_agrees h s) fun _ => Agrees.pure _

theorem afterMessage_agrees (s : State) : Agrees (afterMessage st fsI s) (afterMessage st fs s) := by
  unfold afterMessage
  agree [refreshScreens_agrees h, checkInvariants_agrees h, publish_agrees h]

omit [MonadNote (StateT C Id)] in
theorem startInstance_agrees (s : State) (c : Chart) : Agrees (startInstance st fsI s c) (startInstance st fs s c) := by
  unfold startInstance; agree [initialContextOf_agrees h]

omit [MonadNote (StateT C Id)] in
theorem commandEnsures_agrees (name : String) (input : Value) (before after : Records) (now : Time) :
    Agrees (commandEnsures st fsI name input before after now) (commandEnsures st fs name input before after now) := by
  unfold commandEnsures; agree [h.ensures]

omit [MonadNote (StateT C Id)] in
theorem integrityViolations_agrees (records : Records) (name : String) :
    Agrees (integrityViolations st fsI records name) (integrityViolations st fs records name) := by
  unfold integrityViolations
  refine Agrees.bind (Agrees.mapM (fun row => ?_) _) (fun _ => ?_)
  · unfold rowViolations
    exact Agrees.bind (h.invariant _ _) fun r => by rcases r with _ | _ | _ <;> exact Agrees.pure _
  · exact Agrees.bind (h.serviceInvariant _) fun r => by rcases r with _ | _ | _ <;> exact Agrees.pure _

theorem requirementsRejection_agrees (records : Records) (now : Time) (name : String) (input : Value) :
    Agrees (requirementsRejection st fsI records now name input) (requirementsRejection st fs records now name input) := by
  unfold requirementsRejection
  agree [note_agrees, firstFalse_agrees (fun _ => h.binding _ _ _ _ _), firstFalse_agrees (fun _ => h.requirement _ _ _ _ _)]

theorem evaluate_agrees (records : Records) (now : Time) (name : String) (raw : Value) :
    Agrees (evaluate st fsI records now name raw) (evaluate st fs records now name raw) := by
  unfold evaluate
  agree [h.parse, requirementsRejection_agrees h, h.decide, normalizeEmits_agrees h, commandEnsures_agrees h,
    integrityViolations_agrees h]

theorem processCommand_agrees (s : State) (name : String) (raw : Value) (id : Option LineId) (step : Nat) :
    Agrees (processCommand st fsI s name raw id step) (processCommand st fs s name raw id step) := by
  unfold processCommand; agree [evaluate_agrees h, note_agrees]

theorem settleScreen_agrees (name : InstanceId) (r : Processing) :
    Agrees (settleScreen st fsI name r) (settleScreen st fs name r) := by
  unfold settleScreen; agree [note_agrees, settle_agrees h]

theorem drain_agrees (fuel : Nat) (s : State) (q : Queue) :
    Agrees (drain st fsI fuel s q) (drain st fs fuel s q) := by
  induction fuel generalizing s q with
  | zero => simp only [drain]; agree [refreshScreens_agrees h]
  | succ fuel ih =>
    simp only [drain]
    agree [runWork_agrees h, processCommand_agrees h, sendEntered_agrees h, refreshScreens_agrees h,
      settleScreen_agrees h, ih]

theorem fireDue_agrees (to : Time) (fuel : Nat) (tie : Option Time) (s : State) :
    Agrees (fireDue st fsI to fuel tie s) (fireDue st fs to fuel tie s) := by
  induction fuel generalizing s tie with
  | zero => unfold fireDue; agree []
  | succ fuel ih => unfold fireDue; agree [note_agrees, settled_agrees h, fire_agrees h, drain_agrees h, afterMessage_agrees h, ih]

theorem finish_agrees (s : State) : Agrees (finish st fsI s) (finish st fs s) := by
  unfold finish; agree [afterMessage_agrees h, fireDue_agrees h]

theorem message_agrees (s : State) (q : Queue) : Agrees (message st fsI s q) (message st fs s q) := by
  unfold message; agree [drain_agrees h, finish_agrees h]

theorem send_agrees (s : State) (name : Spec.Ref) (id : Option LineId) (raw : Value) :
    Agrees (send st fsI s name id raw) (send st fs s name id raw) := by
  unfold send; agree [message_agrees h, processCommand_agrees h]

theorem call_agrees (s : State) (name : Spec.Ref) (id : Option LineId) (raw : Value) :
    Agrees (call st fsI s name id raw) (call st fs s name id raw) := by
  unfold call; agree [resolveChecked_agrees h, message_agrees h]

theorem subscribe_agrees (s : State) (name : Spec.Ref) (id : Option LineId) (raw : Value) :
    Agrees (subscribe st fsI s name id raw) (subscribe st fs s name id raw) := by
  unfold subscribe; agree [message_agrees h]

theorem endSubscription_agrees (s : State) (id : LineId) :
    Agrees (endSubscription st fsI s id) (endSubscription st fs s id) := by
  unfold endSubscription; agree [message_agrees h]

theorem deliver_agrees (s : State) (name : Spec.Ref) (id : LineId) (raw payload : Value)
    (request : Option LineId) :
    Agrees (deliver st fsI s name id raw payload request) (deliver st fs s name id raw payload request) := by
  unfold deliver; exact message_agrees h _ _

theorem redeliver_agrees (s : State) (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId) :
    Agrees (redeliver st fsI s name id raw resultOf) (redeliver st fs s name id raw resultOf) := by
  unfold redeliver; agree [message_agrees h]

theorem receive_agrees (s : State) (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId) :
    Agrees (receive st fsI s name id raw resultOf) (receive st fs s name id raw resultOf) := by
  unfold receive; agree [h.parse, deliver_agrees h, redeliver_agrees h]

omit [MonadNote (StateT C Id)] in
theorem decodedOutput_agrees (target : Spec.Ref) (answer : Answer) :
    Agrees (decodedOutput st fsI target answer) (decodedOutput st fs target answer) := by
  unfold decodedOutput; agree [h.parse]

omit [MonadNote (StateT C Id)] in
theorem decodedAnswer_agrees (id : LineId) (target : Spec.Ref) (answer : Answer) :
    Agrees (decodedAnswer st fsI id target answer) (decodedAnswer st fs id target answer) := by
  unfold decodedAnswer
  dsimp only
  agree [decodedOutput_agrees h]

omit [MonadNote (StateT C Id)] in
theorem checkAnswer_agrees (p : Pending) (answer : Answer) :
    Agrees (checkAnswer st fsI p answer) (checkAnswer st fs p answer) := by
  unfold checkAnswer
  dsimp only
  agree [decodedAnswer_agrees h]

theorem answerRequest_agrees (s : State) (id : Option LineId) (p : Pending) (answer : Answer) :
    Agrees (answerRequest st fsI s id p answer) (answerRequest st fs s id p answer) := by
  unfold answerRequest
  agree [checkAnswer_agrees h, settled_agrees h, deliverAnswer_agrees h, message_agrees h]

theorem answerIn_agrees (s : State) (id to : LineId) (answer : Answer) :
    Agrees (answerIn st fsI s id to answer) (answerIn st fs s id to answer) := by
  unfold answerIn; agree [message_agrees h, answerRequest_agrees h]

omit [MonadNote (StateT C Id)] in
theorem decodedEvents_agrees (x : Exchange) : Agrees (decodedEvents fsI x) (decodedEvents fs x) := by
  unfold decodedEvents; agree [h.parse]

theorem checkAssumedAnswer_agrees (x : Exchange) (input : Value) (events : List Emit) (s : State) (a : Answer) :
    Agrees (checkAssumedAnswer st fsI x input events s a) (checkAssumedAnswer st fs x input events s a) := by
  unfold checkAssumedAnswer
  agree [decodedAnswer_agrees h, firstFalse_agrees (fun _ => h.inputRequirement _ _ _),
    firstFalse_agrees (fun _ => Agrees.map _ (h.resultEnsures _ _ _ _ _))]

theorem checkExchanges_agrees (s : State) : Agrees (checkExchanges st fsI s) (checkExchanges st fs s) := by
  unfold checkExchanges checkExchange
  agree [h.parse, decodedEvents_agrees h, checkAssumedAnswer_agrees h]

theorem startRecords_agrees (s : State) : Agrees (startRecords st fsI s) (startRecords st fs s) := by
  unfold startRecords; agree [h.defaults, expectFound_agrees]

theorem begin_agrees (s : State) : Agrees (begin st fsI s) (begin st fs s) := by
  unfold begin startInstances; agree [startRecords_agrees h, startInstance_agrees h, message_agrees h]

theorem operate_agrees (s : State) (screen : InstanceId) (control : String) (payload : Value) :
    Agrees (operate st fsI s screen control payload) (operate st fs s screen control payload) := by
  unfold operate
  dsimp only
  split
  · exact Agrees.pure _
  split
  · exact Agrees.pure _
  refine Agrees.bind (h.parse _ _) (fun _ => ?_)
  split
  · exact Agrees.pure _
  · exact Agrees.pure _
  refine Agrees.bind (acceptsOperation_agrees h _ _ _ _) (fun _ => ?_)
  split
  · exact Agrees.pure _
  · exact Agrees.bind (settled_agrees h _ _ (dispatch_agrees h _ _ _ _) _) (fun _ => message_agrees h _ _)
  · exact Agrees.pure _

theorem restart_agrees (s : State) : Agrees (restart st fsI s) (restart st fs s) := by
  unfold restart; exact begin_agrees h _

end

end Tazuna.Thm.Explore.Instrument

namespace Tazuna.Thm.Explore.Instrument

open Tazuna.Data Tazuna.Service Tazuna.Explore Tazuna.Sim Tazuna.Thm.Data.List

variable {C : Type} {st : Service} {fs : Functions Id} {ifs : InstrumentFunctions Id}

theorem Agrees.lift {α : Type} (x : Id α) : Agrees (C := C) (liftM x) x := by
  unfold Agrees; intro _; rfl

theorem observe_agrees {α : Type} (x : Id α) (f : α → StateT Collect Id Unit) : Agrees (observe x f) x := by
  unfold Agrees observe; intro _; rfl

theorem instrument_agrees : FunctionsAgree (instrument st fs ifs) fs := by
  constructor <;> intros <;> first | exact observe_agrees _ _ | exact Agrees.lift _

end Tazuna.Thm.Explore.Instrument
