import Tazuna.Observe.Instrument
import Tazuna.Thm.Data.List

/-!
Semantics definitions are generic in `m`, so instrumented functions that agree with the plain ones (FunctionsAgree) make
every instrumented definition agree with its plain one.
-/

namespace Tazuna.Thm.Observe.Instrument

open Tazuna.Data Tazuna.Semantics Tazuna.Observe Tazuna.Thm.Data.List

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

theorem Agrees.modifyThen {α : Type} {g : C → C} {x : StateT C Id α} {a : α} (hx : Agrees x a) :
    Agrees (modify g *> x) a := by
  unfold Agrees at *
  intro c
  exact hx _

structure FunctionsAgree (fsI : Functions (StateT C Id)) (fs : Functions Id) : Prop where
  parse : ∀ a b, Agrees (fsI.parse a b) (fs.parse a b)
  canonical : ∀ a b, Agrees (fsI.canonical a b) (fs.canonical a b)
  unordered : ∀ a b, Agrees (fsI.unordered a b) (fs.unordered a b)
  normalize : ∀ a b, Agrees (fsI.normalize a b) (fs.normalize a b)
  binding : ∀ a b c d e, Agrees (fsI.binding a b c d e) (fs.binding a b c d e)
  requirement : ∀ a b c d e, Agrees (fsI.requirement a b c d e) (fs.requirement a b c d e)
  inputRequirement : ∀ a b c, Agrees (fsI.inputRequirement a b c) (fs.inputRequirement a b c)
  decide : ∀ a b c d, Agrees (fsI.decide a b c d) (fs.decide a b c d)
  ensures : ∀ a b c d e, Agrees (fsI.ensures a b c d e) (fs.ensures a b c d e)
  queryEnsures : ∀ a b c d, Agrees (fsI.queryEnsures a b c d) (fs.queryEnsures a b c d)
  resultEnsures : ∀ a b c d, Agrees (fsI.resultEnsures a b c d) (fs.resultEnsures a b c d)
  invariant : ∀ a b, Agrees (fsI.invariant a b) (fs.invariant a b)
  serviceInvariant : ∀ a, Agrees (fsI.serviceInvariant a) (fs.serviceInvariant a)
  chartInvariant : ∀ a b, Agrees (fsI.chartInvariant a b) (fs.chartInvariant a b)
  resolve : ∀ a b c d, Agrees (fsI.resolve a b c d) (fs.resolve a b c d)
  react : ∀ a b c d e, Agrees (fsI.react a b c d e) (fs.react a b c d e)
  comparable : ∀ a b, Agrees (fsI.comparable a b) (fs.comparable a b)
  initialContext : ∀ a b, Agrees (fsI.initialContext a b) (fs.initialContext a b)
  guard : ∀ a b c d, Agrees (fsI.guard a b c d) (fs.guard a b c d)
  assign : ∀ a b c d e, Agrees (fsI.assign a b c d e) (fs.assign a b c d e)
  input : ∀ a b c d, Agrees (fsI.input a b c d) (fs.input a b c d)
  holds : ∀ a b, Agrees (fsI.holds a b) (fs.holds a b)
  deadlines : ∀ a b, Agrees (fsI.deadlines a b) (fs.deadlines a b)
  deadlineAt : ∀ a b c, Agrees (fsI.deadlineAt a b c) (fs.deadlineAt a b c)
  offers : ∀ a b c, Agrees (fsI.offers a b c) (fs.offers a b c)
  showInput : ∀ a b c, Agrees (fsI.showInput a b c) (fs.showInput a b c)
  items : ∀ a b, Agrees (fsI.items a b) (fs.items a b)
  copyContext : ∀ a b, Agrees (fsI.copyContext a b) (fs.copyContext a b)
  singleRecord : ∀ a, Agrees (fsI.singleRecord a) (fs.singleRecord a)
  copyKey : ∀ a b c, Agrees (fsI.copyKey a b c) (fs.copyKey a b c)
  close : ∀ a b, Agrees (fsI.close a b) (fs.close a b)

theorem note_agrees [MonadNote (StateT C Id)] (n : Note) :
    Agrees (MonadNote.note n : StateT C Id Unit) (MonadNote.note n : Id Unit) := by
  unfold Agrees; intro _; rfl

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
theorem withMachine_agrees {name : String} {f : Instance → Processing → StateT C Id Processing}
    {g : Instance → Processing → Id Processing} (hf : ∀ i r, Agrees (f i r) (g i r)) (r : Processing) :
    Agrees (withMachine name f r) (withMachine name g r) := by
  unfold withMachine; agree [hf]

omit [MonadNote (StateT C Id)] in
theorem endWith_agrees {e : String → String → Processing → StateT C Id Processing}
    {e' : String → String → Processing → Id Processing} (he : ∀ c n r, Agrees (e c n r) (e' c n r))
    (c : String) (r : Processing) : Agrees (endWith e c r) (endWith e' c r) := by
  unfold endWith; refine withMachine_agrees (fun i r => ?_) r; agree [unlessHalted_agrees, he]

section
variable (h : FunctionsAgree fsI fs)
include h

omit [MonadNote (StateT C Id)] in
theorem runAssign_agrees (name : String) (a : Assignment) (scope : Option String) (extra : Extra) (r : Processing) :
    Agrees (runAssign fsI st name a scope extra r) (runAssign fs st name a scope extra r) := by
  unfold runAssign; refine withMachine_agrees (fun i r => ?_) r; agree [h.assign]

theorem leaveWith_agrees {e : String → String → Processing → StateT C Id Processing}
    {e' : String → String → Processing → Id Processing} (he : ∀ c n r, Agrees (e c n r) (e' c n r))
    (name n : String) (r : Processing) :
    Agrees (leaveWith fsI st e name n r) (leaveWith fs st e' name n r) := by
  unfold leaveWith; agree [runAssign_agrees h, unlessHalted_agrees, endWith_agrees he]

theorem exitOne_agrees (fuel : Nat) (name n : String) (r : Processing) :
    Agrees (exitOne fsI st fuel name n r) (exitOne fs st fuel name n r) := by
  induction fuel generalizing name n r with
  | zero => exact Agrees.pure _
  | succ fuel ih =>
    unfold exitOne; refine withMachine_agrees (fun i r => ?_) r
    agree [unlessHalted_agrees, endWith_agrees ih, leaveWith_agrees h ih]

theorem closeFinal_agrees (step : Nat) (name : String) (r : Processing) :
    Agrees (closeFinal fsI st step name r) (closeFinal fs st step name r) := by
  unfold closeFinal; refine withMachine_agrees (fun i r => ?_) r
  agree [h.close, endWith_agrees (exitOne_agrees h _)]

omit [MonadNote (StateT C Id)] in
theorem rearm_agrees (s : State) : Agrees (rearm st fsI s) (rearm st fs s) := by
  unfold rearm; agree [h.deadlineAt]

omit [MonadNote (StateT C Id)] in
theorem request_agrees (step : Nat) (name state : String) (a : Activity) (r : Processing) :
    Agrees (request fsI st step name state a r) (request fs st step name state a r) := by
  unfold request; refine withMachine_agrees (fun i r => ?_) r; agree [h.input]

omit [MonadNote (StateT C Id)] in
theorem initialContextOf_agrees (chart : String) (input : Value) :
    Agrees (initialContextOf fsI st chart input) (initialContextOf fs st chart input) := by
  unfold initialContextOf; agree [h.initialContext]

omit [MonadNote (StateT C Id)] in
theorem openScreen_agrees (step : Nat) (name state : String) (a : Activity) (r : Processing) :
    Agrees (openScreen fsI st step name state a r) (openScreen fs st step name state a r) := by
  unfold openScreen; refine withMachine_agrees (fun i r => ?_) r; agree [h.input, firstFalse_agrees (fun _ => h.inputRequirement _ _ _), initialContextOf_agrees h]

omit [MonadNote (StateT C Id)] in
theorem activate_agrees (step : Nat) (name state : String) (a : Activity) (r : Processing) :
    Agrees (activate fsI st step name state a r) (activate fs st step name state a r) := by
  unfold activate; agree [openScreen_agrees h, request_agrees h]

theorem activateEntered_agrees (e : String × String × Nat) (r : Processing) :
    Agrees (activateEntered fsI st e r) (activateEntered fs st e r) := by
  unfold activateEntered; refine withMachine_agrees (fun i r => ?_) r; agree [unlessHalted_agrees, activate_agrees h]

theorem sendEntered_agrees (r : Processing) : Agrees (sendEntered fsI st r) (sendEntered fs st r) := by
  unfold sendEntered; agree [activateEntered_agrees h]

theorem enterOne_agrees (step : Nat) (name n : String) (r : Processing) :
    Agrees (enterOne fsI st step name n r) (enterOne fs st step name n r) := by
  unfold enterOne; refine withMachine_agrees (fun i r => ?_) r
  agree [runAssign_agrees h, closeFinal_agrees h, endWith_agrees (exitOne_agrees h _), h.deadlines]

theorem enter_agrees (step : Nat) (name : String) (targets : List String) (r : Processing) :
    Agrees (enter fsI st step name targets r) (enter fs st step name targets r) := by
  unfold enter; refine withMachine_agrees (fun i r => ?_) r; agree [unlessHalted_agrees, enterOne_agrees h]

theorem microstep_agrees (step : Nat) (name : String) (chosen : List (String × Transition)) (extra : Extra) (r : Processing) :
    Agrees (microstep fsI st step name chosen extra r) (microstep fs st step name chosen extra r) := by
  unfold microstep; refine withMachine_agrees (fun i r => ?_) r
  agree [note_agrees, runAssign_agrees h, unlessHalted_agrees, exitOne_agrees h, enterOne_agrees h]

omit [MonadNote (StateT C Id)] in
theorem choose_agrees (s : State) (i : Instance) (extra : Extra) (ts : List Transition) :
    Agrees (choose fsI st s i extra ts) (choose fs st s i extra ts) := by
  induction ts with
  | nil => exact Agrees.pure _
  | cons t rest ih => unfold choose; agree [h.guard, ih]

theorem firstLevel_agrees (s : State) (extra : Extra) (levels : List (Instance × List Transition)) :
    Agrees (firstLevel fsI st s extra levels) (firstLevel fs st s extra levels) := by
  induction levels with
  | nil => exact Agrees.pure _
  | cons l rest ih => unfold firstLevel; agree [choose_agrees h, ih]

omit [MonadNote (StateT C Id)] in
theorem reaches_agrees (c : Instance) (payload : Value) : Agrees (reaches fsI st c payload) (reaches fs st c payload) := by
  unfold reaches; agree [h.copyKey]

omit [MonadNote (StateT C Id)] in
theorem reachedCopies_agrees (s : State) (top : Instance) (payload : Value) :
    Agrees (reachedCopies fsI st s top payload) (reachedCopies fs st s top payload) := by
  unfold reachedCopies; agree [reaches_agrees h]

omit [MonadNote (StateT C Id)] in
theorem eventLeaves_agrees (s : State) (top : Instance) (payload : Value) :
    Agrees (eventLeaves fsI st s top payload) (eventLeaves fs st s top payload) := by
  unfold eventLeaves; agree [reachedCopies_agrees h]

theorem pick_agrees (s : State) (top : Instance) (trigger : List String) (extra : Extra) (l : String × Option String) :
    Agrees (pick fsI st s top trigger extra l) (pick fs st s top trigger extra l) := by
  unfold pick; agree [firstLevel_agrees h]

theorem select_agrees (s : State) (top : Instance) (trigger : List String) (extra : Extra)
    (leaves : List (String × Option String)) :
    Agrees (select fsI st s top trigger extra leaves) (select fs st s top trigger extra leaves) := by
  unfold select; agree [pick_agrees h]

theorem startCopy_agrees (step : Nat) (owner map : String) (key : Value) (encodedKey : String) (r : Processing) :
    Agrees (startCopy fsI st step owner map key encodedKey r) (startCopy fs st step owner map key encodedKey r) := by
  unfold startCopy; refine withMachine_agrees (fun i r => ?_) r; agree [h.copyContext, enter_agrees h]

theorem exitLeftCopy_agrees (owner map : String) (itemKeys : List String) (r : Processing) (k : String) :
    Agrees (exitLeftCopy fsI st owner map itemKeys r k) (exitLeftCopy fs st owner map itemKeys r k) := by
  unfold exitLeftCopy; agree [unlessHalted_agrees, endWith_agrees (exitOne_agrees h _)]

theorem syncMap_agrees (step : Nat) (owner : String) (r : Processing) (map : String) :
    Agrees (syncMap fsI st step owner r map) (syncMap fs st step owner r map) := by
  unfold syncMap; agree [h.items, exitLeftCopy_agrees h, unlessHalted_agrees, startCopy_agrees h]

theorem syncCopies_agrees (step : Nat) (owner : String) (r : Processing) :
    Agrees (syncCopies fsI st step owner r) (syncCopies fs st step owner r) := by
  unfold syncCopies; agree [syncMap_agrees h]

theorem alwaysRound_agrees (step : Nat) (owner : String)
    {k : Instance → List (String × Transition) → Processing → StateT C Id Processing}
    {k' : Instance → List (String × Transition) → Processing → Id Processing} (hk : ∀ o c r, Agrees (k o c r) (k' o c r))
    (r : Processing) : Agrees (alwaysRound fsI st step owner k r) (alwaysRound fs st step owner k' r) := by
  unfold alwaysRound; agree [syncCopies_agrees h, select_agrees h, hk]

theorem settleFrom_agrees (step : Nat) (owner : String) (roundsLeft : Nat) (r : Processing) :
    Agrees (settleFrom fsI st step owner roundsLeft r) (settleFrom fs st step owner roundsLeft r) := by
  induction roundsLeft generalizing r with
  | zero => unfold settleFrom; exact alwaysRound_agrees h step owner (fun _ _ _ => Agrees.pure _) r
  | succ n ih =>
    unfold settleFrom
    exact alwaysRound_agrees h step owner (fun _ _ r => by agree [microstep_agrees h, ih]) r

theorem settle_agrees (step : Nat) (name : String) (r : Processing) :
    Agrees (settle fsI st step name r) (settle fs st step name r) := by
  unfold settle; exact settleFrom_agrees h step _ _ r

theorem settleAround_agrees (step : Nat) (owner : String) {f : Processing → StateT C Id Processing}
    {g : Processing → Id Processing} (hf : ∀ r, Agrees (f r) (g r)) (r : Processing) :
    Agrees (settleAround fsI st step owner f r) (settleAround fs st step owner g r) := by
  unfold settleAround; agree [settleFrom_agrees h, unlessHalted_agrees hf]

theorem settled_agrees (step : Nat) (name : Option String) {f : Processing → StateT C Id Processing}
    {g : Processing → Id Processing} (hf : ∀ r, Agrees (f r) (g r)) (r : Processing) :
    Agrees (settled fsI st step name f r) (settled fs st step name g r) := by
  cases name with
  | none => exact hf r
  | some n => unfold settled; agree [note_agrees, settleAround_agrees h step _ hf]

theorem applyCompletion_agrees (step : Nat) (name : String) (ts : List Transition) (extra : Extra) (r : Processing) :
    Agrees (applyCompletion fsI st step name ts extra r) (applyCompletion fs st step name ts extra r) := by
  unfold applyCompletion; refine withMachine_agrees (fun i r => ?_) r
  agree [choose_agrees h, microstep_agrees h]

theorem handle_agrees (step : Nat) (name state : String) (a : Activity) (answer : Answer) (r : Processing) :
    Agrees (handle fsI st step name state a answer r) (handle fs st step name state a answer r) := by
  unfold handle; refine withMachine_agrees (fun i r => ?_) r; agree [applyCompletion_agrees h]

theorem dispatch_agrees (step : Nat) (name key : String) (payload : Value) (r : Processing) :
    Agrees (dispatch fsI st step name key payload r) (dispatch fs st step name key payload r) := by
  unfold dispatch
  agree [eventLeaves_agrees h, select_agrees h, microstep_agrees h]

theorem receiveWork_agrees (step : Nat) (name : String) (received : List (String × Value)) (r : Processing) :
    Agrees (receiveWork fsI st step name received r) (receiveWork fs st step name received r) := by
  unfold receiveWork; agree [dispatch_agrees h, settle_agrees h]

theorem done_agrees (step : Nat) (name n : String) (r : Processing) :
    Agrees (done fsI st step name n r) (done fs st step name n r) := by
  unfold done; refine withMachine_agrees (fun i r => ?_) r; agree [applyCompletion_agrees h]

theorem doneWork_agrees (step : Nat) (name : String) (fuel : Nat) (r : Processing) :
    Agrees (doneWork fsI st step name fuel r) (doneWork fs st step name fuel r) := by
  induction fuel generalizing r with
  | zero => unfold doneWork; agree []
  | succ fuel ih => unfold doneWork; agree [settle_agrees h, done_agrees h, ih]

theorem startWork_agrees (step : Nat) (name : String) (r : Processing) :
    Agrees (startWork fsI st step name r) (startWork fs st step name r) := by
  unfold startWork; refine withMachine_agrees (fun i r => ?_) r; agree [enter_agrees h, unlessHalted_agrees, settle_agrees h]

theorem answerTo_agrees (step : Nat) (a : Activity) (answer : Answer) (requester : Requester) (r : Processing) :
    Agrees (answerTo fsI st step a answer requester r) (answerTo fs st step a answer requester r) := by
  cases requester <;> unfold answerTo <;> agree [handle_agrees h]

theorem deliverAnswer_agrees (step : Nat) (p : Pending) (answer : Answer) (r : Processing) :
    Agrees (deliverAnswer fsI st step p answer r) (deliverAnswer fs st step p answer r) := by
  unfold deliverAnswer; agree [answerTo_agrees h]

omit [MonadNote (StateT C Id)] in
theorem normalizeEmits_agrees (name : String) (emits : List Emit) :
    Agrees (normalizeEmits st fsI name emits) (normalizeEmits st fs name emits) := by
  unfold normalizeEmits; agree [h.normalize]

theorem runWork_agrees (s : State) (q : Queue) (step : Nat) (w : Work) :
    Agrees (runWork st fsI s q step w) (runWork st fs s q step w) := by
  unfold runWork
  refine settled_agrees h step _ (fun r => ?_) _
  obtain ⟨s, q⟩ := r
  cases w <;> unfold workBody <;>
    agree [h.react, h.normalize, answerTo_agrees h, startWork_agrees h, receiveWork_agrees h, doneWork_agrees h,
      withMachine_agrees, applyCompletion_agrees h]

omit [MonadNote (StateT C Id)] in
theorem resolveChecked_agrees (s : State) (name : String) (raw : Value) :
    Agrees (resolveChecked st fsI s name raw) (resolveChecked st fs s name raw) := by
  unfold resolveChecked normalizeOutput; agree [h.parse, firstFalse_agrees (fun _ => h.inputRequirement _ _ _), h.resolve, h.normalize,
    h.queryEnsures]

omit [MonadNote (StateT C Id)] in
theorem publishOne_agrees (s : State) (sub : Subscription) :
    Agrees (publishOne st fsI s sub) (publishOne st fs s sub) := by
  unfold publishOne; agree [resolveChecked_agrees h, h.comparable]

omit [MonadNote (StateT C Id)] in
theorem publish_agrees (s : State) : Agrees (publish st fsI s) (publish st fs s) := by
  unfold publish; agree [publishOne_agrees h]

omit [MonadNote (StateT C Id)] in
theorem wantedShows_agrees (s : State) (i : Instance) : Agrees (wantedShows st fsI s i) (wantedShows st fs s i) := by
  unfold wantedShows; agree [h.showInput]

omit [MonadNote (StateT C Id)] in
theorem refresh_agrees (s : State) (owner : String) : Agrees (refresh st fsI s owner) (refresh st fs s owner) := by
  unfold refresh; agree [wantedShows_agrees h]

omit [MonadNote (StateT C Id)] in
theorem refreshScreens_agrees (s : State) : Agrees (refreshScreens st fsI s) (refreshScreens st fs s) := by
  unfold refreshScreens; agree [refresh_agrees h]

omit [MonadNote (StateT C Id)] in
theorem offeringStates_agrees (s : State) (top : Instance) (control : String) (payload : Value) :
    Agrees (offeringStates fsI st s top control payload) (offeringStates fs st s top control payload) := by
  unfold offeringStates; agree [reachedCopies_agrees h]

omit [MonadNote (StateT C Id)] in
theorem offered_agrees (s : State) (top : Instance) (control : String) (payload : Value) :
    Agrees (offered fsI st s top control payload) (offered fs st s top control payload) := by
  unfold offered; agree [offeringStates_agrees h, h.offers]

omit [MonadNote (StateT C Id)] in
theorem acceptsOperation_agrees (s : State) (screen control : String) (payload : Value) :
    Agrees (acceptsOperation fsI st s screen control payload) (acceptsOperation fs st s screen control payload) := by
  unfold acceptsOperation; agree [offered_agrees h]

theorem fire_agrees (step : Nat) (t : Deadline) (r : Processing) :
    Agrees (fire fsI st step t r) (fire fs st step t r) := by
  unfold fire; agree [withMachine_agrees, applyCompletion_agrees h]

omit [MonadNote (StateT C Id)] in
theorem checkHolds_agrees (s : State) : Agrees (checkHolds st fsI s) (checkHolds st fs s) := by
  unfold checkHolds; agree [h.holds]

omit [MonadNote (StateT C Id)] in
theorem invariantViolations_agrees (s : State) :
    Agrees (invariantViolations st fsI s) (invariantViolations st fs s) := by
  unfold invariantViolations
  exact Agrees.bind (Agrees.mapM (fun _ => Agrees.bind (h.chartInvariant _ _) fun r => by
    cases r <;> exact Agrees.pure _) _) fun _ => Agrees.pure _

omit [MonadNote (StateT C Id)] in
theorem checkInvariants_agrees (s : State) : Agrees (checkInvariants st fsI s) (checkInvariants st fs s) := by
  unfold checkInvariants; exact Agrees.bind (invariantViolations_agrees h s) fun _ => Agrees.pure _

omit [MonadNote (StateT C Id)] in
theorem afterMessage_agrees (s : State) : Agrees (afterMessage st fsI s) (afterMessage st fs s) := by
  unfold afterMessage
  agree [refreshScreens_agrees h, checkHolds_agrees h, checkInvariants_agrees h, rearm_agrees h, publish_agrees h]

omit [MonadNote (StateT C Id)] in
theorem addResult_agrees (s : State) (id : String) (e : Emit) :
    Agrees (addResult st fsI s id e) (addResult st fs s id e) := by
  unfold addResult; agree [h.resultEnsures]

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

theorem processCommand_agrees (s : State) (name : String) (raw : Value) (id : Option String) (step : Nat) :
    Agrees (processCommand st fsI s name raw id step) (processCommand st fs s name raw id step) := by
  unfold processCommand; agree [evaluate_agrees h, note_agrees]

theorem settleScreen_agrees (name : String) (r : Processing) :
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

theorem send_agrees (s : State) (name : String) (id : Option String) (raw : Value) :
    Agrees (send st fsI s name id raw) (send st fs s name id raw) := by
  unfold send; agree [h.canonical, message_agrees h, processCommand_agrees h]

theorem call_agrees (s : State) (name : String) (id : Option String) (raw : Value) :
    Agrees (call st fsI s name id raw) (call st fs s name id raw) := by
  unfold call; agree [h.canonical, resolveChecked_agrees h, message_agrees h]

theorem subscribe_agrees (s : State) (name : String) (id : Option String) (raw : Value) (handle : Option String) :
    Agrees (subscribe st fsI s name id raw handle) (subscribe st fs s name id raw handle) := by
  unfold subscribe; agree [h.canonical, message_agrees h]

theorem endOpened_agrees (s : State) (id : String) :
    Agrees (endOpened st fsI s id) (endOpened st fs s id) := by
  unfold endOpened; agree [message_agrees h]

theorem endSubscription_agrees (s : State) (subscription : Ended) :
    Agrees (endSubscription st fsI s subscription) (endSubscription st fs s subscription) := by
  unfold endSubscription; agree [endOpened_agrees h]

theorem deliver_agrees (s : State) (name : String) (id : Option String) (payload : Value) (request : Option Pending) :
    Agrees (deliver st fsI s name id payload request) (deliver st fs s name id payload request) := by
  unfold deliver
  split
  dsimp only
  cases request
  · exact Agrees.bind (Agrees.pure _) (fun _ => message_agrees h _ _)
  · exact Agrees.bind (addResult_agrees h _ _ _) (fun _ => message_agrees h _ _)

theorem redeliver_agrees (s : State) (name : String) (id : Option String) (raw : Value) (resultOf : Option String)
    (first : Delivery) :
    Agrees (redeliver st fsI s name id raw resultOf first) (redeliver st fs s name id raw resultOf first) := by
  unfold redeliver; agree [h.canonical, message_agrees h]

theorem receive_agrees (s : State) (name : String) (id : Option String) (raw : Value) (resultOf : Option String) :
    Agrees (receive st fsI s name id raw resultOf) (receive st fs s name id raw resultOf) := by
  unfold receive; agree [h.parse, deliver_agrees h, redeliver_agrees h]

omit [MonadNote (StateT C Id)] in
theorem chosen_agrees (name : String) (input : Value) (ps : List Pending) :
    Agrees (chosen st fsI name input ps) (chosen st fs name input ps) := by
  induction ps with
  | nil => exact Agrees.pure _
  | cons p ps ih => simp only [chosen]; agree [h.canonical, ih]

omit [MonadNote (StateT C Id)] in
theorem answerable_agrees (s : State) (sender name : String) (choice : Option Choice) :
    Agrees (s.answerable st fsI sender name choice) (s.answerable st fs sender name choice) := by
  unfold State.answerable; agree [chosen_agrees h]

omit [MonadNote (StateT C Id)] in
theorem writtenAnswer_agrees (a : Activity) (answer : Answer) :
    Agrees (writtenAnswer st fsI a answer) (writtenAnswer st fs a answer) := by
  unfold writtenAnswer; agree [h.parse]

omit [MonadNote (StateT C Id)] in
theorem checkAnswer_agrees (p : Pending) (answer : Answer) :
    Agrees (checkAnswer st fsI p answer) (checkAnswer st fs p answer) := by
  unfold checkAnswer
  dsimp only
  agree [firstFalse_agrees (fun _ => h.inputRequirement _ _ _), writtenAnswer_agrees h, h.resultEnsures]

omit [MonadNote (StateT C Id)] in
theorem answering_agrees (s : State) (sender name : String) (choice : Option Choice) :
    Agrees (s.answering st fsI sender name choice) (s.answering st fs sender name choice) := by
  unfold State.answering; agree [answerable_agrees h]

theorem answerRequest_agrees (s : State) (p : Pending) (answer : Answer) :
    Agrees (answerRequest st fsI s p answer) (answerRequest st fs s p answer) := by
  unfold answerRequest
  agree [checkAnswer_agrees h, settled_agrees h, deliverAnswer_agrees h, message_agrees h]

theorem mock_agrees (s : State) (sender name : String) (answer : Answer) (choice : Option Choice)
    (handle : Option String) :
    Agrees (mock st fsI s sender name answer choice handle) (mock st fs s sender name answer choice handle) := by
  unfold mock
  agree [answering_agrees h, answerRequest_agrees h]

theorem answerById_agrees (s : State) (to target : String) (answer : Answer) :
    Agrees (answerById st fsI s to target answer) (answerById st fs s to target answer) := by
  unfold answerById
  agree [answerRequest_agrees h]

omit [MonadNote (StateT C Id)] in
theorem startRecords_agrees (s : State) : Agrees (startRecords st fsI s) (startRecords st fs s) := by
  unfold startRecords; agree [h.singleRecord]

theorem begin_agrees (s : State) : Agrees (begin st fsI s) (begin st fs s) := by
  unfold begin startInstances; agree [startRecords_agrees h, startInstance_agrees h, message_agrees h]

theorem advance_agrees (s : State) (input : Step) : Agrees (advance st fsI s input) (advance st fs s input) := by
  unfold advance
  dsimp only
  split
  · exact Agrees.pure _
  refine Agrees.bind (fireDue_agrees h _ _ _ _) (fun _ => ?_)
  split
  · exact Agrees.pure _
  split
  · exact Agrees.pure _
  · exact begin_agrees h _

theorem operate_agrees (s : State) (screen control : String) (payload : Value) (accepted : Bool) :
    Agrees (operate st fsI s screen control payload accepted) (operate st fs s screen control payload accepted) := by
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
  split
  · exact Agrees.bind (settled_agrees h _ _ (dispatch_agrees h _ _ _ _) _) (fun _ => message_agrees h _ _)
  · exact message_agrees h _ _
  · exact Agrees.pure _
  · exact Agrees.pure _

theorem restart_agrees (s : State) : Agrees (restart st fsI s) (restart st fs s) := by
  unfold restart; exact begin_agrees h _

theorem arrive_agrees (s : State) (input : Step) : Agrees (arrive st fsI s input) (arrive st fs s input) := by
  unfold arrive
  agree [restart_agrees h, send_agrees h, call_agrees h, subscribe_agrees h, endSubscription_agrees h, receive_agrees h, mock_agrees h,
    answerById_agrees h, operate_agrees h]

theorem step_agrees (s : State) (input : Step) : Agrees (step st fsI s input) (step st fs s input) := by
  unfold step
  agree [advance_agrees h, arrive_agrees h]

end

end Tazuna.Thm.Observe.Instrument

namespace Tazuna.Thm.Observe.Instrument

open Tazuna.Data Tazuna.Semantics Tazuna.Observe Tazuna.Thm.Data.List

variable {C : Type} {st : Service} {fs : Functions Id} {ifs : InstrumentFunctions Id}

theorem Agrees.lift {α : Type} (x : Id α) : Agrees (C := C) (liftM x) x := by
  unfold Agrees; intro _; rfl

theorem observe_agrees {α : Type} (x : Id α) (f : α → StateT Collect Id Unit) : Agrees (observe x f) x := by
  unfold Agrees observe; intro _; rfl

theorem instrument_agrees : FunctionsAgree (instrument st fs ifs) fs := by
  constructor <;> intros <;> first | exact observe_agrees _ _ | exact Agrees.lift _

theorem reversed_result_reported {ε α : Type} (definition : Syntax.Ref) (function : String) (original answer : α)
    (again : Id (Except ε α)) (same : α → α → Bool) (c : Collect) (ha : again = .ok answer) :
    ((orderAudit definition function original again same).run c).2 =
      if definition ∈ c.reportedOrder ∨ same original answer then c
      else c.reportOrder definition (OrderDependent.reversedResult definition function).toViolation := by
  by_cases hm : definition ∈ c.reportedOrder
  · simp [orderAudit, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, hm]
  · simp only [StateT.run, orderAudit, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, hm,
      ↓reduceIte, liftM, monadLift, MonadLift.monadLift, StateT.lift, ha, reportOrder, modify, modifyGet,
      MonadStateOf.modifyGet, false_or]
    split <;> rfl

theorem reversed_exception_reported {ε α : Type} (definition : Syntax.Ref) (function : String) (original : α)
    (again : Id (Except ε α)) (same : α → α → Bool) (e : ε) (c : Collect) (ha : again = .error e) :
    ((orderAudit definition function original again same).run c).2 =
      if definition ∈ c.reportedOrder then c
      else c.reportOrder definition (OrderDependent.reversedException definition function).toViolation := by
  by_cases hm : definition ∈ c.reportedOrder
  · simp [orderAudit, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, hm]
  · simp only [StateT.run, orderAudit, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, hm,
      ↓reduceIte, liftM, monadLift, MonadLift.monadLift, StateT.lift, ha, reportOrder, modify, modifyGet,
      MonadStateOf.modifyGet]
    rfl

theorem report_keeps (c : Collect) (v w : Violation) (h : v ∈ c.violations) : v ∈ (c.report w).violations := by
  unfold Collect.report
  split
  · exact h
  · exact List.mem_append_left _ h

theorem report_adds (c : Collect) (w : Violation) : w ∈ (c.report w).violations := by
  unfold Collect.report
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton_self _)

theorem foldl_report (f : OrderDependent → Violation) :
    ∀ (rs : List OrderDependent) (c : Collect), (∀ v ∈ c.violations, v ∈ (rs.foldl (fun c r => c.report (f r)) c).violations) ∧
      ∀ r ∈ rs, f r ∈ (rs.foldl (fun c r => c.report (f r)) c).violations
  | [], _ => ⟨fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | r :: rs, c => by
    obtain ⟨hk, ha⟩ := foldl_report f rs (c.report (f r))
    refine ⟨fun v hv => hk v (report_keeps c v _ hv), fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hk _ (report_adds c _)
    · exact ha x hx

theorem finding_reported (c : Collect) (check : RegionCheck) (p : RegionPair) (r : OrderDependent)
    (hc : check.halted = false) (hp : p ∈ check.pairs) (hr : r ∈ regionFindings check.chart c.accessOf p) :
    r.toViolation ∈ (c.checkRegions check).violations := by
  simp only [Collect.checkRegions, hc]
  exact (foldl_report _ _ c).2 r (List.mem_flatMap.mpr ⟨p, hp, hr⟩)

theorem both_writes_reported (c : Collect) (check : RegionCheck) (p : RegionPair) (v : String × String)
    (hc : check.halted = false) (hp : p ∈ check.pairs) (ha : v ∈ (c.accessOf p.first).writes)
    (hb : v ∈ (c.accessOf p.second).writes) :
    (OrderDependent.bothAssign check.chart p.state p.firstRef p.secondRef v.2).toViolation ∈
      (c.checkRegions check).violations := by
  refine finding_reported c check p _ hc hp ?_
  unfold regionFindings
  exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨v, hb, by simp [ha]⟩)

theorem second_writes_first_reads_reported (c : Collect) (check : RegionCheck) (p : RegionPair) (v : String × String)
    (hc : check.halted = false) (hp : p ∈ check.pairs) (hb : v ∈ (c.accessOf p.second).writes)
    (ha : v ∉ (c.accessOf p.first).writes) (hr : v ∈ (c.accessOf p.first).reads) :
    (OrderDependent.assignRead check.chart p.state p.secondRef p.firstRef v.2).toViolation ∈
      (c.checkRegions check).violations := by
  refine finding_reported c check p _ hc hp ?_
  unfold regionFindings
  exact List.mem_append_left _ (List.mem_filterMap.mpr ⟨v, hb, by simp [ha, hr]⟩)

theorem first_writes_second_reads_reported (c : Collect) (check : RegionCheck) (p : RegionPair) (v : String × String)
    (hc : check.halted = false) (hp : p ∈ check.pairs) (ha : v ∈ (c.accessOf p.first).writes)
    (hb : v ∉ (c.accessOf p.second).writes) (hr : v ∈ (c.accessOf p.second).reads) :
    (OrderDependent.assignRead check.chart p.state p.firstRef p.secondRef v.2).toViolation ∈
      (c.checkRegions check).violations := by
  refine finding_reported c check p _ hc hp ?_
  unfold regionFindings
  exact List.mem_append_right _ (List.mem_filterMap.mpr ⟨v, List.mem_filter.mpr ⟨ha, by simp [hb]⟩, by simp [hr]⟩)

theorem separate_values_report_nothing (c : Collect) (check : RegionCheck)
    (hw : ∀ p ∈ check.pairs, ∀ v ∈ (c.accessOf p.second).writes, v ∉ (c.accessOf p.first).writes ∧ v ∉ (c.accessOf p.first).reads)
    (hr : ∀ p ∈ check.pairs, ∀ v ∈ (c.accessOf p.first).writes, v ∉ (c.accessOf p.second).reads) :
    (c.checkRegions check).violations = c.violations := by
  have hn : ∀ p ∈ check.pairs, regionFindings check.chart c.accessOf p = [] := by
    intro p hp
    unfold regionFindings
    rw [List.append_eq_nil_iff, List.filterMap_eq_nil_iff, List.filterMap_eq_nil_iff]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · obtain ⟨h1, h2⟩ := hw p hp v hv
      simp [h1, h2]
    · simp [hr p hp v (List.mem_filter.mp hv).1]
  have he : check.pairs.flatMap (regionFindings check.chart c.accessOf) = [] :=
    List.flatMap_eq_nil_iff.mpr hn
  unfold Collect.checkRegions
  split
  · rfl
  · rw [he]; rfl

theorem unordered_overlap_candidate (s : State) (c : Collect) (stopped : Option Violation) (i j n : Nat)
    (a b : StepAccess) (hs : (s.halted <|> stopped) = none) (ha : c.steps[n]? = some (i, a))
    (hb : (j, b) ∈ c.steps.toList.drop (n + 1)) (hm : (s.steps[i]?.map (·.message)) = (s.steps[j]?.map (·.message)))
    (hl : leadsTo s i j = false) (hc : a.commutes b = false) (hn : a.name ≠ b.name)
    (ho : overlaps a.access b.access = true) :
    (i, j) ∈ candidates s c stopped := by
  unfold candidates
  rw [hs]
  refine List.mem_flatMap.mpr ⟨((i, a), n), List.mem_zipIdx_iff_getElem?.mpr ?_, List.mem_filterMap.mpr ⟨(j, b), hb, ?_⟩⟩
  · simpa using ha
  · simp [hm, hl, hc, hn, ho]

theorem candidate_unordered (s : State) (c : Collect) (stopped : Option Violation) (i j : Nat)
    (h : (i, j) ∈ candidates s c stopped) :
    (s.halted <|> stopped) = none ∧ ∃ a b, (i, a) ∈ c.steps ∧ (j, b) ∈ c.steps ∧
      (s.steps[i]?.map (·.message)) = (s.steps[j]?.map (·.message)) ∧ leadsTo s i j = false ∧
      a.commutes b = false ∧ a.name ≠ b.name ∧ overlaps a.access b.access = true := by
  unfold candidates at h
  cases hs : (s.halted <|> stopped) with
  | some _ => simp [hs] at h
  | none =>
  refine ⟨rfl, ?_⟩
  simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨⟨⟨i', a⟩, n⟩, hz, hf⟩ := List.mem_flatMap.mp h
  obtain ⟨⟨j', b⟩, hd, he⟩ := List.mem_filterMap.mp hf
  have hia : (i', a) ∈ c.steps := Array.mem_toList_iff.mp (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hz))
  have hjb : (j', b) ∈ c.steps := Array.mem_toList_iff.mp (List.mem_of_mem_drop hd)
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    bne_iff_ne, ne_eq, Prod.mk.injEq] at he
  obtain ⟨⟨⟨⟨⟨hm, ho⟩, hc⟩, hn⟩, hl⟩, rfl, rfl⟩ := he
  exact ⟨a, b, hia, hjb, hm, hl, hc, hn, ho⟩

theorem runFrom_agrees {stepperI : Stepper (StateT C Id)} {stepper : Stepper Id}
    (hs : ∀ s i, Agrees (stepperI s i) (stepper s i)) (s : State) (inputs : List Step) :
    Agrees (runFrom stepperI s inputs) (runFrom stepper s inputs) := by
  induction inputs generalizing s with
  | nil => exact Agrees.pure _
  | cons i rest ih => unfold runFrom; agree [hs, ih]

theorem instrumented_run_eq (inputs : List Step) (c : Collect) :
    ((instrumentedRun st fs ifs inputs).run c).1 = run st fs inputs := by
  have := runFrom_agrees (step_agrees (st := st) (instrument_agrees (st := st) (fs := fs) (ifs := ifs))) {} inputs
  unfold Agrees at this
  exact this c

end Tazuna.Thm.Observe.Instrument
