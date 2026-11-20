import Tazuna.Sim.Run
import Tazuna.Thm.Explore.Instrument

/-!
The audit's agreement for each service input (Thm.Explore.Instrument) lifted to the whole run: instrumented functions
that agree with the plain ones make `execute` and `simulate` return the same world.
-/

namespace Tazuna.Thm.Sim.Audit

open Tazuna.Data Tazuna.Service Tazuna.Sim Tazuna.Thm.Explore.Instrument
open Tazuna.Scenario (Fact ValueRef Template)

variable {C ε : Type}

theorem AgreesE.bind {α β : Type} {x : ExceptT ε (StateT C Id) α} {y : ExceptT ε Id α}
    {f : α → ExceptT ε (StateT C Id) β} {g : α → ExceptT ε Id β}
    (hx : Agrees x.run y.run) (hf : ∀ a, Agrees (f a).run (g a).run) : Agrees (x >>= f).run (y >>= g).run := by
  show Agrees (Bind.bind (m := StateT C Id) x.run (ExceptT.bindCont f)) (Bind.bind (m := Id) y.run (ExceptT.bindCont g))
  refine Agrees.bind hx fun e => ?_
  cases e with
  | error e => exact Agrees.pure _
  | ok a => exact hf a

theorem AgreesE.map {α β : Type} {x : ExceptT ε (StateT C Id) α} {y : ExceptT ε Id α} (f : α → β)
    (hx : Agrees x.run y.run) : Agrees (f <$> x).run (f <$> y).run := by
  show Agrees (ExceptT.map f x).run (ExceptT.map f y).run
  unfold ExceptT.map ExceptT.run ExceptT.mk
  refine Agrees.bind hx fun e => ?_
  cases e <;> exact Agrees.pure _

theorem AgreesE.pure {α : Type} (a : α) :
    Agrees (Pure.pure a : ExceptT ε (StateT C Id) α).run (Pure.pure a : ExceptT ε Id α).run :=
  Agrees.pure _

theorem AgreesE.throw {α : Type} (e : ε) :
    Agrees (MonadExcept.throw e : ExceptT ε (StateT C Id) α).run (MonadExcept.throw e : ExceptT ε Id α).run :=
  Agrees.pure _

theorem AgreesE.lift {α : Type} {x : StateT C Id α} {a : Id α} (hx : Agrees x a) :
    Agrees (ExceptT.lift x : ExceptT ε (StateT C Id) α).run (ExceptT.lift a : ExceptT ε Id α).run :=
  Agrees.map _ hx

theorem AgreesE.mapGetD {α β : Type} {f : α → ExceptT ε (StateT C Id) β} {g : α → ExceptT ε Id β}
    {d : ExceptT ε (StateT C Id) β} {d' : ExceptT ε Id β} (hf : ∀ a, Agrees (f a).run (g a).run)
    (hd : Agrees d.run d'.run) (o : Option α) : Agrees ((o.map f).getD d).run ((o.map g).getD d').run := by
  cases o
  · exact hd
  · exact hf _

theorem Agrees.monadLift {α : Type} {x : StateT C Id α} {a : Id α} (hx : Agrees x a) :
    Agrees (monadLift x : StateT C Id α) (monadLift a : Id α) := hx

theorem AgreesE.foldlM {α β : Type} {f : β → α → ExceptT ε (StateT C Id) β} {g : β → α → ExceptT ε Id β}
    (hf : ∀ b a, Agrees (f b a).run (g b a).run) (xs : List α) (init : β) :
    Agrees (xs.foldlM f init).run (xs.foldlM g init).run := by
  induction xs generalizing init with
  | nil => exact AgreesE.pure _
  | cons x xs ih => exact AgreesE.bind (hf init x) (fun b => ih b)

theorem AgreesE.mapM {α β : Type} {f : α → ExceptT ε (StateT C Id) β} {g : α → ExceptT ε Id β}
    (hf : ∀ a, Agrees (f a).run (g a).run) (xs : List α) : Agrees (xs.mapM f).run (xs.mapM g).run := by
  induction xs with
  | nil => exact AgreesE.pure _
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact AgreesE.bind (hf x) fun b => AgreesE.bind ih fun bs => AgreesE.pure _

theorem AgreesE.filterMapM {α β : Type} {f : α → ExceptT ε (StateT C Id) (Option β)} {g : α → ExceptT ε Id (Option β)}
    (hf : ∀ a, Agrees (f a).run (g a).run) (xs : List α) :
    Agrees (xs.filterMapM f).run (xs.filterMapM g).run := by
  unfold List.filterMapM
  suffices ∀ (ys : List α) (acc : List β),
      Agrees (List.filterMapM.loop f ys acc).run (List.filterMapM.loop g ys acc).run from this xs []
  intro ys
  induction ys with
  | nil => intro acc; exact AgreesE.pure _
  | cons y ys ih =>
    intro acc
    simp only [List.filterMapM.loop]
    exact AgreesE.bind (hf y) (fun b => by cases b <;> exact ih _)

theorem AgreesE.filterM {α : Type} {f : α → ExceptT ε (StateT C Id) Bool} {g : α → ExceptT ε Id Bool}
    (hf : ∀ a, Agrees (f a).run (g a).run) (xs : List α) : Agrees (xs.filterM f).run (xs.filterM g).run := by
  unfold List.filterM
  suffices ∀ (ys acc : List α), Agrees (List.filterAuxM f ys acc).run (List.filterAuxM g ys acc).run from
    AgreesE.bind (this xs []) fun _ => AgreesE.pure _
  intro ys
  induction ys with
  | nil => intro acc; exact AgreesE.pure _
  | cons y ys ih =>
    intro acc
    simp only [List.filterAuxM]
    exact AgreesE.bind (hf y) (fun b => ih _)

theorem Agrees.filterM {α : Type} {f : α → StateT C Id Bool} {g : α → Id Bool}
    (hf : ∀ a, Agrees (f a) (g a)) (xs : List α) : Agrees (xs.filterM f) (xs.filterM g) := by
  unfold List.filterM
  suffices ∀ (ys acc : List α), Agrees (List.filterAuxM f ys acc) (List.filterAuxM g ys acc) from
    Agrees.bind (this xs []) fun _ => Agrees.pure _
  intro ys
  induction ys with
  | nil => intro acc; exact Agrees.pure _
  | cons y ys ih =>
    intro acc
    simp only [List.filterAuxM]
    exact Agrees.bind (hf y) (fun b => ih _)

/-- `agree` with the ExceptT rules tried first, and a lift into ExceptT matched up to its instances. -/
syntax "agreeE" "[" term,* "]" : tactic
macro_rules
  | `(tactic| agreeE [$ts,*]) => do
    let mut given ← `(tactic| fail "no lemma applies")
    for t in ts.getElems do
      given ← `(tactic| first | with_reducible apply $t | $given:tactic)
    `(tactic| repeat' (first
      | $given:tactic
      | with_reducible apply AgreesE.bind
      | with_reducible apply AgreesE.map
      | with_reducible apply AgreesE.foldlM
      | with_reducible apply AgreesE.mapM
      | with_reducible apply AgreesE.filterMapM
      | with_reducible apply AgreesE.filterM
      | with_reducible apply Agrees.filterM
      | with_reducible apply Agrees.mapM
      | with_reducible apply Agrees.monadLift
      | exact AgreesE.pure _
      | exact AgreesE.throw _
      | refine AgreesE.lift ?_
      | exact Agrees.pure _
      | refine Agrees.bind ?_ (fun _ => ?_)
      | refine Agrees.map _ ?_
      | refine Agrees.foldlM (fun _ _ => ?_) _ _
      | refine Agrees.filterMapM (fun _ => ?_) _
      | with_reducible exact note_agrees _
      | split
      | (dsimp only)
      | intro _))

variable {fsOfI : String → Functions (StateT C Id)} {fsOf : String → Functions Id}
  (h : ∀ q, FunctionsAgree (fsOfI q) (fsOf q))
include h

theorem comparedOr_agrees (q : String) (schema : Schema) (v : Value) :
    Agrees (comparedOr (fsOfI q) schema v) (comparedOr (fsOf q) schema v) := by
  unfold comparedOr; agree [(h q).unordered]

theorem picks_agrees (q : String) (schema : Schema) (pick : Option Value) (v : Value) :
    Agrees (picks (fsOfI q) schema pick v) (picks (fsOf q) schema pick v) := by
  unfold picks; agree [comparedOr_agrees h]

theorem comparedContent_agrees (w : World) (k : Nat) :
    Agrees (w.comparedContent? fsOfI k) (w.comparedContent? fsOf k) := by
  unfold World.comparedContent?; agree [comparedOr_agrees h]

theorem alikeMessages_agrees (w : World) (i : Nat) (fact : Fact) (found : List Nat) :
    Agrees (w.alikeMessages fsOfI i fact found).run (w.alikeMessages fsOf i fact found).run := by
  unfold World.alikeMessages Sim.ofExcept; agreeE [comparedContent_agrees h]

set_option linter.unusedSectionVars false in
mutual
theorem messagesOf_agrees (w : World) (i : Nat) (fact : Fact) :
    Agrees (w.messagesOf fsOfI i fact).run (w.messagesOf fsOf i fact).run := by
  unfold World.messagesOf
  cases fact with
  | request o kind target input =>
    cases input <;> agreeE [alikeMessages_agrees h, picks_agrees h, fill_agrees w i _]
  | event o event payload receiver =>
    cases payload <;> agreeE [alikeMessages_agrees h, picks_agrees h, fill_agrees w i _]
  | «end» o subscription =>
    dsimp only
    exact AgreesE.bind (messagesOf_agrees w i subscription) fun _ => by (try unfold Sim.ofExcept); agreeE []
  | answer | line | screen => dsimp only; (try unfold Sim.ofExcept); agreeE []
termination_by 2 * sizeOf fact
decreasing_by all_goals (simp_wf; omega)

theorem partOf_agrees (w : World) (i : Nat) (fact : Fact) (part : Scenario.Part) :
    Agrees (w.partOf fsOfI i fact part).run (w.partOf fsOf i fact part).run := by
  unfold World.partOf
  have via := messagesOf_agrees w i fact
  dsimp only
  split <;> (try unfold Sim.ofExcept) <;> agreeE [via, comparedOr_agrees h]
termination_by 2 * sizeOf fact + 1

theorem observed_agrees (w : World) (i : Nat) (r : ValueRef) :
    Agrees (w.observed fsOfI i r).run (w.observed fsOf i r).run := by
  obtain ⟨fact, part, path⟩ := r
  unfold World.observed
  exact AgreesE.bind (partOf_agrees w i fact part) fun _ => by agreeE []
termination_by 2 * sizeOf r
decreasing_by simp_wf; omega

theorem fill_agrees (w : World) (i : Nat) (t : Template) :
    Agrees (w.fill fsOfI i t).run (w.fill fsOf i t).run := by
  obtain ⟨value, holes⟩ := t
  unfold World.fill
  refine AgreesE.foldlM (fun v a => ?_) _ _
  obtain ⟨⟨path, fill⟩, mem⟩ := a
  cases fill with
  | ref r => exact AgreesE.bind (observed_agrees w i r) fun _ => AgreesE.pure _
  | created => exact AgreesE.pure _
termination_by 2 * sizeOf t
decreasing_by
  have := List.sizeOf_lt_of_mem mem
  simp only [Scenario.Hole.mk.sizeOf_spec, Scenario.Fill.ref.sizeOf_spec] at this; simp_wf; omega
end

theorem requestIds_agrees (w : World) (i : Nat) (peer : String) (fact : Fact) :
    Agrees (w.requestIds fsOfI i peer fact).run (w.requestIds fsOf i peer fact).run := by
  unfold World.requestIds; agreeE [messagesOf_agrees h]

theorem comparedAnswer_agrees (q : String) (target : Option Spec.Ref) (a : Answer) :
    Agrees (comparedAnswer (fsOfI q) target a) (comparedAnswer (fsOf q) target a) := by
  unfold comparedAnswer; agreeE [comparedOr_agrees h]

theorem comparedAnswerValue_agrees (q : String) (target : Option Spec.Ref) (v : Value) :
    Agrees (comparedAnswerValue (fsOfI q) target v) (comparedAnswerValue (fsOf q) target v) := by
  unfold comparedAnswerValue; agreeE [comparedAnswer_agrees h]

theorem sameValue_agrees (w : World) (q : String) (schema : Schema) (peer : String) (t : Template) (e a : Value) :
    Agrees (w.sameValue (fsOfI q) schema peer t e a) (w.sameValue (fsOf q) schema peer t e a) := by
  unfold World.sameValue; agreeE [comparedOr_agrees h]

theorem given_agrees [MonadNote (StateT C Id)] (w : World) (j : Spec.Structure) (sc : Scenario) :
    Agrees (w.given j fsOfI sc) (w.given j fsOf sc) := by
  unfold World.given givenRows givenInvariants; agreeE [parseOutside_agrees (h _), (h _).invariant, (h _).serviceInvariant]

theorem offeredAt_agrees [MonadNote (StateT C Id)] (q : String) (st : Service) (s : State) (o : Opened) (control : String) (payload : Value) :
    Agrees (offeredAt st (fsOfI q) s o control payload) (offeredAt st (fsOf q) s o control payload) := by
  unfold offeredAt; agreeE [parseOutside_agrees (h q), acceptsOperation_agrees (h q)]

omit h in
theorem peerMessage_agrees (w : World) (i : Nat) (peer : String) {f : Message → StateT C Id Bool}
    {g : Message → Id Bool} (hf : ∀ msg, Agrees (f msg) (g msg)) :
    Agrees (w.peerMessage i peer f) (w.peerMessage i peer g) := by
  unfold World.peerMessage; agreeE [Agrees.filterM, hf]

omit h in
theorem forEach_agrees {α : Type} (w : World) (xs : List α) {f : World → α → StateT C Id World}
    {g : World → α → Id World} (hf : ∀ v x, Agrees (f v x) (g v x)) :
    Agrees (w.forEach xs f) (w.forEach xs g) := by
  unfold World.forEach; agreeE [hf]

theorem found_agrees [MonadNote (StateT C Id)] (w : World) (expectations : List Scenario.Expectation) (i : Nat) (l : Scenario.Line) :
    Agrees (w.found fsOfI expectations i l) (w.found fsOf expectations i l) := by
  unfold World.found; agreeE [AgreesE.mapGetD (fill_agrees h w i), offeredAt_agrees h]

theorem compared_agrees [MonadNote (StateT C Id)] (w : World) (own : String) (lines : List Scenario.Line)
    (found : List (Nat × Except InvalidScenario Bool)) (k : Nat) (e : Scenario.Expectation) :
    Agrees (w.compared fsOfI own lines found k e).run (w.compared fsOf own lines found k e).run := by
  unfold World.compared
  agreeE [fill_agrees h, messagesOf_agrees h, comparedOr_agrees h, comparedAnswer_agrees h,
    comparedAnswerValue_agrees h, expectFound_agrees]

theorem expect_agrees [MonadNote (StateT C Id)] (w : World) (own : String) (lines : List Scenario.Line) (es : List Scenario.Expectation)
    (found : List (Nat × Except InvalidScenario Bool)) :
    Agrees (w.expect fsOfI own lines es found) (w.expect fsOf own lines es found) := by
  unfold World.expect; agreeE [compared_agrees h]

variable [MonadNote (StateT C Id)]

theorem ended_agrees (w : World) : Agrees (w.ended fsOfI) (w.ended fsOf) := by
  unfold World.ended; agreeE [checkExchanges_agrees (h _)]

theorem arriveFrom_agrees (q : String) (st : Service) (s : State) (sender : String) (id : LineId) (body : LineBody) :
    Agrees (arriveFrom st (fsOfI q) s sender id body) (arriveFrom st (fsOf q) s sender id body) := by
  unfold arriveFrom
  agreeE [send_agrees (h q), call_agrees (h q), subscribe_agrees (h q), endSubscription_agrees (h q),
    answerIn_agrees (h q), receive_agrees (h q)]

theorem arriveAll_go_agrees (q : String) (st : Service) (first : Nat) (arrivals : List Arrival) (s : State) :
    Agrees (arriveAll.go st (fsOfI q) first arrivals s) (arriveAll.go st (fsOf q) first arrivals s) := by
  cases arrivals with
  | nil => unfold arriveAll.go; exact Agrees.pure _
  | cons next more =>
    rw [arriveAll.go, arriveAll.go]
    split
    · exact Agrees.pure _
    · dsimp only
      split
      · exact Agrees.pure _
      · refine Agrees.bind (note_agrees _) fun _ => Agrees.bind (arriveFrom_agrees h q _ _ _ _ _) fun _ =>
          Agrees.bind (note_agrees _) fun _ => ?_
        exact arriveAll_go_agrees q st first _ _
termination_by arrivals.length
decreasing_by simp only [List.length_eraseIdx_of_lt (Fin.isLt _)]; simp

theorem requestOf_agrees (q : String) (type : Scenario.RequestType) (target : Spec.Ref) (id : Option LineId)
    (v : Value) (st : Service) (s : State) :
    Agrees (requestOf type target id v st (fsOfI q) s) (requestOf type target id v st (fsOf q) s) := by
  unfold requestOf; agreeE [send_agrees (h q), call_agrees (h q), subscribe_agrees (h q)]

theorem fireTo_agrees (q : String) (time : Time) (st : Service) (s : State) :
    Agrees (fireTo time st (fsOfI q) s) (fireTo time st (fsOf q) s) := by
  unfold fireTo; agreeE [fireDue_agrees (h q), publish_agrees (h q)]

variable [MonadActing (StateT C Id)]
  (hact : ∀ {α : Type} (q : String) (x : StateT C Id α) (a : α), Agrees x a → Agrees (MonadActing.acting q x) a)
include hact

omit h [MonadNote (StateT C Id)] in
theorem act_agrees (w : World) (o : Scenario.Origin) (service : String)
    {f : Service → Functions (StateT C Id) → State → StateT C Id State} {g : Service → Functions Id → State → Id State}
    (hf : ∀ st s, Agrees (f st (fsOfI service) s) (g st (fsOf service) s)) :
    Agrees (w.act fsOfI o service f) (w.act fsOf o service g) := by
  unfold World.act
  split
  · exact Agrees.pure _
  · exact Agrees.bind (hact _ _ _ (hf _ _)) fun _ => Agrees.pure _

theorem deliver_agrees (w : World) (o : Scenario.Origin) (receiver : String) (ks : List Nat) :
    Agrees (w.deliver fsOfI o receiver ks) (w.deliver fsOf o receiver ks) := by
  unfold World.deliver
  dsimp only
  split
  · exact act_agrees hact _ _ _ (fun _ _ => arriveFrom_agrees h _ _ _ _ _ _)
  · exact act_agrees hact _ _ _ (fun _ _ => by unfold arriveAll; exact arriveAll_go_agrees h _ _ _ _ _)

theorem clientRequest_agrees (w : World) (i : Nat) (type : Scenario.RequestType) (target : Spec.Ref)
    (input : Template) (sameIdAs : Option Nat) :
    Agrees (w.clientRequest fsOfI i type target input sameIdAs) (w.clientRequest fsOf i type target input sameIdAs) := by
  unfold World.clientRequest World.resolving
  agreeE [fill_agrees h, act_agrees hact, requestOf_agrees h]

theorem deliverCarried_agrees (w : World) (i : Nat) (ks : List Nat) :
    Agrees (w.deliverCarried fsOfI i ks) (w.deliverCarried fsOf i ks) := by
  unfold World.deliverCarried; agreeE [deliver_agrees h hact]

theorem take_agrees (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line) :
    Agrees (w.take fsOfI own lines i l) (w.take fsOf own lines i l) := by
  unfold World.take World.resolving World.attempt
  split <;> agreeE [clientRequest_agrees h hact, fill_agrees h, messagesOf_agrees h, requestIds_agrees h,
    act_agrees hact, deliverCarried_agrees h hact, forEach_agrees, peerMessage_agrees, sameValue_agrees h,
    comparedAnswerValue_agrees h, endSubscription_agrees (h _), operate_agrees (h _), restart_agrees (h _),
    fireTo_agrees h]

theorem step_agrees (w : World) (sc : Scenario) (l : Scenario.Line) (i : Nat) :
    Agrees (w.step fsOfI sc l i) (w.step fsOf sc l i) := by
  unfold World.step World.line; agreeE [take_agrees h hact]

theorem beginAll_agrees (w : World) : Agrees (w.beginAll fsOfI) (w.beginAll fsOf) := by
  unfold World.beginAll; agreeE [act_agrees hact, begin_agrees (h _)]

/--
An audited run of the lines of a scenario returns the world of the plain run, whatever the audit collected before:
the run that explore appends lines to.
-/
theorem execute_agrees (j : Spec.Structure) (start : World) (sc : Scenario) :
    Agrees (execute j fsOfI start sc) (execute j fsOf start sc) := by
  unfold execute World.execute; agreeE [given_agrees h, beginAll_agrees h hact, step_agrees h hact]

/--
An audited run of a whole scenario returns the world of the plain run, whatever the audit collected before: `test`'s
audits for `BagOrderDependent` and `ChoiceDependent` change no simulation.
-/
theorem simulate_agrees (j : Spec.Structure) (start : World) (sc : Scenario) :
    Agrees (simulate j fsOfI start sc) (simulate j fsOf start sc) := by
  unfold simulate World.stepFinding
  agreeE [given_agrees h, beginAll_agrees h hact, step_agrees h hact, found_agrees h, ended_agrees h,
    expect_agrees h]

end Tazuna.Thm.Sim.Audit
