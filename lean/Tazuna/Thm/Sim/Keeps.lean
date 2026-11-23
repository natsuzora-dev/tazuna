import Tazuna.Sim.Run
import Tazuna.Thm.Sim.Run

/-!
What a line keeps of each running service's state, for any relation that the inputs of a line keep: the world-level
steps of a line (posting, routing, delivering, and the client's requests) only pass the inputs to the services.
-/

namespace Tazuna.Thm.Sim.Keeps

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Data.Basic

variable {fsOf : String → Functions Id}

/--
A relation between a running service's state before and after it processes something, with the facts about it that a
line needs: it is a preorder, and the inputs that a line gives a service keep it.
-/
structure StateRel where
  R : State → State → Prop
  refl : ∀ s, R s s
  trans : ∀ {a b c}, R a b → R b c → R a c
  stepOrder : ∀ x o, R x { x with stepOrder := o }
  checkStepOrder : ∀ x, R x (checkStepOrder x)
  arriveFrom : ∀ (st : Service) (fs : Functions Id) (s : State) sender id body, R s (arriveFrom st fs s sender id body)
  arriveAll : ∀ (st : Service) (fs : Functions Id) arrivals (s : State), R s (arriveAll st fs arrivals s)
  requestOf : ∀ type name id v caller (st : Service) (fs : Functions Id) (s : State),
    R s (requestOf type name id v caller st fs s)

/-- Every running service of `w'` is related by `ρ` to its state in `w`. -/
def KeepsWorld (ρ : StateRel) (w w' : World) : Prop := ∀ p, ρ.R (w.state p) (w'.state p)

theorem KeepsWorld.refl (ρ : StateRel) (w : World) : KeepsWorld ρ w w := fun _ => ρ.refl _

theorem KeepsWorld.trans {ρ : StateRel} {a b c : World} (h₁ : KeepsWorld ρ a b) (h₂ : KeepsWorld ρ b c) :
    KeepsWorld ρ a c :=
  fun p => ρ.trans (h₁ p) (h₂ p)

theorem keepsWorld_states {ρ : StateRel} {w w' w'' : World} (h : KeepsWorld ρ w w') (hs : w''.states = w'.states) : KeepsWorld ρ w w'' :=
  fun p => by unfold World.state; rw [hs]; exact h p

theorem keepsWorld_report {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (r : InvalidScenario) : KeepsWorld ρ w (w'.report r) :=
  keepsWorld_states h (by unfold World.report; split <;> rfl)

theorem keepsWorld_post {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (o : Scenario.Origin) (sender receiver : String)
    (l : Line) (definition : Spec.Ref) : KeepsWorld ρ w (w'.post o sender receiver l definition) := by
  unfold World.post; dsimp only; split
  · exact keepsWorld_report h _
  · exact keepsWorld_states h rfl

theorem keepsWorld_route {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (o : Scenario.Origin) (service : String)
    (lines : List Line) : KeepsWorld ρ w (w'.route o service lines) := by
  unfold World.route
  refine foldl_keeps (KeepsWorld ρ w) _ (fun v l hv => ?_) _ _ h
  dsimp only
  (repeat' split) <;> first
    | exact hv
    | exact keepsWorld_post hv _ _ _ _ _
    | (refine foldl_keeps (KeepsWorld ρ w) _ (fun u x hu => ?_) _ _ hv
       split <;> first | exact hu | exact keepsWorld_post hu _ _ _ _ _)

theorem lookup_map_ne (l : List (String × State)) (k p : String) (t : State) (hp : (p == k) = false) :
    (l.map fun (q, x) => if q == k then (q, t) else (q, x)).lookup p = l.lookup p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨q, x⟩ := a
    show List.lookup p ((if q == k then (q, t) else (q, x)) :: _) = List.lookup p ((q, x) :: l)
    by_cases hq : (q == k) = true
    · simp only [hq, ↓reduceIte]; rw [List.lookup_cons, List.lookup_cons]
      have : (p == q) = false := by
        have := beq_iff_eq.mp hq; subst this; exact hp
      simp only [this]; exact ih
    · simp only [Bool.not_eq_true] at hq; simp only [hq, Bool.false_eq_true, ↓reduceIte]
      rw [List.lookup_cons, List.lookup_cons]
      split
      · rfl
      · exact ih

theorem lookup_map_eq (l : List (String × State)) (k : String) (t : State) :
    (l.map fun (q, x) => if q == k then (q, t) else (q, x)).lookup k = (l.lookup k).map fun _ => t := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨q, x⟩ := a
    show List.lookup k ((if q == k then (q, t) else (q, x)) :: _) = (List.lookup k ((q, x) :: l)).map _
    by_cases hq : (q == k) = true
    · have := beq_iff_eq.mp hq; subst this
      simp only [hq, ↓reduceIte]; rw [List.lookup_cons, List.lookup_cons]; simp
    · simp only [Bool.not_eq_true] at hq; simp only [hq, Bool.false_eq_true, ↓reduceIte]
      rw [List.lookup_cons, List.lookup_cons]
      have : (k == q) = false := by
        subst_vars; simp only [beq_eq_false_iff_ne, ne_eq] at hq ⊢; exact fun h => hq h.symm
      simp only [this]; exact ih

theorem keepsWorld_act {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (o : Scenario.Origin) (service : String)
    (f : Service → Functions Id → State → Id State) (hf : ∀ st s, ρ.R s (f st (fsOf service) s))
    : KeepsWorld ρ w (w'.act fsOf o service f) := by
  unfold World.act
  split
  · exact h
  · rename_i st _
    refine keepsWorld_route ?_ _ _ _
    intro p
    refine ρ.trans (h p) ?_
    unfold World.state
    dsimp only
    by_cases hp : (p == service) = true
    · have hp' : p = service := by simpa using hp
      subst hp'
      rw [lookup_map_eq]
      cases hl : w'.states.lookup p with
      | none => exact ρ.refl _
      | some x =>
        simp only [Option.map_some, Option.getD_some]
        split
        · exact ρ.trans (ρ.trans (ρ.stepOrder x _) (hf _ _)) (ρ.checkStepOrder _)
        · exact ρ.trans (ρ.stepOrder x _) (hf _ _)
    · rw [lookup_map_ne _ _ _ _ (by simpa using hp)]
      exact ρ.refl _

theorem keepsWorld_setStatus {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (k : Nat) (status : Status) :
    KeepsWorld ρ w (w'.setStatus k status) := keepsWorld_states h rfl

theorem keepsWorld_carry {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (i k : Nat) : KeepsWorld ρ w (w'.carry i k) :=
  keepsWorld_states h rfl

theorem keepsWorld_recordSent {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (i : Nat) (service : String) (before : Nat)
    (id : Option LineId) : KeepsWorld ρ w (w'.recordSent i service before id) :=
  keepsWorld_states h (by unfold World.recordSent; (repeat' split) <;> rfl)

theorem keepsWorld_stated {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (i : Nat) (msg : Message) :
    KeepsWorld ρ w (w'.stated i msg) := by
  unfold World.stated; split
  · exact keepsWorld_report h _
  · exact keepsWorld_states h rfl

theorem keepsWorld_nextId {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (peer name : String) :
    KeepsWorld ρ w (w'.nextId peer name).1 := keepsWorld_states h rfl

theorem keepsWorld_resolving {α : Type} {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (r : ExceptT InvalidScenario Id α)
    (k : α → Id World) (hk : ∀ a, KeepsWorld ρ w (k a)) : KeepsWorld ρ w (w'.resolving r k) := by
  unfold World.resolving; simp only [bind]; split
  · exact keepsWorld_report h _
  · exact hk _

theorem keepsWorld_attempt {α : Type} {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (r : Except InvalidScenario α)
    (k : α → Id World) (hk : ∀ a, KeepsWorld ρ w (k a)) : KeepsWorld ρ w (w'.attempt r k) := by
  unfold World.attempt; split
  · exact keepsWorld_report h _
  · exact hk _

theorem keepsWorld_setStatuses {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (ks : List Nat) (status : Status) :
    KeepsWorld ρ w (ks.foldl (fun w k => w.setStatus k status) w') :=
  foldl_keeps (KeepsWorld ρ w) _ (fun _ k hv => keepsWorld_setStatus hv k status) _ _ h

theorem keepsWorld_deliver {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (o : Scenario.Origin) (receiver : String)
    (ks : List Nat) : KeepsWorld ρ w (w'.deliver fsOf o receiver ks) := by
  unfold World.deliver
  dsimp only
  split
  · exact keepsWorld_act (keepsWorld_setStatuses h _ _) _ _ _ (fun st s => ρ.arriveFrom _ _ _ _ _ _)
  · exact keepsWorld_act (keepsWorld_setStatuses h _ _) _ _ _ (fun st s => ρ.arriveAll _ _ _ _)

theorem keepsWorld_deliverCarried {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (i : Nat) (ks : List Nat) :
    KeepsWorld ρ w (w'.deliverCarried fsOf i ks) := by
  unfold World.deliverCarried
  simp only [bind, pure, foldlM_id]
  have hc : KeepsWorld ρ w (ks.foldl (fun w k => w.carry i k) w') :=
    foldl_keeps (KeepsWorld ρ w) _ (fun v k hv => keepsWorld_carry hv _ _) _ _ h
  refine foldl_keeps (KeepsWorld ρ w) _ (fun v r hv => ?_) _ _ hc
  split
  · exact hv
  · split
    · exact keepsWorld_setStatuses hv _ _
    · refine foldl_keeps (KeepsWorld ρ w) _ (fun u k hu => ?_) _ _ (keepsWorld_deliver hv _ _ _)
      repeat' split
      all_goals first
        | exact hu
        | exact foldl_keeps (KeepsWorld ρ w) _ (fun x l hx => keepsWorld_recordSent hx _ _ _ _) _ _ hu

theorem keepsWorld_clientRequest {ρ : StateRel} {w w' : World} (h : KeepsWorld ρ w w') (i : Nat) (type : Scenario.RequestType)
    (target : Spec.Ref) (input : Scenario.Template) (sameIdAs : Option Nat) (caller : Option Caller) :
    KeepsWorld ρ w (w'.clientRequest fsOf i type target input sameIdAs caller) := by
  unfold World.clientRequest
  simp only [bind, pure]
  split
  · exact keepsWorld_report h _
  · refine keepsWorld_resolving h _ _ fun v => ?_
    repeat' split
    all_goals first
      | exact keepsWorld_report h _
      | exact keepsWorld_recordSent (keepsWorld_act h _ _ _ (fun st s => ρ.requestOf _ _ _ _ _ _ _ _)) _ _ _ _

theorem keepsWorld_now_iff {ρ : StateRel} {w w' : World} (now : Time) : KeepsWorld ρ w { w' with now } ↔ KeepsWorld ρ w w' := Iff.rfl

theorem keepsWorld_inFlight_iff {ρ : StateRel} {w w' : World} (leftInFlight : List (Nat × Nat)) :
    KeepsWorld ρ w { w' with leftInFlight } ↔ KeepsWorld ρ w w' := Iff.rfl

theorem keepsWorld_messages_iff {ρ : StateRel} {w w' : World} (messages : Array Message) :
    KeepsWorld ρ w { w' with messages } ↔ KeepsWorld ρ w w' := Iff.rfl

/--
Closes `KeepsWorld ρ w x` where `x` is built from `w` by steps that keep `ρ`, with `leaf` closing `ρ.R s (f s)` for
the inputs that a line gives a service directly.
-/
macro "keeps_tac " leaf:tacticSeq : tactic => `(tactic| repeat' (first
  | contradiction
  | with_reducible assumption
  | with_reducible exact KeepsWorld.refl _ _
  | with_reducible apply keepsWorld_report
  | with_reducible apply keepsWorld_carry
  | with_reducible apply keepsWorld_recordSent
  | with_reducible apply keepsWorld_stated
  | with_reducible apply keepsWorld_nextId
  | with_reducible apply keepsWorld_setStatus
  | with_reducible apply keepsWorld_deliverCarried
  | with_reducible apply keepsWorld_clientRequest
  | (with_reducible refine keepsWorld_act ?_ _ _ _ (fun st s => ?_))
  | simp only [keepsWorld_now_iff, keepsWorld_inFlight_iff, keepsWorld_messages_iff]
  | with_reducible refine keepsWorld_resolving ?_ _ _ fun _ => ?_
  | with_reducible refine keepsWorld_attempt ?_ _ _ fun _ => ?_
  | with_reducible refine foldl_keeps _ _ (fun _ _ _ => ?_) _ _ ?_
  | with_reducible refine Tazuna.Thm.Sim.Run.forEach_keeps _ ?_ fun _ _ _ _ => ?_
  | with_reducible ($leaf)
  | dsimp only
  | split))

/-- A line keeps `ρ` when its steps do, as `take` states for the line, and a line whose values report changes no state. -/
theorem keepsWorld_line {ρ : StateRel} (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line)
    (h : KeepsWorld ρ w (w.take fsOf own lines i l)) : KeepsWorld ρ w (w.line fsOf own lines i l) := by
  unfold World.line
  dsimp only
  split
  · exact keepsWorld_report (.refl ρ w) _
  · exact h

theorem keepsWorld_beginAll {ρ : StateRel} (hb : ∀ st (fs : Functions Id) s, ρ.R s (begin st fs s)) (w : World) :
    KeepsWorld ρ w (w.beginAll fsOf) := by
  unfold World.beginAll
  rw [foldlM_id]
  refine foldl_keeps (KeepsWorld ρ w) _ (fun v x hv => ?_) _ _ (.refl _ w)
  dsimp only
  split
  · exact hv
  · exact keepsWorld_act hv _ _ _ (fun st s => hb _ _ _)

theorem keeps_lookup_map {ρ : StateRel} (l : List (String × State)) (g : String × State → String × State)
    (h : ∀ a, (g a).1 = a.1 ∧ ρ.R a.2 (g a).2) (p : String) :
    ρ.R ((l.lookup p).getD { service := p }) (((l.map g).lookup p).getD { service := p }) := by
  induction l with
  | nil => exact ρ.refl _
  | cons a l ih =>
    obtain ⟨q, x⟩ := a
    obtain ⟨h₁, h₂⟩ := h (q, x)
    show ρ.R ((List.lookup p ((q, x) :: l)).getD { service := p }) ((List.lookup p (g (q, x) :: _)).getD { service := p })
    rw [show g (q, x) = (q, (g (q, x)).2) from Prod.ext h₁ rfl, List.lookup_cons, List.lookup_cons]
    split
    · exact h₂
    · exact ih

theorem keepsWorld_given {ρ : StateRel} (hr : ∀ s rows, ρ.R s { s with records := rows }) (w : World)
    (j : Spec.Structure) (sc : Scenario) : KeepsWorld ρ w (w.given j fsOf sc) := by
  unfold World.given
  simp only [bind, pure]
  rw [foldlM_id]
  have hn : ∀ (rs : List InvalidScenario) (v : World), (rs.foldl World.note v).states = v.states := by
    intro rs; induction rs with
    | nil => intro v; rfl
    | cons r rs ih => intro v; simp only [List.foldl_cons]; rw [ih]; rfl
  refine foldl_keeps (KeepsWorld ρ w) _ (fun v x hv => ?_) _ _ (keepsWorld_states (.refl _ w) (hn _ _))
  intro p
  refine ρ.trans (hv p) ?_
  have : ∀ (l : List (String × State)) (k : String) (rows : Records),
      l.map (fun (q, s) => if q == k then (q, { s with records := rows }) else (q, s)) =
        l.map fun a => (a.1, if a.1 == k then { a.2 with records := rows } else a.2) := by
    intro l k rows; congr 1; funext a; obtain ⟨q, s⟩ := a; show ite _ _ _ = (q, ite _ _ _); cases q == k <;> rfl
  split
  split
  all_goals
    simp only [World.state, hn]
    rw [this]
    apply keeps_lookup_map
    intro a
    refine ⟨rfl, ?_⟩
    split
    · exact hr _ _
    · exact ρ.refl _

/-- Each running service of a world that World.startWith gives holds no lines, and its state names it. -/
theorem startWith_state (sc : Scenario) (services : List (String × Service)) (p : String) :
    ((World.startWith sc services).state p).lines = #[] ∧ ((World.startWith sc services).state p).service = p := by
  unfold World.startWith World.state
  dsimp only
  induction runningOf sc with
  | nil => exact ⟨rfl, rfl⟩
  | cons q l ih =>
    rw [List.map_cons, List.lookup_cons]
    split
    · rename_i h; exact ⟨rfl, (beq_iff_eq.mp h).symm⟩
    · exact ih

/--
The lines of a scenario keep `ρ` from the start, when beginning, Given's records and every line's steps keep it, as
`take` states for the line.
-/
theorem execute_keeps {ρ : StateRel} (hb : ∀ st (fs : Functions Id) s, ρ.R s (begin st fs s))
    (hr : ∀ s rows, ρ.R s { s with records := rows })
    (ht : ∀ (w : World) own lines i l, KeepsWorld ρ w (w.take fsOf own lines i l)) (j : Spec.Structure)
    (start : World) (sc : Scenario) : KeepsWorld ρ start (execute j fsOf start sc) := by
  unfold execute World.execute
  simp only [bind, pure]
  have hg := keepsWorld_given (fsOf := fsOf) hr start j sc
  split
  · exact hg
  · rw [foldlM_id]
    refine foldl_keeps (KeepsWorld ρ start) _ (fun v x hv => hv.trans ?_) _ _ (hg.trans (keepsWorld_beginAll hb _))
    unfold World.step
    split
    · exact .refl _ _
    · exact keepsWorld_line _ _ _ _ _ (ht _ _ _ _ _)

end Tazuna.Thm.Sim.Keeps
