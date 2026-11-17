import Tazuna.Sim.Run
import Tazuna.Thm.Service.Keys
import Tazuna.Thm.Service.KeyGrowth

/-!
The createKey values of the participants of a simulation: each participant's values differ from each other, and from
every string that the scenario may write, so a Given record never holds a key that a participant creates later.
-/

namespace Tazuna.Thm.Sim.Keys

open Tazuna.Data Tazuna.Semantics Tazuna.Sim
open Tazuna.Thm.Service.Keys Tazuna.Thm.Service.KeyGrowth
open Tazuna.Thm.Data.Basic

/--
A string that writtenKey? lets a scenario write is no createKey value of a keyed entity of a running participant `p`,
in any state whose values `p` qualifies.
-/
theorem unwritten_not_created {w : World} {p : String} {st : Service} (hs : (p, st) ∈ w.services) {s : State}
    (ho : s.keyOwner = some p) {e k : String} (he : e ∈ st.entities) (hk : st.singles.contains e = false)
    (hw : w.writtenKey? (.str k) = none) : (e, k) ∉ s.created := by
  intro h
  obtain ⟨n, hn, hc⟩ := created_form h
  rw [ho] at hc
  have hkey := keyChars_isKeyOf p e n hn k hc
  simp only [World.writtenKey?, World.keyEntity?, Value.strings, List.findSome?_cons, List.findSome?_nil] at hw
  split at hw
  · cases hw
  · rename_i hnone
    simp only [Option.map_eq_none_iff] at hnone
    have := List.findSome?_eq_none_iff.mp hnone (p, st) hs
    simp only [Option.map_eq_none_iff, List.find?_eq_none] at this
    exact this e he (by simp only [hkey, Bool.and_true, Bool.not_eq_eq_eq_not, Bool.not_true]; exact hk)

variable {fsOf : String → Functions Id}

/-- Every participant of `w'` keeps the createKey values that it has in `w`. -/
def KeepsWorld (w w' : World) : Prop := ∀ p, KeepsKeys (w.state p) (w'.state p)

theorem KeepsWorld.refl (w : World) : KeepsWorld w w := fun _ => .refl _

theorem KeepsWorld.trans {a b c : World} (h₁ : KeepsWorld a b) (h₂ : KeepsWorld b c) : KeepsWorld a c :=
  fun p => (h₁ p).trans (h₂ p)

theorem keepsWorld_states {w w' w'' : World} (h : KeepsWorld w w') (hs : w''.states = w'.states) : KeepsWorld w w'' :=
  fun p => by unfold World.state; rw [hs]; exact h p

theorem keepsWorld_report {w w' : World} (h : KeepsWorld w w') (r : Report) : KeepsWorld w (w'.report r) :=
  keepsWorld_states h (by unfold World.report; split <;> rfl)

theorem keepsWorld_post {w w' : World} (h : KeepsWorld w w') (o : Scenario.Origin) (sender receiver : String) (l : Line)
    (channel : Option String) : KeepsWorld w (w'.post o sender receiver l channel) := by
  unfold World.post; dsimp only; split
  · exact keepsWorld_report h _
  · exact keepsWorld_states h rfl

theorem keepsWorld_route {w w' : World} (h : KeepsWorld w w') (o : Scenario.Origin) (service : String)
    (lines : List Line) : KeepsWorld w (w'.route o service lines) := by
  unfold World.route
  refine foldl_keeps (KeepsWorld w) _ (fun v l hv => ?_) _ _ h
  dsimp only
  (repeat' split) <;> first
    | exact hv
    | exact keepsWorld_post hv _ _ _ _ _
    | (refine foldl_keeps (KeepsWorld w) _ (fun u x hu => ?_) _ _ hv
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

theorem keeps_stepOrder (x : State) (o : List StepName) : KeepsKeys x { x with stepOrder := o } := .refl _

theorem keeps_checkStepOrder (x : State) : KeepsKeys x (checkStepOrder x) := by
  unfold checkStepOrder; split <;> keys_leaf

theorem keepsWorld_checkComputed {w w' : World} (h : KeepsWorld w w') (service : String) (sent : List Line)
    (records : Records) : KeepsWorld w (w'.checkComputed service sent records) := by
  unfold World.checkComputed
  repeat' split
  all_goals first | exact h | exact keepsWorld_report h _

theorem keepsWorld_act {w w' : World} (h : KeepsWorld w w') (o : Scenario.Origin) (service : String)
    (f : Service → Functions Id → State → Id State) (hf : ∀ st s, KeepsKeys s (f st (fsOf service) s))
    (reopen : Bool) : KeepsWorld w (w'.act fsOf o service f reopen) := by
  unfold World.act
  split
  · exact h
  · rename_i st _
    apply keepsWorld_checkComputed
    refine keepsWorld_route ?_ _ _ _
    intro p
    refine (h p).trans ?_
    unfold World.state
    dsimp only
    by_cases hp : (p == service) = true
    · have hp' : p = service := by simpa using hp
      subst hp'
      rw [lookup_map_eq]
      cases hl : w'.states.lookup p with
      | none => exact .refl _
      | some x =>
        simp only [Option.map_some, Option.getD_some]
        split
        · exact ((keeps_stepOrder x _).trans (hf _ _)).trans (keeps_checkStepOrder _)
        · exact (keeps_stepOrder x _).trans (hf _ _)
    · rw [lookup_map_ne _ _ _ _ (by simpa using hp)]
      exact .refl _

theorem keeps_answerIn (st : Service) (fs : Functions Id) (s : State) (to : String) (a : Answer) :
    KeepsKeys s (answerIn st fs s to a) := by
  unfold answerIn
  split
  · exact (by keys_leaf : KeepsKeys s { s with takenAnswers := _ }).trans (keeps_answerRequest _ _ _)
  · refine KeepsKeys.trans ?_ (keeps_message _ _)
    keys_leaf

theorem keeps_arriveFrom (st : Service) (fs : Functions Id) (s : State) (sender id : String) (body : LineBody) :
    KeepsKeys s (arriveFrom st fs s sender id body) := by
  unfold arriveFrom
  dsimp only
  split
  · exact keeps_send _ _ _ _
  · exact keeps_call _ _ _ _
  · exact keeps_subscribe _ _ _ _
  · exact keeps_endSubscription _ _
  · split
    · exact keeps_answerIn _ _ _ _ _
    · exact .refl _
  · exact keeps_receive _ _ _ _ _
  · exact .refl _

theorem keeps_fireTo (time : Time) (st : Service) (fs : Functions Id) (s : State) :
    KeepsKeys s (fireTo time st fs s) := by
  simp only [fireTo, id_bind]
  keys_close (keeps_fireDue (st := st) (fs := fs) time Limit.dueDeadlines.max none s)

theorem keeps_requestOf (type : Scenario.RequestType) (name : String) (id : Option String) (v : Value)
    (st : Service) (fs : Functions Id) (s : State) : KeepsKeys s (requestOf type name id v st fs s) := by
  cases type
  · exact keeps_send _ _ _ _
  · exact keeps_call _ _ _ _
  · exact keeps_subscribe _ _ _ _

theorem keepsWorld_setStatus {w w' : World} (h : KeepsWorld w w') (k : Nat) (status : Status) :
    KeepsWorld w (w'.setStatus k status) := keepsWorld_states h rfl

theorem keepsWorld_carry {w w' : World} (h : KeepsWorld w w') (i k : Nat) : KeepsWorld w (w'.carry i k) :=
  keepsWorld_states h rfl

theorem keepsWorld_recordSent {w w' : World} (h : KeepsWorld w w') (i : Nat) (service : String) (before : Nat) :
    KeepsWorld w (w'.recordSent i service before) :=
  keepsWorld_states h (by unfold World.recordSent; split <;> rfl)

theorem keepsWorld_stated {w w' : World} (h : KeepsWorld w w') (i : Nat) (msg : Message) :
    KeepsWorld w (w'.stated i msg) := by
  unfold World.stated; split
  · exact keepsWorld_report h _
  · exact keepsWorld_states h rfl

theorem keepsWorld_nextId {w w' : World} (h : KeepsWorld w w') (peer name : String) :
    KeepsWorld w (w'.nextId peer name).1 := keepsWorld_states h rfl

theorem keepsWorld_resolving {α : Type} {w w' : World} (h : KeepsWorld w w') (r : ExceptT Report Id α)
    (k : α → Id World) (hk : ∀ a, KeepsWorld w (k a)) : KeepsWorld w (w'.resolving r k) := by
  unfold World.resolving; simp only [bind]; split
  · exact keepsWorld_report h _
  · exact hk _

theorem keepsWorld_attempt {α : Type} {w w' : World} (h : KeepsWorld w w') (r : Except Report α)
    (k : α → Id World) (hk : ∀ a, KeepsWorld w (k a)) : KeepsWorld w (w'.attempt r k) := by
  unfold World.attempt; split
  · exact keepsWorld_report h _
  · exact hk _

theorem keepsWorld_deliver {w w' : World} (h : KeepsWorld w w') (o : Scenario.Origin) (k : Nat) :
    KeepsWorld w (w'.deliver fsOf o k) := by
  unfold World.deliver; split
  · exact h
  · exact keepsWorld_act (keepsWorld_setStatus h _ _) _ _ _ (fun st s => keeps_arriveFrom _ _ _ _ _ _) _

theorem keepsWorld_deliverCarried {w w' : World} (h : KeepsWorld w w') (i k : Nat) :
    KeepsWorld w (w'.deliverCarried fsOf i k) := by
  unfold World.deliverCarried
  simp only [bind, pure]
  repeat' split
  all_goals first
    | exact keepsWorld_carry h _ _
    | exact keepsWorld_setStatus (keepsWorld_carry h _ _) _ _
    | exact keepsWorld_deliver (keepsWorld_carry h _ _) _ _
    | (refine foldl_keeps (KeepsWorld w) _ (fun v l hv => ?_) _ _ (keepsWorld_deliver (keepsWorld_carry h _ _) _ _)
       split
       · exact hv
       · exact keepsWorld_recordSent hv _ _ _)

theorem keepsWorld_clientRequest {w w' : World} (h : KeepsWorld w w') (i : Nat) (type : Scenario.RequestType)
    (target : Syntax.Ref) (input : Scenario.Template) (sameIdAs : Option Nat) :
    KeepsWorld w (w'.clientRequest fsOf i type target input sameIdAs) := by
  unfold World.clientRequest
  simp only [bind, pure]
  split
  · exact keepsWorld_report h _
  · refine keepsWorld_resolving h _ _ fun v => ?_
    repeat' split
    all_goals first
      | exact keepsWorld_report h _
      | exact keepsWorld_recordSent (keepsWorld_act h _ _ _ (fun st s => keeps_requestOf _ _ _ _ _ _ _) _) _ _ _

theorem keepsWorld_now_iff {w w' : World} (now : Time) : KeepsWorld w { w' with now } ↔ KeepsWorld w w' := Iff.rfl

theorem keepsWorld_inFlight_iff {w w' : World} (inFlight : List (Nat × Nat)) :
    KeepsWorld w { w' with inFlight } ↔ KeepsWorld w w' := Iff.rfl

theorem keepsWorld_messages_iff {w w' : World} (messages : Array Message) :
    KeepsWorld w { w' with messages } ↔ KeepsWorld w w' := Iff.rfl

theorem keepsWorld_deliverInOrder {w w' : World} (h : KeepsWorld w w') (i k : Nat) :
    KeepsWorld w (w'.deliverInOrder fsOf i k) := by
  unfold World.deliverInOrder; simp only [pure]
  repeat' split
  · exact h
  · exact keepsWorld_report h _
  · exact keepsWorld_deliverCarried h _ _

/-- Closes `KeepsWorld w x` where `x` is built from `w` by steps that keep every participant's createKey values. -/
macro "kw_tac" : tactic => `(tactic| repeat' (first
  | contradiction
  | with_reducible assumption
  | with_reducible exact KeepsWorld.refl _
  | with_reducible apply keepsWorld_report
  | with_reducible apply keepsWorld_carry
  | with_reducible apply keepsWorld_recordSent
  | with_reducible apply keepsWorld_stated
  | with_reducible apply keepsWorld_nextId
  | with_reducible apply keepsWorld_setStatus
  | with_reducible apply keepsWorld_deliverCarried
  | with_reducible apply keepsWorld_clientRequest
  | with_reducible apply keepsWorld_deliverInOrder
  | (with_reducible refine keepsWorld_act ?_ _ _ _ (fun st s => ?_) _)
  | simp only [keepsWorld_now_iff, keepsWorld_inFlight_iff, keepsWorld_messages_iff]
  | with_reducible refine keepsWorld_resolving ?_ _ _ fun _ => ?_
  | with_reducible refine keepsWorld_attempt ?_ _ _ fun _ => ?_
  | with_reducible refine foldl_keeps _ _ (fun _ _ _ => ?_) _ _ ?_
  | with_reducible exact keeps_endSubscription _ _
  | with_reducible exact keeps_operate _ _ _ _
  | with_reducible exact keeps_restart _
  | with_reducible exact keeps_fireTo _ _ _ _
  | dsimp only
  | split))

theorem keepsWorld_take (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line) :
    KeepsWorld w (w.take fsOf own lines i l) := by
  cases l <;> simp only [World.take, bind, pure, foldlM_id]
  all_goals kw_tac

theorem keepsWorld_line (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line) :
    KeepsWorld w (w.line fsOf own lines i l) := by
  unfold World.line
  dsimp only
  split
  · exact keepsWorld_report (.refl w) _
  · exact keepsWorld_take w own lines i l

/-- A line of When keeps every participant's createKey values: it may only add to them. -/
theorem step_keepsKeys (w : World) (sc : Scenario) (l : Scenario.Line) (i : Nat) :
    KeepsWorld w (w.step fsOf sc l i) := by
  unfold World.step
  split
  · exact .refl w
  · exact keepsWorld_line w _ _ i l

theorem keepsWorld_beginAll (w : World) : KeepsWorld w (w.beginAll fsOf) := by
  unfold World.beginAll
  rw [foldlM_id]
  refine foldl_keeps (KeepsWorld w) _ (fun v x hv => ?_) _ _ (.refl w)
  dsimp only
  split
  · exact hv
  · exact keepsWorld_act hv _ _ _ (fun st s => keeps_begin _) _

theorem keeps_lookup_map (l : List (String × State)) (g : String × State → String × State)
    (h : ∀ a, (g a).1 = a.1 ∧ KeepsKeys a.2 (g a).2) (p : String) :
    KeepsKeys ((l.lookup p).getD {}) (((l.map g).lookup p).getD {}) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
    obtain ⟨q, x⟩ := a
    obtain ⟨h₁, h₂⟩ := h (q, x)
    show KeepsKeys ((List.lookup p ((q, x) :: l)).getD {}) ((List.lookup p (g (q, x) :: _)).getD {})
    rw [show g (q, x) = (q, (g (q, x)).2) from Prod.ext h₁ rfl, List.lookup_cons, List.lookup_cons]
    split
    · exact h₂
    · exact ih

theorem keeps_ite_records (c : Bool) (x : State) (rows : Records) :
    KeepsKeys x (if c = true then { x with records := rows } else x) := by
  cases c <;> exact .refl _

theorem keepsWorld_given (w : World) (j : Syntax.Structure) (sc : Scenario) : KeepsWorld w (w.given j fsOf sc) := by
  unfold World.given
  simp only [bind, pure]
  rw [foldlM_id]
  have hn : ∀ (rs : List Report) (v : World), (rs.foldl World.note v).states = v.states := by
    intro rs; induction rs with
    | nil => intro v; rfl
    | cons r rs ih => intro v; simp only [List.foldl_cons]; rw [ih]; rfl
  refine foldl_keeps (KeepsWorld w) _ (fun v x hv => ?_) _ _ (keepsWorld_states (.refl w) (hn _ _))
  intro p
  refine (hv p).trans ?_
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
    split <;> exact .refl _

/-- The lines of a scenario keep every participant's createKey values from the start: they may only add to them. -/
theorem walk_keepsKeys (j : Syntax.Structure) (start : World) (sc : Scenario) :
    KeepsWorld start (walk j fsOf start sc) := by
  unfold walk World.walk
  simp only [bind, pure]
  have hg := keepsWorld_given (fsOf := fsOf) start j sc
  split
  · exact hg
  · rw [foldlM_id]
    refine foldl_keeps (KeepsWorld start) _ (fun v x hv => hv.trans (step_keepsKeys _ _ _ _)) _ _
      (hg.trans (keepsWorld_beginAll _))

theorem givenKeys_prefix (o : Option String) {es es' : List String} (h : es <+: es') :
    givenKeys { owner := o } es <+: givenKeys { owner := o } es' := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨(givenKeys { owner := o } (es ++ t)).drop es.length, ?_⟩
  conv => rhs; rw [← List.take_append_drop es.length (givenKeys { owner := o } (es ++ t))]
  congr 1
  apply List.ext_getElem
  · simp [length_givenKeys]
  · intro i h₁ h₂
    have hi : i < es.length := by simpa [length_givenKeys] using h₁
    obtain ⟨a₁, a₂⟩ := givenKeys_getElem_pair o es i h₁
    have h₂' : i < (givenKeys { owner := o } (es ++ t)).length := by simp [length_givenKeys]; omega
    obtain ⟨b₁, b₂⟩ := givenKeys_getElem_pair o (es ++ t) i h₂'
    rw [List.getElem_take]
    have ht : (es ++ t).take i = es.take i := List.take_append_of_le_length (Nat.le_of_lt hi)
    have he : (es ++ t)[i]'(by simp; omega) = es[i] := List.getElem_append_left hi
    apply Prod.ext
    · rw [a₁, b₁, he]
    · apply String.toList_inj.mp
      rw [a₂, b₂, he, ht]

/-- A participant keeps every createKey value that it has: each is among its values in any later world. -/
theorem created_kept {w w' : World} (h : KeepsWorld w w') (p : String) :
    (w.state p).created <+: (w'.state p).created := by
  unfold State.created
  rw [(h p).1]
  exact givenKeys_prefix _ (h p).2

/--
No createKey value of a running participant at the end of the lines of a scenario equals a key of a keyed entity that
the start's writtenKey? lets the scenario write: the participant qualifies its values by its name throughout the run.
-/
theorem walk_unwritten_not_created (j : Syntax.Structure) (start : World) (sc : Scenario) {p : String} {st : Service}
    (hs : (p, st) ∈ start.services) (ho : (start.state p).keyOwner = some p) {e k : String} (he : e ∈ st.entities)
    (hk : st.singles.contains e = false) (hw : start.writtenKey? (.str k) = none) :
    (e, k) ∉ ((walk j fsOf start sc).state p).created :=
  unwritten_not_created hs (((walk_keepsKeys j start sc) p).1.trans ho) he hk hw

end Tazuna.Thm.Sim.Keys
