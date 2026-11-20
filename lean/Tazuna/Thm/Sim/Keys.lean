import Tazuna.Sim.Run
import Tazuna.Thm.Sim.Run
import Tazuna.Thm.Sim.Keeps
import Tazuna.Thm.Service.Keys
import Tazuna.Thm.Service.KeyGrowth
import Tazuna.Thm.Guarantee

/-!
The createKey values of the running services of a simulation: each running service's values differ from each other, and from
every string that the scenario may write, so a Given record never holds a key that a running service creates later.
-/

namespace Tazuna.Thm.Sim.Keys

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Service.Keys Tazuna.Thm.Service.KeyGrowth
open Tazuna.Thm.Data.Basic Tazuna.Thm.Sim.Keeps

/--
A string that writtenKey? lets a scenario write is no createKey value of a keyed entity of a running service `p`,
in any state whose values `p` qualifies.
-/
@[guarantee] theorem unwritten_not_created {w : World} {p : String} {st : Service} (hs : (p, st) ∈ w.services) {s : State}
    (ho : s.service = p) {e k : String} (he : e ∈ st.entities) (hk : st.singles.contains e = false)
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

theorem keeps_stepOrder (x : State) (o : List StepName) : KeepsKeys x { x with stepOrder := o } := .refl _

theorem keeps_checkStepOrder (x : State) : KeepsKeys x (checkStepOrder x) := by
  unfold checkStepOrder; split <;> keys_leaf

theorem keeps_answerIn (st : Service) (fs : Functions Id) (s : State) (id to : LineId) (a : Answer) :
    KeepsKeys s (answerIn st fs s id to a) := by
  unfold answerIn
  split
  · refine KeepsKeys.trans ?_ (keeps_message _ _)
    keys_leaf
  · dsimp only
    split
    · exact (by keys_leaf : KeepsKeys s { s with deliveries := _ }).trans (keeps_answerRequest _ _ _ _)
    · refine KeepsKeys.trans ?_ (keeps_message _ _)
      keys_leaf

theorem keeps_arriveFrom (st : Service) (fs : Functions Id) (s : State) (sender : String) (id : LineId)
    (body : LineBody) :
    KeepsKeys s (arriveFrom st fs s sender id body) := by
  unfold arriveFrom
  dsimp only
  split
  · exact keeps_send _ _ _ _
  · exact keeps_call _ _ _ _
  · exact keeps_subscribe _ _ _ _
  · exact keeps_endSubscription _ _
  · split
    · exact keeps_answerIn _ _ _ _ _ _
    · exact .refl _
  · exact keeps_receive _ _ _ _ _
  · exact .refl _

theorem keeps_arriveAll (st : Service) (fs : Functions Id) (arrivals : List Arrival) (s : State) :
    KeepsKeys s (arriveAll st fs arrivals s) := by
  unfold arriveAll
  suffices ∀ first arrivals s, KeepsKeys s (arriveAll.go st fs first arrivals s) from this _ _ s
  intro first arrivals s
  fun_induction arriveAll.go st fs first arrivals s
  all_goals simp only [bind, pure]
  all_goals first
    | exact .refl _
    | keys_leaf
    | (rename_i hx ih; refine KeepsKeys.trans ?_ (ih _)
       refine KeepsKeys.trans (KeepsKeys.trans ?_ (keeps_arriveFrom st fs _ _ _ _)) ⟨rfl, List.prefix_refl _⟩
       have hs := congrArg Prod.fst hx; simp only at hs; rw [← hs]
       keys_leaf)

theorem keeps_fireTo (time : Time) (st : Service) (fs : Functions Id) (s : State) :
    KeepsKeys s (fireTo time st fs s) := by
  simp only [fireTo, id_bind]
  have h := keeps_fireDue (st := st) (fs := fs) time Limit.dueDeadlines.max none s
  split
  · keys_close h
  · refine KeepsKeys.trans ?_ (keeps_publish _)
    keys_close h

theorem keeps_requestOf (type : Scenario.RequestType) (name : Spec.Ref) (id : Option LineId) (v : Value)
    (st : Service) (fs : Functions Id) (s : State) : KeepsKeys s (requestOf type name id v st fs s) := by
  cases type
  · exact keeps_send _ _ _ _
  · exact keeps_call _ _ _ _
  · exact keeps_subscribe _ _ _ _

/-- Keeping the createKey values, which every input of a line does. -/
abbrev keysRel : StateRel where
  R := KeepsKeys
  refl := .refl
  trans := .trans
  stepOrder := keeps_stepOrder
  checkStepOrder := keeps_checkStepOrder
  arriveFrom := keeps_arriveFrom
  arriveAll := keeps_arriveAll
  requestOf := keeps_requestOf

theorem keepsWorld_take (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line) :
    KeepsWorld keysRel w (w.take fsOf own lines i l) := by
  cases l <;> simp only [World.take, bind, pure, foldlM_id]
  all_goals keeps_tac first
    | exact keeps_endSubscription _ _
    | exact keeps_operate _ _ _ _
    | exact keeps_restart _
    | exact keeps_fireTo _ _ _ _

/-- A line of When keeps every running service's createKey values: it may only add to them. -/
theorem step_keepsKeys (w : World) (sc : Scenario) (l : Scenario.Line) (i : Nat) :
    KeepsWorld keysRel w (w.step fsOf sc l i) := by
  unfold World.step
  split
  · exact .refl _ w
  · exact keepsWorld_line w _ _ i l (keepsWorld_take w _ _ i l)

theorem keepsWorld_beginAll (w : World) : KeepsWorld keysRel w (w.beginAll fsOf) := by
  unfold World.beginAll
  rw [foldlM_id]
  refine foldl_keeps (KeepsWorld keysRel w) _ (fun v x hv => ?_) _ _ (.refl _ w)
  dsimp only
  split
  · exact hv
  · exact keepsWorld_act hv _ _ _ (fun st s => keeps_begin _)

theorem keeps_lookup_map (l : List (String × State)) (g : String × State → String × State)
    (h : ∀ a, (g a).1 = a.1 ∧ KeepsKeys a.2 (g a).2) (p : String) :
    KeepsKeys ((l.lookup p).getD { service := p }) (((l.map g).lookup p).getD { service := p }) := by
  induction l with
  | nil => exact .refl _
  | cons a l ih =>
    obtain ⟨q, x⟩ := a
    obtain ⟨h₁, h₂⟩ := h (q, x)
    show KeepsKeys ((List.lookup p ((q, x) :: l)).getD { service := p }) ((List.lookup p (g (q, x) :: _)).getD { service := p })
    rw [show g (q, x) = (q, (g (q, x)).2) from Prod.ext h₁ rfl, List.lookup_cons, List.lookup_cons]
    split
    · exact h₂
    · exact ih

theorem keepsWorld_given (w : World) (j : Spec.Structure) (sc : Scenario) : KeepsWorld keysRel w (w.given j fsOf sc) := by
  unfold World.given
  simp only [bind, pure]
  rw [foldlM_id]
  have hn : ∀ (rs : List InvalidScenario) (v : World), (rs.foldl World.note v).states = v.states := by
    intro rs; induction rs with
    | nil => intro v; rfl
    | cons r rs ih => intro v; simp only [List.foldl_cons]; rw [ih]; rfl
  refine foldl_keeps (KeepsWorld keysRel w) _ (fun v x hv => ?_) _ _ (keepsWorld_states (.refl _ w) (hn _ _))
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

/-- The lines of a scenario keep every running service's createKey values from the start: they may only add to them. -/
@[guarantee] theorem execute_keepsKeys (j : Spec.Structure) (start : World) (sc : Scenario) :
    KeepsWorld keysRel start (execute j fsOf start sc) := by
  unfold execute World.execute
  simp only [bind, pure]
  have hg := keepsWorld_given (fsOf := fsOf) start j sc
  split
  · exact hg
  · rw [foldlM_id]
    refine foldl_keeps (KeepsWorld keysRel start) _ (fun v x hv => hv.trans (step_keepsKeys _ _ _ _)) _ _
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

/-- A running service keeps every createKey value that it has: each is among its values in any later world. -/
@[guarantee] theorem created_kept {w w' : World} (h : KeepsWorld keysRel w w') (p : String) :
    (w.state p).created <+: (w'.state p).created := by
  unfold State.created
  rw [(h p).1]
  exact givenKeys_prefix _ (h p).2

/--
No createKey value of a running service at the end of the lines of a scenario equals a key of a keyed entity that
the start's writtenKey? lets the scenario write: the running service qualifies its values by its name throughout the run.
-/
@[guarantee] theorem execute_unwritten_not_created (j : Spec.Structure) (start : World) (sc : Scenario) {p : String} {st : Service}
    (hs : (p, st) ∈ start.services) (ho : (start.state p).service = p) {e k : String} (he : e ∈ st.entities)
    (hk : st.singles.contains e = false) (hw : start.writtenKey? (.str k) = none) :
    (e, k) ∉ ((execute j fsOf start sc).state p).created :=
  unwritten_not_created hs (((execute_keepsKeys j start sc) p).1.trans ho) he hk hw

end Tazuna.Thm.Sim.Keys
