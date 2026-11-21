import Tazuna.Thm.Sim.Keeps
import Tazuna.Thm.Service.LineIds
import Tazuna.Thm.Guarantee

/-!
The ids of each running service's own lines: no two requests that a running service sends carry one id, at any point
of a run, so a request's receiver never finds its id already used (RejectionKind.blamesSender).
-/

namespace Tazuna.Thm.Sim.LineIds

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Data.Basic Tazuna.Thm.Sim.Keeps Tazuna.Thm.Service.State Tazuna.Thm.Service.LineIds
open Tazuna.Thm.Service.Query

variable {fsOf : String → Functions Id}

theorem keepsIds_answerIn (st : Service) (fs : Functions Id) (s : State) (id to : LineId) (a : Answer) :
    KeepsIds s (answerIn st fs s id to a) := by
  unfold answerIn
  split
  · refine KeepsIds.trans ?_ (keepsIds_message _ _)
    ids_leaf
  · dsimp only
    split
    · refine KeepsIds.trans ?_ (keepsIds_answerRequest _ _ _ _)
      exact .of_lines rfl
    · refine KeepsIds.trans ?_ (keepsIds_message _ _)
      ids_leaf

theorem keepsIds_arriveFrom (st : Service) (fs : Functions Id) (s : State) (sender : String) (id : LineId)
    (body : LineBody) : KeepsIds s (arriveFrom st fs s sender id body) := by
  unfold arriveFrom
  dsimp only
  split
  · exact keepsIds_send _ _ _ _
  · exact keepsIds_call _ _ _ _
  · exact keepsIds_subscribe _ _ _ _
  · exact keepsIds_endSubscription _ _
  · split
    · exact keepsIds_answerIn _ _ _ _ _ _
    · exact .refl _
  · exact keepsIds_receive _ _ _ _ _
  · exact .refl _

theorem keepsIds_arriveAll (st : Service) (fs : Functions Id) (arrivals : List Arrival) (s : State) :
    KeepsIds s (arriveAll st fs arrivals s) := by
  unfold arriveAll
  suffices ∀ first arrivals s, KeepsIds s (arriveAll.go st fs first arrivals s) from this _ _ s
  intro first arrivals s
  fun_induction arriveAll.go st fs first arrivals s
  all_goals simp only [bind, pure]
  all_goals first
    | exact .refl _
    | exact .of_lines (by simp)
    | (rename_i hx ih; refine KeepsIds.trans ?_ (ih _)
       refine KeepsIds.trans ?_ (keepsIds_arriveFrom st fs _ _ _ _)
       have hs := congrArg Prod.fst hx; simp only at hs; rw [← hs]
       exact .of_lines rfl)

theorem keepsIds_fireTo (time : Time) (st : Service) (fs : Functions Id) (s : State) :
    KeepsIds s (fireTo time st fs s) := by
  simp only [fireTo, id_bind]
  refine (keepsIds_fireDue (st := st) (fs := fs) time Limit.dueDeadlines.max none s).trans ?_
  split
  · exact .of_lines rfl
  · refine KeepsIds.trans ?_ publish_grows.keepsIds
    ids_leaf

/-- Keeping the lines and numbering each `out` line as State.write does, which every input of a line does. -/
abbrev idsRel : StateRel where
  R := KeepsIds
  refl := .refl
  trans := .trans
  stepOrder _ _ := .of_lines rfl
  checkStepOrder x := by unfold checkStepOrder; split <;> exact .of_lines (by simp)
  arriveFrom := keepsIds_arriveFrom
  arriveAll := keepsIds_arriveAll
  requestOf type _ _ _ _ _ _ := by cases type <;> first
    | exact keepsIds_send _ _ _ _ | exact keepsIds_call _ _ _ _ | exact keepsIds_subscribe _ _ _ _

theorem keepsWorld_take (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line) :
    KeepsWorld idsRel w (w.take fsOf own lines i l) := by
  cases l <;> simp only [World.take, bind, pure, foldlM_id]
  all_goals keeps_tac first
    | exact keepsIds_endSubscription _ _
    | exact keepsIds_operate _ _ _ _
    | exact keepsIds_restart _
    | exact keepsIds_fireTo _ _ _ _

/--
No two requests that a running service sends carry one id, at any point of the lines of a scenario from a start where
each running service's lines are numbered (as Given leaves them, with none): each `out` line keeps its place, and
the service numbers each one it writes by its name and the count of the lines before it with that name, so its
receiver never finds a request's id already used.
-/
@[guarantee] theorem sent_ids_distinct (j : Spec.Structure) (start : World) (sc : Scenario) (p : String)
    (h : Numbered (start.state p).service (start.state p).lines) :
    let lines := ((execute j fsOf start sc).state p).lines
    (start.state p).lines.toList <+: lines.toList ∧
      ∀ i k (hik : i < k) (hk : k < lines.size), lines[i].dir = .out → lines[k].dir = .out →
        lines[i].id ≠ lines[k].id := by
  have hp := execute_keeps (ρ := idsRel) (fsOf := fsOf) (fun _ _ _ => keepsIds_begin _) (fun _ _ => .of_lines rfl)
    keepsWorld_take j start sc p
  exact ⟨hp.1, fun _ _ hik hk => numbered_ids_distinct (hp.2 h) hik hk⟩

end Tazuna.Thm.Sim.LineIds
