import Tazuna.Thm.Semantics.Sim.Keeps
import Tazuna.Thm.Semantics.Service.LineIds
import Tazuna.Thm.Guarantee

/-!
The ids of each running service's own lines: no two requests that a running service sends carry one id, at any point
of a run, so a request's receiver never finds its id already used (RejectionKind.blamesSender).
-/

namespace Tazuna.Thm.Semantics.Sim.LineIds

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Sim
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Sim.Keeps Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Semantics.Service.LineIds
open Tazuna.Thm.Semantics.Service.Query

variable {fsOf : String → Functions Id}

theorem keepsIds_answerIn (st : Service) (fs : Functions Id) (s : Service.State) (id to : LineId) (a : Answer) :
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

theorem keepsIds_arriveFrom (st : Service) (fs : Functions Id) (s : Service.State) (sender : String) (id : LineId)
    (body : LineBody) : KeepsIds s (arriveFrom st fs s sender id body) := by
  unfold arriveFrom
  dsimp only
  split
  · exact keepsIds_send _ _ _ _ _
  · exact keepsIds_call _ _ _ _ _
  · exact keepsIds_subscribe _ _ _ _ _
  · exact keepsIds_endSubscription _ _
  · split
    · exact keepsIds_answerIn _ _ _ _ _ _
    · exact .refl _
  · exact keepsIds_receive _ _ _ _ _
  · exact .refl _

theorem keepsIds_arriveAll (st : Service) (fs : Functions Id) (arrivals : List Arrival) (s : Service.State) :
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

theorem keepsIds_fireTo (time : Time) (st : Service) (fs : Functions Id) (s : Service.State) :
    KeepsIds s (fireTo time st fs s) := by
  simp only [fireTo, id_bind]
  refine (keepsIds_fireDue (st := st) (fs := fs) time Limit.dueDeadlines.max none s).trans ?_
  split
  · exact .of_lines (by simp)
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
  requestOf type _ _ _ _ _ _ _ := by cases type <;> first
    | exact keepsIds_send _ _ _ _ _ | exact keepsIds_call _ _ _ _ _ | exact keepsIds_subscribe _ _ _ _ _

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
each running service's lines are numbered (as `World.start` leaves them, with none): each `out` line keeps its place,
and the service numbers each one it writes by its name and the count of the lines before it with that name. A request
message carries its line's id (post_message), and its receiver keys ids by sender, so it never finds a request's id
already used.
-/
@[guarantee] theorem sent_ids_distinct (j : Ir.Structure) (start : World) (sc : Scenario) (p : String)
    (h : Numbered (start.state p).service (start.state p).lines) :
    let lines := ((execute j fsOf start sc).state p).lines
    (start.state p).lines.toList <+: lines.toList ∧
      ∀ i k (hik : i < k) (hk : k < lines.size), lines[i].dir = .out → lines[k].dir = .out →
        lines[i].id ≠ lines[k].id := by
  have hp := execute_keeps (ρ := idsRel) (fsOf := fsOf) (fun _ _ _ => keepsIds_begin _) (fun _ _ => .of_lines rfl)
    keepsWorld_take j start sc p
  exact ⟨hp.1, fun _ _ hik hk => numbered_ids_distinct (hp.2 h) hik hk⟩

/--
A message that World.post adds carries the line's id and sender: a receiver reads a request's id from its `out` line.
-/
@[guarantee] theorem post_message (w : World) (o : Scenario.Origin) (sender receiver : String) (l : Line)
    (definition : Ir.Ref) :
    ∃ new, (w.post o sender receiver l definition).messages = w.messages ++ new ∧
      ∀ msg ∈ new, msg.id = l.id ∧ msg.sender = sender := by
  rcases hr : w.role receiver with _ | role <;> simp only [World.post, World.report, hr]
  · exact ⟨#[], by (repeat' split) <;> rfl, by simp⟩
  · exact ⟨#[_], by rw [Array.push_eq_append], by simp⟩

theorem startWith_numbered (sc : Scenario) (services : List (String × Service))
    (stepOrders : List (Scenario.Origin × String × List StepName)) (p : String) :
    let s := ({ World.startWith sc services with stepOrders } : World).state p
    Numbered s.service s.lines := by
  show Numbered _ ((World.startWith sc services).state p).lines
  rw [(startWith_state sc services p).1]; exact numbered_empty _

/--
No two requests that a running service sends carry one id, in a run from a world that World.start returns, whatever
step orders test's search sets: the start holds no lines.
-/
@[guarantee] theorem start_sent_ids_distinct (j : Ir.Structure) (sc : Scenario) (services : List (String × Service))
    (stepOrders : List (Scenario.Origin × String × List StepName)) (p : String) :
    let lines := ((execute j fsOf { World.startWith sc services with stepOrders } sc).state p).lines
    ∀ i k (hik : i < k) (hk : k < lines.size), lines[i].dir = .out → lines[k].dir = .out →
      lines[i].id ≠ lines[k].id :=
  (sent_ids_distinct j _ sc p (startWith_numbered sc services stepOrders p)).2

end Tazuna.Thm.Semantics.Sim.LineIds
