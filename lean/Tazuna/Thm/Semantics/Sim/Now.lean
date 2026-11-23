import Tazuna.Thm.Semantics.Sim.Keeps
import Tazuna.Thm.Semantics.Service.Now
import Tazuna.Thm.Guarantee

/-!
The current time of each running service, which every line that the service writes carries, moves only at a clock line.
-/

namespace Tazuna.Thm.Semantics.Sim.Now

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Semantics.Sim
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Sim.Keeps Tazuna.Thm.Semantics.Service.Now

variable {fsOf : String → Functions Id}

theorem answerIn_now (st : Service) (fs : Functions Id) (s : Service.State) (id to : LineId) (a : Answer) :
    (answerIn st fs s id to a).now = s.now := by
  unfold answerIn
  split
  · rw [message_now]; simp [State.write, State.newMessage]
  · dsimp only
    split
    · exact answerRequest_now _ _ _ _
    · rw [message_now]; simp [State.write, State.newMessage]

theorem arriveFrom_now (st : Service) (fs : Functions Id) (s : Service.State) (sender : String) (id : LineId)
    (body : LineBody) : (arriveFrom st fs s sender id body).now = s.now := by
  unfold arriveFrom
  dsimp only
  split
  · exact send_now _ _ _ _ _
  · exact call_now _ _ _ _ _
  · exact subscribe_now _ _ _ _ _
  · exact endSubscription_now _ _
  · split
    · exact answerIn_now _ _ _ _ _ _
    · rfl
  · exact receive_now _ _ _ _ _
  · rfl

theorem arriveAll_now (st : Service) (fs : Functions Id) (arrivals : List Arrival) (s : Service.State) :
    (arriveAll st fs arrivals s).now = s.now := by
  unfold arriveAll
  suffices ∀ first arrivals s, (arriveAll.go st fs first arrivals s).now = s.now from this _ _ s
  intro first arrivals s
  fun_induction arriveAll.go st fs first arrivals s
  all_goals simp only [bind, pure]
  all_goals first
    | rfl
    | simp
    | (rename_i hx ih; rw [ih, arriveFrom_now]
       have hs := congrArg Prod.fst hx; simp only at hs; rw [← hs]; rfl)

/-- Keeping the current time, which every input of a line but a clock advance does. -/
abbrev nowRel : StateRel where
  R s t := t.now = s.now
  refl _ := rfl
  trans h₁ h₂ := h₂.trans h₁
  stepOrder _ _ := rfl
  checkStepOrder x := by unfold checkStepOrder; split <;> simp
  arriveFrom := arriveFrom_now
  arriveAll := arriveAll_now
  requestOf type _ _ _ _ _ _ _ := by cases type <;> first
    | exact send_now _ _ _ _ _ | exact call_now _ _ _ _ _ | exact subscribe_now _ _ _ _ _

/--
Only a clock line moves the current time of a running service, the time that every line it writes carries: any other
line keeps the current time of every running service.
-/
@[guarantee] theorem only_clock_moves_time (w : World) (own : String) (lines : List Scenario.Line) (i : Nat)
    (l : Scenario.Line) (hl : ∀ t, l ≠ .at t) (p : String) :
    ((w.line fsOf own lines i l).state p).now = (w.state p).now := by
  refine keepsWorld_line (ρ := nowRel) w own lines i l ?_ p
  cases l with
  | «at» t => exact absurd rfl (hl t)
  | _ =>
    simp only [World.take, bind, pure, foldlM_id]
    all_goals keeps_tac first
      | exact endSubscription_now _ _
      | exact operate_now _ _ _ _
      | exact restart_now _

end Tazuna.Thm.Semantics.Sim.Now
