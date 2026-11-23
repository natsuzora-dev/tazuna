import Tazuna.Semantics.Service.Screen.Subscription
import Tazuna.Thm.Semantics.Service.Chart.Exit

namespace Tazuna.Thm.Semantics.Service.Screen.Subscription

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.Chart.Exit Tazuna.Thm.Semantics.Service.Chart.Queue Tazuna.Thm.Semantics.Service.State Tazuna.Thm.Ir.Shape Tazuna.Thm.Semantics.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : Service.State} {service : String}

def kept (wanted : List Wanted) (p : Pending) : Bool := (inputOf wanted (p.requester.slot?.getD "")).any (· == p.input)

theorem endShowStep_fixed (wanted : List Wanted) (owner : InstanceId) (t : Service.State)
    (p : Pending) : (t.endShowStep wanted owner p).fixed = t.fixed := by
  dsimp only [State.endShowStep]
  split
  · rfl
  · split <;> rfl

theorem subscribeStep_fixed (opened : List Pending) (owner : InstanceId) (t : Service.State)
    (w : Wanted) : (t.subscribeStep opened owner w).fixed = t.fixed := by
  obtain ⟨slot, a, input⟩ := w
  dsimp only [State.subscribeStep]
  split
  · rfl
  · exact await_fixed ..

theorem syncShows_fixed (owner : InstanceId) (wanted : List Wanted) :
    (s.syncShows owner wanted).fixed = s.fixed :=
  (foldl_fixed _ (subscribeStep_fixed _ _) _ _).trans (foldl_fixed _ (endShowStep_fixed _ _) _ _)

theorem refresh_fixed (owner : InstanceId) : (refresh st fs s owner).fixed = s.fixed := by
  unfold refresh
  split
  · rfl
  · split
    · rfl
    · simp only [id_bind]
      split
      · exact report_fixed ..
      · exact syncShows_fixed _ _

theorem refreshScreens_fixed : (refreshScreens st fs s).fixed = s.fixed := by
  unfold refreshScreens
  rw [foldlM_id]
  exact foldl_fixed _ (fun t i => by
    split
    · rfl
    · exact refresh_fixed _) _ _

theorem endShowStep_grows (wanted : List Wanted) (owner : InstanceId) (t : Service.State)
    (p : Pending) : Grows t (t.endShowStep wanted owner p) := by
  dsimp only [State.endShowStep]
  split
  · exact Grows.refl _
  · split
    · exact (endSubscription_grows (s := t) p).trans rfl (Grows.of_lines (s := t.endSubscription p) rfl)
    · exact endSubscription_grows _

theorem subscribeStep_grows (opened : List Pending) (owner : InstanceId) (t : Service.State)
    (w : Wanted) : Grows t (t.subscribeStep opened owner w) := by
  obtain ⟨slot, a, input⟩ := w
  dsimp only [State.subscribeStep]
  split
  · exact Grows.refl _
  · exact (grows_write (s := t) Dir.out none _ _ _ _).trans rfl (Grows.of_lines rfl)

theorem syncShows_grows (owner : InstanceId) (wanted : List Wanted) :
    Grows s (s.syncShows owner wanted) :=
  (foldl_grows _ (endShowStep_grows _ _) (fun t p => congrArg Fixed.now (endShowStep_fixed _ _ t p)) _ _).trans
    (congrArg Fixed.now (foldl_fixed _ (endShowStep_fixed _ _) _ _))
    (foldl_grows _ (subscribeStep_grows _ _) (fun t w => congrArg Fixed.now (subscribeStep_fixed _ _ t w)) _ _)

theorem refresh_grows (owner : InstanceId) : Grows s (refresh st fs s owner) := by
  unfold refresh
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · simp only [id_bind]
      split
      · exact Grows.of_lines (report_lines ..)
      · exact syncShows_grows _ _

theorem refreshScreens_grows : Grows s (refreshScreens st fs s) := by
  unfold refreshScreens
  rw [foldlM_id]
  refine foldl_grows _ (fun t i => ?_) (fun t i => ?_) _ _
  · split
    · exact Grows.refl _
    · exact refresh_grows _
  · split
    · rfl
    · exact congrArg Fixed.now (refresh_fixed _)

end Tazuna.Thm.Semantics.Service.Screen.Subscription
