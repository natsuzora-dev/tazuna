import Tazuna.Semantics.Service.Response
import Tazuna.Thm.Semantics.Service.State
import Tazuna.Thm.Semantics.Value.Basic

/-!
The responses' observer changes only the obligations and the findings: what a state holds besides is the same after it.
-/

namespace Tazuna.Thm.Semantics.Service.Response

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service Tazuna.Thm.Semantics.Value.Basic Tazuna.Thm.Semantics.Service.State

variable {st : Service} {fs : Functions Id} {s : Service.State}

theorem report_preserves {α : Type} (g : Service.State → α) (hv : ∀ (t : Service.State) v, g { t with violations := v } = g t)
    (hh : ∀ (t : Service.State) h, g { t with halted := h } = g t) (t : Service.State) (f : Finding) : g (t.report f) = g t := by
  unfold State.report State.halt State.violate
  split
  · exact hh _ _
  · exact hv _ _

theorem observeResponses_preserves {α : Type} (g : Service.State → α) (hg : ∀ (t : Service.State) f, g (t.report f) = g t)
    (ho : ∀ (t : Service.State) os, g { t with obligations := os } = g t) : g (observeResponses st fs s) = g s := by
  unfold observeResponses
  split
  · rfl
  · rw [foldlM_id]
    refine foldl_keeps (fun b => g b = g s) _ ?_ _ _ (ho s _)
    intro b row hb
    simp only [id_bind]
    split <;> simp only [id_pure]
    · rw [hg]; exact hb
    · rw [ho]; exact hb

@[simp] theorem observeResponses_fixed : (observeResponses st fs s).fixed = s.fixed :=
  observeResponses_preserves State.fixed (fun _ f => report_fixed f) (fun _ _ => rfl)

@[simp] theorem observeResponses_records : (observeResponses st fs s).records = s.records :=
  observeResponses_preserves (·.records) (fun _ f => report_records f) (fun _ _ => rfl)

@[simp] theorem observeResponses_lines : (observeResponses st fs s).lines = s.lines :=
  observeResponses_preserves (·.lines) (fun _ f => report_lines f) (fun _ _ => rfl)

@[simp] theorem observeResponses_now : (observeResponses st fs s).now = s.now :=
  observeResponses_preserves (·.now) (fun _ f => report_now f) (fun _ _ => rfl)

@[simp] theorem observeResponses_service : (observeResponses st fs s).service = s.service :=
  observeResponses_preserves (·.service) (fun _ f => report_service f) (fun _ _ => rfl)

@[simp] theorem observeResponses_createdEntities :
    (observeResponses st fs s).createdEntities = s.createdEntities :=
  observeResponses_preserves (·.createdEntities) (report_preserves (·.createdEntities) (fun _ _ => rfl) (fun _ _ => rfl))
    (fun _ _ => rfl)

theorem observeResponses_grows : Grows s (observeResponses st fs s) :=
  Grows.of_lines observeResponses_lines observeResponses_service

@[simp] theorem passTime_records (t : Time) : (s.passTime st t).records = s.records := by
  simp [State.passTime]

@[simp] theorem passTime_lines (t : Time) : (s.passTime st t).lines = s.lines := by
  simp [State.passTime]

@[simp] theorem passTime_now (t : Time) : (s.passTime st t).now = max s.now t := by
  simp [State.passTime]

@[simp] theorem passTime_service (t : Time) : (s.passTime st t).service = s.service := by
  simp [State.passTime]

@[simp] theorem passTime_createdEntities (t : Time) : (s.passTime st t).createdEntities = s.createdEntities := by
  simp only [State.passTime]
  exact reportAll_preserves (·.createdEntities)
    (fun t _ => report_preserves (·.createdEntities) (fun _ _ => rfl) (fun _ _ => rfl) t _) _ _

end Tazuna.Thm.Semantics.Service.Response
