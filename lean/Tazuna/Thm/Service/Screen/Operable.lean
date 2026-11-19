import Tazuna.Service.Screen.Operable
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Service.Screen.Operable

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem accepting_skips (resource : InstanceId) (pre rest : List InstanceId)
    (hp : ∀ r ∈ pre, r ≠ resource ∧ ∀ i, s.machine? r = some i → i.modal = false) :
    State.accepting.go s resource (pre ++ rest) = State.accepting.go s resource rest := by
  induction pre with
  | nil => rfl
  | cons r pre ih =>
    simp only [List.cons_append]
    obtain ⟨hn, ho⟩ := hp r List.mem_cons_self
    conv => lhs; rw [State.accepting.go]
    rw [ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))]
    cases hm : s.machine? r with
    | none => rfl
    | some i =>
      have hn' : (r == resource) = false := by simpa using hn
      simp [hn', ho i hm]

/-- An instance that a modal `opens` opened after the operated instance `resource` covers it. -/
theorem modal_child_covers (resource : InstanceId) (pre rest : List InstanceId) (c : InstanceId) (ci : Instance)
    (hp : ∀ r ∈ pre, r ≠ resource ∧ ∀ i, s.machine? r = some i → i.modal = false)
    (hc : s.machine? c = some ci) (hn : c ≠ resource) (hm : ci.modal = true) :
    State.accepting.go s resource (pre ++ c :: rest) = .error (.covered ci.chart.name) := by
  rw [accepting_skips resource pre (c :: rest) hp, State.accepting.go]
  have hn' : (c == resource) = false := by simpa using hn
  simp [hc, hn', hm]

/--
The operated instance `resource` accepts when only non-modal instances were opened after it, whatever their charts, so
several open instances of one screen are each operable (B13).
-/
theorem nonmodal_child_lets_parent (resource : InstanceId) (pre rest : List InstanceId) (pi : Instance)
    (hp : ∀ r ∈ pre, r ≠ resource ∧ ∀ i, s.machine? r = some i → i.modal = false)
    (hpi : s.machine? resource = some pi) :
    State.accepting.go s resource (pre ++ resource :: rest) = .ok pi := by
  rw [accepting_skips resource pre (resource :: rest) hp, State.accepting.go]
  simp [hpi]

end Tazuna.Thm.Service.Screen.Operable
