import Tazuna.Service.Screen.Operable
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Service.Screen.Operable

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem accepting_skips (resource : InstanceId) (pre rest : List InstanceId)
    (hp : ∀ r ∈ pre, r ≠ resource ∧ ∀ i, s.machine? r = some i → ∀ o, i.opener = some o → o.modal = false) :
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
      simp only [hn', Bool.false_eq_true, ↓reduceIte]
      cases hop : i.opener with
      | none => rfl
      | some o => simp [ho i hm o hop]

/-- An instance that a modal `opens` opened after the operated instance `resource` covers it. -/
theorem modal_child_covers (resource : InstanceId) (pre rest : List InstanceId) (c : InstanceId) (ci : Instance) (o : Opener)
    (hp : ∀ r ∈ pre, r ≠ resource ∧ ∀ i, s.machine? r = some i → ∀ o, i.opener = some o → o.modal = false)
    (hc : s.machine? c = some ci) (hn : c ≠ resource) (ho : ci.opener = some o) (hm : o.modal = true) :
    State.accepting.go s resource (pre ++ c :: rest) = .error (.covered ci.chart.name) := by
  rw [accepting_skips resource pre (c :: rest) hp, State.accepting.go]
  have hn' : (c == resource) = false := by simpa using hn
  simp [hc, hn', ho, hm]

/--
The operated instance `resource` accepts when only non-modal instances were opened after it, whatever their charts, so
several open instances of one screen are each operable (B13).
-/
theorem nonmodal_child_lets_parent (resource : InstanceId) (pre rest : List InstanceId) (pi : Instance)
    (hp : ∀ r ∈ pre, r ≠ resource ∧ ∀ i, s.machine? r = some i → ∀ o, i.opener = some o → o.modal = false)
    (hpi : s.machine? resource = some pi) :
    State.accepting.go s resource (pre ++ resource :: rest) = .ok pi := by
  rw [accepting_skips resource pre (resource :: rest) hp, State.accepting.go]
  simp [hpi]

theorem accepts_iff (resource : InstanceId) (control : String) (payload : Value) (top : Instance) :
    acceptsOperation fs st s resource control payload = .ok (.ok top) ↔
      s.accepting resource = .ok top ∧ ∃ applied, offered fs st s top control payload = .ok applied ∧
        applied.any (·.2.admits payload) = true := by
  unfold acceptsOperation
  constructor
  · intro h
    split at h
    · cases h
    · rename_i top' ha
      simp only [id_bind] at h
      split at h
      · cases h
      · rename_i applied ho
        split at h
        · rename_i hl
          cases h
          exact ⟨ha, applied, ho, hl⟩
        · cases h
  · rintro ⟨ha, applied, ho, hl⟩
    simp only [ha, id_bind, ho, hl, ↓reduceIte, id_pure]

theorem foldlM_zip {α β ε : Type} (f : Except ε (List β) → α → Id (Except ε (List β))) (R : β → α → Prop)
    (herr : ∀ v x, f (.error v) x = .error v) (hok : ∀ done x r, f (.ok done) x = .ok r → ∃ p, r = done ++ [p] ∧ R p x) :
    ∀ (l : List α) (acc : Except ε (List β)) (r : List β), l.foldlM f acc = .ok r →
      ∃ done rest, acc = .ok done ∧ r = done ++ rest ∧ rest.length = l.length ∧ ∀ p ∈ rest.zip l, R p.1 p.2
  | [], acc, r, h => ⟨r, [], by simpa using h, by simp, rfl, by simp⟩
  | x :: l, acc, r, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨done', rest, hacc', rfl, hl, hf⟩ := foldlM_zip f R herr hok l _ r h
    cases acc with
    | error v => simp [herr] at hacc'
    | ok done =>
      obtain ⟨p, rfl, hp⟩ := hok done x done' hacc'
      refine ⟨done, p :: rest, rfl, by simp, by simp [hl], ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp
      · exact hf q hq

end Tazuna.Thm.Service.Screen.Operable
