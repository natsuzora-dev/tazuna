import Tazuna.Service.Screen.Operable
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Service.Screen.Operable

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem accepting_skips (screen : String) (pre rest : List String)
    (hp : ∀ r ∈ pre, ∀ i, s.machine? r = some i → i.chart.name ≠ screen ∧ ∀ o, i.opener = some o → o.modal = false) :
    State.accepting.go s screen (pre ++ rest) = State.accepting.go s screen rest := by
  induction pre with
  | nil => rfl
  | cons r pre ih =>
    simp only [List.cons_append]
    have hr := hp r List.mem_cons_self
    conv => lhs; rw [State.accepting.go]
    rw [ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))]
    cases hm : s.machine? r with
    | none => rfl
    | some i =>
      obtain ⟨hn, ho⟩ := hr i hm
      have hn' : (i.chart.name == screen) = false := by simpa using hn
      simp only [hn', Bool.false_eq_true, ↓reduceIte]
      cases hop : i.opener with
      | none => rfl
      | some o => simp [ho o hop]

theorem modal_child_covers (screen : String) (pre rest : List String) (c : String) (ci : Instance) (o : Opener)
    (hp : ∀ r ∈ pre, ∀ i, s.machine? r = some i → i.chart.name ≠ screen ∧ ∀ o, i.opener = some o → o.modal = false)
    (hc : s.machine? c = some ci) (hn : ci.chart.name ≠ screen) (ho : ci.opener = some o) (hm : o.modal = true) :
    State.accepting.go s screen (pre ++ c :: rest) = .error (.covered ci.chart.name) := by
  rw [accepting_skips screen pre (c :: rest) hp, State.accepting.go]
  have hn' : (ci.chart.name == screen) = false := by simpa using hn
  simp [hc, hn', ho, hm]

theorem nonmodal_child_lets_parent (screen : String) (pre rest : List String) (p : String) (pi : Instance)
    (hp : ∀ r ∈ pre, ∀ i, s.machine? r = some i → i.chart.name ≠ screen ∧ ∀ o, i.opener = some o → o.modal = false)
    (hpi : s.machine? p = some pi) (hn : pi.chart.name = screen) :
    State.accepting.go s screen (pre ++ p :: rest) = .ok pi := by
  rw [accepting_skips screen pre (p :: rest) hp, State.accepting.go]
  simp [hpi, hn]

theorem accepts_iff (screen control : String) (payload : Value) (top : Instance) :
    acceptsOperation fs st s screen control payload = .ok (.ok top) ↔
      s.accepting screen = .ok top ∧ ∃ applied, offered fs st s top control payload = .ok applied ∧
        (applied = [] ∨ applied.any (·.2.contains payload) = true) := by
  unfold acceptsOperation
  constructor
  · intro h
    split at h
    · cases h
    · rename_i top' ha
      simp only [id_bind] at h
      split at h
      · cases h
      · rename_i ho
        cases h
        exact ⟨ha, [], ho, Or.inl rfl⟩
      · rename_i applied hn ho
        split at h
        · rename_i hl
          cases h
          exact ⟨ha, applied, ho, Or.inr hl⟩
        · cases h
  · rintro ⟨ha, applied, ho, hl⟩
    simp only [ha, id_bind, ho]
    rcases hl with rfl | hl
    · rfl
    · cases applied with
      | nil => simp at hl
      | cons x xs =>
        simp only [hl, ↓reduceIte, id_pure]

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
