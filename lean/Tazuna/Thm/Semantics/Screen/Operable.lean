import Tazuna.Semantics.Screen.Operable
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Semantics.Screen.Operable

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

theorem not_accepted_without_instance (screen control : String) (payload : Value) (r : Refusal)
    (h : s.accepting screen = .error r) : acceptsOperation fs st s screen control payload = .ok (.error r) := by
  simp [acceptsOperation, h]

theorem innermost_has_no_offering_descendant (c : Chart) (found : List (Instance × String)) (x : Instance × String)
    (hx : x ∈ innermostOffers c found) :
    x ∈ found ∧ ∀ y ∈ found, y.2 ≠ x.2 → c.tree.isDescendant y.2 x.2 = false := by
  unfold innermostOffers at hx
  obtain ⟨hm, hn⟩ := List.mem_filter.mp hx
  refine ⟨hm, fun y hy hne => ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq,
    not_and, Bool.not_eq_true] at hn
  exact hn y hy hne

theorem deepest_offers_apply (c : Chart) (found : List (Instance × String)) (x : Instance × String) (hx : x ∈ found)
    (hd : ∀ y ∈ found, y.2 ≠ x.2 → c.tree.isDescendant y.2 x.2 = false) : x ∈ innermostOffers c found := by
  unfold innermostOffers
  refine List.mem_filter.mpr ⟨hx, ?_⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq,
    not_and, Bool.not_eq_true]
  exact fun y hy hne => hd y hy hne

theorem innermost_offers_applied (top : Instance) (control : String) (found : List (Instance × String))
    (h : innermostOffers top.chart found ≠ []) :
    appliedOffers top control found = (innermostOffers top.chart found).map fun (h, n) => (h, some n) := by
  have : (innermostOffers top.chart found).isEmpty = false := by
    cases e : innermostOffers top.chart found with
    | nil => exact absurd e h
    | cons _ _ => rfl
  simp [appliedOffers, this]

theorem root_offers_otherwise (top : Instance) (control : String) (found : List (Instance × String))
    (h : innermostOffers top.chart found = []) (hr : control ∈ top.chart.offers) :
    appliedOffers top control found = [(top, none)] := by
  simp [appliedOffers, h, hr]

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

theorem offered_lists_every_applied (top : Instance) (control : String) (payload : Value)
    (applied : List (Option String × List Value)) (h : offered fs st s top control payload = .ok applied) :
    ∃ found, offeringStates fs st s top control payload = .ok found ∧
      let l := appliedOffers top control found
      applied.length = l.length ∧
        ∀ p ∈ applied.zip l, p.1.1 = p.2.2 ∧ fs.offers (s.scopeOf p.2.1 p.2.2) s.records control = .ok p.1.2 := by
  unfold offered at h
  simp only [id_bind] at h
  split at h
  · cases h
  rename_i found hfound
  refine ⟨found, hfound, ?_⟩
  obtain ⟨done, rest, hd, rfl, hl, hf⟩ := foldlM_zip _
    (fun (a : Option String × List Value) (x : Instance × Option String) =>
      a.1 = x.2 ∧ fs.offers (s.scopeOf x.1 x.2) s.records control = .ok a.2) (fun _ _ => rfl) (fun done x r hx => by
    obtain ⟨holder, state⟩ := x
    simp only [pure] at hx
    split at hx
    · cases hx
    · rename_i payloads he
      cases hx
      exact ⟨_, rfl, rfl, he⟩) _ _ _ h
  cases hd
  exact ⟨by simpa using hl, by simpa using hf⟩

theorem accepting_go_ignores_pending (screen : String) (ps : List Pending) (l : List String) :
    State.accepting.go { s with pending := ps } screen l = State.accepting.go s screen l := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    rw [State.accepting.go, State.accepting.go, ih]
    rfl

theorem offeringStates_ignores_pending (top : Instance) (control : String) (payload : Value) (ps : List Pending) :
    offeringStates fs st { s with pending := ps } top control payload = offeringStates fs st s top control payload := rfl

theorem offered_ignores_pending (top : Instance) (control : String) (payload : Value) (ps : List Pending) :
    offered fs st { s with pending := ps } top control payload = offered fs st s top control payload := by
  unfold offered
  rw [offeringStates_ignores_pending]
  rfl

theorem accepting_ignores_pending (screen control : String) (payload : Value) (ps : List Pending) :
    acceptsOperation fs st { s with pending := ps } screen control payload = acceptsOperation fs st s screen control payload := by
  unfold acceptsOperation
  have ha : ({ s with pending := ps } : State).accepting screen = s.accepting screen :=
    accepting_go_ignores_pending screen ps _
  rw [ha]
  split
  · rfl
  · rw [offered_ignores_pending]

end Tazuna.Thm.Semantics.Screen.Operable
