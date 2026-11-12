import Tazuna.Semantics.Service.Contract
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Semantics.Service.Contract

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id}

theorem missingRef_iff (records : Records) (input : Value) (refs : List (String × Syntax.Ref)) :
    (missingRef st records input refs).missing = true ↔
      ∃ field r v, (field, r) ∈ refs ∧ r.service = st.service ∧ r.name ∈ st.entities ∧ input.field? field = some v ∧
        v ≠ .null ∧ records.any (fun row => row.entity == r.name && row.key == v.keyString) = false := by
  induction refs with
  | nil => simp [missingRef]
  | cons p rest ih =>
    obtain ⟨field, r⟩ := p
    let first : Prop := ∃ v, input.field? field = some v ∧ v ≠ .null ∧ r.service = st.service ∧ r.name ∈ st.entities ∧
      records.any (fun row => row.entity == r.name && row.key == v.keyString) = false
    have key : (missingRef st records input ((field, r) :: rest)).missing = true ↔
        first ∨ (missingRef st records input rest).missing = true := by
      simp only [missingRef, first]
      split
      · rename_i hf
        refine ⟨Or.inr, fun h => h.elim (fun ⟨v, hv, hn, _⟩ => ?_) id⟩
        rw [hf] at hv; cases hv
      · rename_i hf
        refine ⟨Or.inr, fun h => h.elim (fun ⟨v, hv, hn, _⟩ => ?_) id⟩
        rw [hf] at hv; injection hv with hv; exact absurd hv.symm hn
      · rename_i v hn hf
        by_cases hown : (r.service == st.service && decide (r.name ∈ st.entities)) = true
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hown
          simp only [hown, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
          by_cases hany : records.any (fun row => row.entity == r.name && row.key == v.keyString) = true
          · simp only [hany, ↓reduceIte]
            refine ⟨Or.inr, fun h => h.elim (fun ⟨w, hw, _, _, _, ha⟩ => ?_) id⟩
            rw [hf] at hw; injection hw with hw; subst hw; rw [hany] at ha; cases ha
          · simp only [hany, Bool.false_eq_true, ↓reduceIte, true_iff]
            exact Or.inl ⟨v, hf, hn, trivial, trivial, by simpa using hany⟩
        · simp only [hown, Bool.false_eq_true, ↓reduceIte]
          refine ⟨Or.inr, fun h => h.elim (fun ⟨w, hw, _, hs, he, _⟩ => ?_) id⟩
          simp [hs, he] at hown
    rw [key, ih]
    constructor
    · rintro (⟨v, hv, hn, hs, he, ha⟩ | ⟨f, r', v, hm, h⟩)
      · exact ⟨field, r, v, List.mem_cons_self .., hs, he, hv, hn, ha⟩
      · exact ⟨f, r', v, List.mem_cons_of_mem _ hm, h⟩
    · rintro ⟨f, r', v, hm, hs, he, hv, hn, ha⟩
      rcases List.mem_cons.mp hm with h | h
      · injection h with h₁ h₂; subst h₁ h₂; exact Or.inl ⟨v, hv, hn, hs, he, ha⟩
      · exact Or.inr ⟨f, r', v, h, hs, he, hv, hn, ha⟩

theorem failed_ensures_blames_command (name : String) (input : Value) (before after : Records) (now : Time) (c : String)
    (he : fs.ensures name input before after now = .ok (some c)) :
    commandEnsures st fs name input before after now = [.failedEnsures (st.ref name) c] := by
  simp [commandEnsures, he, Service.failedEnsures]

theorem met_ensures_reports_nothing (name : String) (input : Value) (before after : Records) (now : Time)
    (he : fs.ensures name input before after now = .ok none) : commandEnsures st fs name input before after now = [] := by
  simp [commandEnsures, he]

end Tazuna.Thm.Semantics.Service.Contract
