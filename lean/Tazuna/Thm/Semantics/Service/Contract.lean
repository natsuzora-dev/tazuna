import Tazuna.Semantics.Service.Contract
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Semantics.Service.Contract

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id}

theorem firstFalse_eq_some_iff (test : String → Id (Except Issue Bool)) (ns : List String) (n : String) :
    firstFalse test ns = .ok (some n) ↔
      ∃ pre post, ns = pre ++ n :: post ∧ (∀ x ∈ pre, test x = .ok true) ∧ test n = .ok false := by
  induction ns with
  | nil => simp [firstFalse]
  | cons x xs ih =>
    simp only [firstFalse, id_bind]
    rcases hx : test x with e | _ | _
    · simp only [id_pure, reduceCtorEq, false_iff]
      rintro ⟨pre, post, he, hp, hn⟩
      cases pre with
      | nil => injection he with h₁; subst h₁; rw [hx] at hn; cases hn
      | cons y ys => injection he with h₁ _; rw [hp x (by rw [h₁]; exact List.mem_cons_self ..)] at hx; cases hx
    · simp only [id_pure]
      constructor
      · intro h
        injection h with h
        injection h with h
        subst h
        exact ⟨[], xs, rfl, by simp, hx⟩
      · rintro ⟨pre, post, he, hp, hn⟩
        cases pre with
        | nil => injection he with h₁; rw [h₁]
        | cons y ys =>
          injection he with h₁ _
          rw [hp x (by rw [h₁]; exact List.mem_cons_self ..)] at hx; cases hx
    · rw [ih]
      constructor
      · rintro ⟨pre, post, he, hp, hn⟩
        refine ⟨x :: pre, post, by rw [he]; rfl, fun z hz => ?_, hn⟩
        rcases List.mem_cons.mp hz with h | h
        · rw [h]; exact hx
        · exact hp z h
      · rintro ⟨pre, post, he, hp, hn⟩
        cases pre with
        | nil => injection he with h₁; subst h₁; rw [hx] at hn; cases hn
        | cons y ys =>
          injection he with h₁ h₂
          exact ⟨ys, post, h₂, fun z hz => hp z (List.mem_cons_of_mem _ hz), hn⟩

theorem firstFalse_eq_none_iff (test : String → Id (Except Issue Bool)) (ns : List String) :
    firstFalse test ns = .ok none ↔ ∀ x ∈ ns, test x = .ok true := by
  induction ns with
  | nil => simp [firstFalse]
  | cons x xs ih =>
    simp only [firstFalse, id_bind, List.mem_cons, forall_eq_or_imp]
    rcases test x with e | _ | _
    · simp
    · simp only [id_pure]
      exact ⟨fun h => (by cases h), fun h => (by cases h.1)⟩
    · simp [ih]

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

theorem missing_ref_rejected_not_found (records : Records) (now : Time) (name : String) (input : Value)
    (hm : (missingRef st records input (st.requirementsOf name).refs).missing = true) :
    requirementsRejection st fs records now name input = .ok (some { kind := .notFound }) := by
  simp [requirementsRejection, hm]

theorem requirementsRejection_of_refs (records : Records) (now : Time) (name : String) (input : Value)
    (hm : (missingRef st records input (st.requirementsOf name).refs).missing = false) :
    requirementsRejection st fs records now name input =
      match firstFalse (fun b => fs.binding name b input records now) (st.requirementsOf name).binds with
      | .error e => .error (issueViolation st (st.ref name) e)
      | .ok (some b) => .ok (some { kind := .requires, reason := some b })
      | .ok none =>
        match firstFalse (fun c => fs.requirement name c input records now) (st.requirementsOf name).requires with
        | .error e => .error (issueViolation st (st.ref name) e)
        | .ok (some c) => .ok (some { kind := .requires, reason := some c })
        | .ok none => .ok none := by
  simp only [requirementsRejection, hm, Bool.false_eq_true, ↓reduceIte, id_bind]
  rfl

theorem unbound_rejected_with_first_null_binds (records : Records) (now : Time) (name : String) (input : Value)
    (b : String) (pre post : List String) (hm : (missingRef st records input (st.requirementsOf name).refs).missing = false)
    (hb : (st.requirementsOf name).binds = pre ++ b :: post)
    (hpre : ∀ x ∈ pre, fs.binding name x input records now = .ok true)
    (hn : fs.binding name b input records now = .ok false) :
    requirementsRejection st fs records now name input = .ok (some { kind := .requires, reason := some b }) := by
  rw [requirementsRejection_of_refs records now name input hm,
    (firstFalse_eq_some_iff _ _ b).mpr ⟨pre, post, hb, hpre, hn⟩]

theorem failed_requires_rejected_with_first_failing (records : Records) (now : Time) (name : String) (input : Value)
    (c : String) (pre post : List String) (hm : (missingRef st records input (st.requirementsOf name).refs).missing = false)
    (hb : ∀ x ∈ (st.requirementsOf name).binds, fs.binding name x input records now = .ok true)
    (hr : (st.requirementsOf name).requires = pre ++ c :: post)
    (hpre : ∀ x ∈ pre, fs.requirement name x input records now = .ok true)
    (hn : fs.requirement name c input records now = .ok false) :
    requirementsRejection st fs records now name input = .ok (some { kind := .requires, reason := some c }) := by
  rw [requirementsRejection_of_refs records now name input hm,
    (firstFalse_eq_none_iff _ _).mpr hb, (firstFalse_eq_some_iff _ _ c).mpr ⟨pre, post, hr, hpre, hn⟩]

theorem failed_ensures_blames_command (name : String) (input : Value) (before after : Records) (now : Time) (c : String)
    (he : fs.ensures name input before after now = .ok (some c)) :
    commandEnsures st fs name input before after now = [.failedEnsures (st.ref name) c] := by
  simp [commandEnsures, he, Service.failedEnsures]

theorem met_ensures_reports_nothing (name : String) (input : Value) (before after : Records) (now : Time)
    (he : fs.ensures name input before after now = .ok none) : commandEnsures st fs name input before after now = [] := by
  simp [commandEnsures, he]

end Tazuna.Thm.Semantics.Service.Contract
