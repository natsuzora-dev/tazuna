import Tazuna.Semantics.Service.Functions
import Tazuna.Thm.Semantics.Value.Basic
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Semantics.Service.Functions

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Service
open Tazuna.Thm.Semantics.Value.Basic

variable {st : Service} {fs : Functions Id}

theorem issueViolation_halts (owner : Ir.Ref) (e : Issue) (mismatch : Schema → Fault)
    (hm : ∀ s, (mismatch s).halts = true) : (issueViolation owner e mismatch).halts = true := by
  unfold issueViolation
  split
  all_goals first | rfl | exact hm _

theorem issueViolation_halts_default (owner : Ir.Ref) (e : Issue) :
    (issueViolation owner e).halts = true :=
  issueViolation_halts owner e _ fun _ => rfl

theorem not_issue_of_not_halts {owner : Ir.Ref} {e : Issue} {mismatch : Schema → Fault}
    (hm : ∀ s, (mismatch s).halts = true) {f : Fault} (hr : f.halts = false)
    (h : f = issueViolation owner e mismatch) : False := by
  have hh := issueViolation_halts owner e mismatch hm
  rw [← h, hr] at hh
  cases hh

theorem mapChecked_mem {α β : Type} (f : α → Id (Except Issue β)) :
    ∀ (xs : List α) (ys : List β), mapChecked f xs = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by
    simp only [mapChecked, pure] at h
    injection h with h
    subst h
    cases hy
  | x :: xs, ys, h, y, hy => by
    simp only [mapChecked, bind] at h
    split at h
    · cases h
    · rename_i z hz
      split at h
      · cases h
      · rename_i zs hzs
        injection h with h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, hz⟩
        · obtain ⟨x', hx', hf⟩ := mapChecked_mem f xs zs hzs y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

/-- What the sorting functions keep of a value that spec code made: the sorted value, as its schema parses it. -/
theorem checked_parses (schema : Schema) (v x : Value) (h : fs.checked st schema v = .ok x) :
    fs.parse schema (st.sorted (m := Id) schema v) = .ok (some x) := by
  simp only [Functions.checked, Functions.parseSorted, bind] at h
  split at h
  · rename_i hp
    injection h with h
    subst h
    exact hp
  · cases h
  · cases h

/--
What the sorting functions keep of a value that spec code made: the sorted value as its schema parses it, sorted again,
since parse may fill a default that the schema writes out of order.
-/
theorem sortingParse_checked (schema : Schema) (v x : Value) (h : (fs.sortingParse st).checked st schema v = .ok x) :
    ∃ y, fs.parse schema (st.sorted (m := Id) schema v) = .ok (some y) ∧ x = st.sorted (m := Id) schema y := by
  have hp := checked_parses (fs := fs.sortingParse st) schema v x h
  simp only [Functions.sortingParse, bind] at hp
  split at hp
  · rename_i y hy
    injection hp with hp
    injection hp with hp
    exact ⟨y, hy, hp.symm⟩
  · rename_i hn
    exact absurd hp (by simpa [pure] using hn x)

/--
Each event that the sorting decide answers is one that decide wrote. One that the command lists has its payload sorted,
as its event's schema parses it, and sorted again; an unlisted one keeps the payload that decide wrote.
-/
theorem sorting_decide_parsed (name : String) (input : Value) (caller : Caller) (records : Records) (now : Time)
    (groups : List (List Emit)) (h : (fs.sorting st).decide name input caller records now = .ok groups) :
    ∃ decided, fs.decide name input caller records now = .ok decided ∧
      ∀ g ∈ groups, ∀ o ∈ g, ∃ d ∈ decided, ∃ e ∈ d,
        if st.lists name e then
          o.event = e.event ∧ ∃ y, fs.parse (.payload e.event) (st.sorted (m := Id) (.payload e.event) e.payload) =
            .ok (some y) ∧ o.payload = st.sorted (m := Id) (.payload e.event) y
        else o = e := by
  simp only [Functions.sorting, bind] at h
  split at h
  · cases h
  · rename_i decided hd
    refine ⟨decided, hd, fun g hg o ho => ?_⟩
    obtain ⟨d, hd', hdg⟩ := mapChecked_mem _ _ _ h g hg
    obtain ⟨e, he, heo⟩ := mapChecked_mem _ _ _ hdg o ho
    refine ⟨d, hd', e, he, ?_⟩
    split at heo
    · rename_i hl
      simp only [hl, ↓reduceIte]
      simp only [Except.map, pure] at heo
      split at heo
      · cases heo
      · rename_i payload hc
        injection heo with heo
        subst heo
        exact ⟨rfl, sortingParse_checked _ _ _ hc⟩
    · rename_i hl
      simp only [hl, Bool.false_eq_true, ↓reduceIte]
      injection heo with heo
      exact heo.symm

/-- A query's output is the sorted output of resolve, as its output schema parses it, sorted again. -/
@[guarantee] theorem sorting_resolve_parsed (name : String) (input : Value) (caller : Caller) (records : Records)
    (now : Time) (output : Value) (h : (fs.sorting st).resolve name input caller records now = .ok output) :
    ∃ raw, fs.resolve name input caller records now = .ok raw ∧
      ∃ y, fs.parse (.output (st.ref name)) (st.sorted (m := Id) (.output (st.ref name)) raw) = .ok (some y) ∧
        output = st.sorted (m := Id) (.output (st.ref name)) y := by
  simp only [Functions.sorting, bind] at h
  split at h
  · rename_i raw hr
    exact ⟨raw, hr, sortingParse_checked _ _ _ h⟩
  · cases h

end Tazuna.Thm.Semantics.Service.Functions
