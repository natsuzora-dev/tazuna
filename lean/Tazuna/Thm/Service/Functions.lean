import Tazuna.Service.Functions
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Service.Functions

open Tazuna.Data Tazuna.Semantics
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id}

theorem issueViolation_halts (owner : Syntax.Ref) (e : Issue) (mismatch : Schema → Fault)
    (hm : ∀ s, (mismatch s).halts = true) : (issueViolation st owner e mismatch).halts = true := by
  unfold issueViolation
  split
  all_goals first | rfl | exact hm _

theorem issueViolation_halts_default (owner : Syntax.Ref) (e : Issue) :
    (issueViolation st owner e).halts = true :=
  issueViolation_halts owner e _ fun _ => rfl

theorem not_issue_of_not_halts {owner : Syntax.Ref} {e : Issue} {mismatch : Schema → Fault}
    (hm : ∀ s, (mismatch s).halts = true) {f : Fault} (hr : f.halts = false)
    (h : f = issueViolation st owner e mismatch) : False := by
  have hh := issueViolation_halts (st := st) owner e mismatch hm
  rw [← h, hr] at hh
  cases hh

def NormalizedEmit (st : Service) (fs : Functions Id) (e o : Emit) : Prop :=
  o.event = e.event ∧ fs.normalize (.payload e.event) (st.sorted (.payload e.event) e.payload) = .ok (some o.payload)

theorem normalizeEmits_fold (name : String) (es : List Emit) (done out : List Emit)
    (h : (es.foldlM (m := Id) (init := (.ok done : Except Fault (List Emit))) fun acc e => do
        match acc with
        | .error r => pure (.error r)
        | .ok done =>
          match ← fs.normalize (.payload e.event) (st.sorted (.payload e.event) e.payload) with
          | .error i => pure (.error (issueViolation st (st.ref name) i))
          | .ok (some payload) => pure (.ok (done ++ [{ e with payload }]))
          | .ok none => pure (.error (.emittedPayloadSchema (st.ref name) (st.refOf e.event)))) =
        .ok out) :
    ∃ os, out = done ++ os ∧ os.length = es.length ∧ ∀ p ∈ es.zip os, NormalizedEmit st fs p.1 p.2 := by
  induction es generalizing done with
  | nil =>
    simp only [List.foldlM_nil, id_pure] at h
    injection h with h
    exact ⟨[], by simp [h], rfl, by simp⟩
  | cons e es ih =>
    simp only [List.foldlM_cons, id_bind] at h
    cases hn : fs.normalize (.payload e.event) (st.sorted (.payload e.event) e.payload) with
    | error i =>
      simp only [hn, id_pure] at h
      rw [foldlM_error _ (fun v x => rfl)] at h
      cases h
    | ok o =>
      cases o with
      | none =>
        simp only [hn, id_pure] at h
        rw [foldlM_error _ (fun v x => rfl)] at h
        cases h
      | some payload =>
        simp only [hn, id_pure] at h
        obtain ⟨os, ho, hl, hp⟩ := ih _ h
        refine ⟨{ e with payload } :: os, by simp [ho], by simp [hl], ?_⟩
        intro p hp'
        simp only [List.zip_cons_cons, List.mem_cons] at hp'
        rcases hp' with rfl | hp'
        · exact ⟨rfl, hn⟩
        · exact hp p hp'

end Tazuna.Thm.Service.Functions
