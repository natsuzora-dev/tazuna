import Tazuna.Service.Functions
import Tazuna.Thm.Data.Basic

namespace Tazuna.Thm.Service.Functions

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic

variable {st : Service} {fs : Functions Id}

theorem issueViolation_halts (owner : Spec.Ref) (e : Issue) (mismatch : Schema → Fault)
    (hm : ∀ s, (mismatch s).halts = true) : (issueViolation owner e mismatch).halts = true := by
  unfold issueViolation
  split
  all_goals first | rfl | exact hm _

theorem issueViolation_halts_default (owner : Spec.Ref) (e : Issue) :
    (issueViolation owner e).halts = true :=
  issueViolation_halts owner e _ fun _ => rfl

theorem not_issue_of_not_halts {owner : Spec.Ref} {e : Issue} {mismatch : Schema → Fault}
    (hm : ∀ s, (mismatch s).halts = true) {f : Fault} (hr : f.halts = false)
    (h : f = issueViolation owner e mismatch) : False := by
  have hh := issueViolation_halts owner e mismatch hm
  rw [← h, hr] at hh
  cases hh

end Tazuna.Thm.Service.Functions
