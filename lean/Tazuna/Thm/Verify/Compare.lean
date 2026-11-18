import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

/-- A restart ends every subscription, so no answer after it is dropped as a repeat of an answer before it. -/
theorem restart_ends_subscriptions (l : Line) (id : String) (ls : List (Option Line)) (o : List (String × Option String))
    (h : l.body = .restart .in id) :
    withoutRepeatedAnswers.go (some l :: ls) o = some l :: withoutRepeatedAnswers.go ls [] := by
  simp [withoutRepeatedAnswers.go, h]

end Tazuna.Thm.Verify.Compare
