import Tazuna.Thm.Data.Trace
import Tazuna.Verify.Prepare

namespace Tazuna.Thm.Verify.Prepare

open Tazuna.Data Tazuna.Syntax Tazuna.Thm.Data.Trace Tazuna.Verify

theorem verifyLines_after_malformed {m : Type → Type} [Monad m] (s : Structure) (service : String)
    (ask : Definition → Part → Value → m CValue) (snapshot : List (Option TraceLine))
    (pre post₁ post₂ : List (FileLine TraceLine)) :
    verifyLines s service ask snapshot (pre ++ .malformed :: post₁) =
      verifyLines s service ask snapshot (pre ++ .malformed :: post₂) := by
  simp only [verifyLines, untilMalformed_append_malformed]

end Tazuna.Thm.Verify.Prepare
