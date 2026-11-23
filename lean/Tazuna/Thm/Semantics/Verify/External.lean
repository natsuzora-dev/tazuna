import Tazuna.Semantics.Verify.External

namespace Tazuna.Thm.Semantics.Verify.External

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Verify

/-- The value that TS `byLine` sorts violations by. -/
def lineOf : Finding → Option Value
  | .mismatch m => m.place.lookup "line"
  | .uncomparable u => u.place.lookup "line"

end Tazuna.Thm.Semantics.Verify.External
