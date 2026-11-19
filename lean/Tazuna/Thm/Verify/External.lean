import Tazuna.Verify.External

namespace Tazuna.Thm.Verify.External

open Tazuna.Data Tazuna.Spec Tazuna.Verify

/-- The value that TS `byLine` sorts violations by. -/
def lineOf : Finding → Option Value
  | .mismatch m => m.place.lookup "line"
  | .uncomparable u => u.place.lookup "line"
  | .after line .. => some (ToValue.toValue line)

end Tazuna.Thm.Verify.External
