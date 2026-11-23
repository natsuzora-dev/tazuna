import Lean.Attributes

namespace Tazuna.Thm.Guarantee

open Lean

/-- `@[guarantee]` marks a theorem that docs/guarantees.md cites as a guarantee. tazuna-codegen lists them for TS. -/
initialize guaranteeAttr : TagAttribute ←
  registerTagAttribute `guarantee "A theorem that docs/guarantees.md cites as a guarantee." fun name => do
    let .thmInfo _ ← getConstInfo name | throwError "@[guarantee] marks a theorem, and {name} is not one"

end Tazuna.Thm.Guarantee
