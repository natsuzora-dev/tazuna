import Lean.Elab.Command
import Lean.Elab.InfoTree.Util
import Lean.Linter.Basic

/-! The `silentDefault` linter flags every reference to a `getD` or `headD` function. Its fallback stands in for a
missing value without saying so, where a width or membership proof would make the value total. A use whose default
has a meaning, such as `none` meaning no entries, stays behind `set_option linter.tazuna.silentDefault false in`
with a comment that gives the meaning. -/

namespace Tazuna.Linter

open Lean Elab Command

register_option linter.tazuna.silentDefault : Bool := {
  defValue := true
  descr := "flag getD and headD, whose fallback stands in for a missing value"
}

/-- Whether the constant is a `getD` or `headD` of any namespace, such as `List.getD` or `Option.getD`. -/
def silentDefault? : Name → Bool
  | .str _ s => s == "getD" || s == "headD"
  | _ => false

def silentDefaultLinter : Linter where
  run := withSetOptionIn fun _ => do
    unless Linter.getLinterValue linter.tazuna.silentDefault (← Linter.getLinterOptions) do return
    if (← MonadLog.hasErrors) then return
    let mut seen : Std.HashSet String.Pos.Raw := {}
    for tree in ← getInfoTrees do
      let refs : Array (Syntax × Name) := tree.foldInfo (init := #[]) fun _ info acc =>
        match info with
        | .ofTermInfo ti =>
          match ti.expr with
          | .const n _ => if silentDefault? n then acc.push (ti.stx, n) else acc
          | _ => acc
        | _ => acc
      for (stx, n) in refs do
        let some pos := stx.getPos? (canonicalOnly := true) | continue
        if seen.contains pos then continue
        seen := seen.insert pos
        Linter.logLint linter.tazuna.silentDefault stx
          m!"`{n}` falls back to a default where the value is missing. Make the value total (a Fin index, a \
          length-indexed list, a proof of membership), or say what the default means."

initialize addLinter silentDefaultLinter

end Tazuna.Linter
