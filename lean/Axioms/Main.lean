import Lean.Util.CollectAxioms
import Lean.Util.Path
import Lean.CoreM

open Lean

/-- The axioms a proof in `Tazuna` may use. A `sorry` elaborates to the axiom `sorryAx`, so it fails too. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The modules of the `Tazuna` library, found as lakefile.toml's glob `Tazuna.+` finds them. -/
def modules : IO (Array Name) := do
  let files ← System.FilePath.walkDir "Tazuna"
  return files.filterMap fun f =>
    if f.extension == some "lean" then
      some <| (f.withExtension "").components.foldl Name.str .anonymous
    else none

/-- The entry point, run in `lean/` after `lake build`. It exits 1 when a constant of `Tazuna` uses another axiom. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules ((← modules).map ({ module := · })) {} (leakEnv := true) (loadExts := true)
  let check : CoreM (Array (Name × Array Name)) := do
    let mut bad := #[]
    for (name, _) in env.constants.map₁.toList do
      let some idx := env.getModuleIdxFor? name | continue
      unless (`Tazuna).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
      let axioms := (← collectAxioms name).filter (!allowed.contains ·)
      unless axioms.isEmpty do bad := bad.push (name, axioms)
    return bad
  let (bad, _) ← check.toIO { fileName := "", fileMap := default } { env }
  for (name, axioms) in bad.qsort (·.1.lt ·.1) do
    IO.eprintln s!"tazuna-axioms: {privateToUserName name} depends on {axioms.toList}."
  return if bad.isEmpty then 0 else 1
