import Lean.Util.Path
import Lean.CoreM

open Lean

/-- Components Lean generates under a declaration: equation lemmas, matchers, proof and recursion helpers. -/
def generated (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" ||
  ["induct", "mutual_induct", "fun_cases", "brecOn", "below", "binductionOn", "rec", "recOn",
   "casesOn", "noConfusion", "noConfusionType", "ibelow", "sizeOf_spec", "inj", "injEq",
   "ctorIdx", "toCtorIdx", "ofNat", "toNat", "induct_unfolding", "eq_def", "partial_correctness",
   "fixpoint_induct", "elim", "ctorElim", "ctorElimType"].contains s

/-- The declaration a constant belongs to: its name with generated trailing components removed. -/
partial def owner (env : Environment) : Name → Name
  | n@(.str p s) => if generated s && env.contains p then owner env p else n
  | n => n

/-- The modules of the `Tazuna` library, found as lakefile.toml's glob `Tazuna.+` finds them. -/
def modules : IO (Array Name) := do
  let files ← System.FilePath.walkDir "Tazuna"
  return files.filterMap fun f =>
    if f.extension == some "lean" then
      some <| (f.withExtension "").components.foldl Name.str .anonymous
    else none

/--
The entry point, run in `lean/` after `lake build`. It prints one line per declaration of `Tazuna`: kind, module, name,
then the declarations of `Tazuna` that it uses. test/theorems.diff.ts reads it.
-/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules ((← modules).map ({ module := · })) {} (leakEnv := true) (loadExts := false)
  let inTazuna (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if (`Tazuna).isPrefixOf m then some m else none
  let mut uses : Std.HashMap Name (Name × String × Std.HashSet Name) := {}
  for (name, info) in env.constants.map₁.toList do
    let some m := inTazuna name | continue
    let o := owner env name
    let kind := match env.find? o with
      | some (.thmInfo _) => "theorem"
      | some (.defnInfo _) => "def"
      | some (.inductInfo _) => "inductive"
      | some (.ctorInfo _) => "ctor"
      | some (.opaqueInfo _) => "opaque"
      | some (.axiomInfo _) => "axiom"
      | _ => "other"
    let refs := (info.getUsedConstantsAsSet.toList.filterMap fun r =>
      if (inTazuna r).isSome then
        let ro := owner env r
        if ro == o then none else some ro
      else none)
    let (_, _, prev) := uses.getD o (m, kind, {})
    uses := uses.insert o (m, kind, refs.foldl (·.insert ·) prev)
  for (o, (m, kind, refs)) in uses.toList do
    IO.println s!"{kind}\t{m}\t{privateToUserName o}\t{" ".intercalate (refs.toList.map (toString ∘ privateToUserName))}"
