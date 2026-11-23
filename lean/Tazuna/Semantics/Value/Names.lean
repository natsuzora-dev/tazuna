import Lean.Elab.Term

open Lean Elab Term in
/-- `constructorNames% T` elaborates to the constructor names of inductive type `T`, in declaration order. -/
elab "constructorNames% " t:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo t
  let some (.inductInfo info) := (← getEnv).find? name | throwError "{name} is not an inductive type"
  return toExpr (info.ctors.map fun c => c.componentsRev.head!.toString)

open Lean Elab Term Meta in
/-- `samples% T` elaborates to one value per constructor of `T`, with `default` arguments, in declaration order. -/
elab "samples% " t:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo t
  let some (.inductInfo info) := (← getEnv).find? name | throwError "{name} is not an inductive type"
  let values ← info.ctors.mapM fun c => do
    forallTelescope (← getConstInfoCtor c).type fun args _ => do
      let defaults ← args.mapM fun a => do mkAppOptM ``Inhabited.default #[← inferType a, none]
      pure (mkAppN (mkConst c) defaults)
  mkListLit (mkConst name) values
