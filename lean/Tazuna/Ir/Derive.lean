import Lean.Elab.Command

namespace Tazuna.Ir

open Lean Elab Command

/--
The arguments of constructor `ctor`, by name. It fails on an unnamed argument, since the argument's name is the field's
name.
-/
def namedFields {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (ctor : Name) : m (List (String × Expr)) := do
  let rec go : Expr → m (List (String × Expr))
    | .forallE n type body _ => do
      if n.hasMacroScopes then throwError "{ctor}: every argument needs a name, which names its field"
      if type.hasLooseBVars then throwError "{ctor}: an argument's type depends on another argument"
      pure ((n.toString (escape := false), type) :: (← go body))
    | _ => pure []
  go (← getConstInfoCtor ctor).type

def constructors {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (type : Name) : m (List Name) := do
  let some (.inductInfo info) := (← getEnv).find? type | throwError "{type} is not an inductive type"
  pure info.ctors

/--
The match alternative for `ctor` that binds each argument named in `bound` to a variable of its own name, and the
others to `_`.
-/
def matchAlt (ctor : Name) (bound : List String) (body : Term) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let pattern ← (← namedFields ctor).toArray.mapM fun (n, _) =>
    if bound.contains n then `($(mkIdent (.mkSimple n)):ident) else `(_)
  `(Lean.Parser.Term.matchAltExpr| | $(mkIdent ctor):ident $pattern* => $body)

end Tazuna.Ir
