import Tazuna.Data.Derive
import Tazuna.Data.Value

namespace Tazuna.Data

open Lean Elab Command

def kindName (group ctor : Name) : String := s!"{group.getString!}.{ctor.getString!}"

structure GroupFields where
  definition : Option Expr
  data : List (String × Expr)

def groupFields {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (ctor : Name) : m GroupFields := do
  let fields ← namedFields ctor
  pure { definition := fields.lookup "definition", data := fields.filter (·.1 != "definition") }

def objectOf (names : List String) : CommandElabM Term := do
  let fields ← names.mapM fun n => `(($(quote n), ToValue.toValue $(mkIdent (.mkSimple n))))
  `(Value.obj [$(fields.toArray),*])

/--
`derive_group T` defines `T.kind`, `"<last component of T>.<constructor>"`; `T.definition`, the constructor's argument
`definition`, or null when it has none; `T.data`, its other arguments keyed by name; and `T.toValue`,
`{kind, definition, data}`.
-/
elab "derive_group " t:ident : command => do
  let group ← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)
  let ctors ← constructors group
  let kindAlts ← ctors.toArray.mapM fun ctor => matchAlt ctor [] (quote (kindName group ctor))
  let definitionAlts ← ctors.toArray.mapM fun ctor => do
    match (← groupFields ctor).definition with
    | some _ => matchAlt ctor ["definition"] (← `(ToValue.toValue $(mkIdent `definition)))
    | none => matchAlt ctor [] (← `(Value.null))
  let dataAlts ← ctors.toArray.mapM fun ctor => do
    let names := (← groupFields ctor).data.map (·.1)
    matchAlt ctor names (← objectOf names)
  -- `group` is already fully qualified, and `def` prefixes the current namespace.
  let root := `_root_ ++ group
  let (kind, definition, data) := (mkIdent (root ++ `kind), mkIdent (root ++ `definition), mkIdent (root ++ `data))
  elabCommand (← `(def $kind : $(mkIdent group) → String := fun $kindAlts:matchAlt*))
  elabCommand (← `(def $definition : $(mkIdent group) → Value := fun $definitionAlts:matchAlt*))
  elabCommand (← `(def $data : $(mkIdent group) → Value := fun $dataAlts:matchAlt*))
  elabCommand (← `(def $(mkIdent (root ++ `toValue)) (v : $(mkIdent group)) : Value :=
    .obj [("kind", .str ($kind v)), ("definition", $definition v), ("data", $data v)]))

end Tazuna.Data
