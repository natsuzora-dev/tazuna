import Tazuna.Data.Derive
import Tazuna.Data.Value

namespace Tazuna.Data

open Lean Elab Command

def kindName (group ctor : Name) : String := s!"{group.getString!}.{ctor.getString!}"

/--
The names of the arguments that place a violation: the scenario and the line of the compared file. A report writes
them beside the data, in its `scenario` and `location`.
-/
def placeNames : List String := ["scenario", "line"]

structure GroupFields where
  definition : Option Expr
  place : List (String × Expr)
  data : List (String × Expr)

def groupFields {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (ctor : Name) : m GroupFields := do
  let fields ← namedFields ctor
  pure {
    definition := fields.lookup "definition"
    place := fields.filter (·.1 ∈ placeNames)
    data := fields.filter fun (n, _) => n != "definition" && n ∉ placeNames }

def fieldsOf (names : List String) : CommandElabM Term := do
  let fields ← names.mapM fun n => `(($(quote n), ToValue.toValue $(mkIdent (.mkSimple n))))
  `(([$(fields.toArray),*] : List (String × Value)))

def objectOf (names : List String) : CommandElabM Term := do
  `(Value.obj $(← fieldsOf names))

/--
`derive_group T` defines `T.kind`, `"<last component of T>.<constructor>"`; `T.definition`, the constructor's argument
`definition`, or null when it has none; `T.place`, its arguments named in `placeNames`, keyed by name; `T.data`, its
other arguments keyed by name; and `T.toValue`, `{kind, definition, ...place, data}`.
-/
elab "derive_group " t:ident : command => do
  let group ← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)
  let ctors ← constructors group
  let kindAlts ← ctors.toArray.mapM fun ctor => matchAlt ctor [] (quote (kindName group ctor))
  let definitionAlts ← ctors.toArray.mapM fun ctor => do
    match (← groupFields ctor).definition with
    | some _ => matchAlt ctor ["definition"] (← `(ToValue.toValue $(mkIdent `definition)))
    | none => matchAlt ctor [] (← `(Value.null))
  let placeAlts ← ctors.toArray.mapM fun ctor => do
    let names := (← groupFields ctor).place.map (·.1)
    matchAlt ctor names (← fieldsOf names)
  let dataAlts ← ctors.toArray.mapM fun ctor => do
    let names := (← groupFields ctor).data.map (·.1)
    matchAlt ctor names (← objectOf names)
  -- `group` is already fully qualified, and `def` prefixes the current namespace.
  let root := `_root_ ++ group
  let (kind, definition, data) := (mkIdent (root ++ `kind), mkIdent (root ++ `definition), mkIdent (root ++ `data))
  let place := mkIdent (root ++ `place)
  elabCommand (← `(def $kind : $(mkIdent group) → String := fun $kindAlts:matchAlt*))
  elabCommand (← `(def $definition : $(mkIdent group) → Value := fun $definitionAlts:matchAlt*))
  elabCommand (← `(def $place : $(mkIdent group) → List (String × Value) := fun $placeAlts:matchAlt*))
  elabCommand (← `(def $data : $(mkIdent group) → Value := fun $dataAlts:matchAlt*))
  elabCommand (← `(def $(mkIdent (root ++ `toValue)) (v : $(mkIdent group)) : Value :=
    .obj ([("kind", .str ($kind v)), ("definition", $definition v)] ++ $place v ++ [("data", $data v)])))

end Tazuna.Data
