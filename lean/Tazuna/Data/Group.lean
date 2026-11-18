import Tazuna.Data.Wire

namespace Tazuna.Data

open Lean Elab Command

/--
A violation. `kind` is the group and the constructor, such as `Fault.exception`, and `definition` is the definition
that caused the violation, or null when the subject is no definition.
-/
structure Violation where
  kind : String
  definition : Value
  data : Value
deriving DecidableEq, Repr, Inhabited

derive_wire Violation

/-- The field that `derive_group T flatten f` names, by group. -/
initialize groupFlatten : MapDeclarationExtension String ← mkMapDeclarationExtension

/--
The names of the arguments that place a violation: the scenario and the line of the compared file. A report writes
them beside the data, in its `scenario` and `location`.
-/
def placeNames : List String := ["scenario", "line"]

/--
A kind of a group: a constructor, or, for a constructor with the flattened field `field`, a constructor `inner` of that
field's type, which the kind is named after.
-/
structure Member where
  ctor : Name
  inner : Option (String × Name) := none

def Member.named (m : Member) : Name := (m.inner.map (·.2)).getD m.ctor

def kindName (group : Name) (m : Member) : String := s!"{group.getString!}.{m.named.getString!}"

/-- The kinds of `group`, in declaration order, a flattened constructor's in its place. -/
def members {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (group : Name) : m (List Member) := do
  let flatten := groupFlatten.find? (← getEnv) group
  (← constructors group).flatMapM fun ctor => do
    let some field := flatten | return [{ ctor }]
    let some (_, .const type _) := (← namedFields ctor).find? (·.1 == field) | return [{ ctor }]
    return (← constructors type).map fun inner => { ctor, inner := some (field, inner) }

structure GroupFields where
  definition : Option Expr
  place : List (String × Expr)
  data : List (String × Expr)

/-- The arguments of `m`, the flattened field's replaced by the arguments of the inner constructor. -/
def memberArguments {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (member : Member) :
    m (List (String × Expr)) := do
  let fields ← namedFields member.ctor
  let some (field, inner) := member.inner | return fields
  return fields.filter (·.1 != field) ++ (← namedFields inner)

def groupFields {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (member : Member) : m GroupFields := do
  let fields ← memberArguments member
  pure {
    definition := fields.lookup "definition"
    place := fields.filter (·.1 ∈ placeNames)
    data := fields.filter fun (n, _) => n != "definition" && n ∉ placeNames }

/-- `matchAlt` for `member`, whose flattened field is matched against its inner constructor. -/
def memberAlt (member : Member) (bound : List String) (body : Term) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAlt) := do
  let bind (n : String) : CommandElabM Term :=
    if bound.contains n then `($(mkIdent (.mkSimple n)):ident) else `(_)
  let pattern ← (← namedFields member.ctor).toArray.mapM fun (n, _) => do
    match member.inner with
    | some (field, inner) =>
      if n == field then
        let innerPattern ← (← namedFields inner).toArray.mapM fun (n, _) => bind n
        `(($(mkIdent inner):ident $innerPattern*))
      else bind n
    | none => bind n
  `(Lean.Parser.Term.matchAltExpr| | $(mkIdent member.ctor):ident $pattern* => $body)

def fieldsOf (names : List String) : CommandElabM Term := do
  let fields ← names.mapM fun n => `(($(quote n), ToValue.toValue $(mkIdent (.mkSimple n))))
  `(([$(fields.toArray),*] : List (String × Value)))

def objectOf (names : List String) : CommandElabM Term := do
  `(Value.obj $(← fieldsOf names))

syntax groupOption := &"flatten" ident

/--
`derive_group T (flatten f)?` defines `T.kind`, `"<last component of T>.<constructor>"`; `T.definition`, the
constructor's argument `definition`, or null when it has none; `T.place`, its arguments named in `placeNames`, keyed by
name; `T.data`, its other arguments keyed by name; `T.line?`, its argument `line`, if any; `T.toValue`,
`{kind, definition, ...place, data}`, which is also `ToValue T`; and `T.toViolation`. Under `flatten f`, as in serde, a
constructor's argument `f` writes its own constructor in its place: the kind is named after that constructor, and its
arguments follow the others in the data.
-/
elab "derive_group " t:ident option:(groupOption)? : command => do
  let group ← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)
  if let some o := option then
    let `(groupOption| flatten $f:ident) := o | throwErrorAt o "unknown option"
    modifyEnv (groupFlatten.insert · group f.getId.toString)
  let members ← members group
  for member in members do
    let names := (← memberArguments member).map (·.1)
    if names.eraseDups.length != names.length then
      throwError "{member.ctor}: the flattened constructor {member.named} repeats an argument name"
  let kindAlts ← members.toArray.mapM fun member => memberAlt member [] (quote (kindName group member))
  let definitionAlts ← members.toArray.mapM fun member => do
    match (← groupFields member).definition with
    | some _ => memberAlt member ["definition"] (← `(ToValue.toValue $(mkIdent `definition)))
    | none => memberAlt member [] (← `(Value.null))
  let placeAlts ← members.toArray.mapM fun member => do
    let names := (← groupFields member).place.map (·.1)
    memberAlt member names (← fieldsOf names)
  let lineAlts ← members.toArray.mapM fun member => do
    if (← groupFields member).place.any (·.1 == "line") then memberAlt member ["line"] (← `(some $(mkIdent `line)))
    else memberAlt member [] (← `(none))
  let dataAlts ← members.toArray.mapM fun member => do
    let names := (← groupFields member).data.map (·.1)
    memberAlt member names (← objectOf names)
  -- `group` is already fully qualified, and `def` prefixes the current namespace.
  let root := `_root_ ++ group
  let (kind, definition, data) := (mkIdent (root ++ `kind), mkIdent (root ++ `definition), mkIdent (root ++ `data))
  let place := mkIdent (root ++ `place)
  elabCommand (← `(def $kind : $(mkIdent group) → String := fun $kindAlts:matchAlt*))
  elabCommand (← `(def $definition : $(mkIdent group) → Value := fun $definitionAlts:matchAlt*))
  elabCommand (← `(def $place : $(mkIdent group) → List (String × Value) := fun $placeAlts:matchAlt*))
  elabCommand (← `(def $data : $(mkIdent group) → Value := fun $dataAlts:matchAlt*))
  elabCommand (← `(def $(mkIdent (root ++ `line?)) : $(mkIdent group) → Option Nat := fun $lineAlts:matchAlt*))
  elabCommand (← `(def $(mkIdent (root ++ `toValue)) (v : $(mkIdent group)) : Value :=
    .obj ([("kind", .str ($kind v)), ("definition", $definition v)] ++ $place v ++ [("data", $data v)])))
  elabCommand (← `(instance : ToValue $(mkIdent group) := ⟨$(mkIdent (root ++ `toValue))⟩))
  elabCommand (← `(def $(mkIdent (root ++ `toViolation)) (v : $(mkIdent group)) : Violation :=
    { kind := $kind v, definition := $definition v, data := $data v }))

end Tazuna.Data
