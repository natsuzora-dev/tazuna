import Tazuna.Data.Derive
import Tazuna.Data.Value

/-!
This module derives JSON codecs from Lean types. The options are serde's container and field attributes of the same
names, and serde_with's `skip_serializing_none`. Generate writes the Zod schema from the same options.
-/

namespace Tazuna.Data

open Lean Elab Command

structure WireOptions where
  tag : Option String := none
  tagAfter : Option String := none
  kebabCase : Bool := false
  flatten : Option String := none
  skipSerializingNone : Bool := false
  tryFrom : Option Name := none
  untagged : Bool := false
deriving Inhabited

initialize wireOptions : MapDeclarationExtension WireOptions ← mkMapDeclarationExtension

def kebabCase (name : String) : String :=
  String.join (name.toList.map fun c => if c.isUpper then "-" ++ c.toLower.toString else c.toString)

/--
A field as the JSON writes it. An `Option` field is null when it is none, or absent under skip_serializing_none
(`optional`). A `flattened` field writes the fields of its value, of type `written`, in its place.
-/
inductive WireField where
  | required (name : String) (type : Expr)
  | optional (name : String) (type : Expr)
  | flattened (name : String) (written : Name)

def WireField.name : WireField → String
  | .required name _ | .optional name _ | .flattened name _ => name

/-- A constructor as the JSON writes it. `name` is the constructor's name, in kebab case under rename_all. -/
structure WireConstructor where
  ctor : Name
  name : String
  fields : List WireField

/--
The object field that holds the constructor's name, written first, or after the field `after`. serde always writes the
tag first; `after` keeps a fixed field order such as the trace line's `time, dir, type, id`.
-/
structure Tag where
  name : String
  after : Option String

/-- The fields written before the tag, and those written after it. -/
def Tag.split (tag : Tag) (fields : List WireField) : List WireField × List WireField :=
  match tag.after with
  | none => ([], fields)
  | some field =>
    let count := fields.findIdx (·.name == field) + 1
    (fields.take count, fields.drop count)

inductive WireShape where
  /-- A string: the constructor's name. -/
  | enum (ctors : List WireConstructor)
  /-- An object of the constructor's fields and the tag. -/
  | tagged (tag : Tag) (ctors : List WireConstructor)
  | object (ctor : Name) (fields : List WireField)
  /--
  An object of the fields of the first constructor that reads it, without a tag. No two constructors have the same
  field names.
  -/
  | untagged (ctors : List WireConstructor)
  /-- An object whose flattened field `body`, of a type with a tag, writes that tag and its constructor's fields. -/
  | flattened (ctor : Name) (before : List WireField) (body : WireField) (tag : Tag) (ctors : List WireConstructor)
      (after : List WireField)

/-- The type that `type` is written as: S under try_from S, or `type` itself. -/
def writtenAs {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (type : Name) : m Name := do
  let some options := wireOptions.find? (← getEnv) type | throwError "{type} has no derive_wire"
  pure (options.tryFrom.getD type)

def wireField {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (options : WireOptions) (field : String × Expr) :
    m WireField := do
  if options.flatten == some field.1 then
    let .const type _ := field.2 | throwError "{field.1}: a flatten field has a type with derive_wire"
    return .flattened field.1 (← writtenAs type)
  match field.2 with
  | .app (.const ``Option _) inner =>
    return if options.skipSerializingNone then .optional field.1 inner else .required field.1 field.2
  | type => return .required field.1 type

def wireConstructors {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (type : Name) (options : WireOptions) :
    m (List WireConstructor) := do
  (← constructors type).mapM fun ctor => do
    let name := if options.kebabCase then kebabCase ctor.getString! else ctor.getString!
    pure { ctor, name, fields := ← (← namedFields ctor).mapM (wireField options) }

def tagOf {m : Type → Type} [Monad m] [MonadError m] (name : String) (options : WireOptions)
    (ctors : List WireConstructor) : m Tag := do
  if let some field := options.tagAfter then
    for c in ctors do
      unless c.fields.any (·.name == field) do throwError "{c.ctor} has no field {field} for the tag to follow"
  return { name, after := options.tagAfter }

def isObject {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (type : Name) : m Bool := do
  let some options := wireOptions.find? (← getEnv) type | throwError "{type} has no derive_wire"
  return options.tag.isNone && options.flatten.isNone && (← constructors type).length == 1

/--
The one place that decides how `derive_wire` and the Zod schema write a type with derive_wire. Leaf types (`Option`,
`List`, and a `List` of key-value pairs) are written by their FromValue and ToValue instances and by `zodSchema`.
-/
def wireShape {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (type : Name) : m WireShape := do
  let some options := wireOptions.find? (← getEnv) type | throwError "{type} has no derive_wire"
  let ctors ← wireConstructors type options
  if options.untagged then
    unless options.tag.isNone && options.flatten.isNone do
      throwError "{type}: an untagged type has no tag or flatten field"
    let shapes := ctors.map fun c => (c.fields.map (·.name)).mergeSort (· ≤ ·)
    if shapes.eraseDups.length != shapes.length then throwError "{type}: two constructors have the same field names"
    return .untagged ctors
  if ctors.all (·.fields.isEmpty) then
    unless options.tag.isNone && options.flatten.isNone do throwError "{type}: a string has no tag or flatten field"
    return .enum ctors
  match options.tag, options.flatten, ctors with
  | some tag, none, _ => return .tagged (← tagOf tag options ctors) ctors
  | some tag, some field, _ =>
    unless ctors.any (·.fields.any (·.name == field)) do throwError "{type}.{field}: no such field"
    for c in ctors do
      for f in c.fields do
        if let .flattened _ written := f then
          unless ← isObject written do
            throwError "{c.ctor}.{field}: a flatten field of a constructor has an object type"
    return .tagged (← tagOf tag options ctors) ctors
  | none, none, [c] => return .object c.ctor c.fields
  | none, some body, [c] =>
    match c.fields.dropWhile (·.name != body) with
    | field@(.flattened _ bodyType) :: after =>
      let some bodyOptions := wireOptions.find? (← getEnv) bodyType | throwError "{bodyType} has no derive_wire"
      let some tag := bodyOptions.tag | throwError "{type}.{body}: a flatten field of a structure has a type with a tag"
      let bodyCtors ← wireConstructors bodyType bodyOptions
      return .flattened c.ctor (c.fields.takeWhile (·.name != body)) field (← tagOf tag bodyOptions bodyCtors) bodyCtors
        after
    | _ => throwError "{type}.{body}: no such field"
  | none, _, _ => throwError "{type}: a type with several constructors that take arguments needs a tag"

def expectObject (v : Value) : Except String Unit :=
  match v with
  | .obj _ => pure ()
  | _ => throw "expected an object"

def requiredField {α : Type} [FromValue α] (v : Value) (key : String) : Except String α :=
  match v.field? key with
  | some x => FromValue.fromValue x
  | none => throw s!"missing field {key}"

def optionalField {α : Type} [FromValue α] (v : Value) (key : String) : Except String (Option α) :=
  match v.field? key with
  | some x => some <$> FromValue.fromValue x
  | none => pure none

def requiredEntry {α : Type} [ToValue α] (key : String) (a : α) : List (String × Value) :=
  [(key, ToValue.toValue a)]

def optionalEntry {α : Type} [ToValue α] (key : String) : Option α → List (String × Value)
  | some a => [(key, ToValue.toValue a)]
  | none => []

def flattenedEntries {α : Type} [ToValue α] (a : α) : List (String × Value) :=
  match ToValue.toValue a with
  | .obj fields => fields
  | _ => []

declare_syntax_cat wireOption (behavior := symbol)
syntax &"tag" str (&"after" ident)? : wireOption
syntax &"rename_all" str : wireOption
syntax &"flatten" ident : wireOption
syntax &"skip_serializing_none" : wireOption
syntax &"try_from" ident : wireOption
syntax &"untagged" : wireOption

def wireOptionsOf (options : Array (TSyntax `wireOption)) : CommandElabM WireOptions :=
  options.foldlM (init := {}) fun o option => do
    match option with
    | `(wireOption| tag $s:str $[after $f:ident]?) =>
      pure { o with tag := some s.getString, tagAfter := f.map (·.getId.toString) }
    | `(wireOption| rename_all $s:str) =>
      unless s.getString == "kebab-case" do throwErrorAt s "rename_all supports only \"kebab-case\""
      pure { o with kebabCase := true }
    | `(wireOption| flatten $f:ident) => pure { o with flatten := some f.getId.toString }
    | `(wireOption| skip_serializing_none) => pure { o with skipSerializingNone := true }
    | `(wireOption| try_from $t:ident) =>
      pure { o with tryFrom := some (← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)) }
    | `(wireOption| untagged) => pure { o with untagged := true }
    | _ => throwErrorAt option "unknown option"

def decodeField (v : Ident) : WireField → CommandElabM Term
  | .required name _ => `(requiredField $v $(quote name))
  | .optional name _ => `(optionalField $v $(quote name))
  | .flattened _ _ => `(FromValue.fromValue $v)

def encodeEntry : WireField → CommandElabM Term
  | .required name _ => `(requiredEntry $(quote name) $(mkIdent (.mkSimple name)))
  | .optional name _ => `(optionalEntry $(quote name) $(mkIdent (.mkSimple name)))
  | .flattened name _ => `(flattenedEntries $(mkIdent (.mkSimple name)))

def applied (ctor : Name) (args : List Term) : CommandElabM Term := do
  args.foldlM (init := ← `(pure $(mkIdent ctor))) fun acc arg => `($acc <*> $arg)

def objectInstances (self v : Ident) (ctor : Name) (decoded : List Term) (entries : List Term) : CommandElabM Unit := do
  let decode ← applied ctor decoded
  elabCommand (← `(instance : FromValue $self := ⟨fun $v:ident => do
    expectObject $v
    $decode:term⟩))
  let encodeAlt ← matchAlt ctor ((← namedFields ctor).map (·.1)) (← `(Value.obj (List.flatten [$(entries.toArray),*])))
  elabCommand (← `(instance : ToValue $self := ⟨fun $encodeAlt:matchAlt⟩))

/--
`derive_wire T options*` defines `FromValue T` and `ToValue T` in the shape that `wireShape` decides. A type with a
tag also gets `T.<tag>`, the constructor's name, in kebab case under rename_all. Under try_from S, T is a structure that
extends S with proofs: it is read as S and converted by `T.tryFrom : S → Except String T`, and written as its S.
-/
elab "derive_wire " t:ident options:wireOption* : command => do
  let type ← liftCoreM (realizeGlobalConstNoOverloadWithInfo t)
  let wire ← wireOptionsOf options
  modifyEnv (wireOptions.insert · type wire)
  let self := mkIdent type
  let v := mkIdent `v
  if let some source := wire.tryFrom then
    let tryFrom := mkIdent (`_root_ ++ type ++ `tryFrom)
    let toSource := mkIdent (`_root_ ++ type ++ .mkSimple s!"to{source.getString!}")
    elabCommand (← `(instance : FromValue $self := ⟨fun $v:ident => FromValue.fromValue $v >>= $tryFrom:ident⟩))
    elabCommand (← `(instance : ToValue $self := ⟨fun x => ToValue.toValue ($toSource:ident x)⟩))
    return
  match ← wireShape type with
  | .enum ctors =>
    let names := ", ".intercalate (ctors.map (·.name))
    let decodeAlts ← ctors.toArray.mapM fun c =>
      `(Lean.Parser.Term.matchAltExpr| | .str $(quote c.name) => pure $(mkIdent c.ctor):ident)
    let otherwise ← `(Lean.Parser.Term.matchAltExpr| | _ => throw $(quote s!"expected one of {names}"))
    elabCommand (← `(instance : FromValue $self := ⟨fun $(decodeAlts.push otherwise):matchAlt*⟩))
    let encodeAlts ← ctors.toArray.mapM fun c => do matchAlt c.ctor [] (← `(Value.str $(quote c.name)))
    elabCommand (← `(instance : ToValue $self := ⟨fun $encodeAlts:matchAlt*⟩))
  | .tagged tag ctors =>
    let decodeAlts ← ctors.toArray.mapM fun c => do
      let decoded ← applied c.ctor (← c.fields.mapM (decodeField v))
      `(Lean.Parser.Term.matchAltExpr| | $(quote c.name) => $decoded)
    let otherwise ← `(Lean.Parser.Term.matchAltExpr| | other => throw ($(quote s!"unknown {tag.name} ") ++ other))
    elabCommand (← `(instance : FromValue $self := ⟨fun $v:ident => do
      expectObject $v
      let name : String ← requiredField $v $(quote tag.name)
      (match name with $(decodeAlts.push otherwise):matchAlt*)⟩))
    let encodeAlts ← ctors.toArray.mapM fun c => do
      let (beforeTag, afterTag) := tag.split c.fields
      let entries := (← beforeTag.mapM encodeEntry) ++ [(← `(requiredEntry $(quote tag.name) $(quote c.name)))] ++
        (← afterTag.mapM encodeEntry)
      matchAlt c.ctor (c.fields.map (·.name)) (← `(Value.obj (List.flatten [$(entries.toArray),*])))
    elabCommand (← `(instance : ToValue $self := ⟨fun $encodeAlts:matchAlt*⟩))
    let nameAlts ← ctors.toArray.mapM fun c => matchAlt c.ctor [] (quote c.name)
    let nameOf := mkIdent (`_root_ ++ type ++ .mkSimple tag.name)
    elabCommand (← `(def $nameOf : $self → String := fun $nameAlts:matchAlt*))
  | .object ctor fields =>
    objectInstances self v ctor (← fields.mapM (decodeField v)) (← fields.mapM encodeEntry)
  | .untagged ctors =>
    let otherwise ← `(throw $(quote s!"expected the fields of a constructor of {type}"))
    let decode ← ctors.foldrM (init := otherwise) fun c rest => do
      `($(← applied c.ctor (← c.fields.mapM (decodeField v))) <|> $rest)
    elabCommand (← `(instance : FromValue $self := ⟨fun $v:ident => do
      expectObject $v
      $decode:term⟩))
    let encodeAlts ← ctors.toArray.mapM fun c => do
      let entries ← c.fields.mapM encodeEntry
      matchAlt c.ctor (c.fields.map (·.name)) (← `(Value.obj (List.flatten [$(entries.toArray),*])))
    elabCommand (← `(instance : ToValue $self := ⟨fun $encodeAlts:matchAlt*⟩))
  | .flattened ctor before body _ _ after =>
    let fields := before ++ [body] ++ after
    objectInstances self v ctor (← fields.mapM (decodeField v)) (← fields.mapM encodeEntry)

end Tazuna.Data
